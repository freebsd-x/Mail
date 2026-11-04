// Mail.xapp — Native email client for FreeBSD-X
//
// Layout:
//   Left  (200px): Account selector + folder tree (Inbox/Sent/Drafts/Trash)
//   Middle(310px): Message list with unread indicator + From/Subject/Date
//   Right (flex):  Message viewer, or Compose form, or empty state
//
// Features:
//   • IMAP4 via libcurl (imaps:// or imap://) for header + body fetch
//   • SMTP / SMTPS via libcurl for sending
//   • Multi-account: persisted to ~/.freebsdx-mail/accounts (TSV)
//   • Message cache: ~/.freebsdx-mail/<acct_id>/<folder>/<uid>.eml
//   • Compose: To, CC, Subject, Body, file attachment via FileChooser portal
//   • MIME handler: message/rfc822 and x-scheme-handler/mailto
//   • LaunchWithFile opens .eml; mailto: URI pre-fills compose To + Subject

#include "xkit/widget.h"
#include "xkit/application.h"
#include "xkit/xbus_client.h"
#include "xkit/fetch.h"
#include "xkit/file_dialog.h"
#include "xkit/media_file.h"
#include "shared/protocol.h"
#include <curl/curl.h>
#include <memory>
#include <string>
#include <vector>
#include <cstring>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <functional>
#include <atomic>
#include <thread>
#include <mutex>
#include <filesystem>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/capsicum.h>
#include <sys/stat.h>
#include <ctime>

using namespace fbx::xkit;
using namespace fbx::shared;
namespace fs = std::filesystem;

// ── Data models ───────────────────────────────────────────────────────────────

struct MailAccount {
    std::string id;          // slug derived from email (dots/@ → _)
    std::string display_name;
    std::string email;
    std::string imap_host;
    uint16_t    imap_port{993};
    bool        imap_ssl{true};
    std::string smtp_host;
    uint16_t    smtp_port{587};
    bool        smtp_ssl{true};
    std::string username;
    std::string password;
};

struct MailMessage {
    uint32_t    uid{0};
    std::string from;
    std::string to;
    std::string cc;
    std::string subject;
    std::string date_str;
    std::string body;        // Plain-text body (decoded / stripped)
    bool        read{false};
    bool        has_attachment{false};
};

// ── Globals ───────────────────────────────────────────────────────────────────

static std::vector<MailAccount>     g_accounts;
static int                          g_active_account = -1;
static std::string                  g_active_folder  = "INBOX";
static std::vector<MailMessage>     g_messages;
static std::mutex                   g_msg_mutex;
static int                          g_selected_msg   = -1;
static std::atomic<bool>            g_syncing{false};
static XBusClient*                  g_xbus = nullptr;

// Forward declarations of UI rebuild hooks (set in main after widget creation)
static std::function<void()>        g_rebuild_msg_list;
static std::function<void()>        g_rebuild_right_pane;
static std::function<void()>        g_rebuild_folder_list;
static std::function<void(const std::string&)> g_open_compose;  // pre-fill mailto

// ── Persistence ───────────────────────────────────────────────────────────────

// The app is sandboxed: past start-up the one place it can reach on disk is its
// own folder, opened (and limited to it) before the sandbox begins. Holds the
// account passwords, so it's private to the user.
static int g_store = -1;

static void openStore() {
    const char* home = std::getenv("HOME");
    const std::string root = std::string(home ? home : "/tmp") + "/.freebsdx-mail";
    (void)::mkdir(root.c_str(), 0700);
    (void)::chmod(root.c_str(), 0700);
    g_store = ::open(root.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (g_store < 0) {
        std::cerr << "[Mail] can't open " << root << ": " << std::strerror(errno) << "\n";
        return;
    }
    cap_rights_t rights;
    cap_rights_init(&rights, CAP_LOOKUP, CAP_CREATE, CAP_READ, CAP_WRITE, CAP_SEEK, CAP_FTRUNCATE, CAP_FSTAT,
                    CAP_FSTATAT, CAP_FCNTL, CAP_FSYNC, CAP_MKDIRAT, CAP_RENAMEAT_SOURCE, CAP_RENAMEAT_TARGET);
    (void)cap_rights_limit(g_store, &rights);
}

static bool storeRead(const std::string& rel, std::string& out) {
    fbx::xserver::UniqueFd fd(::openat(g_store, rel.c_str(), O_RDONLY | O_CLOEXEC));
    return fd && readAllFd(fd.get(), out);
}

// All of it or none of it: written beside the file, then moved over it.
static bool storeWrite(const std::string& rel, const std::string& data) {
    const std::string tmp = rel + ".tmp";
    fbx::xserver::UniqueFd fd(::openat(g_store, tmp.c_str(), O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600));
    if (!fd) return false;
    for (size_t done = 0; done < data.size();) {
        const ssize_t n = ::write(fd.get(), data.data() + done, data.size() - done);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return false;
        done += static_cast<size_t>(n);
    }
    if (::fsync(fd.get()) != 0) return false;
    fd = {};
    return ::renameat(g_store, tmp.c_str(), g_store, rel.c_str()) == 0;
}

static std::vector<std::string> storeList(const std::string& rel) {
    std::vector<std::string> names;
    const int fd = ::openat(g_store, rel.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) return names;
    DIR* dir = ::fdopendir(fd);
    if (!dir) { ::close(fd); return names; }
    while (dirent* e = ::readdir(dir))
        names.emplace_back(e->d_name);
    ::closedir(dir);
    return names;
}

static std::string folderDir(const MailAccount& a, const std::string& folder) {
    return a.id + "/" + folder;
}

static void ensureDirs(const MailAccount& a) {
    (void)::mkdirat(g_store, a.id.c_str(), 0700);
    for (const char* f : {"INBOX", "Sent", "Drafts", "Trash"})
        (void)::mkdirat(g_store, folderDir(a, f).c_str(), 0700);
}

static uint32_t toUint(const std::string& s, uint32_t fallback = 0) {
    char* end = nullptr;
    const unsigned long v = std::strtoul(s.c_str(), &end, 10);
    return end != s.c_str() ? static_cast<uint32_t>(v) : fallback;
}

// A message as this app stores it: headers, a blank line, the body.
static MailMessage parseEml(const std::string& text) {
    MailMessage msg;
    std::istringstream f(text);
    std::string line;
    while (std::getline(f, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (line.empty()) break;
        const auto colon = line.find(':');
        if (colon == std::string::npos) continue;
        const std::string key = line.substr(0, colon);
        std::string val = line.substr(colon + 1);
        if (!val.empty() && val[0] == ' ') val.erase(0, 1);
        if (key == "From")         msg.from     = val;
        else if (key == "To")      msg.to       = val;
        else if (key == "CC")      msg.cc       = val;
        else if (key == "Subject") msg.subject  = val;
        else if (key == "Date")    msg.date_str = val;
        else if (key == "X-UID")   msg.uid      = toUint(val);
        else if (key == "X-Read")  msg.read     = (val == "1");
    }
    std::ostringstream body;
    while (std::getline(f, line)) body << line << '\n';
    msg.body = body.str();
    return msg;
}

// TSV format: id\tdisplay_name\temail\timap_host\timap_port\timap_ssl
//             \tsmtp_host\tsmtp_port\tsmtp_ssl\tusername\tpassword
static void loadAccounts() {
    g_accounts.clear();
    std::string text;
    if (!storeRead("accounts", text)) return;
    std::istringstream f(text);
    std::string line;
    while (std::getline(f, line)) {
        if (line.empty() || line[0] == '#') continue;
        std::istringstream ss(line);
        std::vector<std::string> cols;
        std::string tok;
        while (std::getline(ss, tok, '\t')) cols.push_back(tok);
        if (cols.size() < 11) continue;
        MailAccount a;
        a.id           = cols[0];
        a.display_name = cols[1];
        a.email        = cols[2];
        a.imap_host    = cols[3];
        a.imap_port    = static_cast<uint16_t>(toUint(cols[4], 993));
        a.imap_ssl     = cols[5] == "1";
        a.smtp_host    = cols[6];
        a.smtp_port    = static_cast<uint16_t>(toUint(cols[7], 587));
        a.smtp_ssl     = cols[8] == "1";
        a.username     = cols[9];
        a.password     = cols[10];
        g_accounts.push_back(std::move(a));
    }
}

static bool saveAccounts() {
    std::ostringstream f;
    for (const auto& a : g_accounts) {
        f << a.id           << '\t'
          << a.display_name << '\t'
          << a.email        << '\t'
          << a.imap_host    << '\t'
          << a.imap_port    << '\t'
          << (a.imap_ssl ? "1" : "0") << '\t'
          << a.smtp_host    << '\t'
          << a.smtp_port    << '\t'
          << (a.smtp_ssl ? "1" : "0") << '\t'
          << a.username     << '\t'
          << a.password     << '\n';
    }
    return storeWrite("accounts", f.str());
}

// Save parsed message to local cache as .eml
static void cacheMessage(const MailAccount& a, const std::string& folder,
                          const MailMessage& msg) {
    std::ostringstream f;
    f << "From: "    << msg.from    << "\r\n"
      << "To: "      << msg.to      << "\r\n"
      << "CC: "      << msg.cc      << "\r\n"
      << "Subject: " << msg.subject << "\r\n"
      << "Date: "    << msg.date_str<< "\r\n"
      << "X-UID: "   << msg.uid     << "\r\n"
      << "X-Read: "  << (msg.read ? "1" : "0") << "\r\n"
      << "\r\n"
      << msg.body;
    (void)storeWrite(folderDir(a, folder) + "/" + std::to_string(msg.uid) + ".eml", f.str());
}

// Load messages from local cache for a folder
static std::vector<MailMessage> loadCachedMessages(const MailAccount& a,
                                                    const std::string& folder) {
    std::vector<MailMessage> msgs;
    const std::string dir = folderDir(a, folder);
    for (const std::string& name : storeList(dir)) {
        if (!name.ends_with(".eml")) continue;
        std::string text;
        if (!storeRead(dir + "/" + name, text)) continue;
        MailMessage msg = parseEml(text);
        if (msg.uid > 0) msgs.push_back(std::move(msg));
    }

    // Sort by UID descending (newest first)
    std::sort(msgs.begin(), msgs.end(),
              [](const MailMessage& a, const MailMessage& b){
                  return a.uid > b.uid; });
    return msgs;
}

// ── libcurl helpers ───────────────────────────────────────────────────────────

// The sandbox can't resolve names or open sockets, so the compositor connects
// and curl is given the socket: it thinks it's connecting to the address below.
// Nor can it read the trusted certificates, so they're loaded before it begins.
static std::string g_ca_certs;

static void loadCaCerts() {
    std::vector<std::string> places;
    for (const char* var : {"CURL_CA_BUNDLE", "SSL_CERT_FILE"})
        if (const char* p = std::getenv(var)) places.emplace_back(p);
    places.emplace_back("/etc/ssl/cert.pem");
    places.emplace_back("/usr/local/share/certs/ca-root-nss.crt");
    for (const auto& place : places) {
        std::ifstream f(place, std::ios::binary);
        if (!f) continue;
        g_ca_certs.assign(std::istreambuf_iterator<char>(f), {});
        if (!g_ca_certs.empty()) return;
    }
    std::cerr << "[Mail] no trusted certificates found: secure connections will fail\n";
}

struct Connection {
    std::string host;
    uint16_t    port = 0;
    std::string error;     // from the compositor, which curl doesn't know about
    curl_slist* resolve = nullptr;
    ~Connection() { curl_slist_free_all(resolve); }
};

static curl_socket_t openBrokered(void* data, curlsocktype, curl_sockaddr*) {
    auto* c = static_cast<Connection*>(data);
    ConnectResult r = connectBlocking(c->host, c->port);
    if (!r.ok()) {
        c->error = r.error.empty() ? "couldn't connect" : r.error;
        return CURL_SOCKET_BAD;
    }
    return r.socket.release();   // curl closes it
}

static int alreadyConnected(void*, curl_socket_t, curlsocktype) {
    return CURL_SOCKOPT_ALREADY_CONNECTED;
}

static void useConnection(CURL* curl, Connection& c, const std::string& host, uint16_t port) {
    c.host = host;
    c.port = port;
    const std::string entry = host + ":" + std::to_string(port) + ":127.0.0.1";
    c.resolve = curl_slist_append(nullptr, entry.c_str());
    curl_easy_setopt(curl, CURLOPT_RESOLVE, c.resolve);
    curl_easy_setopt(curl, CURLOPT_OPENSOCKETFUNCTION, openBrokered);
    curl_easy_setopt(curl, CURLOPT_OPENSOCKETDATA, &c);
    curl_easy_setopt(curl, CURLOPT_SOCKOPTFUNCTION, alreadyConnected);
    curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
    curl_blob certs{g_ca_certs.data(), g_ca_certs.size(), CURL_BLOB_NOCOPY};
    curl_easy_setopt(curl, CURLOPT_CAINFO_BLOB, &certs);
    curl_easy_setopt(curl, CURLOPT_CAPATH, nullptr);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 2L);
    // Without TLS from the first byte (imaps, smtps), a password still doesn't
    // cross the network in the clear; a server on this machine may do without.
    const bool local = host == "localhost" || host == "127.0.0.1" || host == "::1";
    curl_easy_setopt(curl, CURLOPT_USE_SSL, local ? CURLUSESSL_TRY : CURLUSESSL_ALL);
}

static std::string curlError(CURLcode rc, const Connection& c) {
    return c.error.empty() ? curl_easy_strerror(rc) : c.error;
}


static size_t curlWrite(char* ptr, size_t sz, size_t nmemb, std::string* s) {
    s->append(ptr, sz * nmemb);
    return sz * nmemb;
}

struct SmtpUpload { const std::string* data; size_t offset; };

static size_t curlRead(char* ptr, size_t sz, size_t nmemb, SmtpUpload* up) {
    size_t avail    = up->data->size() - up->offset;
    size_t to_copy  = std::min(avail, sz * nmemb);
    std::memcpy(ptr, up->data->data() + up->offset, to_copy);
    up->offset += to_copy;
    return to_copy;
}

// ── Header parsing ────────────────────────────────────────────────────────────

// Extract a header value from a raw RFC-822 header block (case-insensitive)

// ── IMAP fetch (runs in background thread) ────────────────────────────────────

// Parse a FETCH response block into MailMessages.
// libcurl delivers each message as a separate write callback sequence;
// by the time we see the full response buffer we split on "* N FETCH".
// Headers in mail may be RFC 2047 encoded: =?utf-8?B?...?= or =?utf-8?Q?...?=.
static std::string decodeWords(const std::string& in) {
    static const auto b64 = [](char c) -> int {
        if (c >= 'A' && c <= 'Z') return c - 'A';
        if (c >= 'a' && c <= 'z') return c - 'a' + 26;
        if (c >= '0' && c <= '9') return c - '0' + 52;
        return c == '+' ? 62 : c == '/' ? 63 : -1;
    };
    std::string out;
    size_t pos = 0;
    bool after_word = false;
    while (pos < in.size()) {
        const size_t start = in.find("=?", pos);
        size_t q1 = start == std::string::npos ? start : in.find('?', start + 2);
        size_t q2 = q1 == std::string::npos ? q1 : in.find('?', q1 + 1);
        size_t end = q2 == std::string::npos ? q2 : in.find("?=", q2 + 1);
        if (end == std::string::npos) { out += in.substr(pos); break; }
        const std::string between = in.substr(pos, start - pos);
        // Only space separates two encoded words: it isn't part of the text.
        if (!after_word || between.find_first_not_of(" \t\r\n") != std::string::npos) out += between;
        const char enc = static_cast<char>(std::toupper(static_cast<unsigned char>(in[q1 + 1])));
        const std::string text = in.substr(q2 + 1, end - q2 - 1);
        if (enc == 'B') {
            uint32_t bits = 0;
            int have = 0;
            for (char c : text) {
                const int v = b64(c);
                if (v < 0) continue;
                bits = (bits << 6) | static_cast<uint32_t>(v);
                have += 6;
                if (have >= 8) { have -= 8; out += static_cast<char>((bits >> have) & 0xFF); }
            }
        } else {
            for (size_t i = 0; i < text.size(); ++i) {
                if (text[i] == '_') out += ' ';
                else if (text[i] == '=' && i + 2 < text.size()) {
                    out += static_cast<char>(std::strtol(text.substr(i + 1, 2).c_str(), nullptr, 16));
                    i += 2;
                } else out += text[i];
            }
        }
        pos = end + 2;
        after_word = true;
    }
    return out;
}

// An IMAP value: an atom, a string or NIL (empty), or a (list).
struct ImapValue {
    std::string text;
    std::vector<ImapValue> list;
};

static ImapValue parseImapValue(const std::string& s, size_t& pos) {
    ImapValue v;
    while (pos < s.size() && s[pos] == ' ') ++pos;
    if (pos >= s.size()) return v;
    if (s[pos] == '(') {
        ++pos;
        while (pos < s.size() && s[pos] != ')') {
            size_t before = pos;
            v.list.push_back(parseImapValue(s, pos));
            while (pos < s.size() && s[pos] == ' ') ++pos;
            if (pos == before) break;
        }
        if (pos < s.size()) ++pos;
    } else if (s[pos] == '"') {
        for (++pos; pos < s.size() && s[pos] != '"'; ++pos) {
            if (s[pos] == '\\' && pos + 1 < s.size()) ++pos;
            v.text += s[pos];
        }
        if (pos < s.size()) ++pos;
    } else {
        while (pos < s.size() && s[pos] != ' ' && s[pos] != ')' && s[pos] != '(') v.text += s[pos++];
        if (v.text == "NIL") v.text.clear();
    }
    return v;
}

// ("name" adl "mailbox" "host") ... as "name <mailbox@host>", comma-separated.
static std::string imapAddresses(const ImapValue& v) {
    std::string out;
    for (const auto& a : v.list) {
        if (a.list.size() < 4) continue;
        const std::string addr = a.list[2].text + "@" + a.list[3].text;
        const std::string name = decodeWords(a.list[0].text);
        if (!out.empty()) out += ", ";
        out += name.empty() ? addr : name + " <" + addr + ">";
    }
    return out;
}

// What `UID FETCH ... (UID FLAGS BODYSTRUCTURE ENVELOPE)` answers, one per line:
// curl hands over only a command's "* " lines, which is why it's this and not the
// raw headers, and why a value the server sends as a literal comes out empty.
static std::vector<MailMessage> parseImapFetch(const std::string& raw) {
    std::vector<MailMessage> msgs;
    std::istringstream lines(raw);
    std::string line;
    while (std::getline(lines, line)) {
        if (!line.starts_with("* ") || line.find(" FETCH ") == std::string::npos) continue;
        MailMessage msg;
        if (auto at = line.find("UID "); at != std::string::npos) msg.uid = toUint(line.substr(at + 4));
        if (msg.uid == 0) continue;
        if (auto at = line.find("FLAGS ("); at != std::string::npos) {
            const auto end = line.find(')', at);
            msg.read = line.substr(at, end - at).find("\\Seen") != std::string::npos;
        }
        if (auto at = line.find("BODYSTRUCTURE ("); at != std::string::npos) {
            std::string upper = line.substr(at);
            std::transform(upper.begin(), upper.end(), upper.begin(), ::toupper);
            msg.has_attachment = upper.find("\"MIXED\"") != std::string::npos;
        }
        if (auto at = line.find("ENVELOPE ("); at != std::string::npos) {
            size_t pos = at + 9;
            const ImapValue env = parseImapValue(line, pos);
            // date subject from sender reply-to to cc ...
            if (env.list.size() >= 7) {
                msg.date_str = env.list[0].text;
                msg.subject  = decodeWords(env.list[1].text);
                msg.from     = imapAddresses(env.list[2]);
                msg.to       = imapAddresses(env.list[5]);
                msg.cc       = imapAddresses(env.list[6]);
            }
        }
        msgs.push_back(std::move(msg));
    }
    std::sort(msgs.begin(), msgs.end(),
              [](const MailMessage& a, const MailMessage& b) { return a.uid > b.uid; });
    return msgs;
}

// Fetch message body for UID; returns plain-text content.
static bool fetchBody(const MailAccount& acct,
                      const std::string& folder, uint32_t uid, std::string& out) {
    CURL* curl = curl_easy_init();
    if (!curl) return false;

    std::string url = std::string(acct.imap_ssl ? "imaps" : "imap")
                    + "://" + acct.imap_host
                    + ":" + std::to_string(acct.imap_port)
                    + "/" + folder + "/;UID=" + std::to_string(uid) + ";SECTION=TEXT";

    std::string response;
    Connection conn;
    useConnection(curl, conn, acct.imap_host, acct.imap_port);
    curl_easy_setopt(curl, CURLOPT_URL,           url.c_str());
    curl_easy_setopt(curl, CURLOPT_USERNAME,       acct.username.c_str());
    curl_easy_setopt(curl, CURLOPT_PASSWORD,       acct.password.c_str());
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION,  curlWrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA,      &response);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 2L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT,        20L);

    CURLcode rc = curl_easy_perform(curl);
    curl_easy_cleanup(curl);
    if (rc != CURLE_OK) {
        out = "(Couldn't load this message: " + curlError(rc, conn) + ")";
        return false;
    }
    out = std::move(response);
    return true;
}

// Background sync: fetch headers for the active folder.
static void syncFolder(const MailAccount& acct, const std::string& folder,
                       std::function<void(std::vector<MailMessage>, std::string)> done_cb) {
    CURL* curl = curl_easy_init();
    if (!curl) { done_cb({}, "curl init failed"); return; }

    std::string url = std::string(acct.imap_ssl ? "imaps" : "imap")
                    + "://" + acct.imap_host
                    + ":" + std::to_string(acct.imap_port)
                    + "/" + folder;

    std::string response;
    Connection conn;
    useConnection(curl, conn, acct.imap_host, acct.imap_port);
    curl_easy_setopt(curl, CURLOPT_URL,           url.c_str());
    curl_easy_setopt(curl, CURLOPT_USERNAME,       acct.username.c_str());
    curl_easy_setopt(curl, CURLOPT_PASSWORD,       acct.password.c_str());
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION,  curlWrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA,      &response);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 2L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT,        30L);
    // The newest messages: which they are, then those (without marking them read).
    curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, "UID SEARCH ALL");
    CURLcode rc = curl_easy_perform(curl);
    if (rc == CURLE_OK) {
        constexpr size_t kNewest = 50;
        std::vector<std::string> uids;
        if (auto at = response.find("* SEARCH"); at != std::string::npos) {
            std::istringstream found(response.substr(at + 8, response.find('\n', at) - at - 8));
            for (std::string uid; found >> uid;) uids.push_back(uid);
        }
        std::string wanted;
        for (size_t i = uids.size() > kNewest ? uids.size() - kNewest : 0; i < uids.size(); ++i)
            wanted += (wanted.empty() ? "" : ",") + uids[i];
        response.clear();
        if (!wanted.empty()) {
            const std::string fetch = "UID FETCH " + wanted + " (UID FLAGS BODYSTRUCTURE ENVELOPE)";
            curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, fetch.c_str());
            rc = curl_easy_perform(curl);
        }
    }
    curl_easy_cleanup(curl);

    if (rc != CURLE_OK) { done_cb({}, curlError(rc, conn)); return; }

    auto msgs = parseImapFetch(response);
    // Cache fetched headers locally
    if (g_active_account >= 0 && g_active_account < (int)g_accounts.size()) {
        ensureDirs(acct);
        for (auto& m : msgs) {
            // A body read earlier is still good: this only brought the headers.
            std::string kept;
            if (storeRead(folderDir(acct, folder) + "/" + std::to_string(m.uid) + ".eml", kept))
                m.body = parseEml(kept).body;
            cacheMessage(acct, folder, m);
        }
    }
    done_cb(std::move(msgs), {});
}

// ── SMTP send ─────────────────────────────────────────────────────────────────

constexpr size_t kMaxAttachment = 25u << 20;   // what mail servers commonly accept

struct Attachment {
    std::string name;
    std::string data;
};

static bool sendSmtp(const MailAccount& acct,
                     const std::string& to, const std::string& cc,
                     const std::string& subject, const std::string& body,
                     const std::vector<Attachment>& attachments,
                     std::string& out_err) {
    CURL* curl = curl_easy_init();
    if (!curl) { out_err = "curl init failed"; return false; }

    // Build multipart or plain message
    std::ostringstream msg_ss;
    msg_ss << "From: " << acct.display_name << " <" << acct.email << ">\r\n"
           << "To: "      << to      << "\r\n";
    if (!cc.empty()) msg_ss << "CC: " << cc << "\r\n";
    msg_ss << "Subject: " << subject << "\r\n"
           << "MIME-Version: 1.0\r\n";

    if (attachments.empty()) {
        msg_ss << "Content-Type: text/plain; charset=utf-8\r\n"
               << "Content-Transfer-Encoding: 8bit\r\n"
               << "\r\n"
               << body << "\r\n";
    } else {
        std::string boundary = "----=_MailBoundary_" + std::to_string(std::time(nullptr));
        msg_ss << "Content-Type: multipart/mixed; boundary=\"" << boundary << "\"\r\n"
               << "\r\n"
               << "--" << boundary << "\r\n"
               << "Content-Type: text/plain; charset=utf-8\r\n"
               << "Content-Transfer-Encoding: 8bit\r\n"
               << "\r\n"
               << body << "\r\n";
        for (const auto& att : attachments) {
            std::string att_name = att.name;   // it goes between quotes in a header
            for (char& c : att_name)
                if (c == '"' || c == '\\' || static_cast<unsigned char>(c) < 0x20) c = '_';
            msg_ss << "--" << boundary << "\r\n"
                   << "Content-Type: application/octet-stream\r\n"
                   << "Content-Disposition: attachment; filename=\"" << att_name << "\"\r\n"
                   << "Content-Transfer-Encoding: base64\r\n"
                   << "\r\n";
            static const char* b64chars =
                "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
            const auto* in = reinterpret_cast<const uint8_t*>(att.data.data());
            const size_t len = att.data.size();
            size_t col = 0;
            for (size_t i = 0; i < len; i += 3) {
                const size_t left = len - i;
                uint32_t b = uint32_t{in[i]} << 16;
                if (left > 1) b |= uint32_t{in[i + 1]} << 8;
                if (left > 2) b |= in[i + 2];
                msg_ss << b64chars[(b >> 18) & 63]
                       << b64chars[(b >> 12) & 63]
                       << (left > 1 ? b64chars[(b >> 6) & 63] : '=')
                       << (left > 2 ? b64chars[b & 63] : '=');
                col += 4;
                if (col >= 76) { msg_ss << "\r\n"; col = 0; }
            }
            msg_ss << "\r\n";
        }
        msg_ss << "--" << boundary << "--\r\n";
    }

    std::string msg_data = msg_ss.str();
    SmtpUpload upload{&msg_data, 0};

    std::string smtp_url = std::string(acct.smtp_ssl ? "smtps" : "smtp")
                         + "://" + acct.smtp_host
                         + ":" + std::to_string(acct.smtp_port);

    struct curl_slist* rcpts = nullptr;
    // Parse comma-separated recipients
    auto add_rcpts = [&](const std::string& field) {
        std::istringstream ss(field);
        std::string addr;
        while (std::getline(ss, addr, ',')) {
            // Trim whitespace
            auto s = addr.find_first_not_of(" \t");
            auto e = addr.find_last_not_of(" \t");
            if (s != std::string::npos)
                rcpts = curl_slist_append(rcpts, addr.substr(s, e - s + 1).c_str());
        }
    };
    add_rcpts(to);
    if (!cc.empty()) add_rcpts(cc);

    std::string from_addr = "<" + acct.email + ">";
    Connection conn;
    useConnection(curl, conn, acct.smtp_host, acct.smtp_port);
    curl_easy_setopt(curl, CURLOPT_URL,           smtp_url.c_str());
    curl_easy_setopt(curl, CURLOPT_USERNAME,       acct.username.c_str());
    curl_easy_setopt(curl, CURLOPT_PASSWORD,       acct.password.c_str());
    curl_easy_setopt(curl, CURLOPT_MAIL_FROM,      from_addr.c_str());
    curl_easy_setopt(curl, CURLOPT_MAIL_RCPT,      rcpts);
    curl_easy_setopt(curl, CURLOPT_READFUNCTION,   curlRead);
    curl_easy_setopt(curl, CURLOPT_READDATA,       &upload);
    curl_easy_setopt(curl, CURLOPT_UPLOAD,         1L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT,        30L);

    CURLcode rc = curl_easy_perform(curl);
    curl_slist_free_all(rcpts);
    curl_easy_cleanup(curl);

    if (rc != CURLE_OK) { out_err = curlError(rc, conn); return false; }
    return true;
}

// ── UI helpers ────────────────────────────────────────────────────────────────

// Shorten an email address like "First Last <user@host>" → "First Last"
static std::string shortFrom(const std::string& from) {
    if (from.empty()) return "(unknown)";
    auto lt = from.find('<');
    if (lt != std::string::npos && lt > 0) {
        std::string name = from.substr(0, lt);
        while (!name.empty() && name.back() == ' ') name.pop_back();
        if (!name.empty()) return name;
    }
    // bare address — trim to 28 chars
    auto at = from.find('@');
    if (at != std::string::npos) return from.substr(0, at);
    return from.size() > 28 ? from.substr(0, 25) + "…" : from;
}

// Format an RFC-822 Date string to "Jan 5" or "HH:MM" if today
static std::string shortDate(const std::string& date_str) {
    if (date_str.empty()) return "";
    // Try to extract month+day from "Mon, 05 Jan 2024 12:34:56 +0000"
    std::istringstream ss(date_str);
    std::string tok;
    std::vector<std::string> parts;
    while (ss >> tok) parts.push_back(tok);
    // Format: Day, DD Mon YYYY HH:MM:SS tz
    if (parts.size() >= 4) {
        std::string day = parts[1].size() == 1 ? ("0" + parts[1]) : parts[1];
        return parts[2] + " " + day; // "Jan 05"
    }
    return date_str.substr(0, 10);
}

static std::string subjectPreview(const std::string& s) {
    if (s.size() > 36) return s.substr(0, 33) + "…";
    return s;
}

// ── Add Account dialog ────────────────────────────────────────────────────────
// Builds a modal-style overlay within the right pane for entering account details.
// Returns the root widget; caller replaces right pane content.

static std::shared_ptr<Widget> buildAddAccountForm(
    std::shared_ptr<FlexColumn> right,
    std::function<void(MailAccount)> on_add,
    std::function<void()>            on_cancel)
{
    (void)right;   // reserved for future inline placement; form is added by caller
    auto form = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{});
    form->setPadding(28.0f);
    form->setGap(10.0f);
    form->setBackgroundColor(Color{0.11f, 0.11f, 0.13f, 1.0f});
    form->setFlexGrow(1.0f);

    auto add_label = [&](const char* text) {
        auto lbl = std::make_shared<TextWidget>(text, 11.0f);
        lbl->setColor(Color{0.65f, 0.65f, 0.65f, 1.0f});
        form->addChild(lbl);
    };
    auto add_input = [&](const char* placeholder, bool password = false)
        -> std::shared_ptr<TextInputWidget>
    {
        auto inp = std::make_shared<TextInputWidget>();
        inp->setPlaceholder(placeholder);
        inp->setFontSize(13.0f);
        inp->setFixedSize(0.0f, 30.0f);
        if (password) inp->setPasswordMode(true);
        form->addChild(inp);
        return inp;
    };

    auto title = std::make_shared<TextWidget>("Add Email Account", 16.0f);
    title->setColor(Color{1.0f, 1.0f, 1.0f, 1.0f});
    form->addChild(title);
    form->addChild(std::make_shared<Spacer>(0, 8));

    add_label("Display Name");  auto inp_name  = add_input("Your Name");
    add_label("Email Address"); auto inp_email = add_input("you@example.com");
    add_label("IMAP Host");     auto inp_imap  = add_input("imap.example.com");
    add_label("IMAP Port");     auto inp_iport = add_input("993");
    add_label("SMTP Host");     auto inp_smtp  = add_input("smtp.example.com");
    add_label("SMTP Port");     auto inp_sport = add_input("587");
    add_label("Username");      auto inp_user  = add_input("username");
    add_label("Password");      auto inp_pass  = add_input("••••••••", true);

    form->addChild(std::make_shared<Spacer>(0, 8));

    // Buttons row
    auto btn_row = std::make_shared<FlexRow>(std::vector<std::shared_ptr<Widget>>{});
    btn_row->setGap(10.0f);

    auto cancel_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>("Cancel", 13.0f),
        [on_cancel]() { on_cancel(); });
    cancel_btn->setFixedSize(80.0f, 30.0f);

    auto add_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>("Add Account", 13.0f),
        [=, on_add=on_add]() {
            MailAccount a;
            a.display_name = inp_name->getText();
            a.email        = inp_email->getText();
            a.imap_host    = inp_imap->getText();
            a.smtp_host    = inp_smtp->getText();
            a.username     = inp_user->getText();
            a.password     = inp_pass->getText();
            try { a.imap_port = static_cast<uint16_t>(std::stoul(inp_iport->getText())); }
            catch (...) { a.imap_port = 993; }
            try { a.smtp_port = static_cast<uint16_t>(std::stoul(inp_sport->getText())); }
            catch (...) { a.smtp_port = 587; }
            a.imap_ssl = (a.imap_port == 993);
            a.smtp_ssl = (a.smtp_port == 465);
            // Derive a safe ID slug from the email
            a.id = a.email;
            for (char& c : a.id)
                if (c == '@' || c == '.' || c == '+') c = '_';
            if (!a.email.empty() && !a.imap_host.empty())
                on_add(std::move(a));
        });
    add_btn->setFixedSize(120.0f, 30.0f);

    btn_row->addChild(cancel_btn);
    btn_row->addChild(add_btn);
    form->addChild(btn_row);

    return form;
}

// A sync finished, on the UI thread. A failure says why and leaves what's shown.
static std::string g_sync_error;

static void finishSync(std::vector<MailMessage> msgs, std::string err) {
    g_sync_error = std::move(err);
    if (g_sync_error.empty()) {
        std::lock_guard<std::mutex> lock(g_msg_mutex);
        g_messages = std::move(msgs);
    }
    g_syncing = false;
    if (g_rebuild_msg_list) g_rebuild_msg_list();
}

// ── Main ──────────────────────────────────────────────────────────────────────

int main(int argc, char** argv) {
    curl_global_init(CURL_GLOBAL_DEFAULT);

    openStore();
    loadCaCerts();
    loadAccounts();
    if (!g_accounts.empty()) g_active_account = 0;

    // ── State shared by lambdas ───────────────────────────────────────────────
    auto compose_to      = std::make_shared<std::string>("");
    auto compose_cc      = std::make_shared<std::string>("");
    auto compose_subject = std::make_shared<std::string>("");
    auto compose_body    = std::make_shared<std::string>("");
    auto compose_attachments = std::make_shared<std::vector<Attachment>>();
    auto compose_mode    = std::make_shared<bool>(false);
    auto status_text     = std::make_shared<std::string>("");

    // ── Left pane ─────────────────────────────────────────────────────────────
    auto left = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{});
    left->setFixedSize(200.0f, 720.0f);
    left->setGap(0.0f);
    left->setBackgroundColor(Color{0.10f, 0.10f, 0.12f, 1.0f});

    // Account header
    auto acct_label = std::make_shared<TextWidget>(
        g_active_account >= 0 ? g_accounts[g_active_account].email : "No account",
        12.0f);
    acct_label->setColor(Color{0.75f, 0.75f, 0.75f, 1.0f});
    acct_label->setPadding(10.0f);

    // Compose button at top of left pane
    auto compose_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>("✏  Compose", 13.0f),
        []() { if (g_open_compose) g_open_compose(""); });
    compose_btn->setFixedSize(180.0f, 34.0f);
    compose_btn->setBackgroundColor(Color{0.18f, 0.48f, 0.88f, 1.0f});

    auto compose_wrap = std::make_shared<FlexColumn>(
        std::vector<std::shared_ptr<Widget>>{compose_btn});
    compose_wrap->setPadding(10.0f);

    // Folder list (rebuilt by g_rebuild_folder_list)
    auto folder_col = std::make_shared<FlexColumn>(
        std::vector<std::shared_ptr<Widget>>{});
    folder_col->setFlexGrow(1.0f);
    folder_col->setGap(2.0f);
    folder_col->setPadding(8.0f);

    // Bottom buttons: Sync + Add Account
    auto sync_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>("⟳  Sync", 12.0f),
        []() {
            if (g_syncing || g_active_account < 0 ||
                g_active_account >= (int)g_accounts.size()) return;
            g_syncing = true;
            const MailAccount acct = g_accounts[g_active_account];
            const std::string folder = g_active_folder;
            std::thread([acct, folder]() {
                syncFolder(acct, folder, [](std::vector<MailMessage> msgs, std::string err) {
                    XApplication::post([msgs = std::move(msgs), err = std::move(err)]() mutable {
                        finishSync(std::move(msgs), std::move(err));
                    });
                });
            }).detach();
        });
    sync_btn->setFixedSize(180.0f, 30.0f);
    sync_btn->setBackgroundColor(Color{0.18f, 0.22f, 0.28f, 1.0f});

    auto add_acct_btn = std::make_shared<ButtonWidget>(
        std::make_shared<TextWidget>("+ Add Account", 12.0f),
        []() {
            // Triggers right pane to show add-account form
            if (g_rebuild_right_pane) {
                g_selected_msg = -2; // sentinel for "show add account form"
                g_rebuild_right_pane();
            }
        });
    add_acct_btn->setFixedSize(180.0f, 30.0f);
    add_acct_btn->setBackgroundColor(Color{0.14f, 0.14f, 0.16f, 1.0f});

    auto bottom_row = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{
        sync_btn,
        std::make_shared<Spacer>(0, 4),
        add_acct_btn,
    });
    bottom_row->setGap(0.0f);
    bottom_row->setPadding(10.0f);

    left->addChild(acct_label);
    left->addChild(compose_wrap);
    left->addChild(folder_col);
    left->addChild(bottom_row);

    // ── Middle pane ───────────────────────────────────────────────────────────
    auto mid = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{});
    mid->setFixedSize(310.0f, 720.0f);
    mid->setGap(0.0f);
    mid->setBackgroundColor(Color{0.12f, 0.12f, 0.14f, 1.0f});

    // Folder name header
    auto folder_header = std::make_shared<TextWidget>(g_active_folder, 15.0f);
    folder_header->setColor(Color{0.9f, 0.9f, 0.9f, 1.0f});
    folder_header->setPadding(12.0f);
    folder_header->setFontWeight(600);   // SemiBold
    mid->addChild(folder_header);

    // Message list scroll (ScrollViewWidget takes its content in the ctor; the
    // column is captured below to rebuild rows on folder/mailbox changes).
    auto msg_list_col = std::make_shared<FlexColumn>(
        std::vector<std::shared_ptr<Widget>>{});
    msg_list_col->setGap(1.0f);
    auto msg_scroll = std::make_shared<ScrollViewWidget>(msg_list_col);
    msg_scroll->setFlexGrow(1.0f);
    mid->addChild(msg_scroll);

    // Status bar at bottom of middle pane
    auto status_lbl = std::make_shared<TextWidget>("", 10.0f);
    status_lbl->setColor(Color{0.5f, 0.5f, 0.5f, 1.0f});
    status_lbl->setPadding(6.0f);
    mid->addChild(status_lbl);

    // ── Right pane ────────────────────────────────────────────────────────────
    auto right = std::make_shared<FlexColumn>(std::vector<std::shared_ptr<Widget>>{});
    right->setFlexGrow(1.0f);
    right->setBackgroundColor(Color{0.09f, 0.09f, 0.10f, 1.0f});

    // ── Root ─────────────────────────────────────────────────────────────────
    auto root = std::make_shared<FlexRow>(std::vector<std::shared_ptr<Widget>>{
        left, mid, right,
    });
    root->setGap(0.0f);
    root->setBackgroundColor(Color{0.08f, 0.08f, 0.09f, 1.0f});

    // ════════════════════════════════════════════════════════════════════════
    // Rebuild: right pane — message viewer, compose form, or add-account form
    // ════════════════════════════════════════════════════════════════════════
    g_rebuild_right_pane = [=]() mutable {
        right->clearChildren();

        // ── Add Account form ────────────────────────────────────────────────
        if (g_selected_msg == -2) {
            auto form = buildAddAccountForm(right,
                [=](MailAccount a) {
                    g_accounts.push_back(std::move(a));
                    g_active_account = static_cast<int>(g_accounts.size()) - 1;
                    const bool saved = saveAccounts();
                    ensureDirs(g_accounts[g_active_account]);
                    acct_label->setText(g_accounts[g_active_account].email +
                                        (saved ? "" : " (not saved)"));
                    g_selected_msg = -1;
                    if (g_rebuild_folder_list) g_rebuild_folder_list();
                    if (g_rebuild_right_pane)  g_rebuild_right_pane();
                },
                [=]() {
                    g_selected_msg = -1;
                    if (g_rebuild_right_pane) g_rebuild_right_pane();
                });
            right->addChild(form);
            return;
        }

        // ── Compose form ────────────────────────────────────────────────────
        if (*compose_mode) {
            auto form = std::make_shared<FlexColumn>(
                std::vector<std::shared_ptr<Widget>>{});
            form->setPadding(20.0f);
            form->setGap(8.0f);
            form->setFlexGrow(1.0f);

            // Header bar
            auto hdr = std::make_shared<FlexRow>(
                std::vector<std::shared_ptr<Widget>>{});
            hdr->setGap(10.0f);
            hdr->setCrossAxisAlignment(CrossAxisAlignment::Center);
            hdr->setFixedSize(0.0f, 40.0f);

            auto hdr_label = std::make_shared<TextWidget>("New Message", 15.0f);
            hdr_label->setColor(Color{0.9f, 0.9f, 0.9f, 1.0f});
            hdr_label->setFontWeight(600);   // SemiBold

            auto discard_btn = std::make_shared<ButtonWidget>(
                std::make_shared<TextWidget>("Discard", 12.0f),
                [=]() {
                    *compose_mode = false;
                    *compose_to = *compose_cc = *compose_subject = *compose_body = "";
                    compose_attachments->clear();
                    g_selected_msg = -1;
                    if (g_rebuild_right_pane) g_rebuild_right_pane();
                });
            discard_btn->setFixedSize(70.0f, 28.0f);
            discard_btn->setBackgroundColor(Color{0.30f, 0.12f, 0.12f, 1.0f});

            // Send button
            auto send_status = std::make_shared<TextWidget>("", 11.0f);
            send_status->setColor(Color{0.5f, 0.85f, 0.5f, 1.0f});

            auto send_btn = std::make_shared<ButtonWidget>(
                std::make_shared<TextWidget>("Send ➤", 13.0f),
                [=]() {
                    if (g_active_account < 0 ||
                        g_active_account >= (int)g_accounts.size()) return;
                    const MailAccount acct = g_accounts[g_active_account];
                    std::string to      = *compose_to;
                    std::string cc      = *compose_cc;
                    std::string subject = *compose_subject;
                    std::string body    = *compose_body;
                    std::vector<Attachment> atts = *compose_attachments;
                    send_status->setText("Sending…");
                    std::thread([=]() {
                        std::string err;
                        bool ok = sendSmtp(acct, to, cc, subject, body, atts, err);
                        XApplication::post([send_status, ok, err] {
                            send_status->setText(ok ? "Sent!" : ("Error: " + err));
                        });
                        if (ok) {
                            // Cache in Sent folder
                            MailMessage sent;
                            sent.uid     = static_cast<uint32_t>(std::time(nullptr));
                            sent.from    = acct.email;
                            sent.to      = to;
                            sent.cc      = cc;
                            sent.subject = subject;
                            sent.body    = body;
                            sent.read    = true;
                            cacheMessage(acct, "Sent", sent);
                        }
                    }).detach();
                });
            send_btn->setFixedSize(90.0f, 30.0f);
            send_btn->setBackgroundColor(Color{0.18f, 0.48f, 0.88f, 1.0f});

            hdr->addChild(hdr_label);
            hdr->addChild(std::make_shared<Spacer>(0, 0)); // flex spacer omitted; use setFlexGrow
            hdr->addChild(discard_btn);
            hdr->addChild(send_btn);
            hdr->addChild(send_status);
            form->addChild(hdr);

            // To / CC / Subject fields
            auto mk_field = [&](const char* lbl, std::shared_ptr<std::string> state,
                                 const char* placeholder) {
                auto row = std::make_shared<FlexRow>(
                    std::vector<std::shared_ptr<Widget>>{});
                row->setGap(8.0f);
                row->setCrossAxisAlignment(CrossAxisAlignment::Center);
                auto l = std::make_shared<TextWidget>(lbl, 12.0f);
                l->setColor(Color{0.55f, 0.55f, 0.55f, 1.0f});
                l->setFixedSize(50.0f, 20.0f);
                auto inp = std::make_shared<TextInputWidget>();
                inp->setPlaceholder(placeholder);
                inp->setFontSize(13.0f);
                inp->setText(*state);
                inp->setFlexGrow(1.0f);
                inp->setFixedSize(0.0f, 30.0f);
                inp->setOnChanged([state](const std::string& v){ *state = v; });
                row->addChild(l);
                row->addChild(inp);
                form->addChild(row);
            };
            mk_field("To:",      compose_to,      "recipient@example.com");
            mk_field("CC:",      compose_cc,      "cc@example.com");
            mk_field("Subject:", compose_subject, "Subject");

            // Attachments row
            auto att_row = std::make_shared<FlexRow>(
                std::vector<std::shared_ptr<Widget>>{});
            att_row->setGap(8.0f);
            att_row->setCrossAxisAlignment(CrossAxisAlignment::Center);
            auto att_lbl = std::make_shared<TextWidget>("📎", 14.0f);
            att_lbl->setFixedSize(50.0f, 20.0f);
            auto att_list_lbl = std::make_shared<TextWidget>(
                compose_attachments->empty() ? "No attachments" :
                    std::to_string(compose_attachments->size()) + " file(s)",
                11.0f);
            att_list_lbl->setColor(Color{0.6f, 0.6f, 0.6f, 1.0f});
            auto att_btn = std::make_shared<ButtonWidget>(
                std::make_shared<TextWidget>("Attach…", 11.0f),
                [=, att_list_lbl=att_list_lbl]() {
                    if (!g_xbus) return;
                    // The sandbox opens no paths: the user picks, and it's read at once.
                    XFileDialog::pickToOpen(*g_xbus, "Attach File", "", [=](XFileDialog::Picked p) {
                        if (p.cancelled) return;
                        std::string data;
                        if (!p.fd || !readAllFd(p.fd.get(), data, kMaxAttachment)) {
                            att_list_lbl->setText("Couldn't attach that file" +
                                                  (p.error.empty() ? std::string{} : ": " + p.error));
                            return;
                        }
                        compose_attachments->push_back({fs::path(p.path).filename().string(), std::move(data)});
                        att_list_lbl->setText(std::to_string(compose_attachments->size()) + " file(s)");
                    });
                });
            att_btn->setFixedSize(70.0f, 26.0f);
            att_row->addChild(att_lbl);
            att_row->addChild(att_list_lbl);
            att_row->addChild(att_btn);
            form->addChild(att_row);

            // Body text area — multi-line (Return inserts a newline; Ctrl+Return
            // isn't used here since the toolbar has an explicit Send button).
            auto body_inp = std::make_shared<MultilineTextInputWidget>();
            body_inp->setPlaceholder("Write your message…");
            body_inp->setFontSize(13.0f);
            body_inp->setText(*compose_body);
            body_inp->setPadding(12.0f);
            body_inp->setBackgroundColor(Color{0.07f, 0.07f, 0.08f, 1.0f});
            body_inp->setOnChanged([compose_body](const std::string& v){
                *compose_body = v;
            });
            auto body_scroll = std::make_shared<ScrollViewWidget>(body_inp);
            body_scroll->setFlexGrow(1.0f);
            form->addChild(body_scroll);

            right->addChild(form);
            return;
        }

        // ── Empty state ─────────────────────────────────────────────────────
        if (g_selected_msg < 0 || g_selected_msg >= (int)g_messages.size()) {
            auto lbl = std::make_shared<TextWidget>(
                g_accounts.empty() ? "Add an account to get started"
                                   : "Select a message",
                14.0f);
            lbl->setColor(Color{0.40f, 0.40f, 0.40f, 1.0f});
            lbl->setPadding(40.0f);
            right->addChild(lbl);
            return;
        }

        // ── Message viewer ──────────────────────────────────────────────────
        const MailMessage& msg = g_messages[g_selected_msg];

        // Header bar
        auto viewer_hdr = std::make_shared<FlexColumn>(
            std::vector<std::shared_ptr<Widget>>{});
        viewer_hdr->setPadding(16.0f);
        viewer_hdr->setGap(4.0f);
        viewer_hdr->setBackgroundColor(Color{0.13f, 0.13f, 0.15f, 1.0f});

        auto subj_w = std::make_shared<TextWidget>(
            msg.subject.empty() ? "(no subject)" : msg.subject, 16.0f);
        subj_w->setColor(Color{1.0f, 1.0f, 1.0f, 1.0f});
        subj_w->setFontWeight(600);   // SemiBold
        viewer_hdr->addChild(subj_w);

        auto from_w = std::make_shared<TextWidget>("From: " + msg.from, 12.0f);
        from_w->setColor(Color{0.70f, 0.70f, 0.70f, 1.0f});
        viewer_hdr->addChild(from_w);

        if (!msg.to.empty()) {
            auto to_w = std::make_shared<TextWidget>("To: " + msg.to, 12.0f);
            to_w->setColor(Color{0.60f, 0.60f, 0.60f, 1.0f});
            viewer_hdr->addChild(to_w);
        }
        if (!msg.cc.empty()) {
            auto cc_w = std::make_shared<TextWidget>("CC: " + msg.cc, 12.0f);
            cc_w->setColor(Color{0.60f, 0.60f, 0.60f, 1.0f});
            viewer_hdr->addChild(cc_w);
        }
        if (!msg.date_str.empty()) {
            auto date_w = std::make_shared<TextWidget>(msg.date_str, 11.0f);
            date_w->setColor(Color{0.50f, 0.50f, 0.50f, 1.0f});
            viewer_hdr->addChild(date_w);
        }

        // Action buttons (Reply, Forward, Delete)
        auto action_row = std::make_shared<FlexRow>(
            std::vector<std::shared_ptr<Widget>>{});
        action_row->setGap(8.0f);
        action_row->setPadding(8.0f);

        auto reply_btn = std::make_shared<ButtonWidget>(
            std::make_shared<TextWidget>("↩ Reply", 12.0f),
            [=]() {
                if (g_selected_msg < 0 || g_selected_msg >= (int)g_messages.size()) return;
                const auto& m = g_messages[g_selected_msg];
                *compose_to      = m.from;
                *compose_subject = "Re: " + m.subject;
                *compose_body    = "\n\n--- Original Message ---\n" + m.body;
                *compose_mode    = true;
                if (g_rebuild_right_pane) g_rebuild_right_pane();
            });
        reply_btn->setFixedSize(80.0f, 26.0f);

        auto fwd_btn = std::make_shared<ButtonWidget>(
            std::make_shared<TextWidget>("→ Forward", 12.0f),
            [=]() {
                if (g_selected_msg < 0 || g_selected_msg >= (int)g_messages.size()) return;
                const auto& m = g_messages[g_selected_msg];
                *compose_subject = "Fwd: " + m.subject;
                *compose_body    = "\n\n--- Forwarded Message ---\nFrom: " +
                                   m.from + "\nSubject: " + m.subject +
                                   "\n\n" + m.body;
                *compose_mode    = true;
                if (g_rebuild_right_pane) g_rebuild_right_pane();
            });
        fwd_btn->setFixedSize(88.0f, 26.0f);

        action_row->addChild(reply_btn);
        action_row->addChild(fwd_btn);

        std::string body_text = msg.body;
        if (body_text.empty()) {
            // If body not yet loaded, fetch in background
            body_text = "Loading…";
            if (g_active_account >= 0 && g_active_account < (int)g_accounts.size()) {
                const MailAccount acct = g_accounts[g_active_account];
                uint32_t uid = msg.uid;
                int sel = g_selected_msg;
                std::thread([acct, uid, sel]() {
                    std::string body;
                    const bool got = fetchBody(acct, g_active_folder, uid, body);
                    XApplication::post([acct, uid, sel, got, body = std::move(body)] {
                        {
                            std::lock_guard<std::mutex> lock(g_msg_mutex);
                            if (sel >= 0 && sel < (int)g_messages.size() && g_messages[sel].uid == uid) {
                                g_messages[sel].body = body.empty() ? "(This message has no text.)" : body;
                                if (got) cacheMessage(acct, g_active_folder, g_messages[sel]);
                            }
                        }
                        if (g_rebuild_right_pane) g_rebuild_right_pane();
                    });
                }).detach();
            }
        }

        auto body_w = std::make_shared<TextWidget>(body_text, 13.0f);
        body_w->setColor(Color{0.88f, 0.88f, 0.88f, 1.0f});
        body_w->setPadding(16.0f);
        auto body_scroll = std::make_shared<ScrollViewWidget>(body_w);
        body_scroll->setFlexGrow(1.0f);

        right->addChild(viewer_hdr);
        right->addChild(action_row);
        right->addChild(body_scroll);
    };

    // ════════════════════════════════════════════════════════════════════════
    // Rebuild: message list (middle pane)
    // ════════════════════════════════════════════════════════════════════════
    g_rebuild_msg_list = [=]() mutable {
        msg_list_col->clearChildren();

        std::lock_guard<std::mutex> lock(g_msg_mutex);
        status_lbl->setText(g_sync_error.empty()
            ? std::to_string(g_messages.size()) + " messages" + (g_syncing ? "  ⟳" : "")
            : "Sync failed: " + g_sync_error);
        if (g_messages.empty()) {
            auto lbl = std::make_shared<TextWidget>(
                g_syncing ? "Syncing…" : "No messages", 12.0f);
            lbl->setColor(Color{0.45f, 0.45f, 0.45f, 1.0f});
            lbl->setPadding(14.0f);
            msg_list_col->addChild(lbl);
            return;
        }

        for (int i = 0; i < (int)g_messages.size(); ++i) {
            const auto& m = g_messages[i];
            auto row = std::make_shared<FlexRow>(
                std::vector<std::shared_ptr<Widget>>{});
            row->setFixedSize(0.0f, 60.0f);
            row->setPadding(10.0f);
            row->setGap(8.0f);
            row->setCrossAxisAlignment(CrossAxisAlignment::Center);

            bool selected = (i == g_selected_msg);
            if (selected)
                row->setBackgroundColor(Color{0.16f, 0.28f, 0.50f, 1.0f});
            else if (!m.read)
                row->setBackgroundColor(Color{0.14f, 0.14f, 0.18f, 1.0f});
            else
                row->setBackgroundColor(Color{0.12f, 0.12f, 0.14f, 1.0f});

            // Unread dot
            auto dot = std::make_shared<FlexColumn>(
                std::vector<std::shared_ptr<Widget>>{});
            dot->setFixedSize(6.0f, 6.0f);
            dot->setBorderRadius(3.0f);
            if (!m.read)
                dot->setBackgroundColor(Color{0.3f, 0.6f, 1.0f, 1.0f});
            else
                dot->setBackgroundColor(Color{0.0f, 0.0f, 0.0f, 0.0f});
            row->addChild(dot);

            // Text column
            auto txt = std::make_shared<FlexColumn>(
                std::vector<std::shared_ptr<Widget>>{});
            txt->setFlexGrow(1.0f);
            txt->setGap(3.0f);

            auto from_w = std::make_shared<TextWidget>(shortFrom(m.from), 13.0f);
            from_w->setColor(Color{1.0f, 1.0f, 1.0f, m.read ? 0.75f : 1.0f});
            from_w->setFontWeight(m.read ? 400 : 600);   // Regular : SemiBold
            txt->addChild(from_w);

            auto subj_w2 = std::make_shared<TextWidget>(
                subjectPreview(m.subject), 11.0f);
            subj_w2->setColor(Color{0.70f, 0.70f, 0.70f, 1.0f});
            txt->addChild(subj_w2);

            row->addChild(txt);

            // Date + attachment indicator
            auto meta = std::make_shared<FlexColumn>(
                std::vector<std::shared_ptr<Widget>>{});
            meta->setGap(2.0f);
            meta->setCrossAxisAlignment(CrossAxisAlignment::End);

            auto date_w2 = std::make_shared<TextWidget>(shortDate(m.date_str), 10.0f);
            date_w2->setColor(Color{0.50f, 0.50f, 0.50f, 1.0f});
            meta->addChild(date_w2);
            if (m.has_attachment) {
                auto att_w = std::make_shared<TextWidget>("📎", 10.0f);
                meta->addChild(att_w);
            }
            row->addChild(meta);

            int idx = i;
            auto clickable = std::make_shared<GestureDetectorWidget>(row,
                [=](float, float) {
                    g_selected_msg = idx;
                    {
                        std::lock_guard<std::mutex> l2(g_msg_mutex);
                        if (idx < (int)g_messages.size())
                            g_messages[idx].read = true;
                    }
                    if (g_rebuild_right_pane) g_rebuild_right_pane();
                    if (g_rebuild_msg_list)   g_rebuild_msg_list();
                });
            msg_list_col->addChild(clickable);
        }

    };

    // ════════════════════════════════════════════════════════════════════════
    // Rebuild: folder list (left pane)
    // ════════════════════════════════════════════════════════════════════════
    g_rebuild_folder_list = [=]() mutable {
        folder_col->clearChildren();

        static const char* kFolders[] = {
            "INBOX", "Sent", "Drafts", "Trash", nullptr
        };
        static const char* kIcons[] = { "📥", "📤", "✏", "🗑", nullptr };

        for (int i = 0; kFolders[i]; ++i) {
            const char* fname = kFolders[i];
            const char* icon  = kIcons[i];
            bool active = (g_active_folder == fname);

            auto row = std::make_shared<FlexRow>(
                std::vector<std::shared_ptr<Widget>>{});
            row->setGap(8.0f);
            row->setFixedSize(0.0f, 32.0f);
            row->setPadding(6.0f);
            row->setCrossAxisAlignment(CrossAxisAlignment::Center);
            row->setBorderRadius(6.0f);

            if (active)
                row->setBackgroundColor(Color{0.18f, 0.28f, 0.44f, 1.0f});
            else
                row->setBackgroundColor(Color{0.0f, 0.0f, 0.0f, 0.0f});

            auto icon_w = std::make_shared<TextWidget>(icon, 13.0f);
            auto name_w = std::make_shared<TextWidget>(fname, 13.0f);
            name_w->setColor(active ? Color{1.0f, 1.0f, 1.0f, 1.0f}
                                    : Color{0.75f, 0.75f, 0.75f, 1.0f});
            row->addChild(icon_w);
            row->addChild(name_w);

            auto clickable = std::make_shared<GestureDetectorWidget>(row,
                [=](float, float) {
                    g_active_folder = fname;
                    folder_header->setText(fname);
                    g_selected_msg = -1;
                    // Load from cache immediately, then sync in background
                    if (g_active_account >= 0 &&
                        g_active_account < (int)g_accounts.size()) {
                        {
                            std::lock_guard<std::mutex> l(g_msg_mutex);
                            g_messages = loadCachedMessages(
                                g_accounts[g_active_account], fname);
                        }
                        if (g_rebuild_msg_list)   g_rebuild_msg_list();
                        if (g_rebuild_right_pane) g_rebuild_right_pane();
                    }
                    if (g_rebuild_folder_list) g_rebuild_folder_list();
                });
            folder_col->addChild(clickable);
        }
    };

    // ── Compose pre-fill helper ───────────────────────────────────────────────
    g_open_compose = [=](const std::string& mailto_uri) {
        *compose_mode    = true;
        *compose_to      = "";
        *compose_cc      = "";
        *compose_subject = "";
        *compose_body    = "";
        compose_attachments->clear();

        // Parse mailto:user@example.com?subject=Hello&body=Text
        if (mailto_uri.starts_with("mailto:")) {
            std::string rest = mailto_uri.substr(7);
            auto q = rest.find('?');
            if (q != std::string::npos) {
                *compose_to = rest.substr(0, q);
                std::string params = rest.substr(q + 1);
                std::istringstream ss(params);
                std::string token;
                while (std::getline(ss, token, '&')) {
                    auto eq = token.find('=');
                    if (eq == std::string::npos) continue;
                    std::string key = token.substr(0, eq);
                    std::string val = token.substr(eq + 1);
                    // URL-decode %XX
                    std::string decoded;
                    for (size_t i2 = 0; i2 < val.size(); ++i2) {
                        if (val[i2] == '%' && i2 + 2 < val.size()) {
                            int hex = std::stoi(val.substr(i2 + 1, 2), nullptr, 16);
                            decoded += static_cast<char>(hex);
                            i2 += 2;
                        } else if (val[i2] == '+') {
                            decoded += ' ';
                        } else {
                            decoded += val[i2];
                        }
                    }
                    if (key == "subject") *compose_subject = decoded;
                    else if (key == "body")    *compose_body    = decoded;
                    else if (key == "cc")      *compose_cc      = decoded;
                }
            } else {
                *compose_to = rest;
            }
        }
        if (g_rebuild_right_pane) g_rebuild_right_pane();
    };

    // ── Pre-load command-line file ────────────────────────────────────────────
    std::string preload_path;
    // xshell opens files with "--open <path>"; a bare path works too.
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        if (a == "--open") { if (i + 1 < argc) preload_path = argv[i + 1]; break; }
        if (!a.empty() && a[0] != '-') { preload_path = a; break; }
    }

    // ── Initial render ────────────────────────────────────────────────────────
    g_rebuild_folder_list();
    // Load cached messages for INBOX
    if (g_active_account >= 0 && g_active_account < (int)g_accounts.size()) {
        std::lock_guard<std::mutex> l(g_msg_mutex);
        g_messages = loadCachedMessages(g_accounts[g_active_account], "INBOX");
    }
    g_rebuild_msg_list();
    g_rebuild_right_pane();

    return XApplication::Run(root, "/tmp/freebsdx.sock", /*sandboxed=*/false,
                             /*is_shell=*/false,
        [=](XBusClient& xbus) {
            g_xbus = &xbus;
            XApplication::setTitle("Mail");

            // Register MIME handlers
            auto reg_mime = [&](const char* mime) {
                MimeSetDefaultRequest req{};
                std::strncpy(req.mime_type_, mime, sizeof(req.mime_type_) - 1);
                std::strncpy(req.app_id_, "com.freebsdx.mail",
                             sizeof(req.app_id_) - 1);
                xbus.Call("com.freebsdx.MIME",
                          static_cast<uint32_t>(MimeOpcode::SetDefaultHandler),
                          {reinterpret_cast<const uint8_t*>(&req), sizeof(req)},
                          nullptr);
            };
            reg_mime("message/rfc822");
            reg_mime("x-scheme-handler/mailto");

            // A mailto: link opened while this window runs.
            xbus.OnBroadcast([=](const XBusMessage& bcast) {
                if (std::strcmp(bcast.service_name_, "com.freebsdx.Shell") != 0 ||
                    bcast.opcode_ != static_cast<uint32_t>(ShellOpcode::LaunchWithFile)) return;
                ShellLaunchRequest req{};
                std::memcpy(&req, bcast.payload_, sizeof(req));
                req.app_id_[sizeof(req.app_id_) - 1]       = '\0';
                req.file_path_[sizeof(req.file_path_) - 1] = '\0';
                if (std::strcmp(req.app_id_, "com.freebsdx.mail") != 0) return;
                const std::string path = req.file_path_;
                if (path.starts_with("mailto:") && g_open_compose) g_open_compose(path);
            });

            // Show a message read from a file, at the top of the list.
            static auto show_eml = [](const std::string& text) {
                MailMessage m = parseEml(text);
                m.uid = static_cast<uint32_t>(std::time(nullptr));
                {
                    std::lock_guard<std::mutex> l(g_msg_mutex);
                    g_messages.insert(g_messages.begin(), std::move(m));
                    g_selected_msg = 0;
                }
                if (g_rebuild_msg_list)   g_rebuild_msg_list();
                if (g_rebuild_right_pane) g_rebuild_right_pane();
            };

            // A dropped file is a path this sandbox can't open: ask through the
            // picker, starting in its folder. A mailto: link needs no file.
            XApplication::setOnDrop("text/uri-list",
                [](float, float, const std::string& data) {
                    std::string path = data;
                    if (path.starts_with("file://")) path = path.substr(7);
                    while (!path.empty() && (path.back() == '\n' ||
                                             path.back() == '\r' ||
                                             path.back() == ' '))
                        path.pop_back();
                    if (path.starts_with("mailto:")) {
                        if (g_open_compose) g_open_compose(path);
                        return;
                    }
                    if (!path.ends_with(".eml") || !g_xbus) return;
                    XFileDialog::pickToOpen(*g_xbus, "Open Message", fs::path(path).parent_path().string(),
                        [](XFileDialog::Picked p) {
                            std::string text;
                            if (p.fd && readAllFd(p.fd.get(), text)) show_eml(text);
                        });
                });

            // From the command line: a mailto: link, or a message file (this
            // runs before the sandbox starts, so a path still opens).
            if (preload_path.starts_with("mailto:")) {
                g_open_compose(preload_path);
            } else if (preload_path.ends_with(".eml")) {
                std::ifstream pf(preload_path, std::ios::binary);
                if (pf) show_eml(std::string(std::istreambuf_iterator<char>(pf), {}));
            }

            // Auto-sync on startup if we have an account
            if (g_active_account >= 0 &&
                g_active_account < (int)g_accounts.size()) {
                g_syncing = true;
                const MailAccount acct = g_accounts[g_active_account];
                const std::string folder = g_active_folder;
                std::thread([acct, folder]() {
                syncFolder(acct, folder, [](std::vector<MailMessage> msgs, std::string err) {
                    XApplication::post([msgs = std::move(msgs), err = std::move(err)]() mutable {
                        finishSync(std::move(msgs), std::move(err));
                    });
                });
            }).detach();
            }
        });
}
