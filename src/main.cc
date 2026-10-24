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

static fs::path mailRoot() {
    const char* home = std::getenv("HOME");
    return fs::path(home ? home : "/tmp") / ".freebsdx-mail";
}

static fs::path accountsFile() { return mailRoot() / "accounts"; }

static fs::path folderDir(const MailAccount& a, const std::string& folder) {
    return mailRoot() / a.id / folder;
}

static void ensureDirs(const MailAccount& a) {
    for (const char* f : {"INBOX", "Sent", "Drafts", "Trash"})
        fs::create_directories(folderDir(a, f));
}

// TSV format: id\tdisplay_name\temail\timap_host\timap_port\timap_ssl
//             \tsmtp_host\tsmtp_port\tsmtp_ssl\tusername\tpassword
static void loadAccounts() {
    g_accounts.clear();
    std::ifstream f(accountsFile());
    if (!f) return;
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
        a.imap_port    = static_cast<uint16_t>(std::stoul(cols[4]));
        a.imap_ssl     = cols[5] == "1";
        a.smtp_host    = cols[6];
        a.smtp_port    = static_cast<uint16_t>(std::stoul(cols[7]));
        a.smtp_ssl     = cols[8] == "1";
        a.username     = cols[9];
        a.password     = cols[10];
        g_accounts.push_back(std::move(a));
    }
}

static void saveAccounts() {
    fs::create_directories(mailRoot());
    std::ofstream f(accountsFile(), std::ios::trunc);
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
}

// Save parsed message to local cache as .eml
static void cacheMessage(const MailAccount& a, const std::string& folder,
                          const MailMessage& msg) {
    auto path = folderDir(a, folder) / (std::to_string(msg.uid) + ".eml");
    std::ofstream f(path, std::ios::trunc);
    f << "From: "    << msg.from    << "\r\n"
      << "To: "      << msg.to      << "\r\n"
      << "CC: "      << msg.cc      << "\r\n"
      << "Subject: " << msg.subject << "\r\n"
      << "Date: "    << msg.date_str<< "\r\n"
      << "X-UID: "   << msg.uid     << "\r\n"
      << "X-Read: "  << (msg.read ? "1" : "0") << "\r\n"
      << "\r\n"
      << msg.body;
}

// Load messages from local cache for a folder
static std::vector<MailMessage> loadCachedMessages(const MailAccount& a,
                                                    const std::string& folder) {
    std::vector<MailMessage> msgs;
    auto dir = folderDir(a, folder);
    if (!fs::is_directory(dir)) return msgs;

    for (const auto& entry : fs::directory_iterator(dir)) {
        if (entry.path().extension() != ".eml") continue;
        std::ifstream f(entry.path());
        if (!f) continue;

        MailMessage msg;
        // Read header lines until blank line
        std::string line;
        while (std::getline(f, line)) {
            if (!line.empty() && line.back() == '\r') line.pop_back();
            if (line.empty()) break;
            auto colon = line.find(':');
            if (colon == std::string::npos) continue;
            std::string key = line.substr(0, colon);
            std::string val = line.substr(colon + 2); // skip ": "
            if (key == "From")    msg.from     = val;
            else if (key == "To")      msg.to      = val;
            else if (key == "CC")      msg.cc      = val;
            else if (key == "Subject") msg.subject = val;
            else if (key == "Date")    msg.date_str= val;
            else if (key == "X-UID")   msg.uid     = static_cast<uint32_t>(std::stoul(val));
            else if (key == "X-Read")  msg.read    = (val == "1");
        }
        // Rest is body
        std::ostringstream body_ss;
        while (std::getline(f, line)) {
            body_ss << line << '\n';
        }
        msg.body = body_ss.str();
        if (msg.uid > 0) msgs.push_back(std::move(msg));
    }

    // Sort by UID descending (newest first)
    std::sort(msgs.begin(), msgs.end(),
              [](const MailMessage& a, const MailMessage& b){
                  return a.uid > b.uid; });
    return msgs;
}

// ── libcurl helpers ───────────────────────────────────────────────────────────

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
static std::string rfcHeader(const std::string& raw, const std::string& name) {
    std::string lraw = raw, lname = name + ":";
    std::transform(lraw.begin(), lraw.end(), lraw.begin(), ::tolower);
    std::transform(lname.begin(), lname.end(), lname.begin(), ::tolower);
    auto pos = lraw.find(lname);
    if (pos == std::string::npos) return "";
    pos += lname.size();
    while (pos < raw.size() && (raw[pos] == ' ' || raw[pos] == '\t')) ++pos;
    auto end = raw.find('\n', pos);
    if (end == std::string::npos) end = raw.size();
    std::string val = raw.substr(pos, end - pos);
    if (!val.empty() && val.back() == '\r') val.pop_back();
    return val;
}

// ── IMAP fetch (runs in background thread) ────────────────────────────────────

// Parse a FETCH response block into MailMessages.
// libcurl delivers each message as a separate write callback sequence;
// by the time we see the full response buffer we split on "* N FETCH".
static std::vector<MailMessage> parseImapFetch(const std::string& raw) {
    std::vector<MailMessage> msgs;
    size_t pos = 0;
    while (pos < raw.size()) {
        // Find next "* N FETCH ("
        auto fetch = raw.find("\r\n* ", pos);
        if (fetch == std::string::npos) fetch = raw.find("\n* ", pos);
        if (fetch == std::string::npos) {
            if (pos == 0) {
                // Maybe response starts with "* "
                if (raw.starts_with("* ")) fetch = 0;
                else break;
            } else break;
        } else {
            fetch += (raw[fetch + 1] == '\n') ? 2 : 3; // skip \r\n or \n
        }
        // Find the literal size marker "{N}\r\n" or just the header block end
        auto brace = raw.find('{', fetch);
        auto next_fetch = raw.find("\n* ", fetch + 2);
        if (brace == std::string::npos ||
            (next_fetch != std::string::npos && brace > next_fetch)) {
            pos = (next_fetch != std::string::npos) ? next_fetch : raw.size();
            continue;
        }

        auto brace_end = raw.find('}', brace);
        if (brace_end == std::string::npos) break;
        size_t literal_sz = 0;
        try { literal_sz = std::stoul(raw.substr(brace + 1, brace_end - brace - 1)); }
        catch (...) { pos = brace_end + 1; continue; }

        // Skip past "\r\n" after "}"
        size_t hdr_start = brace_end + 1;
        if (hdr_start < raw.size() && raw[hdr_start] == '\r') ++hdr_start;
        if (hdr_start < raw.size() && raw[hdr_start] == '\n') ++hdr_start;

        if (hdr_start + literal_sz > raw.size()) break;
        std::string header_block = raw.substr(hdr_start, literal_sz);

        // Extract UID from "* N FETCH (UID N …)" or sequence number
        MailMessage msg;
        // Try to find UID in fetch response
        auto uid_kw = raw.find("UID ", fetch);
        if (uid_kw != std::string::npos && uid_kw < hdr_start) {
            try { msg.uid = std::stoul(raw.substr(uid_kw + 4)); } catch (...) {}
        }
        if (msg.uid == 0) {
            // Use sequence number from "* N FETCH"
            auto star = raw.rfind("* ", brace);
            if (star != std::string::npos) {
                try { msg.uid = std::stoul(raw.substr(star + 2)); } catch (...) {}
            }
        }

        msg.from     = rfcHeader(header_block, "From");
        msg.to       = rfcHeader(header_block, "To");
        msg.cc       = rfcHeader(header_block, "CC");
        msg.subject  = rfcHeader(header_block, "Subject");
        msg.date_str = rfcHeader(header_block, "Date");
        // Check for attachments (simplified: Content-Type multipart)
        std::string ct = rfcHeader(header_block, "Content-Type");
        std::transform(ct.begin(), ct.end(), ct.begin(), ::tolower);
        msg.has_attachment = ct.find("multipart") != std::string::npos;

        if (!msg.from.empty() || !msg.subject.empty())
            msgs.push_back(std::move(msg));

        pos = hdr_start + literal_sz;
    }
    return msgs;
}

// Fetch message body for UID; returns plain-text content.
static std::string fetchBody(const MailAccount& acct,
                              const std::string& folder, uint32_t uid) {
    CURL* curl = curl_easy_init();
    if (!curl) return "";

    std::string url = std::string(acct.imap_ssl ? "imaps" : "imap")
                    + "://" + acct.imap_host
                    + ":" + std::to_string(acct.imap_port)
                    + "/" + folder + "/;UID=" + std::to_string(uid);

    std::string response;
    curl_easy_setopt(curl, CURLOPT_URL,           url.c_str());
    curl_easy_setopt(curl, CURLOPT_USERNAME,       acct.username.c_str());
    curl_easy_setopt(curl, CURLOPT_PASSWORD,       acct.password.c_str());
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION,  curlWrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA,      &response);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 2L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT,        20L);
    curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST,
                     ("UID FETCH " + std::to_string(uid) + " BODY[TEXT]").c_str());

    CURLcode rc = curl_easy_perform(curl);
    curl_easy_cleanup(curl);
    return (rc == CURLE_OK) ? response : "";
}

// Background sync: fetch headers for the active folder.
static void syncFolder(const MailAccount& acct, const std::string& folder,
                       std::function<void(std::vector<MailMessage>)> done_cb) {
    CURL* curl = curl_easy_init();
    if (!curl) { done_cb({}); return; }

    std::string url = std::string(acct.imap_ssl ? "imaps" : "imap")
                    + "://" + acct.imap_host
                    + ":" + std::to_string(acct.imap_port)
                    + "/" + folder;

    std::string response;
    curl_easy_setopt(curl, CURLOPT_URL,           url.c_str());
    curl_easy_setopt(curl, CURLOPT_USERNAME,       acct.username.c_str());
    curl_easy_setopt(curl, CURLOPT_PASSWORD,       acct.password.c_str());
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION,  curlWrite);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA,      &response);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
    curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 2L);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT,        30L);
    // Fetch headers for all messages (newest 50 via RECENT or 1:* limited by server)
    curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST,
                     "UID FETCH 1:* (FLAGS RFC822.HEADER)");

    CURLcode rc = curl_easy_perform(curl);
    curl_easy_cleanup(curl);

    if (rc != CURLE_OK) { done_cb({}); return; }

    auto msgs = parseImapFetch(response);
    // Cache fetched headers locally
    if (g_active_account >= 0 && g_active_account < (int)g_accounts.size()) {
        ensureDirs(acct);
        for (const auto& m : msgs)
            cacheMessage(acct, folder, m);
    }
    done_cb(std::move(msgs));
}

// ── SMTP send ─────────────────────────────────────────────────────────────────

static bool sendSmtp(const MailAccount& acct,
                     const std::string& to, const std::string& cc,
                     const std::string& subject, const std::string& body,
                     const std::vector<std::string>& attachments,
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
        for (const auto& att_path : attachments) {
            std::ifstream af(att_path, std::ios::binary);
            if (!af) continue;
            std::string att_data((std::istreambuf_iterator<char>(af)),
                                  std::istreambuf_iterator<char>());
            std::string att_name = fs::path(att_path).filename().string();
            msg_ss << "--" << boundary << "\r\n"
                   << "Content-Type: application/octet-stream\r\n"
                   << "Content-Disposition: attachment; filename=\"" << att_name << "\"\r\n"
                   << "Content-Transfer-Encoding: base64\r\n"
                   << "\r\n";
            // Base64 encode (simple implementation)
            static const char* b64chars =
                "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
            const uint8_t* in = reinterpret_cast<const uint8_t*>(att_data.data());
            size_t len = att_data.size(), i = 0, col = 0;
            while (i < len) {
                uint32_t b  = in[i++] << 16;
                if (i < len) b |= in[i++] << 8;
                if (i < len) b |= in[i++];
                msg_ss << b64chars[(b >> 18) & 63]
                       << b64chars[(b >> 12) & 63]
                       << b64chars[(b >>  6) & 63]
                       << b64chars[(b      ) & 63];
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

    if (rc != CURLE_OK) { out_err = curl_easy_strerror(rc); return false; }
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

// ── Main ──────────────────────────────────────────────────────────────────────

int main(int argc, char** argv) {
    curl_global_init(CURL_GLOBAL_DEFAULT);

    loadAccounts();
    if (!g_accounts.empty()) g_active_account = 0;

    // ── State shared by lambdas ───────────────────────────────────────────────
    auto compose_to      = std::make_shared<std::string>("");
    auto compose_cc      = std::make_shared<std::string>("");
    auto compose_subject = std::make_shared<std::string>("");
    auto compose_body    = std::make_shared<std::string>("");
    auto compose_attachments = std::make_shared<std::vector<std::string>>();
    auto compose_mode    = std::make_shared<bool>(false);
    auto status_text     = std::make_shared<std::string>("");
    auto chooser_req     = std::make_shared<uint32_t>(0);

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
                syncFolder(acct, folder, [](std::vector<MailMessage> msgs) {
                    {
                        std::lock_guard<std::mutex> lock(g_msg_mutex);
                        g_messages = std::move(msgs);
                    }
                    g_syncing = false;
                    if (g_rebuild_msg_list) g_rebuild_msg_list();
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
                    saveAccounts();
                    ensureDirs(g_accounts[g_active_account]);
                    acct_label->setText(g_accounts[g_active_account].email);
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
                    std::vector<std::string> atts = *compose_attachments;
                    send_status->setText("Sending…");
                    std::thread([=]() {
                        std::string err;
                        bool ok = sendSmtp(acct, to, cc, subject, body, atts, err);
                        try {
                            send_status->setText(ok ? "Sent!" : ("Error: " + err));
                        } catch (...) {}
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
                    FileChooserRequest req{};
                    req.opcode_       = static_cast<uint32_t>(
                                            FileChooserOpcode::OpenFiles);
                    req.multi_select_ = 1;
                    std::strncpy(req.title_, "Attach Files", sizeof(req.title_) - 1);
                    static uint32_t s_req_id = 1000;
                    req.request_id_   = ++s_req_id;
                    *chooser_req      = s_req_id;
                    g_xbus->Call("com.freebsdx.FileChooser",
                                 static_cast<uint32_t>(FileChooserOpcode::OpenFiles),
                                 {reinterpret_cast<const uint8_t*>(&req), sizeof(req)},
                                 nullptr);
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
                    std::string body = fetchBody(acct, g_active_folder, uid);
                    try {
                        std::lock_guard<std::mutex> lock(g_msg_mutex);
                        if (sel < (int)g_messages.size() && g_messages[sel].uid == uid) {
                            g_messages[sel].body = body;
                            cacheMessage(acct, g_active_folder, g_messages[sel]);
                        }
                    } catch (...) {}
                    if (g_rebuild_right_pane) g_rebuild_right_pane();
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

        status_lbl->setText(std::to_string(g_messages.size()) + " messages"
                            + (g_syncing ? "  ⟳" : ""));
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
    if (argc >= 2) preload_path = argv[1];

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

            // Combined broadcast handler: LaunchWithFile + FileChooser responses
            xbus.OnBroadcast([=](const XBusMessage& bcast) {
                // ── LaunchWithFile (Shell → open .eml or mailto: URI) ─────
                if (std::strcmp(bcast.service_name_, "com.freebsdx.Shell") == 0 &&
                    bcast.opcode_ == static_cast<uint32_t>(ShellOpcode::LaunchWithFile))
                {
                    ShellLaunchRequest req{};
                    std::memcpy(&req, bcast.payload_, sizeof(req));
                    req.app_id_[sizeof(req.app_id_) - 1]       = '\0';
                    req.file_path_[sizeof(req.file_path_) - 1] = '\0';

                    if (std::strcmp(req.app_id_, "com.freebsdx.mail") != 0) return;

                    std::string path = req.file_path_;
                    if (path.starts_with("mailto:")) {
                        if (g_open_compose) g_open_compose(path);
                        return;
                    }
                    // .eml file → parse and display
                    std::ifstream f(path);
                    if (!f) return;
                    MailMessage msg_local;
                    msg_local.uid = static_cast<uint32_t>(std::time(nullptr));
                    std::string line;
                    while (std::getline(f, line)) {
                        if (!line.empty() && line.back() == '\r') line.pop_back();
                        if (line.empty()) break;
                        auto colon = line.find(':');
                        if (colon == std::string::npos) continue;
                        std::string key = line.substr(0, colon);
                        std::string val = line.substr(colon + 2);
                        if (key == "From")         msg_local.from     = val;
                        else if (key == "To")      msg_local.to       = val;
                        else if (key == "Subject") msg_local.subject  = val;
                        else if (key == "Date")    msg_local.date_str = val;
                    }
                    std::ostringstream body_ss;
                    while (std::getline(f, line)) body_ss << line << '\n';
                    msg_local.body = body_ss.str();
                    {
                        std::lock_guard<std::mutex> l(g_msg_mutex);
                        g_messages.insert(g_messages.begin(), msg_local);
                        g_selected_msg = 0;
                    }
                    if (g_rebuild_msg_list)   g_rebuild_msg_list();
                    if (g_rebuild_right_pane) g_rebuild_right_pane();
                    return;
                }

                // ── FileChooser response (attachment selection result) ─────
                if (std::strcmp(bcast.service_name_,
                                "com.freebsdx.FileChooser") == 0 &&
                    bcast.opcode_ == static_cast<uint32_t>(FileChooserOpcode::Response))
                {
                    FileChooserResponse resp{};
                    std::memcpy(&resp, bcast.payload_, sizeof(resp));
                    if (resp.request_id_ != *chooser_req || resp.cancelled_) return;
                    if (resp.path_[0] != '\0') {
                        compose_attachments->emplace_back(resp.path_);
                        if (g_rebuild_right_pane) g_rebuild_right_pane();
                    }
                }
            });

            // Drag-and-drop of .eml files or mailto: URIs
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
                    if (!path.ends_with(".eml")) return;
                    std::ifstream f(path);
                    if (!f) return;
                    MailMessage msg_local;
                    msg_local.uid = static_cast<uint32_t>(std::time(nullptr));
                    std::string line;
                    while (std::getline(f, line)) {
                        if (!line.empty() && line.back() == '\r') line.pop_back();
                        if (line.empty()) break;
                        auto colon = line.find(':');
                        if (colon == std::string::npos) continue;
                        std::string key = line.substr(0, colon);
                        std::string val = line.substr(colon + 2);
                        if (key == "From")         msg_local.from     = val;
                        else if (key == "To")      msg_local.to       = val;
                        else if (key == "Subject") msg_local.subject  = val;
                        else if (key == "Date")    msg_local.date_str = val;
                    }
                    std::ostringstream body_ss;
                    while (std::getline(f, line)) body_ss << line << '\n';
                    msg_local.body = body_ss.str();
                    {
                        std::lock_guard<std::mutex> l(g_msg_mutex);
                        g_messages.insert(g_messages.begin(), msg_local);
                        g_selected_msg = 0;
                    }
                    if (g_rebuild_msg_list)   g_rebuild_msg_list();
                    if (g_rebuild_right_pane) g_rebuild_right_pane();
                });

            // Pre-load from argv[1]: mailto: URI or .eml file
            if (!preload_path.empty()) {
                if (preload_path.starts_with("mailto:")) {
                    g_open_compose(preload_path);
                } else if (preload_path.ends_with(".eml")) {
                    std::ifstream pf(preload_path);
                    if (pf) {
                        MailMessage pm;
                        pm.uid = static_cast<uint32_t>(std::time(nullptr));
                        std::string pline;
                        while (std::getline(pf, pline)) {
                            if (!pline.empty() && pline.back() == '\r') pline.pop_back();
                            if (pline.empty()) break;
                            auto colon = pline.find(':');
                            if (colon == std::string::npos) continue;
                            std::string key = pline.substr(0, colon);
                            std::string val = pline.substr(colon + 2);
                            if (key == "From")         pm.from     = val;
                            else if (key == "To")      pm.to       = val;
                            else if (key == "Subject") pm.subject  = val;
                            else if (key == "Date")    pm.date_str = val;
                        }
                        std::ostringstream pbody;
                        while (std::getline(pf, pline)) pbody << pline << '\n';
                        pm.body = pbody.str();
                        {
                            std::lock_guard<std::mutex> l(g_msg_mutex);
                            g_messages.insert(g_messages.begin(), pm);
                            g_selected_msg = 0;
                        }
                        g_rebuild_msg_list();
                        g_rebuild_right_pane();
                    }
                }
            }

            // Auto-sync on startup if we have an account
            if (g_active_account >= 0 &&
                g_active_account < (int)g_accounts.size()) {
                g_syncing = true;
                const MailAccount acct = g_accounts[g_active_account];
                const std::string folder = g_active_folder;
                std::thread([acct, folder]() {
                    syncFolder(acct, folder, [](std::vector<MailMessage> msgs) {
                        if (!msgs.empty()) {
                            std::lock_guard<std::mutex> l(g_msg_mutex);
                            g_messages = std::move(msgs);
                        }
                        g_syncing = false;
                        if (g_rebuild_msg_list) g_rebuild_msg_list();
                    });
                }).detach();
            }
        });
}
