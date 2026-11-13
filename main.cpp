// PoltergeistLauncher — C++17, Linux port: GLFW + OpenGL3 + Dear ImGui + libcurl.
// Vanilla / Fabric / Forge / NeoForge / Quilt / OptiFine, Java auto-detect+download, offline / Ely.by / Microsoft,
// custom backgrounds from screenshots, crash explainer.
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/utsname.h>
#include <curl/curl.h>
#include <cstdint>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <atomic>
#include <thread>
#include <mutex>
#include <deque>
#include <map>
#include <set>
#include <optional>
#include <random>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <algorithm>
#include <cmath>
#include <cstring>
#include <cctype>
#include <chrono>
#include <tuple>
#include <dlfcn.h>
#include "imgui.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include <GLFW/glfw3.h>
#include <nlohmann/json.hpp>
#include <miniz.h>
#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_PNG
#define STBI_ONLY_JPEG
#define STBI_ONLY_BMP
#define STBI_ONLY_TGA
#include <stb_image.h>

namespace fs = std::filesystem;
using json = nlohmann::json;
static const char* kVer = "0.0.5";

// ====== Настройка: Azure Client ID для входа через Microsoft (см. объяснение в ответе) ======
static const std::string kMsClientId = ""; // можно оставить пустым: ID вводится в приложении (вкладка «Аккаунт») и сохраняется в config.json
static std::mutex gIdMu; static std::string gMsId = kMsClientId;
static std::string MsId() { std::lock_guard<std::mutex> l(gIdMu); return gMsId; }
static void SetMsId(const std::string& v) { std::lock_guard<std::mutex> l(gIdMu); gMsId = v; }
static const std::string kAuthlibUrl = "https://github.com/yushijinhun/authlib-injector/releases/download/v1.2.5/authlib-injector-1.2.5.jar";

// ============================ Утилиты ============================
// Linux: все пути и строки — UTF-8 (std::string), W()/U8() оставлены как заглушки для совместимости с остальным кодом.
extern char** environ;
static void Sleep(unsigned ms) { std::this_thread::sleep_for(std::chrono::milliseconds(ms)); }
static std::string W(const std::string& s) { return s; }
static std::string U8(const std::string& s) { return s; }
static fs::path P(const std::string& s) { return fs::path(s); }
static std::string PS(const fs::path& p) { return p.string(); }
static std::string Env(const char* n) { const char* v = getenv(n); return v ? std::string(v) : std::string(); }
static std::string HomeDir() { std::string h = Env("HOME"); return h.empty() ? std::string("/tmp") : h; }
static std::string ShQ(const std::string& s) { std::string r = "'"; for (char c : s) { if (c == '\'') r += "'\\''"; else r += c; } return r + "'"; }
static void OpenExternal(const std::string& what) { std::string cmd = "xdg-open " + ShQ(what) + " >/dev/null 2>&1 &"; if (system(cmd.c_str()) != 0) {} }
static std::string ReadAll(const fs::path& p) {
    std::ifstream f(p, std::ios::binary);
    std::stringstream ss; ss << f.rdbuf();
    return ss.str();
}
static void WriteAll(const fs::path& p, const std::string& d) {
    std::error_code ec;
    fs::create_directories(p.parent_path(), ec);
    fs::path t = p; t += ".tmp";
    { std::ofstream f(t, std::ios::binary); f.write(d.data(), (std::streamsize)d.size()); }
    fs::rename(t, p, ec);
}
static json Parse(const std::string& s) { return json::parse(s, nullptr, false); }
static std::string RandHex(int n) {
    static std::random_device rd; static const char* h = "0123456789abcdef";
    std::string s; for (int i = 0; i < n * 2; i++) s += h[rd() % 16]; return s;
}
static std::vector<std::string> Split(const std::string& s, char c) {
    std::vector<std::string> r; std::string cur; std::stringstream ss(s);
    while (std::getline(ss, cur, c)) r.push_back(cur);
    return r;
}
static std::string Q(const std::string& a) { // quoting для CreateProcess
    if (!a.empty() && a.find_first_of(" \t\"") == std::string::npos) return a;
    std::string r = "\""; int bs = 0;
    for (char c : a) {
        if (c == '\\') { bs++; r += c; }
        else if (c == '"') { r.append(bs + 1, '\\'); r += '"'; bs = 0; }
        else { bs = 0; r += c; }
    }
    r.append(bs, '\\'); r += "\""; return r;
}
static std::string Sub(std::string s, const std::map<std::string, std::string>& m) {
    for (auto& [k, v] : m) {
        std::string key = "${" + k + "}"; size_t p = 0;
        while ((p = s.find(key, p)) != std::string::npos) { s.replace(p, key.size(), v); p += v.size(); }
    }
    return s;
}

// ============================ Глобальное состояние ============================
static fs::path gRoot;    // папка игры (версии, библиотеки, Java, instances)
static fs::path gCfgDir;  // папка настроек лаунчера (config.json) — всегда одна и та же
static GLFWwindow* gWin = nullptr; static std::atomic<bool> gGameRunning{false};
static std::atomic<int> gWinCmd{0}; // команды окну из других потоков: 1 свернуть, 2 вернуть, 3 закрыть
static std::mutex gMu;
static std::deque<std::string> gLog;
static std::string gStatus = "Готов к запуску";
static std::atomic<float> gProg{0};
static std::atomic<bool> gBusy{false}, gDelBusy{false};
static bool gShowCrash = false;
static std::string gCrashTitle, gCrashBody;
static std::string gMsCode, gMsUri;
static std::string gAuthMsg; // сообщения входа в аккаунт (показываются только на вкладке «Аккаунты»)
struct Account { int type = 0; std::string name, uuid, token, refresh; }; // 0 offline, 1 Ely.by, 2 Microsoft
static std::optional<Account> gNewAcc;
static std::atomic<bool> gAuthBusy{false};
static char bNick[32] = "Player", bElyU[128], bElyP[160], bJava[260], bMsId[96], bJvm[512];

static std::atomic<bool> gLogOn{true};
static void Log(const std::string& s) { if (!gLogOn) return; std::lock_guard<std::mutex> l(gMu); gLog.push_back(s); if (gLog.size() > 3000) gLog.pop_front(); }
static void Status(const std::string& s) { { std::lock_guard<std::mutex> l(gMu); gStatus = s; } Log(s); }
static void AuthMsg(const std::string& s) { { std::lock_guard<std::mutex> l(gMu); gAuthMsg = s; } Status(s); }
static void ShowError(const std::string& t, const std::string& b) { std::lock_guard<std::mutex> l(gMu); gShowCrash = true; gCrashTitle = t; gCrashBody = b; }

// ============================ HTTP (libcurl) ============================
struct Resp { int status = 0; std::string body; };
static size_t CurlWrite(char* p, size_t s, size_t n, void* u) { static_cast<std::string*>(u)->append(p, s * n); return s * n; }
static Resp Http(const std::string& url, const std::string& method = "GET", const std::string& body = "", const std::string& hdr = "") {
    Resp r;
    CURL* c = curl_easy_init(); if (!c) return r;
    std::string ua = std::string("PoltergeistLauncher/") + kVer + " (github.com/PoltergeistTeam/MCL)";
    curl_easy_setopt(c, CURLOPT_URL, url.c_str());
    curl_easy_setopt(c, CURLOPT_USERAGENT, ua.c_str());
    curl_easy_setopt(c, CURLOPT_FOLLOWLOCATION, 1L);
    curl_easy_setopt(c, CURLOPT_MAXREDIRS, 10L);
    curl_easy_setopt(c, CURLOPT_ACCEPT_ENCODING, "");
    curl_easy_setopt(c, CURLOPT_CONNECTTIMEOUT, 20L);
    curl_easy_setopt(c, CURLOPT_LOW_SPEED_LIMIT, 1L);   // «завис» = ни байта за 60 с
    curl_easy_setopt(c, CURLOPT_LOW_SPEED_TIME, 60L);
    curl_easy_setopt(c, CURLOPT_NOSIGNAL, 1L);
    curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, CurlWrite);
    curl_easy_setopt(c, CURLOPT_WRITEDATA, &r.body);
    if (method == "POST") {
        curl_easy_setopt(c, CURLOPT_POST, 1L);
        curl_easy_setopt(c, CURLOPT_POSTFIELDS, body.data());
        curl_easy_setopt(c, CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)body.size());
    } else if (method != "GET") {
        curl_easy_setopt(c, CURLOPT_CUSTOMREQUEST, method.c_str());
        if (!body.empty()) { curl_easy_setopt(c, CURLOPT_POSTFIELDS, body.data()); curl_easy_setopt(c, CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)body.size()); }
    }
    curl_slist* hl = nullptr;
    { size_t p = 0; while (p < hdr.size()) { size_t e = hdr.find("\r\n", p); if (e == std::string::npos) e = hdr.size(); if (e > p) hl = curl_slist_append(hl, hdr.substr(p, e - p).c_str()); p = e + 2; } }
    if (hl) curl_easy_setopt(c, CURLOPT_HTTPHEADER, hl);
    if (curl_easy_perform(c) == CURLE_OK) { long sc = 0; curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &sc); r.status = (int)sc; }
    else r.body.clear();
    if (hl) curl_slist_free_all(hl);
    curl_easy_cleanup(c);
    return r;
}
static Resp PostJson(const std::string& url, const json& j) {
    return Http(url, "POST", j.dump(), "Content-Type: application/json\r\nAccept: application/json\r\n");
}
static std::string UrlEnc(const std::string& s) {
    static const char* h = "0123456789ABCDEF"; std::string r;
    for (unsigned char c : s) { if (isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~') r += (char)c; else { r += '%'; r += h[c >> 4]; r += h[c & 15]; } }
    return r;
}
static std::string Form(std::initializer_list<std::pair<std::string, std::string>> kv) {
    std::string r; for (auto& [k, v] : kv) { if (!r.empty()) r += '&'; r += k + "=" + UrlEnc(v); } return r;
}
static const char* kFormHdr = "Content-Type: application/x-www-form-urlencoded\r\n";

static bool Download(const std::string& url, const fs::path& dst, bool force = false) {
    std::error_code ec;
    if (!force && fs::exists(dst, ec) && fs::file_size(dst, ec) > 0) return true;
    for (int i = 0; i < 3; i++) {
        Resp r = Http(url);
        if (r.status == 200 && !r.body.empty()) { WriteAll(dst, r.body); return true; }
        Sleep(300);
    }
    return false;
}
struct Job { std::string url; fs::path dst; };
static void DownloadAll(const std::vector<Job>& jobs, float p0, float p1) { // 8 потоков
    size_t total = jobs.size(); if (!total) return;
    std::atomic<size_t> idx{0}, done{0};
    auto worker = [&] {
        for (;;) {
            size_t i = idx++; if (i >= total) break;
            Download(jobs[i].url, jobs[i].dst);
            size_t d = ++done; if (d % 16 == 0 || d == total) gProg = p0 + (p1 - p0) * (float)d / (float)total;
        }
    };
    std::vector<std::thread> th; for (int i = 0; i < 8; i++) th.emplace_back(worker);
    for (auto& t : th) t.join();
}
static bool Unzip(const fs::path& zip, const fs::path& dst, bool skipMeta = false) {
    std::string data = ReadAll(zip); if (data.empty()) return false;
    mz_zip_archive z{};
    if (!mz_zip_reader_init_mem(&z, data.data(), data.size(), 0)) return false;
    for (mz_uint i = 0; i < mz_zip_reader_get_num_files(&z); i++) {
        mz_zip_archive_file_stat st;
        if (!mz_zip_reader_file_stat(&z, i, &st) || mz_zip_reader_is_file_a_directory(&z, i)) continue;
        std::string name = st.m_filename;
        if (name.find("..") != std::string::npos) continue;
        if (skipMeta && name.rfind("META-INF", 0) == 0) continue;
        size_t sz = 0; void* p = mz_zip_reader_extract_to_heap(&z, i, &sz, 0);
        if (!p) continue;
        WriteAll(dst / P(name), std::string((const char*)p, sz));
        mz_free(p);
    }
    mz_zip_reader_end(&z);
    return true;
}

// ============================ Java ============================
struct JavaInfo { std::string exe; int major; };
static int JavaMajorFromHome(const fs::path& home) {
    std::string rel = ReadAll(home / "release");
    auto p = rel.find("JAVA_VERSION=\"");
    if (p == std::string::npos) return 0;
    std::string v = rel.substr(p + 14, 16);
    int a = atoi(v.c_str());
    if (a == 1) { auto d = v.find('.'); return d == std::string::npos ? 0 : atoi(v.c_str() + d + 1); }
    return a;
}
static int RunProcess(const std::string& cmd, const fs::path& cwd, std::string& captured);
static std::string HostArch() { struct utsname u; if (uname(&u) == 0) { std::string m = u.machine; if (m == "aarch64" || m == "arm64") return "arm64"; } return "x86_64"; }
static int MajorFromName(const std::string& n) { // java-17-openjdk-amd64 -> 17, java-1.8.0-openjdk -> 8, jdk-21.0.2 -> 21
    for (size_t i = 0; i < n.size(); i++) if (isdigit((unsigned char)n[i])) {
        int a = atoi(n.c_str() + i);
        if (a == 1 && i + 2 < n.size() && n[i + 1] == '.') return atoi(n.c_str() + i + 2);
        return a;
    }
    return 0;
}
static bool HasAwt(const fs::path& h) { // у «headless»-пакетов дистрибутивов нет libawt_xawt.so — Minecraft на них не запустится
    std::error_code ec;
    for (const char* r : {"lib/libawt_xawt.so", "lib/amd64/libawt_xawt.so", "lib/aarch64/libawt_xawt.so", "jre/lib/amd64/libawt_xawt.so", "jre/lib/aarch64/libawt_xawt.so"})
        if (fs::exists(h / r, ec)) return true;
    return false;
}
static std::vector<JavaInfo> FindJavas() {
    std::vector<fs::path> homes; std::error_code ec;
    auto add = [&](const fs::path& h) { if (fs::exists(h / "bin" / "java", ec)) homes.push_back(h); };
    auto scan = [&](const fs::path& d) { if (!fs::is_directory(d, ec)) return; for (auto& e : fs::directory_iterator(d, ec)) if (e.is_directory(ec)) add(e.path()); };
    std::string home = HomeDir();
    for (const char* d : {"/usr/lib/jvm", "/usr/lib64/jvm", "/usr/java", "/usr/lib/java", "/usr/local/java", "/usr/local/lib/jvm", "/opt/java", "/opt/jdk", "/opt/jvm", "/opt"}) scan(d);
    for (const char* d : {".sdkman/candidates/java", ".jdks", ".asdf/installs/java", ".local/share/mise/installs/java", ".local/share/JetBrains/jdks"}) scan(fs::path(home) / d);
    std::string jh = Env("JAVA_HOME"); if (!jh.empty()) add(fs::path(jh));
    for (auto& p : Split(Env("PATH"), ':')) { // java из PATH (через симлинки к реальному JDK)
        if (p.empty()) continue;
        fs::path j = fs::path(p) / "java";
        if (fs::exists(j, ec)) { fs::path rp = fs::canonical(j, ec); if (!ec) add(rp.parent_path().parent_path()); }
    }
    for (auto& e : fs::directory_iterator(gRoot / "runtime", ec)) { add(e.path()); scan(e.path()); }
    fs::path mc = fs::path(home) / ".minecraft" / "runtime"; // Java от официального лаунчера
    if (fs::is_directory(mc, ec))
        for (auto it = fs::recursive_directory_iterator(mc, ec); it != fs::recursive_directory_iterator(); it.increment(ec)) {
            if (ec) break;
            if (it->path().filename() == "java" && it->path().parent_path().filename() == "bin") homes.push_back(it->path().parent_path().parent_path());
        }
    std::set<std::string> seen; std::vector<JavaInfo> out;
    for (auto& h : homes) {
        std::error_code e2; std::string key = PS(fs::weakly_canonical(h, e2)); if (!seen.insert(key).second) continue;
        if (!HasAwt(h)) continue;
        int m = JavaMajorFromHome(h); if (m <= 0) m = MajorFromName(PS(h.filename())); if (m <= 0) continue;
        out.push_back({PS(h / "bin" / "java"), m});
    }
    std::sort(out.begin(), out.end(), [](auto& a, auto& b) { return a.major < b.major; });
    return out;
}
static std::string PickJava(int need) {
    auto js = FindJavas(); std::string best; int bm = 999;
    for (auto& j : js) if (j.major >= need && j.major < bm) { bm = j.major; best = j.exe; }
    return best;
}
static bool InstallJavaVer(int need) { // скачать и распаковать Temurin JRE нужной версии
    Status("Скачиваю Java " + std::to_string(need) + " (Temurin)...");
    fs::path tgz = gRoot / "runtime" / ("temurin-" + std::to_string(need) + ".tar.gz");
    std::string arch = HostArch() == "arm64" ? "aarch64" : "x64";
    std::string url = "https://api.adoptium.net/v3/binary/latest/" + std::to_string(need) + "/ga/linux/" + arch + "/jre/hotspot/normal/eclipse";
    if (!Download(url, tgz, true)) return false;
    fs::path dst = gRoot / "runtime" / std::to_string(need); std::error_code ec; fs::create_directories(dst, ec);
    std::string cap; int code = RunProcess("tar -xzf " + Q(PS(tgz)) + " -C " + Q(PS(dst)), gRoot, cap);
    fs::remove(tgz, ec);
    return code == 0;
}
static std::string EnsureJava(int need) {
    std::string j = PickJava(need); if (!j.empty()) return j;
    if (!InstallJavaVer(need)) return "";
    return PickJava(need);
}
static std::string JavaExe(std::string p) { return p; } // на Linux один бинарник java

// ============================ Версии ============================
struct Ver { std::string id, type, url; };
static std::vector<Ver> gVers; static std::string gLatest; static std::mutex gVerMu;

static void FetchVersions() {
    fs::path c = gRoot / "version_manifest.json";
    Resp r = Http("https://piston-meta.mojang.com/mc/game/version_manifest_v2.json");
    std::string body = (r.status == 200) ? r.body : ReadAll(c);
    if (r.status == 200) WriteAll(c, body);
    json j = Parse(body);
    if (!j.contains("versions")) { Status("Нет интернета: список версий недоступен"); return; }
    std::lock_guard<std::mutex> l(gVerMu);
    gLatest = j["latest"].value("release", "");
    for (auto& v : j["versions"]) gVers.push_back({v.value("id", ""), v.value("type", ""), v.value("url", "")});
}
static std::vector<std::string> NeoVersions() { // версии NeoForge из maven-metadata.xml (по возрастанию)
    std::vector<std::string> r; Resp x = Http("https://maven.neoforged.net/releases/net/neoforged/neoforge/maven-metadata.xml");
    if (x.status != 200) return r;
    size_t p = 0;
    while ((p = x.body.find("<version>", p)) != std::string::npos) {
        size_t e = x.body.find("</version>", p); if (e == std::string::npos) break;
        r.push_back(x.body.substr(p + 9, e - p - 9)); p = e;
    }
    return r;
}
static std::string NeoMcOf(const std::string& v) { // 21.1.172 -> 1.21.1, 21.0.5 -> 1.21, 26.1.x -> 26.1
    int a = 0, b = 0; if (sscanf(v.c_str(), "%d.%d", &a, &b) != 2) return "";
    if (a >= 26) return std::to_string(a) + "." + std::to_string(b);
    return b == 0 ? "1." + std::to_string(a) : "1." + std::to_string(a) + "." + std::to_string(b);
}
static std::set<std::string> gQuiltGames, gNeoGames, gOptiGames;
static std::set<std::string> gFabricGames, gForgeGames; // какие версии поддерживают загрузчики (пусто = не удалось получить, показываем все)
static void FetchLoaderLists() {
    std::set<std::string> fab, forge;
    Resp r = Http("https://meta.fabricmc.net/v2/versions/game");
    json j = Parse(r.body);
    if (j.is_array()) for (auto& x : j) fab.insert(x.value("version", ""));
    r = Http("https://files.minecraftforge.net/net/minecraftforge/forge/promotions_slim.json");
    j = Parse(r.body);
    if (j.is_object() && j.contains("promos") && j["promos"].is_object())
        for (auto it = j["promos"].begin(); it != j["promos"].end(); ++it) { size_t p = it.key().rfind('-'); if (p != std::string::npos) forge.insert(it.key().substr(0, p)); }
    std::set<std::string> quilt, neo, opti;
    r = Http("https://meta.quiltmc.org/v3/versions/game"); j = Parse(r.body);
    if (j.is_array()) for (auto& x : j) if (x.is_object() && x.contains("version") && x["version"].is_string()) quilt.insert(x["version"].get<std::string>());
    for (auto& v : NeoVersions()) { std::string m = NeoMcOf(v); if (!m.empty()) neo.insert(m); }
    r = Http("https://bmclapi2.bangbang93.com/optifine/versionList"); j = Parse(r.body);
    if (j.is_array()) for (auto& x : j) if (x.is_object() && x.contains("mcversion") && x["mcversion"].is_string()) opti.insert(x["mcversion"].get<std::string>());
    std::lock_guard<std::mutex> l(gVerMu); gFabricGames = fab; gForgeGames = forge; gQuiltGames = quilt; gNeoGames = neo; gOptiGames = opti;
}
static bool RuleOk(const json& rules) {
    if (!rules.is_array() || rules.empty()) return true;
    bool ok = false;
    for (auto& r : rules) {
        bool m = true;
        if (r.contains("os")) {
            auto& o = r["os"];
            if (o.contains("name") && o["name"] != "linux") m = false;
            if (o.contains("arch") && o["arch"] != HostArch()) m = false; // x86 / arm64 для чужой архитектуры
        }
        if (r.contains("features")) m = false; // demo / custom resolution и т.п. — выключено
        if (m) ok = (r.value("action", "allow") == "allow");
    }
    return ok;
}
static json Merge(json p, const json& c) {
    for (auto it = c.begin(); it != c.end(); ++it) {
        const std::string& k = it.key(); const json& v = it.value();
        if (k == "libraries") { json l = v; for (auto& x : p["libraries"]) l.push_back(x); p["libraries"] = l; }
        else if (k == "arguments") { for (auto key : {"game", "jvm"}) if (v.contains(key)) for (auto& x : v[key]) p["arguments"][key].push_back(x); }
        else if (k != "inheritsFrom") p[k] = v;
    }
    return p;
}
static json LoadVersionJson(const std::string& id, int depth = 0) {
    fs::path p = gRoot / "versions" / P(id) / P(id + ".json");
    json j = Parse(ReadAll(p));
    if (j.is_discarded() || !j.is_object()) {
        std::string url;
        { std::lock_guard<std::mutex> l(gVerMu); for (auto& v : gVers) if (v.id == id) url = v.url; }
        if (url.empty()) return json();
        Resp r = Http(url); if (r.status != 200) return json();
        WriteAll(p, r.body); j = Parse(r.body);
        if (!j.is_object()) return json();
    }
    if (j.contains("inheritsFrom") && depth < 4) {
        json par = LoadVersionJson(j["inheritsFrom"].get<std::string>(), depth + 1);
        if (par.is_null()) return json();
        return Merge(par, j);
    }
    j["_base"] = j.value("id", id);
    return j;
}
static std::string MavenPath(std::string n) {
    std::string ext = "jar"; auto at = n.find('@');
    if (at != std::string::npos) { ext = n.substr(at + 1); n = n.substr(0, at); }
    auto p = Split(n, ':'); if (p.size() < 3) return "";
    std::string g = p[0]; std::replace(g.begin(), g.end(), '.', '/');
    std::string f = p[1] + "-" + p[2]; if (p.size() > 3) f += "-" + p[3];
    return g + "/" + p[1] + "/" + p[2] + "/" + f + "." + ext;
}
static std::string LibKey(const std::string& n) { auto p = Split(n, ':'); if (p.size() < 2) return n; return p[0] + ":" + p[1] + (p.size() > 3 ? ":" + p[3] : ""); }

struct Prep { std::string cp, assetsId, gameAssets; fs::path natives; };
static void Prepare(const json& v, const std::string& launchId, const fs::path& gameDir, Prep& o) {
    std::string base = v.value("_base", launchId);
    fs::path jar = gRoot / "versions" / P(base) / P(base + ".jar");
    if (v.contains("downloads") && v["downloads"].contains("client")) {
        Status("Проверяю клиент " + base);
        if (!Download(v["downloads"]["client"].value("url", ""), jar)) throw std::runtime_error("Не удалось скачать клиент игры");
    }
    std::vector<Job> jobs; std::vector<fs::path> nativeJars; std::set<std::string> seen; std::vector<std::string> cp;
    for (auto& lib : v["libraries"]) {
        if (!RuleOk(lib.contains("rules") ? lib["rules"] : json())) continue;
        std::string name = lib.value("name", ""), path, url;
        bool hasDl = lib.contains("downloads");
        if (hasDl && lib["downloads"].contains("artifact")) { auto& a = lib["downloads"]["artifact"]; path = a.value("path", ""); url = a.value("url", ""); }
        else if (!lib.contains("natives") && !name.empty()) { path = MavenPath(name); url = lib.value("url", "https://libraries.minecraft.net/") + path; }
        if (!path.empty() && seen.insert(name.empty() ? path : LibKey(name)).second) {
            fs::path f = gRoot / "libraries" / P(path);
            if (!fs::exists(f) && !url.empty()) jobs.push_back({url, f});
            cp.push_back(PS(f));
        }
        if (lib.contains("natives") && lib["natives"].contains("linux") && hasDl && lib["downloads"].contains("classifiers")) {
            std::string c = lib["natives"]["linux"].get<std::string>();
            auto k = c.find("${arch}"); if (k != std::string::npos) c.replace(k, 7, "64");
            auto& cls = lib["downloads"]["classifiers"];
            if (cls.contains(c)) {
                fs::path f = gRoot / "libraries" / P(cls[c].value("path", ""));
                if (!fs::exists(f)) jobs.push_back({cls[c].value("url", ""), f});
                nativeJars.push_back(f);
            }
        }
    }
    Status("Скачиваю библиотеки: " + std::to_string(jobs.size()) + " файлов");
    DownloadAll(jobs, 0.05f, 0.3f);
    o.natives = gRoot / "versions" / P(launchId) / "natives";
    std::error_code ec; fs::create_directories(o.natives, ec);
    for (auto& nj : nativeJars) Unzip(nj, o.natives, true);

    // ассеты
    o.assetsId = v["assetIndex"].value("id", "legacy");
    fs::path ip = gRoot / "assets" / "indexes" / P(o.assetsId + ".json");
    Download(v["assetIndex"].value("url", ""), ip);
    json idx = Parse(ReadAll(ip));
    o.gameAssets = PS(gRoot / "assets");
    if (idx.contains("objects")) {
        bool virt = idx.value("virtual", false), mapRes = idx.value("map_to_resources", false);
        std::vector<Job> aj;
        for (auto it = idx["objects"].begin(); it != idx["objects"].end(); ++it) {
            std::string h = it.value().value("hash", ""); if (h.size() < 2) continue;
            fs::path d = gRoot / "assets" / "objects" / h.substr(0, 2) / h;
            if (!fs::exists(d, ec)) aj.push_back({"https://resources.download.minecraft.net/" + h.substr(0, 2) + "/" + h, d});
        }
        Status("Скачиваю ресурсы игры: " + std::to_string(aj.size()) + " файлов");
        DownloadAll(aj, 0.3f, 0.95f);
        if (virt || mapRes) {
            fs::path dir = virt ? gRoot / "assets" / "virtual" / "legacy" : gameDir / "resources";
            for (auto it = idx["objects"].begin(); it != idx["objects"].end(); ++it) {
                std::string h = it.value().value("hash", ""); if (h.size() < 2) continue;
                fs::path dst = dir / P(it.key());
                if (!fs::exists(dst, ec)) { fs::create_directories(dst.parent_path(), ec); fs::copy_file(gRoot / "assets" / "objects" / h.substr(0, 2) / h, dst, ec); }
            }
            if (virt) o.gameAssets = PS(dir);
        }
    }
    cp.push_back(PS(jar));
    for (size_t i = 0; i < cp.size(); i++) o.cp += (i ? ":" : "") + cp[i];
}

// ============================ Fabric / Forge ============================
static std::string FindInstalled(const std::string& prefix, const std::string& suffix) {
    std::error_code ec;
    for (auto& e : fs::directory_iterator(gRoot / "versions", ec)) {
        std::string n = U8(e.path().filename().string());
        if (n.rfind(prefix, 0) == 0 && n.size() >= suffix.size() && n.compare(n.size() - suffix.size(), suffix.size(), suffix) == 0 && fs::exists(e.path() / (e.path().filename().string() + ".json"), ec)) return n;
    }
    return "";
}
static std::vector<std::string> LoaderProfiles(const std::string& loader, const std::string& mc) { // установленные профили загрузчика для версии игры
    std::vector<std::string> r; std::error_code ec;
    for (auto& e : fs::directory_iterator(gRoot / "versions", ec)) {
        if (!e.is_directory(ec)) continue;
        std::string n = U8(e.path().filename().string()); bool ok = false;
        auto starts = [&](const std::string& p) { return n.rfind(p, 0) == 0; };
        auto ends = [&](const std::string& x) { return n.size() >= x.size() && n.compare(n.size() - x.size(), x.size(), x) == 0; };
        if (loader == "Fabric") ok = starts("fabric-loader-") && ends("-" + mc);
        else if (loader == "Quilt") ok = starts("quilt-loader-") && ends("-" + mc);
        else if (loader == "Forge") ok = starts(mc + "-forge-");
        else if (loader == "OptiFine") ok = starts(mc + "-OptiFine_");
        else if (loader == "NeoForge" && starts("neoforge-")) {
            json j = Parse(ReadAll(e.path() / (e.path().filename().string() + ".json")));
            ok = j.is_object() && j.contains("inheritsFrom") && j["inheritsFrom"].is_string() && j["inheritsFrom"].get<std::string>() == mc;
        }
        if (ok) r.push_back(n);
    }
    return r;
}
static std::string InstallFabric(const std::string& mc) {
    Status("Устанавливаю Fabric...");
    Resp r = Http("https://meta.fabricmc.net/v2/versions/loader");
    json j = Parse(r.body); std::string loader;
    if (j.is_array()) for (auto& x : j) if (x.value("stable", false)) { loader = x.value("version", ""); break; }
    if (loader.empty()) return FindInstalled("fabric-loader-", "-" + mc);
    r = Http("https://meta.fabricmc.net/v2/versions/loader/" + mc + "/" + loader + "/profile/json");
    json pj = Parse(r.body);
    if (r.status != 200 || !pj.contains("id")) throw std::runtime_error("Fabric пока не поддерживает версию " + mc);
    std::string id = pj["id"].get<std::string>();
    WriteAll(gRoot / "versions" / P(id) / P(id + ".json"), r.body);
    return id;
}
static int RunProcess(const std::string& cmd, const fs::path& cwd, std::string& captured);
static std::string InstallForge(const std::string& mc, const std::string& javaExe) {
    Status("Устанавливаю Forge (первый раз это долго)...");
    Resp r = Http("https://files.minecraftforge.net/net/minecraftforge/forge/promotions_slim.json");
    json j = Parse(r.body); std::string fv;
    if (j.contains("promos")) {
        auto& pr = j["promos"];
        if (pr.contains(mc + "-recommended")) fv = pr[mc + "-recommended"].get<std::string>();
        else if (pr.contains(mc + "-latest")) fv = pr[mc + "-latest"].get<std::string>();
    }
    if (fv.empty()) { std::string have = FindInstalled(mc + "-forge-", ""); if (!have.empty()) return have; throw std::runtime_error("Для Minecraft " + mc + " не нашёл Forge"); }
    std::string id = mc + "-forge-" + fv;
    std::error_code ec;
    if (fs::exists(gRoot / "versions" / P(id) / P(id + ".json"), ec)) return id;
    std::string full = mc + "-" + fv;
    fs::path inst = gRoot / "cache" / P("forge-" + full + "-installer.jar");
    if (!Download("https://maven.minecraftforge.net/net/minecraftforge/forge/" + full + "/forge-" + full + "-installer.jar", inst))
        throw std::runtime_error("Не скачался установщик Forge");
    if (!fs::exists(gRoot / "launcher_profiles.json")) WriteAll(gRoot / "launcher_profiles.json", "{\"profiles\":{}}");
    std::string cap;
    int code = RunProcess(Q(javaExe) + " -jar " + Q(PS(inst)) + " --installClient " + Q(PS(gRoot)), gRoot, cap);
    if (!fs::exists(gRoot / "versions" / P(id) / P(id + ".json"), ec)) {
        std::string have = FindInstalled(mc + "-forge-", "");
        if (!have.empty()) return have;
        throw std::runtime_error("Установщик Forge завершился с кодом " + std::to_string(code) + ". Смотри вкладку «Лог».");
    }
    return id;
}

static std::string InstallNeoForge(const std::string& mc, const std::string& javaExe) {
    Status("Устанавливаю NeoForge (первый раз это долго)...");
    std::string fv;
    for (auto& v : NeoVersions()) if (NeoMcOf(v) == mc) { bool st = v.find('-') == std::string::npos; if (st || fv.empty() || fv.find('-') != std::string::npos) fv = v; }
    if (fv.empty()) { auto have = LoaderProfiles("NeoForge", mc); if (!have.empty()) return have[0]; throw std::runtime_error("Для Minecraft " + mc + " не нашёл NeoForge (поддерживается 1.20.2 и новее)"); }
    std::string id = "neoforge-" + fv; std::error_code ec;
    if (fs::exists(gRoot / "versions" / P(id) / P(id + ".json"), ec)) return id;
    fs::path inst = gRoot / "cache" / P("neoforge-" + fv + "-installer.jar");
    if (!Download("https://maven.neoforged.net/releases/net/neoforged/neoforge/" + fv + "/neoforge-" + fv + "-installer.jar", inst)) throw std::runtime_error("Не скачался установщик NeoForge");
    if (!fs::exists(gRoot / "launcher_profiles.json")) WriteAll(gRoot / "launcher_profiles.json", "{\"profiles\":{}}");
    std::string cap; int code = RunProcess(Q(javaExe) + " -jar " + Q(PS(inst)) + " --install-client " + Q(PS(gRoot)), gRoot, cap);
    if (!fs::exists(gRoot / "versions" / P(id) / P(id + ".json"), ec)) { cap.clear(); code = RunProcess(Q(javaExe) + " -jar " + Q(PS(inst)) + " --installClient " + Q(PS(gRoot)), gRoot, cap); }
    if (!fs::exists(gRoot / "versions" / P(id) / P(id + ".json"), ec)) {
        auto have = LoaderProfiles("NeoForge", mc); if (!have.empty()) return have[0];
        throw std::runtime_error("Установщик NeoForge завершился с кодом " + std::to_string(code) + ". Смотри вкладку «Лог».");
    }
    return id;
}
static std::string InstallQuilt(const std::string& mc) {
    Status("Устанавливаю Quilt...");
    Resp r = Http("https://meta.quiltmc.org/v3/versions/loader");
    json j = Parse(r.body); std::string loader;
    if (j.is_array()) for (auto& x : j) if (x.is_object() && x.contains("version") && x["version"].is_string()) { std::string v = x["version"].get<std::string>(); if (!v.empty() && v.find('-') == std::string::npos) { loader = v; break; } }
    if (loader.empty()) return FindInstalled("quilt-loader-", "-" + mc);
    r = Http("https://meta.quiltmc.org/v3/versions/loader/" + mc + "/" + loader + "/profile/json");
    json pj = Parse(r.body);
    if (r.status != 200 || !pj.is_object() || !pj.contains("id")) throw std::runtime_error("Quilt пока не поддерживает версию " + mc);
    std::string id = pj["id"].get<std::string>();
    WriteAll(gRoot / "versions" / P(id) / P(id + ".json"), r.body);
    return id;
}
struct OfV { std::string type, patch; };
static bool OfBetter(const OfV& a, const OfV& b) { // a новее/лучше b
    auto key = [](const OfV& o) {
        bool hdu = o.type == "HD_U", pre = o.patch.rfind("pre", 0) == 0;
        int letter = (!o.patch.empty() && isalpha((unsigned char)o.patch[0])) ? toupper((unsigned char)o.patch[0]) : 0, num = o.patch.size() > 1 ? atoi(o.patch.c_str() + 1) : 0;
        return std::make_tuple(hdu, !pre, letter, num);
    };
    return key(a) > key(b);
}
static bool ExtractZipPrefix(const fs::path& zip, const std::string& prefix, const std::string& suffix, std::string& outName, std::string& outData) {
    std::string data = ReadAll(zip); mz_zip_archive z{};
    if (data.empty() || !mz_zip_reader_init_mem(&z, data.data(), data.size(), 0)) return false;
    bool found = false;
    for (mz_uint i = 0; i < mz_zip_reader_get_num_files(&z) && !found; i++) {
        mz_zip_archive_file_stat st;
        if (!mz_zip_reader_file_stat(&z, i, &st) || mz_zip_reader_is_file_a_directory(&z, i)) continue;
        std::string n = st.m_filename;
        if (n.rfind(prefix, 0) == 0 && n.size() > suffix.size() && n.compare(n.size() - suffix.size(), suffix.size(), suffix) == 0) {
            size_t sz = 0; void* p = mz_zip_reader_extract_to_heap(&z, i, &sz, 0);
            if (p) { outName = n; outData.assign((const char*)p, sz); mz_free(p); found = true; }
        }
    }
    mz_zip_reader_end(&z); return found;
}
static bool ZipHasEntry(const fs::path& zip, const char* name) {
    std::string data = ReadAll(zip); mz_zip_archive z{};
    if (data.empty() || !mz_zip_reader_init_mem(&z, data.data(), data.size(), 0)) return false;
    bool ok = mz_zip_reader_locate_file(&z, name, nullptr, 0) >= 0;
    mz_zip_reader_end(&z); return ok;
}
// OptiFine: скачиваем jar (зеркало BMCLAPI), прогоняем optifine.Patcher над ванильным клиентом и пишем профиль версии (как делает установщик OptiFine)
static std::string InstallOptiFine(const std::string& mc, const std::string& javaExe, const json& parent) {
    Status("Устанавливаю OptiFine...");
    Resp r = Http("https://bmclapi2.bangbang93.com/optifine/" + mc); json j = Parse(r.body);
    std::optional<OfV> best;
    if (j.is_array()) for (auto& x : j) {
        if (!x.is_object() || !x.contains("type") || !x.contains("patch") || !x["type"].is_string() || !x["patch"].is_string()) continue;
        OfV o{x["type"].get<std::string>(), x["patch"].get<std::string>()};
        if (o.type.empty() || o.patch.empty()) continue;
        if (!best || OfBetter(o, *best)) best = o;
    }
    if (!best) {
        auto have = LoaderProfiles("OptiFine", mc); if (!have.empty()) return have[0];
        throw std::runtime_error(r.status == 0 ? "Нет соединения с источником OptiFine (интернет / VPN / фаервол)" : "Для Minecraft " + mc + " нет OptiFine");
    }
    std::string full = mc + "_" + best->type + "_" + best->patch, id = mc + "-OptiFine_" + best->type + "_" + best->patch;
    std::error_code ec;
    if (fs::exists(gRoot / "versions" / P(id) / P(id + ".json"), ec)) return id;
    fs::path inst = gRoot / "cache" / P("OptiFine_" + full + ".jar");
    fs::create_directories(inst.parent_path(), ec);
    std::string ofUrl = "https://bmclapi2.bangbang93.com/optifine/" + mc + "/" + best->type + "/" + best->patch;
    auto fetchOf = [&](bool force) { return Download(ofUrl, inst, force) && ZipHasEntry(inst, "optifine/Patcher.class"); };
    if (!fetchOf(false) && !fetchOf(true)) { fs::remove(inst, ec); throw std::runtime_error("Не скачался OptiFine " + full + " (файл битый или источник недоступен)"); }
    fs::path base = gRoot / "versions" / P(mc) / P(mc + ".jar");
    if (!fs::exists(base, ec) || fs::file_size(base, ec) == 0) throw std::runtime_error("Нет ванильного клиента " + mc + " для патча OptiFine");
    fs::path target = gRoot / "libraries" / "optifine" / "OptiFine" / P(full) / P("OptiFine-" + full + ".jar");
    fs::create_directories(target.parent_path(), ec);
    auto runPatch = [&](const std::string& jx, std::string& cap) {
        fs::remove(target, ec); cap.clear();
        int c = RunProcess(Q(jx) + " -Djava.awt.headless=true -cp " + Q(PS(inst)) + " optifine.Patcher " + Q(PS(base)) + " " + Q(PS(inst)) + " " + Q(PS(target)), gRoot, cap);
        return c;
    };
    auto patched = [&]() { std::error_code e2; return fs::exists(target, e2) && fs::file_size(target, e2) > 0; };
    std::string cap; int code = runPatch(javaExe, cap);
    if (!patched() && cap.find("UnsupportedClassVersionError") != std::string::npos) { // Patcher собран под более новую Java
        size_t pv = cap.find("class file version "); int need = pv != std::string::npos ? atoi(cap.c_str() + pv + 19) - 44 : 0;
        if (need < 8) need = 21;
        std::string j2 = EnsureJava(need);
        if (!j2.empty()) { j2 = JavaExe(j2); code = runPatch(j2, cap); }
    }
    if (!patched()) { // возможно, битый кэш: качаем заново и пробуем ещё раз
        if (Download(ofUrl, inst, true) && ZipHasEntry(inst, "optifine/Patcher.class")) code = runPatch(javaExe, cap);
    }
    if (!patched()) {
        fs::remove(target, ec);
        std::string tail = cap; while (!tail.empty() && (tail.back() == '\n' || tail.back() == '\r' || tail.back() == ' ')) tail.pop_back();
        if (tail.size() > 300) tail = tail.substr(tail.size() - 300);
        throw std::runtime_error("Не удалось применить OptiFine (код " + std::to_string(code) + "). " + tail);
    }
    json libs = json::array(); { json o; o["name"] = "optifine:OptiFine:" + full; libs.push_back(o); }
    std::string lwName, lwData;
    if (ExtractZipPrefix(inst, "launchwrapper-of-", ".jar", lwName, lwData)) {
        std::string lv = lwName.substr(17, lwName.size() - 17 - 4);
        WriteAll(gRoot / "libraries" / "optifine" / "launchwrapper-of" / P(lv) / P("launchwrapper-of-" + lv + ".jar"), lwData);
        json o; o["name"] = "optifine:launchwrapper-of:" + lv; libs.push_back(o);
    } else { json o; o["name"] = "net.minecraft:launchwrapper:1.12"; libs.push_back(o); }
    json vj; vj["id"] = id; vj["inheritsFrom"] = mc; vj["mainClass"] = "net.minecraft.launchwrapper.Launch"; vj["libraries"] = libs;
    if (parent.contains("arguments")) vj["arguments"]["game"] = json::array({"--tweakClass", "optifine.OptiFineTweaker"});
    else {
        std::string ma = (parent.contains("minecraftArguments") && parent["minecraftArguments"].is_string()) ? parent["minecraftArguments"].get<std::string>() : std::string();
        vj["minecraftArguments"] = ma + " --tweakClass optifine.OptiFineTweaker";
    }
    WriteAll(gRoot / "versions" / P(id) / P(id + ".json"), vj.dump(2));
    return id;
}

// ============================ Выбор видеокарты (Linux: PRIME offload) ============================
static std::vector<std::pair<std::string, std::string>> gGameEnv; static std::mutex gEnvMu;
static void ApplyGpuPref(const std::string&, int mode) { // 0 авто, 1 встроенная (экономия), 2 дискретная (производительность)
    std::lock_guard<std::mutex> l(gEnvMu); gGameEnv.clear();
    if (mode == 1) { gGameEnv = {{"DRI_PRIME", "0"}, {"__NV_PRIME_RENDER_OFFLOAD", "0"}}; }
    else if (mode == 2) { gGameEnv = {{"DRI_PRIME", "1"}, {"__NV_PRIME_RENDER_OFFLOAD", "1"}, {"__GLX_VENDOR_LIBRARY_NAME", "nvidia"}, {"__VK_LAYER_NV_optimus", "NVIDIA_only"}}; }
}

// ============================ Запуск процесса и разбор крашей ============================
static std::vector<std::string> SplitCmd(const std::string& s) { // обратная операция к Q(): разбор строки команды в argv (правила как в CommandLineToArgv)
    std::vector<std::string> out; std::string cur; bool inq = false, has = false;
    for (size_t i = 0; i < s.size(); i++) {
        char c = s[i];
        if (c == '\\') {
            size_t j = i; while (j < s.size() && s[j] == '\\') j++;
            size_t n = j - i; has = true;
            if (j < s.size() && s[j] == '"') { cur.append(n / 2, '\\'); if (n % 2) { cur += '"'; i = j; } else i = j - 1; }
            else { cur.append(n, '\\'); i = j - 1; }
            continue;
        }
        if (c == '"') { inq = !inq; has = true; continue; }
        if ((c == ' ' || c == '\t') && !inq) { if (has) { out.push_back(cur); cur.clear(); has = false; } continue; }
        cur += c; has = true;
    }
    if (has) out.push_back(cur);
    return out;
}
static int RunProcess(const std::string& cmd, const fs::path& cwd, std::string& captured) {
    std::vector<std::string> args = SplitCmd(cmd); if (args.empty()) { captured = "empty command"; return -1; }
    std::vector<char*> av; for (auto& a : args) av.push_back(&a[0]); av.push_back(nullptr);
    std::vector<std::string> envs; for (char** e = environ; e && *e; e++) envs.push_back(*e);
    { std::lock_guard<std::mutex> l(gEnvMu);
      for (auto& kv : gGameEnv) {
          std::string pre = kv.first + "=";
          envs.erase(std::remove_if(envs.begin(), envs.end(), [&](const std::string& e) { return e.rfind(pre, 0) == 0; }), envs.end());
          envs.push_back(pre + kv.second);
      } }
    std::vector<char*> ev; for (auto& e : envs) ev.push_back(&e[0]); ev.push_back(nullptr);
    int pfd[2]; if (pipe2(pfd, O_CLOEXEC) != 0) { captured = "pipe failed"; return -1; }
    std::string cwdS = PS(cwd);
    pid_t pid = fork();
    if (pid < 0) { close(pfd[0]); close(pfd[1]); captured = "fork failed"; return -1; }
    if (pid == 0) {
        dup2(pfd[1], 1); dup2(pfd[1], 2);
        int dn = open("/dev/null", O_RDONLY); if (dn >= 0) { dup2(dn, 0); if (dn > 2) close(dn); }
        if (!cwdS.empty() && chdir(cwdS.c_str()) != 0) { /* остаёмся в текущей папке */ }
        execvpe(av[0], av.data(), ev.data());
        static const char m[] = "exec failed: command not found or not executable\n"; if (write(2, m, sizeof(m) - 1) < 0) {}
        _exit(127);
    }
    close(pfd[1]);
    std::string part; char buf[4096]; ssize_t n;
    for (;;) {
        n = read(pfd[0], buf, sizeof(buf));
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) break;
        part.append(buf, (size_t)n); size_t p;
        while ((p = part.find('\n')) != std::string::npos) {
            std::string line = part.substr(0, p); if (!line.empty() && line.back() == '\r') line.pop_back();
            Log(line); captured += line + "\n"; part.erase(0, p + 1);
        }
        if (captured.size() > 400000) captured.erase(0, 200000);
    }
    if (!part.empty()) { Log(part); captured += part; }
    close(pfd[0]);
    int st = 0; while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {}
    if (WIFEXITED(st)) return WEXITSTATUS(st);
    if (WIFSIGNALED(st)) return 128 + WTERMSIG(st);
    return -1;
}
static std::pair<std::string, std::string> Analyze(int code, const std::string& t) {
    auto has = [&](const char* s) { return t.find(s) != std::string::npos; };
    if (has("UnsupportedClassVersionError") || has("class file version")) {
        int need = 0; auto p = t.find("class file version "); if (p != std::string::npos) { int v = atoi(t.c_str() + p + 19); need = v > 44 ? v - 44 : 0; }
        return {"Не та версия Java", "Игре или моду нужна Java " + (need ? std::to_string(need) : std::string("новее")) + ". В «Настройках» выбери «Авто» или подходящую Java."};
    }
    if (has("OutOfMemoryError") || has("Java heap space") || has("Could not reserve enough space"))
        return {"Не хватает памяти", "Игре не хватило оперативной памяти. Подними лимит в «Настройках» (для модов обычно 4–6 ГБ) и закрой тяжёлые программы. Если Java 32-бит — поставь 64-бит."};
    if (has("Unrecognized VM option") || has("Could not create the Java Virtual Machine") || has("Invalid maximum heap size"))
        return {"Java не смогла стартовать", "JVM отказалась запускаться: проблема в аргументах или в 32-битной Java. Попробуй «Авто» для Java и меньше ОЗУ."};
    if (has("Found duplicate mods") || has("DuplicateModsFoundException") || has("Duplicate mod"))
        return {"Дубли модов", "В папке mods лежат две копии одного мода. Оставь одну."};
    if (has("Incompatible mod set") || has("Mod resolution failed") || has("Missing or unsupported mandatory dependencies") || has("requires") && has("mod"))
        return {"Конфликт или нехватка зависимостей модов", "Какому-то моду нужна другая версия игры/загрузчика или другой мод (часто Fabric API). Прочитай в логе строки со словом «requires» или «Missing»."};
    if (has("Mixin apply failed") || has("MixinTransformerError") || has("InvalidInjectionException"))
        return {"Мод сломал игру (Mixin)", "Один из модов не совместим с этой версией или с другим модом. Убирай моды по одному, начиная с последних добавленных."};
    if (has("NoClassDefFoundError") || has("ClassNotFoundException"))
        return {"Не найден класс (мод/библиотека)", "Чаще всего мод собран не под эту версию игры или не под этот загрузчик (Fabric/Forge). Проверь версии модов."};
    if (has("UnsatisfiedLinkError") || has("Failed to locate library") || has("lwjgl") && has("natives"))
        return {"Сломались нативные библиотеки", "Удали папку versions/<версия>/natives в папке лаунчера и запусти заново."};
    if (has("GLFW error") || has("Pixel format not accelerated") || has("WGL") || has("Failed to create window") || has("OpenGL"))
        return {"Проблема с видеокартой / OpenGL", "Обнови драйвер видеокарты. На ноутбуке запускай Java на дискретной GPU. Не работает в удалённом рабочем столе."};
    if (has("UnknownHostException") || has("SSLHandshakeException") || has("Connection timed out") || has("Failed to download"))
        return {"Проблема с сетью", "Не получилось скачать что-то по сети. Проверь интернет, VPN, антивирус/фаервол."};
    if (has("Invalid session") || has("Failed to verify username") || has("Bad login"))
        return {"Проблема с аккаунтом", "Сессия недействительна. Перелогинься во вкладке «Аккаунт»."};
    if (code == -1073741819 || code == (int)0xC0000005 || code == 139)
        return {"Аварийное закрытие процесса (0xC0000005 / SIGSEGV)", "Чаще всего виноваты драйвер видеокарты, оверлеи (Discord, MSI Afterburner, GeForce Experience) или антивирус. Отключи оверлеи и обнови драйвер."};
    std::string hint; size_t p = t.find("Exception in thread");
    if (p == std::string::npos) p = t.find("Caused by:");
    if (p != std::string::npos) { size_t e = t.find('\n', p); hint = "\n\nПохоже на:\n" + t.substr(p, std::min<size_t>(e == std::string::npos ? 300 : e - p, 300)); }
    return {"Игра закрылась с кодом " + std::to_string(code), "Точная причина не опознана. Открой вкладку «Лог» и ищи строки с Exception / Error." + hint};
}

// ============================ Аккаунты ============================
static bool ValidNick(const std::string& n) {
    if (n.size() < 3 || n.size() > 16) return false;
    for (unsigned char c : n) if (!(isalnum(c) || c == '_')) return false;
    return true;
}
static const char* kNickHint = "Ник: 3-16 символов, только латиница, цифры и _";
static std::string JStr(const json& j, const char* k) { return (j.is_object() && j.contains(k) && j[k].is_string()) ? j[k].get<std::string>() : std::string(); }
static std::string FirstLine(const std::string& s) { size_t p = s.find_first_of("\r\n"); return p == std::string::npos ? s : s.substr(0, p); }
static void Md5(const unsigned char* data, size_t len, unsigned char out[16]) { // RFC 1321 (для offline-UUID как в Java: UUID.nameUUIDFromBytes)
    static uint32_t K[64]; static bool init = false;
    static const int Rr[64] = {7,12,17,22,7,12,17,22,7,12,17,22,7,12,17,22, 5,9,14,20,5,9,14,20,5,9,14,20,5,9,14,20,
                               4,11,16,23,4,11,16,23,4,11,16,23,4,11,16,23, 6,10,15,21,6,10,15,21,6,10,15,21,6,10,15,21};
    if (!init) { for (int i = 0; i < 64; i++) K[i] = (uint32_t)(4294967296.0 * std::fabs(std::sin((double)(i + 1)))); init = true; }
    std::string m((const char*)data, len); m += (char)0x80;
    while (m.size() % 64 != 56) m += (char)0;
    uint64_t bits = (uint64_t)len * 8; for (int i = 0; i < 8; i++) m += (char)((bits >> (8 * i)) & 0xff);
    uint32_t a0 = 0x67452301, b0 = 0xefcdab89, c0 = 0x98badcfe, d0 = 0x10325476;
    for (size_t off = 0; off < m.size(); off += 64) {
        uint32_t M[16]; for (int i = 0; i < 16; i++) { const unsigned char* q = (const unsigned char*)m.data() + off + i * 4; M[i] = q[0] | (q[1] << 8) | (q[2] << 16) | ((uint32_t)q[3] << 24); }
        uint32_t A = a0, B = b0, C = c0, D = d0;
        for (int i = 0; i < 64; i++) {
            uint32_t F; int g;
            if (i < 16) { F = (B & C) | (~B & D); g = i; }
            else if (i < 32) { F = (D & B) | (~D & C); g = (5 * i + 1) % 16; }
            else if (i < 48) { F = B ^ C ^ D; g = (3 * i + 5) % 16; }
            else { F = C ^ (B | ~D); g = (7 * i) % 16; }
            F = F + A + K[i] + M[g]; A = D; D = C; C = B; B = B + ((F << Rr[i]) | (F >> (32 - Rr[i])));
        }
        a0 += A; b0 += B; c0 += C; d0 += D;
    }
    uint32_t r[4] = {a0, b0, c0, d0}; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) out[i * 4 + j] = (unsigned char)((r[i] >> (8 * j)) & 0xff);
}
static std::string OfflineUuid(const std::string& name) {
    std::string s = "OfflinePlayer:" + name; unsigned char d[16] = {0};
    Md5((const unsigned char*)s.data(), s.size(), d);
    d[6] = (d[6] & 0x0f) | 0x30; d[8] = (d[8] & 0x3f) | 0x80;
    static const char* hx = "0123456789abcdef"; std::string r;
    for (int i = 0; i < 16; i++) { r += hx[d[i] >> 4]; r += hx[d[i] & 15]; }
    return r;
}
static Account MsChain(const std::string& msTok, const std::string& refresh) {
    json b1 = {{"Properties", {{"AuthMethod", "RPS"}, {"SiteName", "user.auth.xboxlive.com"}, {"RpsTicket", "d=" + msTok}}}, {"RelyingParty", "http://auth.xboxlive.com"}, {"TokenType", "JWT"}};
    Resp r = PostJson("https://user.auth.xboxlive.com/user/authenticate", b1);
    if (r.status == 0) throw std::runtime_error("Нет соединения с Xbox Live (интернет / VPN / фаервол)");
    json x = Parse(r.body);
    if (!x.contains("Token")) throw std::runtime_error("Xbox Live: ошибка " + std::to_string(r.status));
    std::string xbl = x["Token"].get<std::string>(), uhs = x["DisplayClaims"]["xui"][0]["uhs"].get<std::string>();
    json b2 = {{"Properties", {{"SandboxId", "RETAIL"}, {"UserTokens", json::array({xbl})}}}, {"RelyingParty", "rp://api.minecraftservices.com/"}, {"TokenType", "JWT"}};
    r = PostJson("https://xsts.auth.xboxlive.com/xsts/authorize", b2);
    x = Parse(r.body);
    if (!x.contains("Token")) {
        std::string why = "XSTS: ошибка " + std::to_string(r.status);
        if (x.contains("XErr")) { long long e = x["XErr"].get<long long>(); if (e == 2148916233LL) why = "У этой учётки Microsoft нет профиля Xbox"; else if (e == 2148916238LL) why = "Детская учётка: нужно разрешение родителя в семейной группе"; else if (e == 2148916235LL) why = "Xbox Live недоступен в стране этой учётки"; else if (e == 2148916236LL || e == 2148916237LL) why = "Нужна проверка возраста учётки Xbox (account.xbox.com)"; }
        throw std::runtime_error(why);
    }
    std::string xsts = x["Token"].get<std::string>();
    r = PostJson("https://api.minecraftservices.com/authentication/login_with_xbox", json{{"identityToken", "XBL3.0 x=" + uhs + ";" + xsts}});
    x = Parse(r.body);
    if (!x.contains("access_token")) {
        std::string em = JStr(x, "errorMessage");
        if (r.status == 403 || em.find("Invalid app registration") != std::string::npos)
            throw std::runtime_error("Mojang не одобрил этот Azure Client ID (Invalid app registration). Подай заявку: https://aka.ms/mce-reviewappid - до одобрения вход через Microsoft не заработает.");
        throw std::runtime_error("Minecraft Services: ошибка " + std::to_string(r.status) + (em.empty() ? "" : " (" + em + ")"));
    }
    std::string tok = x["access_token"].get<std::string>();
    r = Http("https://api.minecraftservices.com/minecraft/profile", "GET", "", "Authorization: Bearer " + tok + "\r\n");
    x = Parse(r.body);
    if (!x.contains("name")) throw std::runtime_error("На этой учётке нет купленной Minecraft Java Edition");
    Account a; a.type = 2; a.name = x["name"].get<std::string>(); a.uuid = x["id"].get<std::string>(); a.token = tok; a.refresh = refresh;
    return a;
}
static void MsRefresh(Account& a) {
    if (a.refresh.empty() || MsId().empty()) throw std::runtime_error("Нужно заново войти через Microsoft");
    Resp r = Http("https://login.microsoftonline.com/consumers/oauth2/v2.0/token", "POST",
                  Form({{"client_id", MsId()}, {"grant_type", "refresh_token"}, {"refresh_token", a.refresh}, {"scope", "XboxLive.signin offline_access"}}), kFormHdr);
    json j = Parse(r.body);
    if (!j.contains("access_token")) throw std::runtime_error("Сессия Microsoft истекла — войди заново");
    a = MsChain(j["access_token"].get<std::string>(), j.value("refresh_token", a.refresh));
}
static void MsLoginThread() {
    if (gAuthBusy.exchange(true)) return;
    struct Done { ~Done() { gAuthBusy = false; } } done_;
    try {
        if (MsId().empty()) throw std::runtime_error("Не задан Azure Client ID — вставь его в поле на вкладке «Аккаунт»");
        AuthMsg("Microsoft: запрашиваю код...");
        Resp r = Http("https://login.microsoftonline.com/consumers/oauth2/v2.0/devicecode", "POST",
                      Form({{"client_id", MsId()}, {"scope", "XboxLive.signin offline_access"}}), kFormHdr);
        json d = Parse(r.body);
        if (!d.contains("device_code")) {
            std::string ed = FirstLine(JStr(d, "error_description"));
            throw std::runtime_error("Microsoft не выдал код" + (ed.empty() ? std::string(". Проверь Client ID.") : ": " + ed));
        }
        std::string uri = d.value("verification_uri", "https://microsoft.com/link");
        { std::lock_guard<std::mutex> l(gMu); gMsCode = d.value("user_code", ""); gMsUri = uri; }
        OpenExternal(uri);
        int interval = d.value("interval", 5), left = d.value("expires_in", 900);
        while (left > 0) {
            Sleep(interval * 1000); left -= interval;
            Resp t = Http("https://login.microsoftonline.com/consumers/oauth2/v2.0/token", "POST",
                          Form({{"client_id", MsId()}, {"grant_type", "urn:ietf:params:oauth:grant-type:device_code"}, {"device_code", d["device_code"].get<std::string>()}}), kFormHdr);
            json j = Parse(t.body);
            if (j.contains("access_token")) {
                AuthMsg("Microsoft: вхожу в Xbox / Minecraft...");
                Account a = MsChain(j["access_token"].get<std::string>(), j.value("refresh_token", ""));
                { std::lock_guard<std::mutex> l(gMu); gNewAcc = a; gMsCode.clear(); }
                AuthMsg("Вошёл как " + a.name); return;
            }
            std::string e = j.value("error", "");
            if (e == "slow_down") interval += 5;
            else if (e != "authorization_pending") { std::string ed = FirstLine(JStr(j, "error_description")); throw std::runtime_error("Вход отменён или истёк (" + e + ")" + (ed.empty() ? "" : ": " + ed)); }
        }
        throw std::runtime_error("Время ожидания кода вышло");
    } catch (std::exception& e) { { std::lock_guard<std::mutex> l(gMu); gMsCode.clear(); } AuthMsg(std::string("Ошибка входа: ") + e.what()); }
}
static void ElyRefresh(Account& a) {
    Resp r = PostJson("https://authserver.ely.by/auth/validate", json{{"accessToken", a.token}});
    if (r.status == 200 || r.status == 204 || r.status == 0) return; // валиден (или нет сети - пробуем как есть)
    if (a.refresh.empty()) throw std::runtime_error("Сессия Ely.by истекла - войди заново во вкладке «Аккаунт»");
    r = PostJson("https://authserver.ely.by/auth/refresh", json{{"accessToken", a.token}, {"clientToken", a.refresh}});
    json j = Parse(r.body);
    if (!j.contains("accessToken")) throw std::runtime_error("Сессия Ely.by истекла - войди заново во вкладке «Аккаунт»");
    a.token = j["accessToken"].get<std::string>();
}
static void ElyLoginThread(std::string u, std::string p) {
    if (gAuthBusy.exchange(true)) return;
    struct Done { ~Done() { gAuthBusy = false; } } done_;
    try {
        AuthMsg("Ely.by: вхожу...");
        std::string ct = RandHex(16);
        Resp r = PostJson("https://authserver.ely.by/auth/authenticate", json{{"username", u}, {"password", p}, {"clientToken", ct}, {"requestUser", true}});
        if (r.status == 0) throw std::runtime_error("Нет соединения с authserver.ely.by (интернет / VPN / фаервол)");
        json j = Parse(r.body);
        if (!j.contains("accessToken")) {
            std::string em = JStr(j, "errorMessage");
            if (em.find("two factor") != std::string::npos || em.find("two-factor") != std::string::npos) em = "включена 2FA - пиши в поле пароля «пароль:код»";
            throw std::runtime_error("Ely.by: " + (em.empty() ? "ошибка " + std::to_string(r.status) : em));
        }
        if (!j.contains("selectedProfile") || !j["selectedProfile"].is_object()) throw std::runtime_error("У аккаунта Ely.by нет выбранного профиля");
        Account a; a.type = 1; a.token = j["accessToken"].get<std::string>(); a.refresh = ct;
        a.name = j["selectedProfile"].value("name", u); a.uuid = j["selectedProfile"].value("id", "");
        { std::lock_guard<std::mutex> l(gMu); gNewAcc = a; }
        AuthMsg("Вошёл как " + a.name + " (Ely.by)");
    } catch (std::exception& e) { AuthMsg(std::string("Ошибка входа: ") + e.what()); }
}

// ============================ Конфиг ============================
struct Config {
    std::string loader = "Vanilla", version, javaPath, bg, shotsDir;
    std::string gameDir; // пусто = стандартная
    bool snapshots = false, showBeta = false, showAlpha = false, slideshow = true;
    int ramMB = 4096, sel = -1, onLaunch = 0; // onLaunch: 0 оставить, 1 свернуть, 2 закрыть
    int lang = 0, color = 1, gpu = 0; // язык (0 ru, 1 en), цвет лаунчера (0..4), видеокарта
    bool light = false, rounded = true, modsOn = true, logsOn = true;
    std::string jvmArgs;
    std::vector<Account> accs;
};
static Config cfg;
static void SaveConfig() {
    json j; j["loader"] = cfg.loader; j["version"] = cfg.version; j["java"] = cfg.javaPath; j["bg"] = cfg.bg; j["shots"] = cfg.shotsDir;
    j["snap"] = cfg.snapshots; j["slide"] = cfg.slideshow; j["ram"] = cfg.ramMB; j["sel"] = cfg.sel; j["msid"] = MsId(); j["gamedir"] = cfg.gameDir; j["beta"] = cfg.showBeta; j["alpha"] = cfg.showAlpha; j["onlaunch"] = cfg.onLaunch;
    j["lang"] = cfg.lang; j["color"] = cfg.color; j["gpu"] = cfg.gpu; j["light"] = cfg.light; j["round"] = cfg.rounded; j["mods"] = cfg.modsOn; j["logs"] = cfg.logsOn; j["jvm"] = cfg.jvmArgs;
    for (auto& a : cfg.accs) j["accs"].push_back({{"type", a.type}, {"name", a.name}, {"uuid", a.uuid}, {"token", a.token}, {"refresh", a.refresh}});
    WriteAll(gCfgDir / "config.json", j.dump(2));
}
static void LoadConfig() {
    json j = Parse(ReadAll(gCfgDir / "config.json")); if (!j.is_object()) return;
    try {
        cfg.loader = j.value("loader", "Vanilla"); cfg.version = j.value("version", ""); cfg.javaPath = j.value("java", ""); cfg.bg = j.value("bg", ""); cfg.shotsDir = j.value("shots", "");
        cfg.snapshots = j.value("snap", false); cfg.slideshow = j.value("slide", true); cfg.ramMB = j.value("ram", 4096); cfg.sel = j.value("sel", -1);
        { std::string id = j.value("msid", ""); if (!id.empty()) SetMsId(id); }
        cfg.gameDir = j.value("gamedir", ""); cfg.showBeta = j.value("beta", false); cfg.showAlpha = j.value("alpha", false); cfg.onLaunch = j.value("onlaunch", 0);
        cfg.lang = j.value("lang", 0); cfg.color = j.value("color", 1); cfg.gpu = j.value("gpu", 0); cfg.light = j.value("light", false); cfg.rounded = j.value("round", true);
        cfg.modsOn = j.value("mods", true); cfg.logsOn = j.value("logs", true); cfg.jvmArgs = j.value("jvm", "");
        if (j.contains("accs")) for (auto& a : j["accs"]) cfg.accs.push_back({a.value("type", 0), a.value("name", ""), a.value("uuid", ""), a.value("token", ""), a.value("refresh", "")});
    } catch (...) {}
}

// ============================ Экземпляры ============================
// Папка экземпляра зависит только от загрузчика и версии игры (а не от версии самого загрузчика):
// так моды и миры не «теряются» при обновлении Fabric/Forge и лежат ровно там, откуда стартует игра.
static const char* const kLoaders[] = {"Vanilla", "Fabric", "Forge", "NeoForge", "Quilt", "OptiFine"};
static const int kNLoaders = 6;
static std::string InstName(const std::string& loader, const std::string& mc) {
    return loader == "Fabric" ? mc + "-fabric" : loader == "Forge" ? mc + "-forge" : loader == "NeoForge" ? mc + "-neoforge" :
           loader == "Quilt" ? mc + "-quilt" : loader == "OptiFine" ? mc + "-optifine" : mc;
}
static void MigrateInstances() { // старые имена (fabric-loader-0.16.9-1.21.1, 1.20.1-forge-47.2.0) -> новые
    std::error_code ec; fs::path root = gRoot / "instances"; std::vector<std::string> names;
    for (auto& e : fs::directory_iterator(root, ec)) if (e.is_directory(ec)) names.push_back(U8(e.path().filename().string()));
    for (auto& n : names) {
        std::string mc, ld;
        if (n.rfind("fabric-loader-", 0) == 0) { std::string rest = n.substr(14); size_t p = rest.find('-'); if (p != std::string::npos) { ld = "Fabric"; mc = rest.substr(p + 1); } }
        else { size_t p = n.find("-forge-"); if (p != std::string::npos && p > 0) { ld = "Forge"; mc = n.substr(0, p); } }
        if (ld.empty() || mc.empty()) continue;
        fs::path to = root / P(InstName(ld, mc));
        if (!fs::exists(to, ec)) fs::rename(root / P(n), to, ec);
    }
}
static void DeleteInstance(const std::string& loader, const std::string& mc) {
    std::error_code ec; fs::path inst = gRoot / "instances", vd = gRoot / "versions";
    fs::remove_all(inst / P(InstName(loader, mc)), ec);
    if (loader != "Vanilla") { for (auto& id : LoaderProfiles(loader, mc)) fs::remove_all(vd / P(id), ec); return; }
    bool used = false; // ваниль нужна загрузчикам этой же версии
    for (int i = 1; i < kNLoaders; i++) if (fs::exists(inst / P(InstName(kLoaders[i], mc)), ec)) used = true;
    if (!used) fs::remove_all(vd / P(mc), ec);
}

// ---------- Настройки конкретного экземпляра (Изменить экземпляр) ----------
struct InstCfg {
    bool memOv = false; int minMB = 512, maxMB = 4096;
    bool javaOv = false, skipCompat = false; std::string javaPath, jvmArgs;
    bool mcOv = false, fullscreen = false; int width = 854, height = 480;
    bool cmdOv = false; std::string wrapper, pre, post;
    bool envOv = false; std::string env; // KEY=VALUE по строкам
};
static fs::path InstCfgPath(const fs::path& d) { return d / "poltergeist_instance.json"; }
static InstCfg LoadInstCfg(const fs::path& d) {
    InstCfg c; json j = Parse(ReadAll(InstCfgPath(d))); if (!j.is_object()) return c;
    try {
        c.memOv = j.value("memOv", false); c.minMB = j.value("minMB", 512); c.maxMB = j.value("maxMB", 4096);
        c.javaOv = j.value("javaOv", false); c.skipCompat = j.value("skipCompat", false); c.javaPath = j.value("javaPath", ""); c.jvmArgs = j.value("jvmArgs", "");
        c.mcOv = j.value("mcOv", false); c.fullscreen = j.value("fullscreen", false); c.width = j.value("width", 854); c.height = j.value("height", 480);
        c.cmdOv = j.value("cmdOv", false); c.wrapper = j.value("wrapper", ""); c.pre = j.value("pre", ""); c.post = j.value("post", "");
        c.envOv = j.value("envOv", false); c.env = j.value("env", "");
    } catch (...) {}
    return c;
}
static void SaveInstCfg(const fs::path& d, const InstCfg& c) {
    json j; j["memOv"] = c.memOv; j["minMB"] = c.minMB; j["maxMB"] = c.maxMB; j["javaOv"] = c.javaOv; j["skipCompat"] = c.skipCompat; j["javaPath"] = c.javaPath; j["jvmArgs"] = c.jvmArgs;
    j["mcOv"] = c.mcOv; j["fullscreen"] = c.fullscreen; j["width"] = c.width; j["height"] = c.height;
    j["cmdOv"] = c.cmdOv; j["wrapper"] = c.wrapper; j["pre"] = c.pre; j["post"] = c.post; j["envOv"] = c.envOv; j["env"] = c.env;
    WriteAll(InstCfgPath(d), j.dump(2));
}
static std::vector<std::pair<std::string, std::string>> ParseEnvText(const std::string& t) {
    std::vector<std::pair<std::string, std::string>> r;
    for (auto line : Split(t, '\n')) {
        while (!line.empty() && (line.back() == '\r' || line.back() == ' ')) line.pop_back();
        size_t b = line.find_first_not_of(" \t"); if (b == std::string::npos || line[b] == '#') continue;
        size_t eq = line.find('=', b); if (eq == std::string::npos || eq == b) continue;
        std::string k = line.substr(b, eq - b); while (!k.empty() && k.back() == ' ') k.pop_back();
        r.push_back({k, line.substr(eq + 1)});
    }
    return r;
}
struct EnvGuard { // выставляет переменные окружения на время запуска и возвращает как было (RunProcess читает environ)
    std::vector<std::pair<std::string, std::optional<std::string>>> old;
    void Set(const std::string& k, const std::string& v) {
        const char* o = getenv(k.c_str());
        if (o) old.push_back({k, std::string(o)}); else old.push_back({k, std::nullopt});
        setenv(k.c_str(), v.c_str(), 1);
    }
    ~EnvGuard() { for (size_t i = old.size(); i-- > 0;) { if (old[i].second) setenv(old[i].first.c_str(), old[i].second->c_str(), 1); else unsetenv(old[i].first.c_str()); } }
};

static void SetGameDir(const std::string& d) { // пустая строка = стандартная папка
    if (gBusy) return;
    fs::path np = d.empty() ? gCfgDir : P(d);
    std::error_code ec; fs::create_directories(np, ec);
    if (ec || !fs::is_directory(np, ec)) { Status("Не удалось использовать эту папку"); return; }
    gRoot = np; cfg.gameDir = (np == gCfgDir) ? std::string() : d; SaveConfig(); MigrateInstances();
    Status("Папка игры: " + PS(gRoot));
}

// ============================ Запуск игры ============================
static void LaunchThread(Config c, Account acc) {
    gBusy = true; gProg = 0;
    try {
        if (acc.type == 2) { Status("Обновляю сессию Microsoft..."); MsRefresh(acc); { std::lock_guard<std::mutex> l(gMu); gNewAcc = acc; } }
        else if (acc.type == 1) { Status("Проверяю сессию Ely.by..."); ElyRefresh(acc); { std::lock_guard<std::mutex> l(gMu); gNewAcc = acc; } }
        fs::path gameDir = gRoot / "instances" / P(InstName(c.loader, c.version));
        InstCfg ic = LoadInstCfg(gameDir); // свои настройки экземпляра
        if (ic.javaOv) { c.javaPath = ic.javaPath; c.jvmArgs = ic.jvmArgs; }
        int xmx = c.ramMB, xms = std::min(c.ramMB, 512);
        if (ic.memOv) { xmx = std::max(256, ic.maxMB); xms = std::clamp(ic.minMB, 128, xmx); }
        Status("Получаю описание версии " + c.version);
        json v = LoadVersionJson(c.version);
        if (v.is_null()) throw std::runtime_error("Не удалось получить версию " + c.version + " (нет интернета?)");
        int need = v.contains("javaVersion") ? v["javaVersion"].value("majorVersion", 8) : 8;
        std::string javaPick = c.javaPath.empty() ? EnsureJava(need) : JavaExe(c.javaPath);
        if (javaPick.empty()) throw std::runtime_error("Java не найдена и не скачалась");
        std::string launchId = c.version;
        Prep pre; Prepare(v, c.version, gameDir, pre); // сначала ваниль (нужна и Forge-установщику)
        if (c.loader == "Fabric") launchId = InstallFabric(c.version);
        else if (c.loader == "Forge") launchId = InstallForge(c.version, javaPick);
        else if (c.loader == "NeoForge") launchId = InstallNeoForge(c.version, javaPick);
        else if (c.loader == "Quilt") launchId = InstallQuilt(c.version);
        else if (c.loader == "OptiFine") launchId = InstallOptiFine(c.version, javaPick, v);
        if (launchId.empty()) throw std::runtime_error("Не удалось установить " + c.loader);
        json lv = launchId == c.version ? v : LoadVersionJson(launchId);
        if (lv.is_null()) throw std::runtime_error("Не нашёл описание профиля " + launchId);
        int need2 = lv.contains("javaVersion") ? lv["javaVersion"].value("majorVersion", 8) : 8;
        std::string java = c.javaPath.empty() ? EnsureJava(need2) : javaPick;
        if (java.empty()) throw std::runtime_error("Java не найдена");
        if (!c.javaPath.empty() && !(ic.javaOv && ic.skipCompat)) { // проверка совместимости своей Java
            int jm = JavaMajorFromHome(P(java).parent_path().parent_path());
            if (jm > 0 && jm < need2) throw std::runtime_error("Выбранная Java " + std::to_string(jm) + " слишком старая: для " + launchId + " нужна Java " + std::to_string(need2) + ". Выбери другую Java или включи «Пропустить проверку совместимости» в настройках экземпляра.");
        }
        Prep pp; Prepare(lv, launchId, gameDir, pp);
        std::error_code ec; fs::create_directories(gameDir, ec); // экземпляр «установлен» только после успешной подготовки

        std::map<std::string, std::string> vars = {
            {"auth_player_name", acc.name}, {"version_name", launchId}, {"game_directory", PS(gameDir)}, {"assets_root", PS(gRoot / "assets")},
            {"assets_index_name", pp.assetsId}, {"auth_uuid", acc.uuid}, {"auth_access_token", acc.type == 0 ? "0" : acc.token}, {"clientid", ""}, {"auth_xuid", ""},
            {"user_type", acc.type == 2 ? "msa" : (acc.type == 1 ? "mojang" : "legacy")}, {"version_type", lv.value("type", "release")},
            {"natives_directory", PS(pp.natives)}, {"launcher_name", "PoltergeistLauncher"}, {"launcher_version", kVer}, {"classpath", pp.cp},
            {"classpath_separator", ":"}, {"library_directory", PS(gRoot / "libraries")}, {"game_assets", pp.gameAssets},
            {"auth_session", acc.token}, {"user_properties", "{}"}};
        std::string base = lv.value("_base", c.version);
        auto addArgs = [&](const json& arr, std::vector<std::string>& out) {
            for (auto& a : arr) {
                auto push = [&](std::string s) {
                    if (s.rfind("-DignoreList", 0) == 0) { auto k = s.find("${version_name}"); if (k != std::string::npos) s.replace(k, 15, base); }
                    out.push_back(Sub(s, vars));
                };
                if (a.is_string()) push(a.get<std::string>());
                else if (a.is_object() && RuleOk(a.contains("rules") ? a["rules"] : json())) {
                    if (a["value"].is_string()) push(a["value"].get<std::string>());
                    else for (auto& x : a["value"]) push(x.get<std::string>());
                }
            }
        };
        std::vector<std::string> jvm, game;
        if (lv.contains("arguments")) { if (lv["arguments"].contains("jvm")) addArgs(lv["arguments"]["jvm"], jvm); if (lv["arguments"].contains("game")) addArgs(lv["arguments"]["game"], game); }
        else {
            jvm = {Sub("-Djava.library.path=${natives_directory}", vars), "-cp", pp.cp};
            for (auto& s : Split(lv.value("minecraftArguments", ""), ' ')) if (!s.empty()) game.push_back(Sub(s, vars));
        }
        if (ic.mcOv) { // параметры окна игры
            if (ic.fullscreen) game.push_back("--fullscreen");
            else { game.push_back("--width"); game.push_back(std::to_string(ic.width)); game.push_back("--height"); game.push_back(std::to_string(ic.height)); }
        }
        std::string cmd = Q(JavaExe(java)) + " -Xmx" + std::to_string(xmx) + "M -Xms" + std::to_string(xms) + "M -XX:+UseG1GC -XX:MaxGCPauseMillis=50";
        if (acc.type == 1) {
            fs::path ai = gRoot / "cache" / "authlib-injector.jar";
            if (!Download(kAuthlibUrl, ai)) throw std::runtime_error("Не скачался authlib-injector (нужен для Ely.by)");
            cmd += " " + Q("-javaagent:" + PS(ai) + "=https://authserver.ely.by/api/authlib-injector");
        }
        if (!c.jvmArgs.empty()) cmd += " " + c.jvmArgs;
        ApplyGpuPref(JavaExe(java), c.gpu);
        for (auto& s : jvm) cmd += " " + Q(s);
        cmd += " " + Q(lv.value("mainClass", "net.minecraft.client.main.Main"));
        for (auto& s : game) cmd += " " + Q(s);

        // пользовательские команды и переменные окружения экземпляра
        std::map<std::string, std::string> iv = {{"INST_NAME", InstName(c.loader, c.version)}, {"INST_ID", launchId}, {"INST_DIR", PS(gameDir)}, {"INST_MC_DIR", PS(gameDir)},
                                                 {"INST_JAVA", JavaExe(java)}, {"INST_MC_VER", c.version}, {"INST_LOADER", c.loader}};
        auto sd = [&](std::string t) { for (auto& [k, val] : iv) { std::string key = "$" + k; size_t p = 0; while ((p = t.find(key, p)) != std::string::npos) { t.replace(p, key.size(), val); p += val.size(); } } return t; };
        EnvGuard eg; for (auto& [k, val] : iv) eg.Set(k, val);
        if (ic.envOv) for (auto& kv : ParseEnvText(ic.env)) eg.Set(kv.first, sd(kv.second));
        if (ic.cmdOv && !ic.wrapper.empty()) cmd = sd(ic.wrapper) + " " + cmd;
        if (ic.cmdOv && !ic.pre.empty()) {
            Status("Выполняю команду перед запуском...");
            std::string pc; int pcode = RunProcess("/bin/sh -c " + Q(sd(ic.pre)), gameDir, pc);
            if (pcode != 0) throw std::runtime_error("Команда перед запуском завершилась с кодом " + std::to_string(pcode) + ", игра не запущена.");
        }

        gProg = 1.0f; Status("Игра запущена (" + launchId + ")");
        gGameRunning = true; int act = c.onLaunch;
        if (act == 1 || act == 2) std::thread([act] { // свернуть/закрыть лаунчер, если игра успешно стартовала и не упала
            for (int i = 0; i < (act == 1 ? 8 : 40) && gGameRunning; i++) Sleep(500);
            if (!gGameRunning) return;
            gWinCmd = (act == 1) ? 1 : 3;
        }).detach();
        std::string cap; int code = RunProcess(cmd, gameDir, cap);
        gGameRunning = false;
        if (ic.cmdOv && !ic.post.empty()) { std::string pc2; RunProcess("/bin/sh -c " + Q(sd(ic.post)), gameDir, pc2); }
        if (act == 1) gWinCmd = 2; // игра закрылась - вернуть лаунчер из фона
        if (gLogOn) WriteAll(gCfgDir / "latest.log", cap);
        if (code != 0) { auto [t, b] = Analyze(code, cap); Status("Игра завершилась с ошибкой: " + t); ShowError(t, b); }
        else Status("Игра закрыта");
    } catch (std::exception& e) {
        Status(std::string("Ошибка: ") + e.what()); ShowError("Не удалось запустить", e.what());
    }
    gBusy = false;
}
static bool AddOffline(const std::string& name) {
    if (!ValidNick(name)) { AuthMsg(kNickHint); return false; }
    for (int i = 0; i < (int)cfg.accs.size(); i++) if (cfg.accs[i].type == 0 && cfg.accs[i].name == name) { cfg.sel = i; SaveConfig(); return true; }
    Account a; a.name = name; a.uuid = OfflineUuid(name); cfg.accs.push_back(a); cfg.sel = (int)cfg.accs.size() - 1; SaveConfig();
    return true;
}
static void StartLaunch() {
    if (gBusy || gDelBusy) return;
    if (cfg.accs.empty() && !AddOffline(bNick)) return; // нет аккаунтов - играем офлайн с ником из поля ввода
    if (cfg.sel < 0 || cfg.sel >= (int)cfg.accs.size()) cfg.sel = 0;
    SaveConfig();
    std::thread(LaunchThread, cfg, cfg.accs[cfg.sel]).detach();
}

// ============================ Фон: скриншоты ============================
struct Tex { GLuint v = 0; int w = 0, h = 0; };
static Tex gBg[2]; static float gFade = 1, gSlideT = 0, gTime = 0;
static std::string gBgNow; static std::vector<std::string> gShots;
static std::mutex gImgMu; static std::vector<unsigned char> gImgData; static int gImgW, gImgH; static bool gImgReady = false;
static std::atomic<bool> gImgLoading{false};

static void LoadBgAsync(std::string path) {
    if (gImgLoading) return;
    gImgLoading = true; gBgNow = path;
    std::thread([path] {
        std::string bytes = ReadAll(P(path)); int w = 0, h = 0, ch = 0;
        unsigned char* d = bytes.empty() ? nullptr : stbi_load_from_memory((const unsigned char*)bytes.data(), (int)bytes.size(), &w, &h, &ch, 4);
        if (d) {
            int f = std::max(1, w / 1920); // быстрый box-downscale для 4K-скриншотов
            int nw = w / f, nh = h / f; std::vector<unsigned char> out((size_t)nw * nh * 4);
            for (int y = 0; y < nh; y++) for (int x = 0; x < nw; x++) for (int c = 0; c < 4; c++) {
                int s = 0; for (int dy = 0; dy < f; dy++) for (int dx = 0; dx < f; dx++) s += d[(((size_t)y * f + dy) * w + (x * f + dx)) * 4 + c];
                out[((size_t)y * nw + x) * 4 + c] = (unsigned char)(s / (f * f));
            }
            stbi_image_free(d);
            std::lock_guard<std::mutex> l(gImgMu); gImgData = std::move(out); gImgW = nw; gImgH = nh; gImgReady = true;
        }
        gImgLoading = false;
    }).detach();
}
static GLuint MakeTex(const unsigned char* px, int w, int h) {
    GLuint t = 0; glGenTextures(1, &t); glBindTexture(GL_TEXTURE_2D, t);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR); glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, 0x812F); glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, 0x812F); // GL_CLAMP_TO_EDGE
    glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, w, h, 0, GL_RGBA, GL_UNSIGNED_BYTE, px);
    return t;
}
static void ScanShots() {
    gShots.clear(); std::error_code ec; std::vector<fs::path> dirs;
    if (!cfg.shotsDir.empty()) dirs.push_back(P(cfg.shotsDir));
    else dirs.push_back(fs::path(HomeDir()) / ".minecraft" / "screenshots");
    for (auto& e : fs::directory_iterator(gRoot / "instances", ec)) dirs.push_back(e.path() / "screenshots");
    for (auto& d : dirs) for (auto& e : fs::directory_iterator(d, ec)) {
        std::string x = e.path().extension().string(); for (auto& ch : x) ch = (char)tolower((unsigned char)ch);
        if (x == ".png" || x == ".jpg" || x == ".jpeg" || x == ".bmp") gShots.push_back(PS(e.path()));
    }
}
static void NextShot() {
    if (gShots.empty()) return; static std::mt19937 rng{std::random_device{}()};
    for (int i = 0; i < 5; i++) { const std::string& s = gShots[rng() % gShots.size()]; if (s != gBgNow || gShots.size() == 1) { LoadBgAsync(s); return; } }
}
static void UpdateBackground(float dt) {
    {
        std::lock_guard<std::mutex> l(gImgMu);
        if (gImgReady) {
            if (gBg[1].v) glDeleteTextures(1, &gBg[1].v);
            gBg[1] = gBg[0]; gBg[0] = {MakeTex(gImgData.data(), gImgW, gImgH), gImgW, gImgH};
            gImgData.clear(); gImgData.shrink_to_fit(); gImgReady = false; gFade = 0;
        }
    }
    gFade = std::min(1.f, gFade + dt * 1.2f);
    if (cfg.slideshow && gShots.size() > 1) { gSlideT += dt; if (gSlideT > 18.f) { gSlideT = 0; NextShot(); } }
}
static std::string RunCapture(const std::string& cmd) {
    FILE* f = popen(cmd.c_str(), "r"); if (!f) return "";
    std::string r; char b[1024]; size_t n; while ((n = fread(b, 1, sizeof(b), f)) > 0) r.append(b, n);
    pclose(f); while (!r.empty() && (r.back() == '\n' || r.back() == '\r')) r.pop_back();
    return r;
}
static bool HaveCmd(const char* c) { return system((std::string("command -v ") + c + " >/dev/null 2>&1").c_str()) == 0; }
static std::string PickFolder(void*) { // нужен zenity (GNOME/GTK) или kdialog (KDE)
    if (HaveCmd("zenity")) return RunCapture("zenity --file-selection --directory --title=" + ShQ("Выбери папку для игры") + " 2>/dev/null");
    if (HaveCmd("kdialog")) return RunCapture("kdialog --getexistingdirectory " + ShQ(HomeDir()) + " 2>/dev/null");
    Status("Для выбора папки нужен zenity или kdialog (установи через менеджер пакетов)"); return "";
}
static std::string PickImage(void*) {
    if (HaveCmd("zenity")) return RunCapture("zenity --file-selection --file-filter=" + ShQ("Изображения | *.png *.jpg *.jpeg *.bmp *.tga") + " 2>/dev/null");
    if (HaveCmd("kdialog")) return RunCapture("kdialog --getopenfilename " + ShQ(HomeDir()) + " " + ShQ("*.png *.jpg *.jpeg *.bmp *.tga|Изображения") + " 2>/dev/null");
    Status("Для выбора файла нужен zenity или kdialog (установи через менеджер пакетов)"); return "";
}

// ============================ UI ============================
enum { S_MAIN, S_ACC, S_MODS, S_SET, S_LOG };
static int gScr = S_MAIN, gSetTab = 0; static float gScrFade = 1;
static void Go(int s) { if (gScr != s) { gScr = s; gScrFade = 0; if (s == S_ACC) { std::lock_guard<std::mutex> l(gMu); gAuthMsg.clear(); } } }
static float gS = 1.f; static int gThemeSig = -1;
static float gCapH = 0.f, gBtnX0 = 1e9f; // зона перетаскивания окна (свой заголовок) для WM_NCHITTEST
static ImFont *gFTitle = nullptr, *gFSub = nullptr; // крупные шрифты: вместо масштабирования, чтобы текст был чётким
static ImVec4 gAccent(0.33f, 0.78f, 0.40f, 1.f), gSoft(1.f, 1.f, 1.f, 0.12f);
static const ImVec4 kPalette[5] = {ImVec4(0.26f, 0.52f, 0.96f, 1.f), ImVec4(0.33f, 0.78f, 0.40f, 1.f), ImVec4(0.92f, 0.30f, 0.30f, 1.f),
                                   ImVec4(0.96f, 0.77f, 0.20f, 1.f), ImVec4(0.25f, 0.80f, 0.92f, 1.f)}; // синий, зелёный, красный, жёлтый, голубой
static const char* T(const char* ru, const char* en) { return cfg.lang == 1 ? en : ru; }
static float R(float v) { return cfg.rounded ? v : 0.f; }
static ImU32 TextCol(float a = 1.f) { ImVec4 c = ImGui::GetStyleColorVec4(ImGuiCol_Text); c.w *= a; return ImGui::GetColorU32(c); }
static ImU32 OnAccent(float a = 1.f) {
    float l = .299f * gAccent.x + .587f * gAccent.y + .114f * gAccent.z;
    return ImGui::GetColorU32(l > 0.64f ? ImVec4(.08f, .09f, .12f, a) : ImVec4(1.f, 1.f, 1.f, a));
}
static void TD(const char* s) { ImGui::TextDisabled("%s", s); }

static void ApplyTheme() {
    gAccent = kPalette[std::clamp(cfg.color, 0, 4)];
    gSoft = cfg.light ? ImVec4(0.f, 0.f, 0.f, .08f) : ImVec4(1.f, 1.f, 1.f, .12f);
    ImGuiStyle& st = ImGui::GetStyle(); st = ImGuiStyle();
    if (cfg.light) ImGui::StyleColorsLight(&st); else ImGui::StyleColorsDark(&st);
    float r = cfg.rounded ? 1.f : 0.f;
    st.FrameRounding = 8 * r; st.PopupRounding = 10 * r; st.GrabRounding = 8 * r; st.ScrollbarRounding = 8 * r; st.WindowRounding = 12 * r; st.ChildRounding = 8 * r;
    st.FramePadding = ImVec2(10, 7); st.ItemSpacing = ImVec2(10, 10); st.ScaleAllSizes(gS);
    ImVec4* c = st.Colors;
    if (cfg.light) {
        c[ImGuiCol_Text] = ImVec4(.09f, .10f, .14f, 1.f); c[ImGuiCol_TextDisabled] = ImVec4(.40f, .42f, .48f, 1.f);
        c[ImGuiCol_FrameBg] = ImVec4(0, 0, 0, .07f); c[ImGuiCol_FrameBgHovered] = ImVec4(0, 0, 0, .12f); c[ImGuiCol_FrameBgActive] = ImVec4(0, 0, 0, .16f);
        c[ImGuiCol_PopupBg] = ImVec4(.97f, .98f, 1.f, .98f); c[ImGuiCol_Button] = ImVec4(0, 0, 0, .10f);
    } else {
        c[ImGuiCol_FrameBg] = ImVec4(1, 1, 1, .08f); c[ImGuiCol_FrameBgHovered] = ImVec4(1, 1, 1, .14f); c[ImGuiCol_FrameBgActive] = ImVec4(1, 1, 1, .18f);
        c[ImGuiCol_PopupBg] = ImVec4(.08f, .09f, .13f, .98f); c[ImGuiCol_Button] = ImVec4(1, 1, 1, .12f);
    }
    c[ImGuiCol_CheckMark] = cfg.light ? gAccent : gAccent; c[ImGuiCol_SliderGrab] = gAccent; c[ImGuiCol_SliderGrabActive] = gAccent;
    c[ImGuiCol_Header] = ImVec4(gAccent.x, gAccent.y, gAccent.z, .35f); c[ImGuiCol_HeaderHovered] = ImVec4(gAccent.x, gAccent.y, gAccent.z, .5f);
    c[ImGuiCol_ButtonHovered] = ImVec4(gAccent.x, gAccent.y, gAccent.z, .45f); c[ImGuiCol_ButtonActive] = ImVec4(gAccent.x, gAccent.y, gAccent.z, .6f);
}

static float Anim(ImGuiID id, float target, float speed, float def = 0.f) {
    float& v = *ImGui::GetStateStorage()->GetFloatRef(id, def);
    v += (target - v) * std::min(1.f, ImGui::GetIO().DeltaTime * speed); return v;
}
static float AnimK(const char* k, float target, float speed, float def = 0.f) { return Anim(ImGui::GetID(k), target, speed, def); }

static bool FancyBtn(const char* label, ImVec2 sz, ImVec4 col, bool enabled = true) {
    ImGui::PushID(label);
    const char* hid = strstr(label, "##"); // видимая часть — до "##"
    if (sz.x <= 0) sz.x = ImGui::GetContentRegionAvail().x;
    ImVec2 p = ImGui::GetCursorScreenPos();
    bool clk = ImGui::InvisibleButton("##b", sz);
    bool hov = ImGui::IsItemHovered() && enabled, act = ImGui::IsItemActive() && enabled;
    float t = AnimK("h", hov ? 1.f : 0.f, 14.f), g = t * 2.5f - (act ? 2.5f : 0.f);
    bool strong = col.w >= 0.85f; ImVec4 c = col;
    if (strong) {
        float k = enabled ? 1.f : .45f; c.x *= k; c.y *= k; c.z *= k;
        c.x = std::min(1.f, c.x + .12f * t); c.y = std::min(1.f, c.y + .12f * t); c.z = std::min(1.f, c.z + .12f * t);
    } else c.w = std::min(1.f, c.w * (enabled ? 1.f : .5f) + .08f * t);
    ImDrawList* dl = ImGui::GetWindowDrawList();
    dl->AddRectFilled(ImVec2(p.x - g, p.y - g), ImVec2(p.x + sz.x + g, p.y + sz.y + g), ImGui::GetColorU32(c), R(sz.y * 0.28f));
    ImVec2 ts = ImGui::CalcTextSize(label, hid);
    ImU32 tc = strong ? OnAccent(enabled ? 1.f : .55f) : TextCol(enabled ? 1.f : .5f);
    dl->AddText(ImVec2(p.x + (sz.x - ts.x) / 2, p.y + (sz.y - ts.y) / 2), tc, label, hid);
    ImGui::PopID();
    return clk && enabled;
}
static bool BackBtn(ImVec2 sz) { // кнопка «назад» со стрелкой
    bool clk = FancyBtn("##back", sz, gSoft);
    ImVec2 a = ImGui::GetItemRectMin(), b = ImGui::GetItemRectMax(), m((a.x + b.x) / 2, (a.y + b.y) / 2);
    float s = (b.y - a.y) * .22f, th = 2.f * gS; ImU32 col = TextCol(); ImDrawList* dl = ImGui::GetWindowDrawList();
    dl->AddLine(ImVec2(m.x + s * 1.5f, m.y), ImVec2(m.x - s * 1.5f, m.y), col, th);
    dl->AddLine(ImVec2(m.x - s * 1.5f, m.y), ImVec2(m.x - s * .4f, m.y - s * 1.1f), col, th);
    dl->AddLine(ImVec2(m.x - s * 1.5f, m.y), ImVec2(m.x - s * .4f, m.y + s * 1.1f), col, th);
    return clk;
}
static void IconCheck(ImDrawList* dl, ImVec2 m, float s, ImU32 col) {
    float th = 2.5f * gS;
    dl->AddLine(ImVec2(m.x - s, m.y), ImVec2(m.x - s * .3f, m.y + s * .7f), col, th);
    dl->AddLine(ImVec2(m.x - s * .3f, m.y + s * .7f), ImVec2(m.x + s, m.y - s * .7f), col, th);
}
static void IconCross(ImDrawList* dl, ImVec2 m, float s, ImU32 col) {
    float th = 2.5f * gS;
    dl->AddLine(ImVec2(m.x - s * .8f, m.y - s * .8f), ImVec2(m.x + s * .8f, m.y + s * .8f), col, th);
    dl->AddLine(ImVec2(m.x - s * .8f, m.y + s * .8f), ImVec2(m.x + s * .8f, m.y - s * .8f), col, th);
}
static void IconTrash(ImDrawList* dl, ImVec2 m, float s, ImU32 col) { // корзина для мусора
    float th = std::max(1.5f, 1.6f * gS);
    ImVec2 body[4] = {ImVec2(m.x - s * .62f, m.y - s * .28f), ImVec2(m.x + s * .62f, m.y - s * .28f), ImVec2(m.x + s * .48f, m.y + s * .95f), ImVec2(m.x - s * .48f, m.y + s * .95f)};
    dl->AddPolyline(body, 4, col, ImDrawFlags_Closed, th);
    dl->AddLine(ImVec2(m.x - s * .88f, m.y - s * .5f), ImVec2(m.x + s * .88f, m.y - s * .5f), col, th);
    dl->AddLine(ImVec2(m.x - s * .28f, m.y - s * .5f), ImVec2(m.x - s * .28f, m.y - s * .86f), col, th);
    dl->AddLine(ImVec2(m.x + s * .28f, m.y - s * .5f), ImVec2(m.x + s * .28f, m.y - s * .86f), col, th);
    dl->AddLine(ImVec2(m.x - s * .28f, m.y - s * .86f), ImVec2(m.x + s * .28f, m.y - s * .86f), col, th);
    dl->AddLine(ImVec2(m.x - s * .2f, m.y + s * .05f), ImVec2(m.x - s * .16f, m.y + s * .68f), col, th * .8f);
    dl->AddLine(ImVec2(m.x + s * .2f, m.y + s * .05f), ImVec2(m.x + s * .16f, m.y + s * .68f), col, th * .8f);
}
static void DrawTrash(ImDrawList* dl, ImVec2 a, ImVec2 b, bool hov, bool enabled) {
    ImVec2 m((a.x + b.x) / 2, (a.y + b.y) / 2); float s = (b.y - a.y) * .30f;
    if (hov && enabled) dl->AddRectFilled(a, b, IM_COL32(225, 70, 70, 70), R((b.y - a.y) * .3f));
    IconTrash(dl, m, s, (hov && enabled) ? IM_COL32(255, 100, 100, 255) : IM_COL32(235, 85, 85, enabled ? 205 : 90));
}
static bool TrashBtn(const char* id, float sz, bool enabled = true) { // квадратная кнопка-корзина
    ImGui::PushID(id); ImVec2 p = ImGui::GetCursorScreenPos();
    bool clk = ImGui::InvisibleButton("##tr", ImVec2(sz, sz)), hov = ImGui::IsItemHovered();
    DrawTrash(ImGui::GetWindowDrawList(), p, ImVec2(p.x + sz, p.y + sz), hov, enabled);
    ImGui::PopID(); return clk && enabled;
}
static void Open(const fs::path& p) { std::error_code ec; fs::create_directories(p, ec); OpenExternal(PS(p)); }
static std::string AccLabel(const Account& a) { return std::string(a.type == 0 ? T("[офлайн] ", "[offline] ") : a.type == 1 ? "[Ely.by] " : "[Microsoft] ") + a.name; }

static void TabBar(const char* const* labels, int n, int& cur, bool fade = true) {
    float em = ImGui::GetFontSize(), h = em * 1.9f; ImVec2 s = ImGui::GetCursorScreenPos(); float x = s.x, tx = s.x, tw = 0;
    ImDrawList* dl = ImGui::GetWindowDrawList();
    for (int i = 0; i < n; i++) {
        ImVec2 ts = ImGui::CalcTextSize(labels[i]); float w = ts.x + em * 1.2f;
        ImGui::SetCursorScreenPos(ImVec2(x, s.y)); ImGui::PushID(i);
        if (ImGui::InvisibleButton("##t", ImVec2(w, h)) && cur != i) { cur = i; if (fade) gScrFade = 0; }
        float t = AnimK("h", (ImGui::IsItemHovered() || cur == i) ? 1.f : 0.f, 12.f);
        dl->AddText(ImVec2(x + em * .6f, s.y + (h - ts.y) / 2), TextCol(.5f + .5f * t), labels[i]);
        if (cur == i) { tx = x; tw = w; }
        x += w; ImGui::PopID();
    }
    float ux = AnimK("ux", tx, 12.f, tx), uw = AnimK("uw", tw, 12.f, tw);
    dl->AddRectFilled(ImVec2(ux + em * .4f, s.y + h), ImVec2(ux + uw - em * .4f, s.y + h + 3), ImGui::GetColorU32(gAccent), 2.f);
    ImGui::SetCursorScreenPos(ImVec2(s.x, s.y + h + em * .8f));
}
static bool VerShown(const Ver& v, const std::string& loader) { // вызывать под gVerMu
    if (v.type == "snapshot" && !cfg.snapshots) return false;
    if (v.type == "old_beta" && !cfg.showBeta) return false;
    if (v.type == "old_alpha" && !cfg.showAlpha) return false;
    if (loader == "Fabric" && !gFabricGames.empty()) return gFabricGames.count(v.id) > 0;
    if (loader == "Forge" && !gForgeGames.empty()) return gForgeGames.count(v.id) > 0;
    if (loader == "Quilt" && !gQuiltGames.empty()) return gQuiltGames.count(v.id) > 0;
    if (loader == "NeoForge" && !gNeoGames.empty()) return gNeoGames.count(v.id) > 0;
    if (loader == "OptiFine" && !gOptiGames.empty()) return gOptiGames.count(v.id) > 0;
    return true;
}
static fs::path CurrentInstanceDir() { return gRoot / "instances" / P(InstName(cfg.loader, cfg.version)); } // папка игры для выбранных загрузчика и версии
static std::set<std::string> gInstNames; static float gInstNamesT = 99.f; // какие экземпляры уже лежат на диске
static void RefreshInstNames(bool force = false) {
    gInstNamesT += ImGui::GetIO().DeltaTime; if (!force && gInstNamesT < 0.7f) return; gInstNamesT = 0;
    std::set<std::string> s2; std::error_code ec;
    for (auto& e : fs::directory_iterator(gRoot / "instances", ec)) if (e.is_directory(ec)) s2.insert(U8(e.path().filename().string()));
    gInstNames = s2;
}
struct DelReq { std::string loader, ver; };
static std::optional<DelReq> gDelAsk; // запрос на удаление (ждёт подтверждения в окне)
static void DeleteThread(std::string loader, std::string ver) {
    gDelBusy = true; Status(std::string(T("Удаляю ", "Deleting ")) + loader + " " + ver + "...");
    DeleteInstance(loader, ver);
    Status(std::string(T("Удалено: ", "Deleted: ")) + loader + " " + ver);
    gDelBusy = false;
}
struct InstInfo { std::string name, loader, ver; };
static InstInfo ParseInst(const std::string& n) {
    InstInfo r; r.name = n; r.loader = "Vanilla"; r.ver = n;
    auto ends = [&](const char* sfx) { size_t l = strlen(sfx); return n.size() > l && n.compare(n.size() - l, l, sfx) == 0; };
    if (ends("-neoforge")) { r.loader = "NeoForge"; r.ver = n.substr(0, n.size() - 9); }
    else if (ends("-quilt")) { r.loader = "Quilt"; r.ver = n.substr(0, n.size() - 6); }
    else if (ends("-optifine")) { r.loader = "OptiFine"; r.ver = n.substr(0, n.size() - 9); }
    else if (ends("-fabric")) { r.loader = "Fabric"; r.ver = n.substr(0, n.size() - 7); }
    else if (ends("-forge")) { r.loader = "Forge"; r.ver = n.substr(0, n.size() - 6); }
    else if (n.rfind("fabric-loader-", 0) == 0) { std::string rest = n.substr(14); size_t p = rest.find('-'); r.loader = "Fabric"; r.ver = p == std::string::npos ? rest : rest.substr(p + 1); }
    else { size_t p = n.find("-forge-"); if (p != std::string::npos && p > 0) { r.loader = "Forge"; r.ver = n.substr(0, p); } }
    return r;
}
static std::vector<InstInfo> gInsts; static float gInstsT = 99.f;
static void ScanInsts(bool force) {
    gInstsT += ImGui::GetIO().DeltaTime; if (!force && gInstsT < 1.f) return; gInstsT = 0;
    std::vector<InstInfo> v; std::error_code ec;
    for (auto& e : fs::directory_iterator(gRoot / "instances", ec)) if (e.is_directory(ec)) v.push_back(ParseInst(U8(e.path().filename().string())));
    std::sort(v.begin(), v.end(), [](const InstInfo& a, const InstInfo& b) { return a.name < b.name; });
    gInsts = v;
}
static std::mutex gSzMu; static std::map<std::string, long long> gSizes; static std::set<std::string> gSzBusy;
static void SizeThread(std::string name) {
    std::error_code ec; long long sum = 0; fs::path d = gRoot / "instances" / P(name);
    for (auto it = fs::recursive_directory_iterator(d, ec); it != fs::recursive_directory_iterator(); it.increment(ec)) {
        if (ec) break;
        if (it->is_regular_file(ec)) sum += (long long)it->file_size(ec);
    }
    std::lock_guard<std::mutex> l(gSzMu); gSizes[name] = sum; gSzBusy.erase(name);
}
static std::string FmtSize(long long b) {
    char t[48]; double v = (double)b;
    if (v < 1024.0) snprintf(t, sizeof(t), "%lld %s", b, T("Б", "B"));
    else if (v < 1048576.0) snprintf(t, sizeof(t), "%.1f %s", v / 1024.0, T("КБ", "KB"));
    else if (v < 1073741824.0) snprintf(t, sizeof(t), "%.1f %s", v / 1048576.0, T("МБ", "MB"));
    else snprintf(t, sizeof(t), "%.2f %s", v / 1073741824.0, T("ГБ", "GB"));
    return t;
}
static std::string FmtDate(const fs::path& p) { // дата создания папки = когда экземпляр скачан (btime, если ФС отдаёт; иначе mtime)
    struct statx sx; if (statx(AT_FDCWD, p.c_str(), 0, STATX_BTIME | STATX_MTIME, &sx) != 0) return "?";
    time_t t = (sx.stx_mask & STATX_BTIME) ? (time_t)sx.stx_btime.tv_sec : (time_t)sx.stx_mtime.tv_sec;
    struct tm tmv; if (!localtime_r(&t, &tmv)) return "?";
    char b[48]; snprintf(b, sizeof(b), "%02d.%02d.%04d %02d:%02d", tmv.tm_mday, tmv.tm_mon + 1, tmv.tm_year + 1900, tmv.tm_hour, tmv.tm_min);
    return b;
}

// ---------- Java: список установленных и установка ----------
static const int kJavaVers[] = {8, 17, 21, 25};
static std::vector<JavaInfo> gJavas; static std::mutex gJavaMu; static std::atomic<bool> gJavaScan{false}; static std::atomic<int> gJavaInst{0};
static void RefreshJavas() {
    if (gJavaScan.exchange(true)) return;
    std::thread([] { auto j = FindJavas(); { std::lock_guard<std::mutex> l(gJavaMu); gJavas = j; } gJavaScan = false; }).detach();
}
static void JavaInstallThread(int v) {
    gJavaInst = v;
    bool ok = InstallJavaVer(v);
    Status(ok ? "Java " + std::to_string(v) + " установлена" : "Не удалось скачать Java " + std::to_string(v));
    { auto j = FindJavas(); std::lock_guard<std::mutex> l(gJavaMu); gJavas = j; }
    gJavaInst = 0;
}

// ---------- Моды (Modrinth) ----------
struct ModHit { std::string id, title, desc, author; long long dl = 0; };
static std::vector<ModHit> gModHits; static std::mutex gModMu; static std::string gModMsg, gModKey, gWantQ, gModChk;
static std::atomic<bool> gModBusy{false}, gModInst{false}, gModChkBusy{false};
static char bModQ[96];
// Установленные моды выбранного экземпляра: id проекта -> файлы в папке mods. Список хранится на диске рядом с папкой mods,
// поэтому «Установлено» остаётся после перезапуска, а удалённые вручную файлы пропадают из списка.
static std::map<std::string, std::vector<std::string>> gModFiles; static fs::path gModFilesDir; static float gModVerifyT = 99.f;
static fs::path ModManifest(const fs::path& inst) { return inst / "poltergeist_mods.json"; }
static void LoadModFiles(const fs::path& inst) { // вызывать под gModMu
    gModFiles.clear(); gModFilesDir = inst;
    json j = Parse(ReadAll(ModManifest(inst)));
    if (!j.is_object() || !j.contains("mods") || !j["mods"].is_object()) return;
    for (auto it = j["mods"].begin(); it != j["mods"].end(); ++it) {
        if (!it.value().is_object() || !it.value().contains("files") || !it.value()["files"].is_array()) continue;
        std::vector<std::string> f; for (auto& x : it.value()["files"]) if (x.is_string()) f.push_back(x.get<std::string>());
        if (!f.empty()) gModFiles[it.key()] = f;
    }
}
static void SaveModFiles() { // под gModMu
    json j; j["mods"] = json::object();
    for (auto& kv : gModFiles) { json o; o["files"] = kv.second; j["mods"][kv.first] = o; }
    WriteAll(ModManifest(gModFilesDir), j.dump(2));
}
static void ModsSync(const fs::path& inst) { // UI-поток: подгрузить список экземпляра и убрать моды, чьи файлы пропали с диска
    std::lock_guard<std::mutex> l(gModMu); std::error_code ec;
    if (inst != gModFilesDir) { LoadModFiles(inst); gModVerifyT = 99.f; }
    gModVerifyT += ImGui::GetIO().DeltaTime; if (gModVerifyT < 1.f) return; gModVerifyT = 0;
    bool ch = false;
    for (auto it = gModFiles.begin(); it != gModFiles.end();) {
        bool ok = true; for (auto& f : it->second) if (!fs::exists(inst / "mods" / P(f), ec)) ok = false;
        if (ok) ++it; else { it = gModFiles.erase(it); ch = true; }
    }
    if (ch) SaveModFiles();
}
static void ModRecord(const fs::path& inst, const std::string& pid, const std::string& fn) {
    std::lock_guard<std::mutex> l(gModMu);
    if (inst != gModFilesDir) LoadModFiles(inst);
    auto& v = gModFiles[pid]; if (std::find(v.begin(), v.end(), fn) == v.end()) v.push_back(fn);
    SaveModFiles();
}
static void ModDelete(const fs::path& inst, const std::string& pid) {
    std::lock_guard<std::mutex> l(gModMu); std::error_code ec;
    if (inst != gModFilesDir) LoadModFiles(inst);
    auto it = gModFiles.find(pid); if (it == gModFiles.end()) return;
    for (auto& f : it->second) fs::remove(inst / "mods" / P(f), ec);
    gModFiles.erase(it); SaveModFiles();
}
static std::string LoaderId(const std::string& l) { return l == "Fabric" ? "fabric" : l == "Forge" ? "forge" : l == "NeoForge" ? "neoforge" : l == "Quilt" ? "quilt" : ""; }
static void ModMsg(const std::string& s) { { std::lock_guard<std::mutex> l(gModMu); gModMsg = s; } Log(s); }
static void ModSearchThread(std::string q, std::string loader, std::string mc) {
    gModBusy = true;
    try {
        std::string cat = loader == "quilt" ? std::string("\"categories:quilt\",\"categories:fabric\"") : "\"categories:" + loader + "\"";
        std::string fac = "[[\"project_type:mod\"],[" + cat + "],[\"versions:" + mc + "\"]]";
        std::string url = "https://api.modrinth.com/v2/search?query=" + UrlEnc(q) + "&facets=" + UrlEnc(fac) + "&limit=40&index=" + (q.empty() ? "downloads" : "relevance");
        Resp r = Http(url); json j = Parse(r.body); std::vector<ModHit> out;
        if (r.status == 200 && j.is_object() && j.contains("hits") && j["hits"].is_array())
            for (auto& h : j["hits"]) {
                ModHit m; m.id = JStr(h, "project_id"); m.title = JStr(h, "title"); m.desc = JStr(h, "description"); m.author = JStr(h, "author");
                if (h.contains("downloads") && h["downloads"].is_number()) m.dl = h["downloads"].get<long long>();
                if (!m.id.empty()) out.push_back(m);
            }
        std::lock_guard<std::mutex> l(gModMu); gModHits = out;
        if (r.status != 200) gModMsg = T("Нет связи с Modrinth (интернет / VPN / фаервол)", "Cannot reach Modrinth (internet / VPN / firewall)");
        else if (out.empty()) gModMsg = T("Ничего не найдено для этой версии и загрузчика", "Nothing found for this version and loader");
        else gModMsg.clear();
    } catch (std::exception& e) { ModMsg(std::string("Modrinth: ") + e.what()); }
    gModBusy = false;
}
static bool InstallModRec(const std::string& pid, const std::string& loader, const std::string& mc, const fs::path& inst, std::set<std::string>& seen, int depth) {
    if (!seen.insert(pid).second) return true;
    Resp r = Http("https://api.modrinth.com/v2/project/" + UrlEnc(pid) + "/version?loaders=" + UrlEnc(loader == "quilt" ? std::string("[\"quilt\",\"fabric\"]") : "[\"" + loader + "\"]") + "&game_versions=" + UrlEnc("[\"" + mc + "\"]"));
    if (r.status == 0) throw std::runtime_error(T("Нет соединения с Modrinth", "No connection to Modrinth"));
    json a = Parse(r.body);
    if (r.status != 200 || !a.is_array() || a.empty()) return false;
    const json* pick = &a[0];
    for (auto& v : a) if (JStr(v, "version_type") == "release") { pick = &v; break; }
    if (!pick->is_object() || !pick->contains("files") || !(*pick)["files"].is_array() || (*pick)["files"].empty()) return false;
    const json& files = (*pick)["files"]; const json* f = &files[0];
    for (auto& x : files) if (x.is_object() && x.contains("primary") && x["primary"].is_boolean() && x["primary"].get<bool>()) { f = &x; break; }
    std::string fn = U8(fs::path(W(JStr(*f, "filename"))).filename().string()), url = JStr(*f, "url");
    if (fn.empty() || url.empty()) return false;
    fs::path dir = inst / "mods"; std::error_code ec; fs::create_directories(dir, ec);
    ModMsg(std::string(T("Скачиваю ", "Downloading ")) + fn);
    if (!Download(url, dir / P(fn))) throw std::runtime_error(std::string(T("Не удалось скачать ", "Failed to download ")) + fn);
    ModRecord(inst, pid, fn);
    if (depth < 3 && pick->contains("dependencies") && (*pick)["dependencies"].is_array())
        for (auto& d : (*pick)["dependencies"]) {
            if (JStr(d, "dependency_type") != "required") continue;
            std::string dp = JStr(d, "project_id"); if (dp.empty()) continue;
            try { InstallModRec(dp, loader, mc, inst, seen, depth + 1); } catch (...) {}
        }
    return true;
}
static void ModInstallThread(std::string pid, std::string title, std::string loader, std::string mc, std::string inst) {
    gModInst = true;
    try {
        std::set<std::string> seen;
        if (InstallModRec(pid, loader, mc, P(inst), seen, 0)) ModMsg(std::string(T("Установлено: ", "Installed: ")) + title);
        else ModMsg(cfg.lang == 1 ? "No versions of \"" + title + "\" for " + loader + " " + mc : "Для мода «" + title + "» нет версий под " + loader + " " + mc);
    } catch (std::exception& e) { ModMsg(std::string(T("Ошибка: ", "Error: ")) + e.what()); }
    gModInst = false;
}
static void ModrinthCheckThread() {
    if (gModChkBusy.exchange(true)) return;
    { std::lock_guard<std::mutex> l(gModMu); gModChk = T("Проверяю...", "Checking..."); }
    auto t0 = std::chrono::steady_clock::now(); Resp r = Http("https://api.modrinth.com/");
    int ms = (int)std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - t0).count();
    { std::lock_guard<std::mutex> l(gModMu); gModChk = r.status == 200 ? std::string(T("Modrinth доступен (", "Modrinth is reachable (")) + std::to_string(ms) + (cfg.lang == 1 ? " ms)" : " мс)")
                                                                          : std::string(T("Нет связи с Modrinth", "Cannot reach Modrinth")) + (r.status ? " (" + std::to_string(r.status) + ")" : ""); }
    gModChkBusy = false;
}

// ---------- Новости ----------
struct NewsItem { const char* ver; const char* ru; const char* en; };
static int gNewsTab = 0; // 0 новости лаунчера, 1 новости игры
static const NewsItem kNews[] = { // новые сверху
    {"v0.0.5", "Пофикшены некоторые баги, добавлено больше загрузчиков, моды полностью работают, доделаны настройки экземпляра.", "Some bugs fixed, more loaders added, mods fully working, instance settings completed."},
    {"v0.0.4", "Фикс визуала и добавление настроек экземпляра.", "Visual fixes and instance settings added."},
    {"v0.0.3", "Добавлено больше настроек. И моды.", "More settings added. And mods."},
    {"v0.0.2", "Hotfix Java. Скачивалась не та версия для 26.1-26.3.", "Java hotfix. The wrong Java version was downloaded for 26.1-26.3."},
    {"v0.0.1", "Добро пожаловать в ОБТ PoltergeistLauncher. Пока контента мало, с обновлениями будем добавлять его.", "Welcome to the PoltergeistLauncher open beta. There is little content for now, we will add more with updates."},
};

static bool Header(const char* title) { // заголовок экрана + стрелка «назад» справа; true = нажали «назад»
    float em = ImGui::GetFontSize(); ImVec2 st = ImGui::GetCursorPos(); float w = ImGui::GetContentRegionAvail().x, bh = em * 2.2f, bw = em * 3.4f;
    ImGui::PushFont(gFTitle); ImVec2 ts = ImGui::CalcTextSize(title);
    ImGui::SetCursorPos(ImVec2(st.x, st.y + (bh - ts.y) / 2)); ImGui::TextColored(gAccent, "%s", title); ImGui::PopFont();
    ImGui::SetCursorPos(ImVec2(st.x + w - bw, st.y)); bool back = BackBtn(ImVec2(bw, bh));
    ImGui::SetCursorPos(ImVec2(st.x, st.y + bh + em * .6f));
    return back;
}
static bool ComboI(const char* id, int& cur, const char* const* items, int n) {
    bool ch = false; ImGui::SetNextItemWidth(std::min(ImGui::GetFontSize() * 18.f, ImGui::GetContentRegionAvail().x));
    if (ImGui::BeginCombo(id, items[std::clamp(cur, 0, n - 1)])) {
        for (int i = 0; i < n; i++) if (ImGui::Selectable(items[i], cur == i)) { cur = i; ch = true; }
        ImGui::EndCombo();
    }
    return ch;
}

// ---------- Главный экран ----------
static void ScrMain() {
    float em = ImGui::GetFontSize(); ImGuiStyle& sty = ImGui::GetStyle(); ImDrawList* dl = ImGui::GetWindowDrawList();
    { // шапка: название слева, версия и «Настройки» справа
        ImVec2 st = ImGui::GetCursorPos(); float w = ImGui::GetContentRegionAvail().x, bh = em * 2.2f, bw = em * 8.f;
        ImGui::PushFont(gFTitle); ImVec2 ts = ImGui::CalcTextSize("PoltergeistLauncher");
        ImGui::SetCursorPos(ImVec2(st.x, st.y + (bh - ts.y) / 2)); ImGui::TextColored(gAccent, "PoltergeistLauncher"); ImGui::PopFont();
        std::string vs = std::string("v") + kVer; ImVec2 vz = ImGui::CalcTextSize(vs.c_str());
        ImGui::SetCursorPos(ImVec2(st.x + w - bw - vz.x - em * .7f, st.y + (bh - vz.y) / 2)); ImGui::TextDisabled("%s", vs.c_str());
        ImGui::SetCursorPos(ImVec2(st.x + w - bw, st.y));
        if (FancyBtn(T("Настройки", "Settings"), ImVec2(bw, bh), gSoft)) Go(S_SET);
        ImGui::SetCursorPos(ImVec2(st.x, st.y + bh + em * .8f));
    }
    { // «Новости» по центру
        ImGui::PushFont(gFSub); const char* nt = T("Новости", "News"); float tw = ImGui::CalcTextSize(nt).x;
        ImGui::SetCursorPosX((ImGui::GetWindowWidth() - tw) / 2); ImGui::TextUnformatted(nt); ImGui::PopFont();
    }
    float bottomH = em * 6.3f + em * 1.9f + sty.ItemSpacing.y * 4; // + ряд переключателя новостей
    ImGui::BeginChild("news", ImVec2(0, std::max(em * 4.f, ImGui::GetContentRegionAvail().y - bottomH)), 0, ImGuiWindowFlags_NoBackground);
    dl = ImGui::GetWindowDrawList();
    if (gNewsTab == 0) for (auto& n : kNews) {
        float aw = ImGui::GetContentRegionAvail().x, cw = std::min(aw, em * 42.f); ImVec2 p = ImGui::GetCursorScreenPos(); float x0 = p.x + (aw - cw) / 2;
        float tw = cw - em * 2; const char* txt = T(n.ru, n.en); ImVec2 ts = ImGui::CalcTextSize(txt, nullptr, false, tw);
        float ch = em * .8f + em * 1.4f + ts.y + em * .8f;
        dl->AddRectFilled(ImVec2(x0, p.y), ImVec2(x0 + cw, p.y + ch), ImGui::GetColorU32(gSoft), R(em * .6f));
        dl->AddText(ImVec2(x0 + em, p.y + em * .8f), ImGui::GetColorU32(gAccent), n.ver);
        dl->AddText(ImGui::GetFont(), ImGui::GetFontSize(), ImVec2(x0 + em, p.y + em * .8f + em * 1.4f), TextCol(.9f), txt, nullptr, tw);
        ImGui::Dummy(ImVec2(aw, ch));
    }
    if (gNewsTab == 1) { const char* et = T("Пока что пусто", "Nothing here yet"); ImGui::SetCursorPosY(ImGui::GetCursorPosY() + em * 1.5f); ImGui::SetCursorPosX((ImGui::GetWindowWidth() - ImGui::CalcTextSize(et).x) / 2); TD(et); }
    ImGui::EndChild();
    dl = ImGui::GetWindowDrawList();
    { // переключатель: новости лаунчера / новости игры
        float sw = em * 11.f, shh = em * 1.9f, gap = sty.ItemSpacing.x, aw2 = ImGui::GetContentRegionAvail().x;
        ImGui::SetCursorPosX(ImGui::GetCursorPosX() + std::max(0.f, (aw2 - (sw * 2 + gap)) / 2));
        if (FancyBtn(T("Новости лаунчера", "Launcher news"), ImVec2(sw, shh), gNewsTab == 0 ? gAccent : gSoft)) gNewsTab = 0;
        ImGui::SameLine();
        if (FancyBtn(T("Новости игры", "Game news"), ImVec2(sw, shh), gNewsTab == 1 ? gAccent : gSoft)) gNewsTab = 1;
    }

    // строка статуса + прогресс слева, мелкие кнопки справа
    float full = ImGui::GetContentRegionAvail().x, sbw = em * 5.4f, rowH = em * 2.6f, sp = sty.ItemSpacing.x;
    int nb = 1 + (cfg.modsOn ? 1 : 0) + (cfg.logsOn ? 1 : 0);
    float leftW = std::max(em * 6.f, full - (nb * sbw + (nb - 1) * sp) - sp * 3); // SameLine(0, sp*2) ниже: запас, чтобы кнопки не вылезали за край
    {
        ImVec2 p = ImGui::GetCursorScreenPos(); float h = em * .3f, pr = AnimK("prog", gProg.load(), 6.f); bool busy = gBusy;
        dl->AddRectFilled(ImVec2(p.x, p.y + 2), ImVec2(p.x + leftW, p.y + 2 + h), ImGui::GetColorU32(ImVec4(gSoft.x, gSoft.y, gSoft.z, gSoft.w * .8f)), R(h / 2));
        if (pr > 0.005f) {
            dl->AddRectFilled(ImVec2(p.x, p.y + 2), ImVec2(p.x + leftW * pr, p.y + 2 + h), ImGui::GetColorU32(gAccent), R(h / 2));
            if (busy) { float sh = fmodf(gTime * 0.8f, 1.f); float sx = p.x + (leftW * pr) * sh; dl->AddRectFilled(ImVec2(sx, p.y + 2), ImVec2(std::min(sx + em * 2, p.x + leftW * pr), p.y + 2 + h), IM_COL32(255, 255, 255, 70), R(h / 2)); }
        }
        std::string st; { std::lock_guard<std::mutex> l(gMu); st = gStatus; }
        ImVec4 clip(p.x, p.y, p.x + leftW, p.y + rowH);
        dl->AddText(ImGui::GetFont(), ImGui::GetFontSize(), ImVec2(p.x, p.y + h + em * .35f), TextCol(.85f), st.c_str(), nullptr, leftW, &clip);
        ImGui::Dummy(ImVec2(leftW, rowH));
    }
    ImGui::SameLine(0, sp * 2);
    if (cfg.logsOn) { if (FancyBtn(T("Лог", "Log"), ImVec2(sbw, em * 1.9f), gSoft)) Go(S_LOG); ImGui::SameLine(); }
    if (FancyBtn(T("Папка", "Folder"), ImVec2(sbw, em * 1.9f), gSoft)) ImGui::OpenPopup("##folders");
    {
        ImVec2 fmin = ImGui::GetItemRectMin(), fmax = ImGui::GetItemRectMax();
        ImGui::SetNextWindowPos(ImVec2(fmax.x, fmin.y - 4), 0, ImVec2(1, 1));
        ImGui::SetNextWindowSize(ImVec2(em * 14, 0));
        if (ImGui::BeginPopup("##folders")) {
            fs::path gd = CurrentInstanceDir(); std::error_code ec;
            if (ImGui::Selectable(T("Открыть папку игры", "Open game folder"))) Open(gd);
            if (ImGui::Selectable(T("Открыть папку mods", "Open mods folder"))) Open(gd / "mods");
            if (fs::exists(gd / "shaderpacks", ec) && ImGui::Selectable(T("Открыть папку shaderpacks", "Open shaderpacks folder"))) Open(gd / "shaderpacks");
            ImGui::EndPopup();
        }
    }
    if (cfg.modsOn) { ImGui::SameLine(); if (FancyBtn(T("Моды", "Mods"), ImVec2(sbw, em * 1.9f), gSoft)) Go(S_MODS); }

    // нижний ряд: версия | ИГРАТЬ | аккаунт
    float avail = ImGui::GetContentRegionAvail().x, bh = em * 2.8f, wl = (avail - 2 * sp) * 0.30f, wc = avail - 2 * sp - 2 * wl; bool busy = gBusy;
    std::string vl = cfg.loader + "  " + (cfg.version.empty() ? std::string(T("загрузка...", "loading...")) : cfg.version);
    if (FancyBtn(vl.c_str(), ImVec2(wl, bh), gSoft)) { RefreshInstNames(true); ImGui::OpenPopup("##vers"); }
    {
        ImVec2 bmin = ImGui::GetItemRectMin(), bmax = ImGui::GetItemRectMax();
        ImGui::SetNextWindowPos(ImVec2(bmin.x, bmin.y - 4), 0, ImVec2(0, 1));
        ImGui::SetNextWindowSize(ImVec2(std::max(bmax.x - bmin.x, em * 16.f), std::max(em * 8.f, std::min(em * 19.f, bmin.y - em))));
        if (ImGui::BeginPopup("##vers")) {
            RefreshInstNames();
            { // выбор загрузчика: выпадающий список (как выбор видеокарты)
                auto fixVer = [&] {
                    std::lock_guard<std::mutex> l(gVerMu); bool ok = false;
                    for (auto& v : gVers) if (v.id == cfg.version && VerShown(v, cfg.loader)) ok = true;
                    if (!ok) { // выбранной версии у этого загрузчика нет — берём самую новую подходящую
                        for (auto& v : gVers) if (v.type == "release" && VerShown(v, cfg.loader)) { cfg.version = v.id; ok = true; break; }
                        if (!ok) for (auto& v : gVers) if (VerShown(v, cfg.loader)) { cfg.version = v.id; break; }
                    }
                };
                ImGui::SetNextItemWidth(-1);
                if (ImGui::BeginCombo("##ldr", cfg.loader.c_str())) {
                    for (int i = 0; i < kNLoaders; i++) {
                        bool sel = cfg.loader == kLoaders[i];
                        if (ImGui::Selectable(kLoaders[i], sel) && !sel) { cfg.loader = kLoaders[i]; fixVer(); }
                        if (sel) ImGui::SetItemDefaultFocus();
                    }
                    ImGui::EndCombo();
                }
            }
            ImGui::Separator();
            ImGui::BeginChild("##vlist", ImVec2(0, 0), false);
            {
                std::lock_guard<std::mutex> l(gVerMu);
                for (auto& v : gVers) {
                    if (!VerShown(v, cfg.loader)) continue;
                    std::string lab = v.id + (v.type == "snapshot" ? T("   [снапшот]", "   [snapshot]") : v.type == "old_beta" ? T("   [бета]", "   [beta]") : v.type == "old_alpha" ? T("   [альфа]", "   [alpha]") : "");
                    bool has = gInstNames.count(InstName(cfg.loader, v.id)) > 0, off = gBusy || gGameRunning || gDelBusy;
                    ImGui::PushID(v.id.c_str());
                    bool clicked = ImGui::Selectable(lab.c_str(), v.id == cfg.version); // полоска выбора — на всю строку
                    if (has) { // версия установлена — справа корзина (удаление с подтверждением)
                        ImVec2 a = ImGui::GetItemRectMin(), b = ImGui::GetItemRectMax(); float h = b.y - a.y, pad = 6.f * gS;
                        ImVec2 ta(b.x - h * 1.1f - pad, a.y), tb(b.x - pad, b.y);
                        bool hovT = ImGui::IsWindowHovered() && ImGui::IsMouseHoveringRect(ta, tb);
                        DrawTrash(ImGui::GetWindowDrawList(), ta, tb, hovT, !off);
                        if (clicked && hovT) { clicked = false; if (!off) { gDelAsk = DelReq{cfg.loader, v.id}; ImGui::CloseCurrentPopup(); } }
                    }
                    if (clicked) { cfg.version = v.id; ImGui::CloseCurrentPopup(); }
                    ImGui::PopID();
                }
            }
            ImGui::EndChild();
            ImGui::EndPopup();
        }
    }
    ImGui::SameLine();
    if (FancyBtn(busy ? T("Работаю...", "Working...") : T("ИГРАТЬ", "PLAY"), ImVec2(wc, bh), gAccent, !busy && !gDelBusy && !cfg.version.empty())) StartLaunch();
    ImGui::SameLine();
    std::string al = (cfg.sel >= 0 && cfg.sel < (int)cfg.accs.size()) ? cfg.accs[cfg.sel].name : std::string(T("Добавить аккаунт", "Add account"));
    if (FancyBtn(al.c_str(), ImVec2(wl, bh), gSoft)) Go(S_ACC);
}

// ---------- Аккаунты ----------
static void ScrAccounts() {
    float em = ImGui::GetFontSize(); ImGuiStyle& sty = ImGui::GetStyle();
    if (Header(T("Аккаунты", "Accounts"))) { Go(S_MAIN); return; }
    float sp = sty.ItemSpacing.x, cw = (ImGui::GetContentRegionAvail().x - 2 * sp) / 3, ch = em * 17.5f, bh = em * 2.2f;
    for (int i = 0; i < 3; i++) {
        if (i) ImGui::SameLine();
        ImGui::PushStyleColor(ImGuiCol_ChildBg, gSoft); ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(em, em));
        ImGui::BeginChild(i == 0 ? "c_ely" : i == 1 ? "c_off" : "c_ms", ImVec2(cw, ch), ImGuiChildFlags_AlwaysUseWindowPadding, ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse);
        ImGui::PopStyleVar(); ImGui::PopStyleColor();
        auto Title = [&](const char* s) { ImGui::PushFont(gFSub); ImGui::TextColored(gAccent, "%s", s); ImGui::PopFont(); ImGui::Dummy(ImVec2(0, em * .1f)); };
        auto Bul = [&](const char* s) { ImGui::PushTextWrapPos(0.f); ImGui::BulletText("%s", s); ImGui::PopTextWrapPos(); };
        float by = ch - em - bh;
        if (i == 0) { // Ely.by
            Title("Ely.by");
            Bul(T("Скины поддерживаются", "Skins supported")); Bul(T("Для пиратской версии", "For non-licensed copies")); Bul(T("Требуется интернет", "Internet required"));
            ImGui::Dummy(ImVec2(0, em * .2f));
            ImGui::SetNextItemWidth(-1); ImGui::InputTextWithHint("##eu", T("Логин или e-mail", "Login or e-mail"), bElyU, sizeof(bElyU));
            ImGui::SetNextItemWidth(-1); ImGui::InputTextWithHint("##ep", T("Пароль (с 2FA: пароль:код)", "Password (with 2FA: password:code)"), bElyP, sizeof(bElyP), ImGuiInputTextFlags_Password);
            ImGui::SetCursorPosY(by);
            if (FancyBtn(T("Войти", "Sign in"), ImVec2(0, bh), gAccent, !gAuthBusy) && bElyU[0]) std::thread(ElyLoginThread, std::string(bElyU), std::string(bElyP)).detach();
        } else if (i == 1) { // офлайн
            Title(T("Офлайн", "Offline"));
            Bul(T("Нет поддержки скинов", "No skin support")); Bul(T("Пиратка / лицензия", "Non-licensed / licensed")); Bul(T("Интернет не требуется", "No internet required"));
            ImGui::Dummy(ImVec2(0, em * .2f));
            ImGui::SetNextItemWidth(-1); ImGui::InputText("##nick", bNick, sizeof(bNick));
            ImGui::PushTextWrapPos(0.f); ImGui::TextDisabled("%s", T(kNickHint, "Nick: 3-16 chars, Latin letters, digits and _")); ImGui::PopTextWrapPos();
            ImGui::SetCursorPosY(by);
            if (FancyBtn(T("Войти", "Sign in"), ImVec2(0, bh), gAccent) && AddOffline(bNick)) Go(S_MAIN);
        } else { // Microsoft
            Title("Microsoft");
            Bul(T("Есть поддержка скинов", "Skins supported")); Bul(T("Лицензия", "Licensed copy")); Bul(T("Требуется интернет", "Internet required"));
            ImGui::Dummy(ImVec2(0, em * .2f));
            if (bMsId[0] == 0) { std::string id = MsId(); snprintf(bMsId, sizeof(bMsId), "%s", id.c_str()); }
            ImGui::SetNextItemWidth(-1);
            if (ImGui::InputTextWithHint("##msid", "Azure Client ID (portal.azure.com)", bMsId, sizeof(bMsId))) SetMsId(bMsId);
            std::string code, uri; { std::lock_guard<std::mutex> l(gMu); code = gMsCode; uri = gMsUri; }
            if (!code.empty()) {
                ImGui::PushTextWrapPos(0.f); ImGui::TextWrapped(T("Открой %s и введи код:", "Open %s and enter the code:"), uri.c_str()); ImGui::PopTextWrapPos();
                ImGui::PushFont(gFTitle); ImGui::TextColored(gAccent, "%s", code.c_str()); ImGui::PopFont();
                ImGui::SameLine(); if (ImGui::SmallButton(T("Копировать", "Copy"))) ImGui::SetClipboardText(code.c_str());
            }
            ImGui::SetCursorPosY(by);
            if (FancyBtn(T("Войти", "Sign in"), ImVec2(0, bh), gAccent, !gAuthBusy)) { SetMsId(bMsId); SaveConfig(); std::thread(MsLoginThread).detach(); }
        }
        ImGui::EndChild();
    }
    TD(T("Сохранённые аккаунты", "Saved accounts"));
    float listH = std::max(em * 3.f, ImGui::GetContentRegionAvail().y - em * 2.6f); int del = -1;
    ImGui::BeginChild("accl", ImVec2(0, listH), 0, ImGuiWindowFlags_NoBackground);
    for (int i = 0; i < (int)cfg.accs.size(); i++) {
        ImGui::PushID(i);
        if (ImGui::Selectable(AccLabel(cfg.accs[i]).c_str(), cfg.sel == i, 0, ImVec2(ImGui::GetContentRegionAvail().x - em * 2.2f, 0))) cfg.sel = i;
        ImGui::SameLine(); if (ImGui::SmallButton("x")) del = i;
        ImGui::PopID();
    }
    if (cfg.accs.empty()) TD(T("Пока нет ни одного аккаунта", "No accounts yet"));
    ImGui::EndChild();
    if (del >= 0) { cfg.accs.erase(cfg.accs.begin() + del); if (cfg.accs.empty()) cfg.sel = -1; else if (cfg.sel == del) cfg.sel = 0; else if (cfg.sel > del) cfg.sel--; SaveConfig(); }
    std::string st; { std::lock_guard<std::mutex> l(gMu); st = gAuthMsg; }
    if (!st.empty()) ImGui::TextWrapped("%s", st.c_str());
}

// ---------- Моды ----------
static void ScrMods() {
    float em = ImGui::GetFontSize(); ImDrawList* dl = ImGui::GetWindowDrawList();
    if (Header(T("Моды", "Mods"))) { Go(S_MAIN); return; }
    std::string ld = LoaderId(cfg.loader);
    std::string key = gWantQ + "|" + ld + "|" + cfg.version;
    if (!ld.empty() && !cfg.version.empty() && key != gModKey && !gModBusy) { gModKey = key; std::thread(ModSearchThread, gWantQ, ld, cfg.version).detach(); }
    fs::path idir = CurrentInstanceDir(); ModsSync(idir);
    float total = ImGui::GetContentRegionAvail().x, lw = total * 0.34f;
    ImGui::BeginChild("modsL", ImVec2(lw, 0), 0, ImGuiWindowFlags_NoBackground);
    TD(T("Сайт для загрузки модов", "Mod download site")); ImGui::TextUnformatted("Modrinth");
    TD(T("Установка на", "Installing for")); ImGui::Text("%s  %s", cfg.loader.c_str(), cfg.version.c_str());
    ImGui::SetNextItemWidth(-1);
    bool go = ImGui::InputTextWithHint("##mq", T("Поиск...", "Search..."), bModQ, sizeof(bModQ), ImGuiInputTextFlags_EnterReturnsTrue);
    if (FancyBtn(T("Найти", "Search"), ImVec2(0, em * 2.f), gSoft)) go = true;
    if (go) { gWantQ = bModQ; gModKey.clear(); } // повторный поиск даже с тем же запросом
    std::string msg; { std::lock_guard<std::mutex> l(gModMu); msg = gModMsg; }
    if (ld.empty()) msg = T("Для модов выбери загрузчик Fabric, Forge, NeoForge или Quilt на главном экране.", "Pick the Fabric, Forge, NeoForge or Quilt loader on the main screen to use mods.");
    if (!msg.empty()) { ImGui::PushTextWrapPos(0.f); ImGui::TextColored(gAccent, "%s", msg.c_str()); ImGui::PopTextWrapPos(); }
    ImGui::EndChild();
    ImGui::SameLine();
    ImGui::BeginChild("modsR", ImVec2(0, 0), 0, ImGuiWindowFlags_NoBackground);
    dl = ImGui::GetWindowDrawList();
    if (!ld.empty()) {
        std::vector<ModHit> hits; std::set<std::string> have;
        { std::lock_guard<std::mutex> l(gModMu); hits = gModHits; for (auto& kv : gModFiles) have.insert(kv.first); }
        if (gModBusy && hits.empty()) TD(T("Загрузка...", "Loading..."));
        bool busyI = gModInst;
        for (int i = 0; i < (int)hits.size(); i++) {
            auto& h = hits[i]; ImGui::PushID(i);
            bool d = have.count(h.id) > 0; // мод уже скачан в этот экземпляр
            ImVec2 p = ImGui::GetCursorScreenPos(); float w = ImGui::GetContentRegionAvail().x, bw = em * 8.5f, dw = em * 6.f, gp = em * .5f, btns = bw + (d ? dw + gp : 0.f), tw = std::max(em * 6.f, w - btns - em * 2.4f);
            ImVec2 ds = ImGui::CalcTextSize(h.desc.c_str(), nullptr, false, tw); float dh = std::min(ds.y, em * 2.4f), rh = em * .7f + em * 1.3f + dh + em * .7f;
            dl->AddRectFilled(p, ImVec2(p.x + w, p.y + rh), ImGui::GetColorU32(gSoft), R(em * .6f));
            dl->AddText(ImVec2(p.x + em, p.y + em * .7f), TextCol(), h.title.c_str());
            ImVec4 clip(p.x, p.y, p.x + em + tw, p.y + rh - em * .4f);
            dl->AddText(ImGui::GetFont(), ImGui::GetFontSize(), ImVec2(p.x + em, p.y + em * .7f + em * 1.3f), TextCol(.65f), h.desc.c_str(), nullptr, tw, &clip);
            float by = p.y + (rh - em * 2.f) / 2, bx = p.x + w - em * .8f - btns;
            ImGui::SetCursorScreenPos(ImVec2(bx, by));
            if (FancyBtn(d ? T("Установлено", "Installed") : T("Установить", "Install"), ImVec2(bw, em * 2.f), d ? gSoft : gAccent, !busyI && !d)) std::thread(ModInstallThread, h.id, h.title, ld, cfg.version, PS(idir)).detach();
            if (d) {
                ImGui::SetCursorScreenPos(ImVec2(bx + bw + gp, by));
                if (FancyBtn(T("Удалить", "Delete"), ImVec2(dw, em * 2.f), ImVec4(.90f, .30f, .30f, .55f), !busyI)) { ModDelete(idir, h.id); ModMsg(std::string(T("Удалено: ", "Removed: ")) + h.title); }
            }
            ImGui::SetCursorScreenPos(p); ImGui::Dummy(ImVec2(w, rh));
            ImGui::PopID();
        }
    }
    ImGui::EndChild();
}

static void ScrLog() {
    if (Header(T("Лог", "Log"))) { Go(S_MAIN); return; }
    ImGui::BeginChild("log", ImVec2(0, 0), false);
    { std::lock_guard<std::mutex> l(gMu);
      ImGuiListClipper cl; cl.Begin((int)gLog.size());
      while (cl.Step()) for (int i = cl.DisplayStart; i < cl.DisplayEnd; i++) ImGui::TextUnformatted(gLog[i].c_str()); }
    if (ImGui::GetScrollY() >= ImGui::GetScrollMaxY() - 4) ImGui::SetScrollHereY(1.f);
    ImGui::EndChild();
}

// ---------- Изменить экземпляр ----------
struct WorldInfo { std::string name, date; };
static std::vector<WorldInfo> gWorlds; static float gWorldsT = 99.f;
static std::map<std::string, long long> gWorldSz; static std::set<std::string> gWorldSzBusy; static std::mutex gWsMu;
static std::atomic<bool> gWorldBusy{false};
static std::string gWorldAsk, gWorldDel; // запрос на удаление мира
static InstCfg gEd; static std::string gEdName; static int gEdTab = 0, gEdNeedJava = 0;
static char eJava[260], eJvm[512], eWrap[512], ePre[512], ePost[512], eEnv[2048];
static std::vector<std::string> gComps; static float gCompsT = 99.f;

static bool ZipDir(const fs::path& dir, const std::string& top, const fs::path& zipPath) { // папка -> zip (внутри лежит папка top)
    std::error_code ec; fs::create_directories(zipPath.parent_path(), ec);
    FILE* f = fopen(zipPath.string().c_str(), "wb"); if (!f) return false;
    mz_zip_archive z{};
    if (!mz_zip_writer_init_cfile(&z, f, 0)) { fclose(f); return false; }
    bool ok = true;
    for (auto it = fs::recursive_directory_iterator(dir, ec); it != fs::recursive_directory_iterator(); it.increment(ec)) {
        if (ec) break;
        if (!it->is_regular_file(ec)) continue;
        fs::path rel = fs::relative(it->path(), dir, ec); if (ec) continue;
        if (rel.filename() == "session.lock") continue; // файл блокировки открытого мира
        std::string name = top + "/" + PS(rel); for (auto& ch : name) if (ch == '\\') ch = '/';
        std::string data = ReadAll(it->path());
        if (!mz_zip_writer_add_mem(&z, name.c_str(), data.data(), data.size(), MZ_DEFAULT_LEVEL)) { ok = false; break; }
    }
    if (ok) ok = mz_zip_writer_finalize_archive(&z) != 0;
    mz_zip_writer_end(&z); fclose(f);
    if (!ok) fs::remove(zipPath, ec);
    return ok;
}
static std::string FmtWriteDate(const fs::path& p) {
    struct stat sb; if (stat(p.c_str(), &sb) != 0) return "?";
    time_t tt = sb.st_mtime; struct tm tmv; if (!localtime_r(&tt, &tmv)) return "?";
    char b2[48]; snprintf(b2, sizeof(b2), "%02d.%02d.%04d %02d:%02d", tmv.tm_mday, tmv.tm_mon + 1, tmv.tm_year + 1900, tmv.tm_hour, tmv.tm_min);
    return b2;
}
static void WorldSizeThread(std::string key, fs::path dir) {
    std::error_code ec; long long sum = 0;
    for (auto it = fs::recursive_directory_iterator(dir, ec); it != fs::recursive_directory_iterator(); it.increment(ec)) {
        if (ec) break;
        if (it->is_regular_file(ec)) sum += (long long)it->file_size(ec);
    }
    std::lock_guard<std::mutex> l(gWsMu); gWorldSz[key] = sum; gWorldSzBusy.erase(key);
}
static void ScanWorlds(bool force) {
    gWorldsT += ImGui::GetIO().DeltaTime; if (!force && gWorldsT < 1.5f) return; gWorldsT = 0;
    std::vector<WorldInfo> v; std::error_code ec;
    for (auto& e : fs::directory_iterator(gRoot / "instances" / P(gEdName) / "saves", ec))
        if (e.is_directory(ec)) { WorldInfo w; w.name = U8(e.path().filename().string()); w.date = FmtWriteDate(e.path()); v.push_back(w); }
    std::sort(v.begin(), v.end(), [](const WorldInfo& a, const WorldInfo& b) { return a.name < b.name; });
    gWorlds = v;
}
static std::string PickSaveZip(void*, const std::string& defName) { // нужен zenity или kdialog
    if (HaveCmd("zenity")) return RunCapture("zenity --file-selection --save --confirm-overwrite --filename=" + ShQ(HomeDir() + "/" + defName) + " 2>/dev/null");
    if (HaveCmd("kdialog")) return RunCapture("kdialog --getsavefilename " + ShQ(HomeDir() + "/" + defName) + " " + ShQ("*.zip|ZIP") + " 2>/dev/null");
    Status(T("Для выбора файла нужен zenity или kdialog (установи через менеджер пакетов)", "zenity or kdialog is needed to choose a file (install it with your package manager)")); return "";
}
static void WorldTask(int kind, std::string inst, std::string world, std::string outPath) { // 0 бэкап, 1 экспорт, 2 удаление
    gWorldBusy = true; std::error_code ec;
    fs::path dir = gRoot / "instances" / P(inst) / "saves" / P(world);
    if (kind == 2) {
        Status(std::string(T("Удаляю мир: ", "Deleting world: ")) + world); fs::remove_all(dir, ec);
        Status(std::string(T("Мир удалён: ", "World deleted: ")) + world);
    } else {
        fs::path z; std::string what;
        if (kind == 0) {
            time_t now = time(nullptr); struct tm st; localtime_r(&now, &st); char ts[64];
            snprintf(ts, sizeof(ts), "%04d-%02d-%02d_%02d-%02d-%02d", st.tm_year + 1900, st.tm_mon + 1, st.tm_mday, st.tm_hour, st.tm_min, st.tm_sec);
            z = gRoot / "instances" / P(inst) / "poltergeist_backups" / P(world + "_" + ts + ".zip"); what = T("Резервная копия", "Backup");
        } else { z = P(outPath); what = T("Экспорт мира", "World export"); }
        Status(what + ": " + world + "...");
        bool ok = ZipDir(dir, world, z);
        Status(ok ? what + std::string(T(" готов: ", " done: ")) + PS(z.filename()) : what + T(" не удался", " failed"));
    }
    gWorldBusy = false;
}
static void InstEditorOpen(const std::string& name) {
    gEdName = name; gEd = LoadInstCfg(gRoot / "instances" / P(name));
    snprintf(eJava, sizeof(eJava), "%s", gEd.javaPath.c_str()); snprintf(eJvm, sizeof(eJvm), "%s", gEd.jvmArgs.c_str());
    snprintf(eWrap, sizeof(eWrap), "%s", gEd.wrapper.c_str()); snprintf(ePre, sizeof(ePre), "%s", gEd.pre.c_str()); snprintf(ePost, sizeof(ePost), "%s", gEd.post.c_str());
    snprintf(eEnv, sizeof(eEnv), "%s", gEd.env.c_str());
    gEdTab = 0; gWorldsT = 99.f; gCompsT = 99.f; gWorldAsk.clear();
    { std::lock_guard<std::mutex> l(gWsMu); gWorldSz.clear(); }
    InstInfo ii = ParseInst(name); gEdNeedJava = 0;
    json vj = Parse(ReadAll(gRoot / "versions" / P(ii.ver) / P(ii.ver + ".json")));
    if (vj.is_object() && vj.contains("javaVersion") && vj["javaVersion"].is_object() && vj["javaVersion"].contains("majorVersion") && vj["javaVersion"]["majorVersion"].is_number_integer())
        gEdNeedJava = vj["javaVersion"]["majorVersion"].get<int>();
    RefreshJavas();
}
static void InstEditorBody(bool& close) {
    float em = ImGui::GetFontSize(); InstInfo ii = ParseInst(gEdName); fs::path dir = gRoot / "instances" / P(gEdName);
    ImGuiIO& io = ImGui::GetIO(); bool ch = false;
    ImGui::PushFont(gFSub); ImGui::TextColored(gAccent, "%s  %s", ii.loader.c_str(), ii.ver.c_str()); ImGui::PopFont();
    const char* labs[7] = {T("Миры", "Worlds"), T("Версия", "Version"), T("Память", "Memory"), "Java", "Minecraft", T("Команды", "Commands"), T("Окружение", "Environment")};
    TabBar(labs, 7, gEdTab, false);
    ImGui::BeginChild("##ebody", ImVec2(0, -(em * 2.8f)), 0, ImGuiWindowFlags_NoBackground);
    ImDrawList* dl = ImGui::GetWindowDrawList();
    if (gEdTab == 0) { // ---- Миры ----
        ScanWorlds(false); bool busyW = gWorldBusy;
        if (FancyBtn(T("Папка saves", "Saves folder"), ImVec2(em * 10, em * 1.9f), gSoft)) Open(dir / "saves");
        ImGui::SameLine(); if (FancyBtn(T("Папка бэкапов", "Backups folder"), ImVec2(em * 11, em * 1.9f), gSoft)) Open(dir / "poltergeist_backups");
        TD(T("Список локальных миров. Бэкап кладётся в папку бэкапов, экспорт — в zip, который выберешь сам.", "Local worlds. A backup goes to the backups folder, export saves a zip where you choose."));
        if (gWorlds.empty()) TD(T("В этом экземпляре пока нет миров.", "No worlds in this instance yet."));
        for (int i = 0; i < (int)gWorlds.size(); i++) {
            const WorldInfo& w = gWorlds[i]; ImGui::PushID(i);
            float aw = ImGui::GetContentRegionAvail().x, rh = em * 3.0f, bh = em * 1.9f, bw = em * 7.f, tw = em * 2.2f, gp = em * .4f; ImVec2 p = ImGui::GetCursorScreenPos();
            float x = p.x + aw - em * .6f - tw, by = p.y + (rh - bh) / 2;
            dl->AddRectFilled(p, ImVec2(p.x + aw, p.y + rh), ImGui::GetColorU32(gSoft), R(em * .6f));
            std::string szs = "...";
            { std::lock_guard<std::mutex> l(gWsMu); auto f = gWorldSz.find(w.name);
              if (f != gWorldSz.end()) szs = FmtSize(f->second); else if (gWorldSzBusy.insert(w.name).second) std::thread(WorldSizeThread, w.name, dir / "saves" / P(w.name)).detach(); }
            float maxw = std::max(em * 4.f, aw - (bw * 2 + tw + gp * 3 + em * 1.6f));
            ImVec4 clip(p.x, p.y, p.x + em + maxw, p.y + rh);
            dl->AddText(ImGui::GetFont(), ImGui::GetFontSize(), ImVec2(p.x + em, p.y + em * .45f), TextCol(), w.name.c_str(), nullptr, 0.f, &clip);
            std::string sub = w.date + "  |  " + szs;
            dl->AddText(ImGui::GetFont(), ImGui::GetFontSize(), ImVec2(p.x + em, p.y + em * 1.55f), TextCol(.55f), sub.c_str(), nullptr, 0.f, &clip);
            ImGui::SetCursorScreenPos(ImVec2(x - gp * 2 - bw * 2, by));
            if (FancyBtn(T("Бэкап", "Backup"), ImVec2(bw, bh), gSoft, !busyW)) std::thread(WorldTask, 0, gEdName, w.name, std::string()).detach();
            ImGui::SetCursorScreenPos(ImVec2(x - gp - bw, by));
            if (FancyBtn(T("Экспорт", "Export"), ImVec2(bw, bh), gSoft, !busyW)) { std::string out = PickSaveZip(nullptr, w.name + ".zip"); if (!out.empty()) std::thread(WorldTask, 1, gEdName, w.name, out).detach(); }
            ImGui::SetCursorScreenPos(ImVec2(x, p.y + (rh - tw) / 2));
            if (TrashBtn("del", tw, !busyW && !gGameRunning)) gWorldAsk = w.name;
            ImGui::SetCursorScreenPos(p); ImGui::Dummy(ImVec2(aw, rh));
            ImGui::PopID();
        }
        if (busyW) { std::string st; { std::lock_guard<std::mutex> l(gMu); st = gStatus; } ImGui::TextColored(gAccent, "%s", st.c_str()); }
    } else if (gEdTab == 1) { // ---- Версия ----
        auto Row = [&](const char* k, const std::string& v) { ImGui::TextDisabled("%s", k); ImGui::SameLine(em * 11.f); ImGui::TextWrapped("%s", v.c_str()); };
        Row(T("Minecraft", "Minecraft"), ii.ver); Row(T("Загрузчик", "Loader"), ii.loader);
        Row(T("Нужна Java", "Required Java"), gEdNeedJava > 0 ? std::to_string(gEdNeedJava) : std::string("?"));
        Row(T("Папка", "Folder"), PS(dir));
        if (FancyBtn(T("Выбрать для запуска", "Select for launch"), ImVec2(em * 14, em * 1.9f), gAccent)) { cfg.loader = ii.loader; cfg.version = ii.ver; SaveConfig(); close = true; }
        ImGui::Dummy(ImVec2(0, em * .3f));
        gCompsT += io.DeltaTime;
        if (gCompsT > 1.f) {
            gCompsT = 0; gComps.clear(); std::error_code ec;
            if (fs::exists(gRoot / "versions" / P(ii.ver) / P(ii.ver + ".json"), ec)) gComps.push_back(ii.ver);
            if (ii.loader != "Vanilla") for (auto& id : LoaderProfiles(ii.loader, ii.ver)) gComps.push_back(id);
        }
        TD(T("Установленные компоненты (патч-файлы)", "Installed components (patch files)"));
        if (gComps.empty()) TD(T("Пока ничего не установлено — всё скачается при первом запуске.", "Nothing installed yet — everything downloads on first launch."));
        for (int i = 0; i < (int)gComps.size(); i++) {
            const std::string id = gComps[i]; ImGui::PushID(i);
            float aw = ImGui::GetContentRegionAvail().x, rh = em * 2.6f, tw = em * 2.2f; ImVec2 p = ImGui::GetCursorScreenPos();
            dl->AddRectFilled(p, ImVec2(p.x + aw, p.y + rh), ImGui::GetColorU32(gSoft), R(em * .6f));
            std::string lab = (id == ii.ver ? std::string("Minecraft  ") : ii.loader + "  ") + id;
            dl->AddText(ImVec2(p.x + em, p.y + (rh - em) / 2), TextCol(), lab.c_str());
            ImGui::SetCursorScreenPos(ImVec2(p.x + aw - em * .6f - tw, p.y + (rh - tw) / 2));
            if (TrashBtn("rm", tw, !gBusy && !gGameRunning && !gDelBusy)) { std::error_code ec; fs::remove_all(gRoot / "versions" / P(id), ec); gCompsT = 99.f; }
            ImGui::SetCursorScreenPos(p); ImGui::Dummy(ImVec2(aw, rh));
            ImGui::PopID();
        }
        TD(T("Удалённый компонент скачается заново при следующем запуске.", "A removed component is downloaded again on the next launch."));
    } else if (gEdTab == 2) { // ---- Память ----
        long pages = sysconf(_SC_PHYS_PAGES), psz = sysconf(_SC_PAGE_SIZE); int maxMb = std::max(2048, (int)((long long)pages * psz / (1024 * 1024) * 3 / 4));
        ch |= ImGui::Checkbox(T("Свои настройки памяти для этого экземпляра", "Override memory for this instance"), &gEd.memOv);
        if (!gEd.memOv) ImGui::TextDisabled(T("Сейчас используется общая настройка: %d МБ (вкладка Java в настройках)", "Global setting in use: %d MB (Java tab in settings)"), cfg.ramMB);
        ImGui::BeginDisabled(!gEd.memOv);
        TD(T("Минимум (Xms)", "Minimum (Xms)")); ImGui::SetNextItemWidth(-1); ch |= ImGui::SliderInt("##emin", &gEd.minMB, 128, maxMb, T("%d МБ", "%d MB"));
        TD(T("Максимум (Xmx)", "Maximum (Xmx)")); ImGui::SetNextItemWidth(-1); ch |= ImGui::SliderInt("##emax", &gEd.maxMB, 256, maxMb, T("%d МБ", "%d MB"));
        gEd.maxMB = std::min(gEd.maxMB, maxMb); gEd.minMB = std::min(gEd.minMB, gEd.maxMB);
        ImGui::EndDisabled();
    } else if (gEdTab == 3) { // ---- Java ----
        ch |= ImGui::Checkbox(T("Свои настройки Java для этого экземпляра", "Override Java for this instance"), &gEd.javaOv);
        ImGui::BeginDisabled(!gEd.javaOv);
        TD("Java"); ImGui::SetNextItemWidth(-1);
        std::string cur = gEd.javaPath.empty() ? std::string(T("Авто (подберу и скачаю сам)", "Auto (pick and download automatically)")) : gEd.javaPath;
        if (ImGui::BeginCombo("##ejava", cur.c_str())) {
            if (ImGui::Selectable(T("Авто (подберу и скачаю сам)", "Auto (pick and download automatically)"), gEd.javaPath.empty())) { gEd.javaPath.clear(); eJava[0] = 0; ch = true; }
            std::lock_guard<std::mutex> l(gJavaMu);
            for (auto& j : gJavas) { std::string t = "Java " + std::to_string(j.major) + "  -  " + j.exe; if (ImGui::Selectable(t.c_str(), gEd.javaPath == j.exe)) { gEd.javaPath = j.exe; snprintf(eJava, sizeof(eJava), "%s", j.exe.c_str()); ch = true; } }
            ImGui::EndCombo();
        }
        ImGui::SetNextItemWidth(-1);
        if (ImGui::InputTextWithHint("##ejp", T("...или свой путь к java", "...or your own path to java"), eJava, sizeof(eJava))) { gEd.javaPath = eJava; ch = true; }
        TD(T("Аргументы JVM", "JVM arguments")); ImGui::SetNextItemWidth(-1);
        if (ImGui::InputTextWithHint("##ejvm", "-XX:+UseZGC -Dfile.encoding=UTF-8", eJvm, sizeof(eJvm))) { gEd.jvmArgs = eJvm; ch = true; }
        ch |= ImGui::Checkbox(T("Пропустить проверку совместимости Java", "Skip Java compatibility check"), &gEd.skipCompat);
        ImGui::EndDisabled();
    } else if (gEdTab == 4) { // ---- Minecraft ----
        ch |= ImGui::Checkbox(T("Свои настройки игры для этого экземпляра", "Override game settings for this instance"), &gEd.mcOv);
        ImGui::BeginDisabled(!gEd.mcOv);
        TD(T("Размер окна игры", "Game window size"));
        ImGui::SetNextItemWidth(em * 8); ch |= ImGui::InputInt("##ew", &gEd.width, 0, 0); ImGui::SameLine(); ImGui::TextUnformatted("x"); ImGui::SameLine();
        ImGui::SetNextItemWidth(em * 8); ch |= ImGui::InputInt("##eh", &gEd.height, 0, 0);
        gEd.width = std::clamp(gEd.width, 1, 16384); gEd.height = std::clamp(gEd.height, 1, 16384);
        ch |= ImGui::Checkbox(T("Запускать в полноэкранном режиме", "Start in fullscreen"), &gEd.fullscreen);
        ImGui::EndDisabled();
    } else if (gEdTab == 5) { // ---- Команды ----
        ch |= ImGui::Checkbox(T("Свои команды для этого экземпляра", "Custom commands for this instance"), &gEd.cmdOv);
        ImGui::BeginDisabled(!gEd.cmdOv);
        TD(T("Команда-обёртка (Wrapper), например gamemoderun или mangohud — ставится перед командой запуска Java", "Wrapper command — placed before the Java launch command")); ImGui::SetNextItemWidth(-1);
        if (ImGui::InputText("##ewrap", eWrap, sizeof(eWrap))) { gEd.wrapper = eWrap; ch = true; }
        TD(T("Команда перед запуском (игра ждёт её завершения)", "Pre-launch command (the game waits for it)")); ImGui::SetNextItemWidth(-1);
        if (ImGui::InputText("##epre", ePre, sizeof(ePre))) { gEd.pre = ePre; ch = true; }
        TD(T("Команда после выхода из игры", "Post-exit command")); ImGui::SetNextItemWidth(-1);
        if (ImGui::InputText("##epost", ePost, sizeof(ePost))) { gEd.post = ePost; ch = true; }
        ImGui::EndDisabled();
        ImGui::PushTextWrapPos(0.f);
        TD(T("Переменные: $INST_DIR и $INST_MC_DIR (папка экземпляра), $INST_NAME, $INST_ID, $INST_MC_VER, $INST_LOADER, $INST_JAVA., они же доступны как переменные окружения. Команды выполняются через sh -c; пути с пробелами бери в кавычки.",
              "Variables: $INST_DIR and $INST_MC_DIR (instance folder), $INST_NAME, $INST_ID, $INST_MC_VER, $INST_LOADER, $INST_JAVA., also available as environment variables. Commands run via sh -c; quote paths with spaces."));
        ImGui::PopTextWrapPos();
    } else { // ---- Переменные окружения ----
        ch |= ImGui::Checkbox(T("Свои переменные окружения для этого экземпляра", "Custom environment variables for this instance"), &gEd.envOv);
        ImGui::BeginDisabled(!gEd.envOv);
        if (ImGui::InputTextMultiline("##eenv", eEnv, sizeof(eEnv), ImVec2(-1, em * 10))) { gEd.env = eEnv; ch = true; }
        ImGui::EndDisabled();
        TD(T("По одной переменной в строке: ИМЯ=значение. Строки с # игнорируются.", "One variable per line: NAME=value. Lines starting with # are ignored."));
    }
    ImGui::EndChild();
    if (ch) SaveInstCfg(dir, gEd);
    if (!gWorldAsk.empty()) { gWorldDel = gWorldAsk; gWorldAsk.clear(); ImGui::OpenPopup("###wdel"); }
    ImGui::SetNextWindowPos(ImVec2(io.DisplaySize.x / 2, io.DisplaySize.y / 2), ImGuiCond_Always, ImVec2(.5f, .5f));
    ImGui::SetNextWindowSize(ImVec2(std::min(em * 28, io.DisplaySize.x - em * 2), 0));
    std::string wid = std::string(T("Удалить мир?", "Delete world?")) + "###wdel";
    if (ImGui::BeginPopupModal(wid.c_str(), nullptr, ImGuiWindowFlags_NoResize)) {
        ImGui::PushFont(gFSub); ImGui::TextColored(ImVec4(1.f, .45f, .4f, 1.f), "%s", gWorldDel.c_str()); ImGui::PopFont();
        ImGui::Separator();
        ImGui::TextWrapped("%s", T("Мир будет удалён безвозвратно. Если нужна копия — сначала сделай бэкап.", "The world will be deleted permanently. Make a backup first if you want a copy."));
        ImGui::Dummy(ImVec2(0, em * .5f));
        ImGui::PushStyleColor(ImGuiCol_Button, ImVec4(.85f, .25f, .25f, .75f)); ImGui::PushStyleColor(ImGuiCol_ButtonHovered, ImVec4(.90f, .30f, .30f, .90f)); ImGui::PushStyleColor(ImGuiCol_ButtonActive, ImVec4(.95f, .35f, .35f, 1.f));
        bool yes = ImGui::Button(T("Удалить", "Delete"), ImVec2(em * 8, 0));
        ImGui::PopStyleColor(3); ImGui::SameLine();
        bool no = ImGui::Button(T("Отмена", "Cancel"), ImVec2(em * 8, 0));
        if (yes && !gWorldBusy) std::thread(WorldTask, 2, gEdName, gWorldDel, std::string()).detach();
        if (yes || no) { ImGui::CloseCurrentPopup(); gWorldsT = 99.f; }
        ImGui::EndPopup();
    }
    if (ImGui::Button(T("Закрыть", "Close"), ImVec2(em * 8, 0))) close = true;
}

// ---------- Настройки ----------
static void ScrSettings() {
    float em = ImGui::GetFontSize(); ImDrawList* dl = ImGui::GetWindowDrawList();
    if (Header(T("Настройки", "Settings"))) { Go(S_MAIN); return; }
    const char* labs[5] = {T("Общие", "General"), T("Кастомизация", "Customization"), T("Компоненты", "Components"), "Java", T("Экземпляры", "Instances")};
    TabBar(labs, 5, gSetTab);
    ImGui::BeginChild("setc", ImVec2(0, 0), 0, ImGuiWindowFlags_NoBackground);
    dl = ImGui::GetWindowDrawList();
    if (gSetTab == 0) { // ---- Общие ----
        TD(T("Папка игры", "Game folder"));
        { std::string gd = PS(gRoot); ImGui::TextWrapped("%s", gd.c_str()); }
        if (FancyBtn(T("Выбрать папку игры...", "Choose game folder..."), ImVec2(em * 14, em * 1.9f), gSoft, !gBusy)) { std::string f = PickFolder(nullptr); if (!f.empty()) { SetGameDir(f); ScanShots(); } }
        if (!cfg.gameDir.empty()) { ImGui::SameLine(); if (FancyBtn(T("Вернуть стандартную", "Reset to default"), ImVec2(em * 12, em * 1.9f), gSoft, !gBusy)) { SetGameDir(""); ScanShots(); } }
        ImGui::Checkbox(T("Моды", "Mods"), &cfg.modsOn);
        if (ImGui::Checkbox(T("Логи", "Logs"), &cfg.logsOn)) gLogOn = cfg.logsOn;
        TD(T("Видеокарта", "Graphics card"));
        { const char* it[] = {T("Авто (решает система)", "Auto (system decides)"), T("Использовать дискретную", "Use discrete GPU"), T("Использовать встроенную", "Use integrated GPU")};
          int g = cfg.gpu == 2 ? 1 : cfg.gpu == 1 ? 2 : 0; if (ComboI("##gpu", g, it, 3)) cfg.gpu = g == 1 ? 2 : g == 2 ? 1 : 0; } // 0 авто, 1 встроенная, 2 дискретная
        if (FancyBtn(T("Проверка подключения к Modrinth", "Check Modrinth connection"), ImVec2(em * 19, em * 1.9f), gSoft, !gModChkBusy)) std::thread(ModrinthCheckThread).detach();
        { std::string chk; { std::lock_guard<std::mutex> l(gModMu); chk = gModChk; } if (!chk.empty()) ImGui::TextColored(gAccent, "%s", chk.c_str()); }
        TD(T("Язык лаунчера", "Launcher language"));
        { const char* it[] = {"Русский", "English"}; ComboI("##lang", cfg.lang, it, 2); }
        TD(T("После запуска игры", "After the game starts"));
        ImGui::RadioButton(T("Оставить лаунчер как есть", "Leave the launcher as is"), &cfg.onLaunch, 0);
        ImGui::RadioButton(T("Свернуть лаунчер в фон (значок в трее; если трея нет — просто свернуть)", "Hide the launcher to background (tray icon; minimize if there is no tray)"), &cfg.onLaunch, 1);
        ImGui::RadioButton(T("Закрыть лаунчер", "Close the launcher"), &cfg.onLaunch, 2);
        TD(T("Показывать в списке версий", "Show in the version list"));
        ImGui::Checkbox(T("Снапшоты", "Snapshots"), &cfg.snapshots);
        ImGui::Checkbox(T("Бета-версии (old_beta)", "Beta versions (old_beta)"), &cfg.showBeta);
        ImGui::Checkbox(T("Альфа-версии (old_alpha)", "Alpha versions (old_alpha)"), &cfg.showAlpha);
    } else if (gSetTab == 1) { // ---- Кастомизация ----
        TD(T("Тема", "Theme"));
        if (FancyBtn(T("Светлая", "Light"), ImVec2(em * 9, em * 2.f), cfg.light ? gAccent : gSoft)) cfg.light = true;
        ImGui::SameLine(); if (FancyBtn(T("Тёмная", "Dark"), ImVec2(em * 9, em * 2.f), cfg.light ? gSoft : gAccent)) cfg.light = false;
        TD(T("Цвет лаунчера", "Launcher color"));
        for (int i = 0; i < 5; i++) {
            ImGui::PushID(i); float d = em * 2.2f; ImVec2 p = ImGui::GetCursorScreenPos();
            if (ImGui::InvisibleButton("##col", ImVec2(d, d))) cfg.color = i;
            ImVec2 m(p.x + d / 2, p.y + d / 2);
            dl->AddCircleFilled(m, d * .36f, ImGui::GetColorU32(kPalette[i]));
            if (cfg.color == i) dl->AddCircle(m, d * .46f, TextCol(), 0, 2.f * gS);
            ImGui::PopID(); if (i < 4) ImGui::SameLine();
        }
        ImGui::Checkbox(T("Закругление углов", "Rounded corners"), &cfg.rounded);
        TD(T("Фон", "Background"));
        if (FancyBtn(T("Загрузить", "Upload"), ImVec2(em * 11, em * 1.9f), gSoft)) { std::string f = PickImage(nullptr); if (!f.empty()) { cfg.bg = f; cfg.slideshow = false; LoadBgAsync(f); } }
        ImGui::SameLine(); if (FancyBtn(T("Скрины из майна", "Minecraft screenshots"), ImVec2(em * 14, em * 1.9f), gSoft)) { ScanShots(); cfg.slideshow = true; NextShot(); }
        ImGui::Checkbox(T("Слайд-шоу (каждые ~18 сек)", "Slideshow (every ~18 s)"), &cfg.slideshow);
        ImGui::TextDisabled(T("Найдено скриншотов: %d", "Screenshots found: %d"), (int)gShots.size());
    } else if (gSetTab == 2) { // ---- Компоненты (Java) ----
        static bool first = true; if (first) { first = false; RefreshJavas(); }
        ImGui::TextColored(gAccent, "%s", T("Рекомендуется установить все Java!", "It is recommended to install all Java versions!"));
        std::vector<JavaInfo> js; { std::lock_guard<std::mutex> l(gJavaMu); js = gJavas; }
        int inst = gJavaInst;
        for (int v : kJavaVers) {
            bool have = false; for (auto& j : js) if (j.major == v) have = true;
            float bh = em * 2.f; ImVec2 p = ImGui::GetCursorScreenPos();
            std::string nm = "Java " + std::to_string(v); dl->AddText(ImVec2(p.x, p.y + (bh - em) / 2), TextCol(), nm.c_str());
            ImGui::Dummy(ImVec2(em * 6.f, bh)); ImGui::SameLine();
            ImGui::PushID(v);
            if (FancyBtn(have ? T("Установлено", "Installed") : (inst == v ? T("Установка...", "Installing...") : T("Установить", "Install")), ImVec2(em * 10, bh), have ? gSoft : gAccent, !have && !inst)) std::thread(JavaInstallThread, v).detach();
            ImGui::PopID();
            ImGui::SameLine(); ImVec2 q = ImGui::GetCursorScreenPos(); ImGui::Dummy(ImVec2(em * 2.f, bh));
            ImVec2 m(q.x + em, q.y + bh / 2);
            if (have) IconCheck(dl, m, em * .5f, ImGui::GetColorU32(ImVec4(.30f, .78f, .38f, 1.f))); else IconCross(dl, m, em * .5f, ImGui::GetColorU32(ImVec4(.92f, .32f, .32f, 1.f)));
        }
        if (gJavaScan) TD(T("Проверяю установленные Java...", "Scanning installed Java..."));
    } else if (gSetTab == 3) { // ---- Java ----
        TD("Java");
        static bool first = true; if (first) { first = false; RefreshJavas(); }
        ImGui::SetNextItemWidth(-1);
        std::string cur = cfg.javaPath.empty() ? std::string(T("Авто (подберу и скачаю сам)", "Auto (pick and download automatically)")) : cfg.javaPath;
        if (ImGui::BeginCombo("##java", cur.c_str())) {
            if (ImGui::Selectable(T("Авто (подберу и скачаю сам)", "Auto (pick and download automatically)"), cfg.javaPath.empty())) { cfg.javaPath.clear(); bJava[0] = 0; }
            std::lock_guard<std::mutex> l(gJavaMu);
            for (auto& j : gJavas) { std::string t = "Java " + std::to_string(j.major) + "  -  " + j.exe; if (ImGui::Selectable(t.c_str(), cfg.javaPath == j.exe)) { cfg.javaPath = j.exe; snprintf(bJava, sizeof(bJava), "%s", j.exe.c_str()); } }
            ImGui::EndCombo();
        }
        ImGui::SetNextItemWidth(-1);
        if (ImGui::InputTextWithHint("##jp", T("...или свой путь к java", "...or your own path to java"), bJava, sizeof(bJava))) cfg.javaPath = bJava;
        TD(T("Аргументы Java", "Java arguments"));
        ImGui::SetNextItemWidth(-1);
        if (ImGui::InputTextWithHint("##jvm", "-XX:+UseZGC -Dfile.encoding=UTF-8", bJvm, sizeof(bJvm))) cfg.jvmArgs = bJvm;
        TD(T("Добавляются после стандартных (-Xmx, G1GC)", "Appended after the defaults (-Xmx, G1GC)"));
        TD(T("Память (ОЗУ)", "Memory (RAM)"));
#ifdef _WIN32
    MEMORYSTATUSEX ms{sizeof(ms)}; GlobalMemoryStatusEx(&ms); int maxMb = std::max(2048, (int)(ms.ullTotalPhys / (1024 * 1024) * 3 / 4));
#else
    long pages = sysconf(_SC_PHYS_PAGES);
    long page_size = sysconf(_SC_PAGE_SIZE);
    long total_memory = pages * page_size;
    int maxMb = std::max(2048, (int)(total_memory / (1024 * 1024) * 3 / 4));
#endif
        ImGui::SetNextItemWidth(-1); ImGui::SliderInt("##ram", &cfg.ramMB, 1024, maxMb, T("%d МБ", "%d MB")); cfg.ramMB = std::min(cfg.ramMB, maxMb);
    } else { // ---- Экземпляры ----
        ScanInsts(false);
        static std::string iSel; static int iModal = 0;
        ImDrawList* cdl = ImGui::GetWindowDrawList();
        TD(T("Все экземпляры. Правая кнопка мыши: информация и изменение экземпляра.", "All instances. Right-click: information and edit instance."));
        if (gInsts.empty()) TD(T("Пока нет ни одного экземпляра. Он появится после первого запуска версии.", "No instances yet. One appears after the first launch of a version."));
        for (int i = 0; i < (int)gInsts.size(); i++) {
            const InstInfo& it = gInsts[i]; ImGui::PushID(i);
            float aw = ImGui::GetContentRegionAvail().x, rh = em * 2.6f; ImVec2 p = ImGui::GetCursorScreenPos();
            ImGui::InvisibleButton("##inst", ImVec2(aw, rh));
            float t = AnimK("h", ImGui::IsItemHovered() ? 1.f : 0.f, 14.f);
            cdl->AddRectFilled(p, ImVec2(p.x + aw, p.y + rh), ImGui::GetColorU32(ImVec4(gSoft.x, gSoft.y, gSoft.z, std::min(1.f, gSoft.w + .10f * t))), R(em * .6f));
            std::string lab = it.loader + "  " + it.ver; ImVec2 ls = ImGui::CalcTextSize(lab.c_str()), ns = ImGui::CalcTextSize(it.name.c_str());
            cdl->AddText(ImVec2(p.x + em, p.y + (rh - ls.y) / 2), TextCol(), lab.c_str());
            cdl->AddText(ImVec2(p.x + aw - ns.x - em, p.y + (rh - ns.y) / 2), TextCol(.45f), it.name.c_str());
            if (ImGui::BeginPopupContextItem("##ictx")) {
                if (ImGui::Selectable(T("Информация", "Information"))) { iSel = it.name; iModal = 1; }
                if (ImGui::Selectable(T("Изменить экземпляр", "Edit instance"))) { iSel = it.name; iModal = 2; }
                ImGui::EndPopup();
            }
            ImGui::PopID();
        }
        if (iModal == 1) {
            { std::lock_guard<std::mutex> l(gSzMu); gSizes.erase(iSel); if (gSzBusy.insert(iSel).second) std::thread(SizeThread, iSel).detach(); }
            ImGui::OpenPopup("###iinfo"); iModal = 0;
        } else if (iModal == 2) { InstEditorOpen(iSel); ImGui::OpenPopup("###iset"); iModal = 0; }
        ImGuiIO& io = ImGui::GetIO();
        auto Center = [&] { ImGui::SetNextWindowPos(ImVec2(io.DisplaySize.x / 2, io.DisplaySize.y / 2), ImGuiCond_Always, ImVec2(.5f, .5f)); ImGui::SetNextWindowSize(ImVec2(std::min(em * 30, io.DisplaySize.x - em * 2), 0)); };
        Center();
        std::string t1 = std::string(T("Информация об экземпляре", "Instance information")) + "###iinfo";
        if (ImGui::BeginPopupModal(t1.c_str(), nullptr, ImGuiWindowFlags_NoResize)) {
            InstInfo ii = ParseInst(iSel); fs::path dir = gRoot / "instances" / P(iSel);
            auto Row = [&](const char* k, const std::string& v) { ImGui::TextDisabled("%s", k); ImGui::SameLine(em * 9.f); ImGui::TextWrapped("%s", v.c_str()); };
            Row(T("Название", "Name"), ii.name); Row(T("Версия игры", "Game version"), ii.ver); Row(T("Загрузчик", "Loader"), ii.loader);
            Row(T("Скачано", "Downloaded"), FmtDate(dir));
            std::string sz = "..."; { std::lock_guard<std::mutex> l(gSzMu); auto f = gSizes.find(iSel); if (f != gSizes.end()) sz = FmtSize(f->second); }
            Row(T("Размер", "Size"), sz);
            Row(T("Папка", "Folder"), PS(dir));
            ImGui::Dummy(ImVec2(0, em * .5f));
            if (ImGui::Button(T("Закрыть", "Close"), ImVec2(em * 8, 0))) ImGui::CloseCurrentPopup();
            ImGui::EndPopup();
        }
        Center();
        ImGui::SetNextWindowSize(ImVec2(std::min(em * 54, io.DisplaySize.x - em * 2), std::min(em * 36, io.DisplaySize.y - em * 2)));
        std::string t2 = std::string(T("Изменить экземпляр", "Edit instance")) + "###iset";
        if (ImGui::BeginPopupModal(t2.c_str(), nullptr, ImGuiWindowFlags_NoResize)) {
            bool cl = false; InstEditorBody(cl);
            if (cl) ImGui::CloseCurrentPopup();
            ImGui::EndPopup();
        }
    }
    ImGui::EndChild();
}
static void DrawCover(ImDrawList* dl, const Tex& t, float alpha, ImVec2 sz) {
    if (!t.v || alpha <= 0.f) return;
    float ar = (float)t.w / t.h, sr = sz.x / sz.y; ImVec2 a(0, 0), b(1, 1);
    if (ar > sr) { float k = sr / ar; a.x = (1 - k) / 2; b.x = 1 - a.x; } else { float k = ar / sr; a.y = (1 - k) / 2; b.y = 1 - a.y; }
    float z = 0.02f + 0.02f * (0.5f + 0.5f * sinf(gTime * 0.15f)); // медленный "Ken Burns"-зум
    float cx = (a.x + b.x) / 2, cy = (a.y + b.y) / 2, hw = (b.x - a.x) / 2 * (1 - z), hh = (b.y - a.y) / 2 * (1 - z);
    dl->AddImage((ImTextureID)(intptr_t)t.v, ImVec2(0, 0), sz, ImVec2(cx - hw, cy - hh), ImVec2(cx + hw, cy + hh), IM_COL32(255, 255, 255, (int)(alpha * 255)));
}
static void DrawUI(float W, float H) {
    // фон
    ImDrawList* bg = ImGui::GetBackgroundDrawList(); ImVec2 sz(W, H);
    if (!gBg[0].v) {
        float t = gTime * 0.2f;
        auto C = [&](float o) { return IM_COL32((int)(30 + 25 * sinf(t + o)), (int)(55 + 30 * sinf(t + o + 2)), (int)(90 + 40 * sinf(t + o + 4)), 255); };
        bg->AddRectFilledMultiColor(ImVec2(0, 0), sz, C(0), C(1.5f), C(3.f), C(4.5f));
    } else { if (gBg[1].v && gFade < 1.f) DrawCover(bg, gBg[1], 1.f, sz); DrawCover(bg, gBg[0], gFade, sz); }
    if (cfg.light) bg->AddRectFilledMultiColor(ImVec2(0, 0), sz, IM_COL32(255, 255, 255, 110), IM_COL32(255, 255, 255, 30), IM_COL32(255, 255, 255, 30), IM_COL32(255, 255, 255, 110));
    else bg->AddRectFilledMultiColor(ImVec2(0, 0), sz, IM_COL32(0, 0, 0, 120), IM_COL32(0, 0, 0, 20), IM_COL32(0, 0, 0, 20), IM_COL32(0, 0, 0, 120));

    ImGui::SetNextWindowPos(ImVec2(0, 0)); ImGui::SetNextWindowSize(sz);
    ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0, 0)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 0);
    ImGui::Begin("root", nullptr, ImGuiWindowFlags_NoDecoration | ImGuiWindowFlags_NoBackground | ImGuiWindowFlags_NoMove | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoBringToFrontOnFocus);
    ImGui::PopStyleVar(2);
    float em = ImGui::GetFontSize(), intro = AnimK("intro", 1.f, 2.5f);
    ImDrawList* dl = ImGui::GetWindowDrawList();
    float tbH = em * 0.9f; gCapH = tbH; // верхняя полоса: за неё окно можно таскать
    float pw = W - em * 2.4f, px = em * 1.2f - (1 - intro) * em * 3, py = tbH, ph = H - tbH - em * 1.2f;
    dl->AddRectFilled(ImVec2(px, py), ImVec2(px + pw, py + ph), cfg.light ? IM_COL32(246, 248, 252, (int)(228 * intro)) : IM_COL32(14, 17, 26, (int)(190 * intro)), R(em * .9f));
    dl->AddRect(ImVec2(px, py), ImVec2(px + pw, py + ph), cfg.light ? IM_COL32(0, 0, 0, (int)(40 * intro)) : IM_COL32(255, 255, 255, (int)(30 * intro)), R(em * .9f));
    ImGui::SetCursorPos(ImVec2(px + em, py + em));
    ImGui::PushStyleVar(ImGuiStyleVar_Alpha, intro);
    ImGui::BeginChild("panel", ImVec2(pw - em * 2, ph - em * 2), false, ImGuiWindowFlags_NoBackground);
    gScrFade = std::min(1.f, gScrFade + ImGui::GetIO().DeltaTime * 7.f);
    ImGui::SetCursorPosY(ImGui::GetCursorPosY() + (1 - gScrFade) * em * .8f);
    ImGui::PushStyleVar(ImGuiStyleVar_Alpha, intro * gScrFade);
    ImGui::BeginChild("content", ImVec2(0, 0), false, ImGuiWindowFlags_NoBackground);
    switch (gScr) { case S_ACC: ScrAccounts(); break; case S_MODS: ScrMods(); break; case S_SET: ScrSettings(); break; case S_LOG: ScrLog(); break; default: ScrMain(); }
    ImGui::EndChild();
    ImGui::PopStyleVar();
    ImGui::EndChild();
    ImGui::PopStyleVar();

    // окно с объяснением краша
    static std::string cT, cB;
    std::string popId = std::string(T("Что-то пошло не так", "Something went wrong")) + "###crash";
    { std::lock_guard<std::mutex> l(gMu); if (gShowCrash) { gShowCrash = false; cT = gCrashTitle; cB = gCrashBody; ImGui::OpenPopup("###crash"); } }
    ImGui::SetNextWindowPos(ImVec2(W / 2, H / 2), ImGuiCond_Always, ImVec2(.5f, .5f));
    ImGui::SetNextWindowSize(ImVec2(std::min(em * 30, W - em * 2), 0));
    if (ImGui::BeginPopupModal(popId.c_str(), nullptr, ImGuiWindowFlags_NoResize)) {
        ImGui::PushFont(gFSub); ImGui::TextColored(ImVec4(1.f, .45f, .4f, 1.f), "%s", cT.c_str()); ImGui::PopFont();
        ImGui::Separator(); ImGui::TextWrapped("%s", cB.c_str()); ImGui::Dummy(ImVec2(0, em * .5f));
        if (cfg.logsOn) { if (ImGui::Button(T("Показать лог", "Show log"), ImVec2(em * 8, 0))) { Go(S_LOG); ImGui::CloseCurrentPopup(); } ImGui::SameLine(); }
        if (ImGui::Button(T("Закрыть", "Close"), ImVec2(em * 8, 0))) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }

    // подтверждение удаления экземпляра (из списка версий)
    static DelReq dr;
    if (gDelAsk) { dr = *gDelAsk; gDelAsk.reset(); ImGui::OpenPopup("###delinst"); }
    ImGui::SetNextWindowPos(ImVec2(W / 2, H / 2), ImGuiCond_Always, ImVec2(.5f, .5f));
    ImGui::SetNextWindowSize(ImVec2(std::min(em * 30, W - em * 2), 0));
    std::string delId = std::string(T("Удалить экземпляр?", "Delete instance?")) + "###delinst";
    if (ImGui::BeginPopupModal(delId.c_str(), nullptr, ImGuiWindowFlags_NoResize)) {
        ImGui::PushFont(gFSub); ImGui::TextColored(ImVec4(1.f, .45f, .4f, 1.f), "%s  %s", dr.loader.c_str(), dr.ver.c_str()); ImGui::PopFont();
        ImGui::Separator();
        ImGui::TextWrapped("%s", T("Папка этого экземпляра будет удалена безвозвратно вместе с мирами, модами, настройками и скриншотами. Общие файлы игры (библиотеки и ресурсы) останутся.",
                                   "This instance folder will be deleted permanently, including worlds, mods, settings and screenshots. Shared game files (libraries and assets) stay."));
        ImGui::Dummy(ImVec2(0, em * .5f));
        ImGui::PushStyleColor(ImGuiCol_Button, ImVec4(.85f, .25f, .25f, .75f)); ImGui::PushStyleColor(ImGuiCol_ButtonHovered, ImVec4(.90f, .30f, .30f, .90f)); ImGui::PushStyleColor(ImGuiCol_ButtonActive, ImVec4(.95f, .35f, .35f, 1.f));
        bool yes = ImGui::Button(T("Удалить", "Delete"), ImVec2(em * 8, 0));
        ImGui::PopStyleColor(3); ImGui::SameLine();
        bool no = ImGui::Button(T("Отмена", "Cancel"), ImVec2(em * 8, 0));
        if (yes && !gBusy && !gGameRunning && !gDelBusy) std::thread(DeleteThread, dr.loader, dr.ver).detach();
        if (yes || no) ImGui::CloseCurrentPopup();
        ImGui::EndPopup();
    }
    ImGui::End();
}

// ============================ Трей (StatusNotifierItem по D-Bus; libdbus подгружается на лету, линковать ничего не нужно) ============================
// Работает в KDE Plasma, XFCE, Cinnamon, MATE, LXQt, Budgie и в GNOME с расширением «AppIndicator and KStatusNotifierItem Support».
// Если трея нет (чистый GNOME без расширения) — лаунчер просто сворачивается, чтобы не потерять окно.
struct DBusConnection; struct DBusMessage;
struct DbErr { const char* name; const char* message; unsigned int bits; void* pad; };
struct alignas(8) DbIter { char b[128]; };
struct DbVTable { void (*unreg)(DBusConnection*, void*); int (*msg)(DBusConnection*, DBusMessage*, void*); void* pad[4]; };
static DBusConnection* gDbus = nullptr; static bool gDbusTried = false, gTrayOn = false; static std::string gTrayName;
static DBusConnection* (*p_bus_get)(int, DbErr*);
static void (*p_err_init)(DbErr*); static int (*p_err_is_set)(const DbErr*); static void (*p_err_free)(DbErr*);
static void (*p_exit_on_disc)(DBusConnection*, int);
static int (*p_req_name)(DBusConnection*, const char*, unsigned int, DbErr*);
static int (*p_rel_name)(DBusConnection*, const char*, DbErr*);
static int (*p_has_owner)(DBusConnection*, const char*, DbErr*);
static DBusMessage* (*p_new_call)(const char*, const char*, const char*, const char*);
static int (*p_append_args)(DBusMessage*, int, ...);
static DBusMessage* (*p_send_block)(DBusConnection*, DBusMessage*, int, DbErr*);
static void (*p_msg_unref)(DBusMessage*);
static int (*p_register_path)(DBusConnection*, const char*, const DbVTable*, void*);
static int (*p_rw_dispatch)(DBusConnection*, int);
static DBusMessage* (*p_new_return)(DBusMessage*);
static int (*p_send)(DBusConnection*, DBusMessage*, unsigned int*);
static void (*p_iter_init_append)(DBusMessage*, DbIter*);
static int (*p_iter_append_basic)(DbIter*, int, const void*);
static int (*p_iter_open)(DbIter*, int, const char*, DbIter*);
static int (*p_iter_close)(DbIter*, DbIter*);
static int (*p_iter_fixed_array)(DbIter*, int, const void*, int);
static int (*p_iter_init)(DBusMessage*, DbIter*);
static void (*p_iter_get_basic)(DbIter*, void*);
static int (*p_iter_next)(DbIter*);
static const char* (*p_get_member)(DBusMessage*);
static const char* (*p_get_iface)(DBusMessage*);
static const int kTrayPx = 24;
static std::vector<unsigned char> gTrayIcon; // ARGB32, как требует StatusNotifierItem
static void TrayBuildIcon() {
    gTrayIcon.assign((size_t)kTrayPx * kTrayPx * 4, 0);
    unsigned char r = (unsigned char)(gAccent.x * 255), g = (unsigned char)(gAccent.y * 255), b = (unsigned char)(gAccent.z * 255);
    for (int y = 0; y < kTrayPx; y++) for (int x = 0; x < kTrayPx; x++) {
        float dx = x + .5f - kTrayPx / 2.f, dy = y + .5f - kTrayPx / 2.f, d = sqrtf(dx * dx + dy * dy);
        float a = std::clamp(kTrayPx / 2.f - 0.5f - d, 0.f, 1.f), w = std::clamp(5.5f - sqrtf(dx * dx + (dy + 1.f) * (dy + 1.f)), 0.f, 1.f); // диск цвета лаунчера + белое «привидение-точка»
        unsigned char* q = &gTrayIcon[((size_t)y * kTrayPx + x) * 4];
        q[0] = (unsigned char)(a * 255); q[1] = (unsigned char)(r + (255 - r) * w); q[2] = (unsigned char)(g + (255 - g) * w); q[3] = (unsigned char)(b + (255 - b) * w);
    }
}
static void TrayVarStr(DbIter* par, const char* v) { DbIter var; p_iter_open(par, 'v', "s", &var); p_iter_append_basic(&var, 's', &v); p_iter_close(par, &var); }
static bool TrayProp(DbIter* par, const std::string& n) { // значение свойства org.kde.StatusNotifierItem внутри variant
    if (n == "Category") TrayVarStr(par, "ApplicationStatus");
    else if (n == "Id" || n == "Title") TrayVarStr(par, "PoltergeistLauncher");
    else if (n == "Status") TrayVarStr(par, "Active");
    else if (n == "IconName" || n == "OverlayIconName" || n == "AttentionIconName" || n == "IconThemePath") TrayVarStr(par, "");
    else if (n == "WindowId") { DbIter var; int z = 0; p_iter_open(par, 'v', "i", &var); p_iter_append_basic(&var, 'i', &z); p_iter_close(par, &var); }
    else if (n == "ItemIsMenu") { DbIter var; unsigned int f = 0; p_iter_open(par, 'v', "b", &var); p_iter_append_basic(&var, 'b', &f); p_iter_close(par, &var); }
    else if (n == "IconPixmap") {
        DbIter var, arr, st, ba; int w = kTrayPx, h = kTrayPx; const unsigned char* px = gTrayIcon.data();
        p_iter_open(par, 'v', "a(iiay)", &var); p_iter_open(&var, 'a', "(iiay)", &arr); p_iter_open(&arr, 'r', nullptr, &st);
        p_iter_append_basic(&st, 'i', &w); p_iter_append_basic(&st, 'i', &h);
        p_iter_open(&st, 'a', "y", &ba); p_iter_fixed_array(&ba, 'y', &px, (int)gTrayIcon.size()); p_iter_close(&st, &ba);
        p_iter_close(&arr, &st); p_iter_close(&var, &arr); p_iter_close(par, &var);
    } else return false;
    return true;
}
static int TrayHandler(DBusConnection* c, DBusMessage* m, void*) { // 0 = обработано, 1 = не наше
    const char* ci = p_get_iface(m); const char* cm = p_get_member(m); if (!ci || !cm) return 1;
    std::string I = ci, M = cm;
    static const char* kProps[] = {"Category", "Id", "Title", "Status", "WindowId", "IconName", "IconPixmap", "OverlayIconName", "AttentionIconName", "ItemIsMenu"};
    if (I == "org.kde.StatusNotifierItem") {
        if (M == "Activate" || M == "SecondaryActivate" || M == "ContextMenu") gWinCmd = 2; // клик по значку — вернуть окно
        DBusMessage* r = p_new_return(m); if (r) { p_send(c, r, nullptr); p_msg_unref(r); }
        return 0;
    }
    if (I == "org.freedesktop.DBus.Properties") {
        DBusMessage* r = p_new_return(m); if (!r) return 0;
        DbIter out; p_iter_init_append(r, &out);
        if (M == "GetAll") {
            DbIter dict, ent; p_iter_open(&out, 'a', "{sv}", &dict);
            for (const char* k : kProps) { p_iter_open(&dict, 'e', nullptr, &ent); p_iter_append_basic(&ent, 's', &k); TrayProp(&ent, k); p_iter_close(&dict, &ent); }
            p_iter_close(&out, &dict);
        } else if (M == "Get") {
            DbIter in; const char* a = nullptr; const char* b = nullptr;
            if (p_iter_init(m, &in)) { p_iter_get_basic(&in, &a); if (p_iter_next(&in)) p_iter_get_basic(&in, &b); }
            if (!b || !TrayProp(&out, b)) TrayVarStr(&out, "");
        }
        p_send(c, r, nullptr); p_msg_unref(r);
        return 0;
    }
    return 1;
}
static bool TrayInit() {
    if (gDbus) return true; if (gDbusTried) return false; gDbusTried = true;
    void* lib = dlopen("libdbus-1.so.3", RTLD_LAZY | RTLD_LOCAL); if (!lib) lib = dlopen("libdbus-1.so", RTLD_LAZY | RTLD_LOCAL); if (!lib) return false;
    bool ok = true;
    auto ld = [&](auto& fp, const char* n) { fp = reinterpret_cast<std::remove_reference_t<decltype(fp)>>(dlsym(lib, n)); if (!fp) ok = false; };
    ld(p_bus_get, "dbus_bus_get"); ld(p_err_init, "dbus_error_init"); ld(p_err_is_set, "dbus_error_is_set"); ld(p_err_free, "dbus_error_free");
    ld(p_exit_on_disc, "dbus_connection_set_exit_on_disconnect"); ld(p_req_name, "dbus_bus_request_name"); ld(p_rel_name, "dbus_bus_release_name"); ld(p_has_owner, "dbus_bus_name_has_owner");
    ld(p_new_call, "dbus_message_new_method_call"); ld(p_append_args, "dbus_message_append_args"); ld(p_send_block, "dbus_connection_send_with_reply_and_block"); ld(p_msg_unref, "dbus_message_unref");
    ld(p_register_path, "dbus_connection_register_object_path"); ld(p_rw_dispatch, "dbus_connection_read_write_dispatch"); ld(p_new_return, "dbus_message_new_method_return"); ld(p_send, "dbus_connection_send");
    ld(p_iter_init_append, "dbus_message_iter_init_append"); ld(p_iter_append_basic, "dbus_message_iter_append_basic"); ld(p_iter_open, "dbus_message_iter_open_container"); ld(p_iter_close, "dbus_message_iter_close_container");
    ld(p_iter_fixed_array, "dbus_message_iter_append_fixed_array"); ld(p_iter_init, "dbus_message_iter_init"); ld(p_iter_get_basic, "dbus_message_iter_get_basic"); ld(p_iter_next, "dbus_message_iter_next");
    ld(p_get_member, "dbus_message_get_member"); ld(p_get_iface, "dbus_message_get_interface");
    if (!ok) return false;
    DbErr e; p_err_init(&e);
    DBusConnection* c = p_bus_get(0, &e); // 0 = сессионная шина
    if (p_err_is_set(&e)) { p_err_free(&e); return false; }
    if (!c) return false;
    p_exit_on_disc(c, 0);
    static const DbVTable vt = {nullptr, TrayHandler, {nullptr, nullptr, nullptr, nullptr}};
    if (!p_register_path(c, "/StatusNotifierItem", &vt, nullptr)) return false;
    TrayBuildIcon(); gDbus = c; return true;
}
static bool TrayAdd() { // повесить значок в трей; false — трея нет
    if (gTrayOn) return true;
    if (!TrayInit()) return false;
    DbErr e; p_err_init(&e);
    int has = p_has_owner(gDbus, "org.kde.StatusNotifierWatcher", &e); if (p_err_is_set(&e)) p_err_free(&e);
    if (!has) return false;
    gTrayName = "org.kde.StatusNotifierItem-" + std::to_string((long)getpid()) + "-1";
    p_req_name(gDbus, gTrayName.c_str(), 4 /* DO_NOT_QUEUE */, &e); if (p_err_is_set(&e)) { p_err_free(&e); return false; }
    DBusMessage* m = p_new_call("org.kde.StatusNotifierWatcher", "/StatusNotifierWatcher", "org.kde.StatusNotifierWatcher", "RegisterStatusNotifierItem");
    if (!m) return false;
    const char* nm = gTrayName.c_str(); p_append_args(m, 's', &nm, 0);
    DBusMessage* rep = p_send_block(gDbus, m, 2000, &e); p_msg_unref(m);
    if (p_err_is_set(&e)) { p_err_free(&e); p_rel_name(gDbus, gTrayName.c_str(), &e); if (p_err_is_set(&e)) p_err_free(&e); return false; }
    if (rep) p_msg_unref(rep);
    gTrayOn = true; return true;
}
static void TrayDel() { // убрать значок: освобождаем имя на шине — хост трея сам удалит иконку
    if (!gTrayOn) return; DbErr e; p_err_init(&e);
    p_rel_name(gDbus, gTrayName.c_str(), &e); if (p_err_is_set(&e)) p_err_free(&e);
    gTrayOn = false;
}
static void TrayPump() { if (gTrayOn && gDbus) p_rw_dispatch(gDbus, 0); }
static void HideToTray() { if (TrayAdd()) glfwHideWindow(gWin); else glfwIconifyWindow(gWin); } // нет трея — не прячем, а сворачиваем

// ============================ GLFW / OpenGL3 (Linux) ============================
static void GlfwErr(int c, const char* d) { fprintf(stderr, "GLFW error %d: %s\n", c, d); }
static std::string ExeDir() { std::error_code ec; fs::path p = fs::read_symlink("/proc/self/exe", ec); return ec ? std::string() : PS(p.parent_path()); }
static std::string FindFont() { // кириллический TTF: рядом с программой, затем типичные места дистрибутивов, затем fontconfig
    std::string dir = ExeDir(); std::error_code ec;
    std::vector<std::string> cand;
    if (!dir.empty()) cand.push_back(dir + "/font.ttf");
    for (const char* f : {
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/usr/share/fonts/TTF/DejaVuSans.ttf", "/usr/share/fonts/dejavu/DejaVuSans.ttf", "/usr/share/fonts/dejavu-sans-fonts/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf", "/usr/share/fonts/liberation/LiberationSans-Regular.ttf", "/usr/share/fonts/liberation-sans/LiberationSans-Regular.ttf", "/usr/share/fonts/TTF/LiberationSans-Regular.ttf",
        "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf", "/usr/share/fonts/noto/NotoSans-Regular.ttf", "/usr/share/fonts/google-noto/NotoSans-Regular.ttf", "/usr/share/fonts/opentype/noto/NotoSans-Regular.ttf",
        "/usr/share/fonts/truetype/ubuntu/Ubuntu-R.ttf", "/usr/share/fonts/TTF/Ubuntu-R.ttf", "/usr/share/fonts/adobe-source-sans/SourceSans3-Regular.otf"}) cand.push_back(f);
    for (auto& f : cand) if (fs::exists(f, ec)) return f;
    std::string fc = RunCapture("fc-match -f '%{file}' 'sans-serif:lang=ru' 2>/dev/null"); // .ttc здесь не подойдёт — берём только ttf/otf
    if (!fc.empty() && (fc.size() > 4) && (fc.compare(fc.size() - 4, 4, ".ttf") == 0 || fc.compare(fc.size() - 4, 4, ".otf") == 0) && fs::exists(fc, ec)) return fc;
    return "";
}
int main(int, char**) {
    curl_global_init(CURL_GLOBAL_DEFAULT);
    { std::string xdg = Env("XDG_DATA_HOME"); fs::path dh = xdg.empty() ? fs::path(HomeDir()) / ".local" / "share" : fs::path(xdg); gCfgDir = dh / "mclauncher"; gRoot = gCfgDir; }
    std::error_code ec; fs::create_directories(gCfgDir, ec);

    glfwSetErrorCallback(GlfwErr);
    if (!glfwInit()) { fprintf(stderr, "Не удалось инициализировать GLFW (нет X11/Wayland-сессии?)\n"); return 1; }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3); glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 0);
#ifdef GLFW_X11_CLASS_NAME
    glfwWindowHintString(GLFW_X11_CLASS_NAME, "PoltergeistLauncher"); glfwWindowHintString(GLFW_X11_INSTANCE_NAME, "PoltergeistLauncher");
#endif
#ifdef GLFW_WAYLAND_APP_ID
    glfwWindowHintString(GLFW_WAYLAND_APP_ID, "PoltergeistLauncher");
#endif
    gWin = glfwCreateWindow(1100, 680, "PoltergeistLauncher", nullptr, nullptr);
    if (!gWin) { fprintf(stderr, "Не удалось создать окно OpenGL 3.0\n"); glfwTerminate(); return 1; }
    glfwMakeContextCurrent(gWin); glfwSwapInterval(1); // VSync — не жжём CPU/GPU

    int ww = 0, wh = 0, fw = 0, fh = 0; glfwGetWindowSize(gWin, &ww, &wh); glfwGetFramebufferSize(gWin, &fw, &fh);
    float fbs = ww > 0 ? (float)fw / (float)ww : 1.f; if (fbs < 1.01f) fbs = 1.f; // Wayland/HiDPI: фреймбуфер больше окна
    float xs = 1.f, ys = 1.f; glfwGetWindowContentScale(gWin, &xs, &ys);
    float S = fbs > 1.f ? 1.f : std::clamp(xs, 1.f, 3.f); gS = S; // X11: масштаб по DPI; Wayland: окно в логических пикселях, а шрифт рисуем в фактических
    if (S != 1.f) glfwSetWindowSize(gWin, (int)(1100 * S), (int)(680 * S));
    glfwSetWindowSizeLimits(gWin, (int)(900 * S), (int)(600 * S), GLFW_DONT_CARE, GLFW_DONT_CARE);

    ImGui::CreateContext(); ImGuiIO& io = ImGui::GetIO(); io.IniFilename = nullptr;
    {
        float fsc = S * fbs; io.FontGlobalScale = 1.f / fbs;
        std::string fp = FindFont(); const ImWchar* rng = io.Fonts->GetGlyphRangesCyrillic();
        if (fp.empty() || !io.Fonts->AddFontFromFileTTF(fp.c_str(), 18.f * fsc, nullptr, rng)) { io.Fonts->AddFontDefault(); fprintf(stderr, "Шрифт с кириллицей не найден: положи font.ttf рядом с программой\n"); }
        else { // крупные шрифты настоящего размера (а не растянутый мелкий): текст остаётся чётким
            gFTitle = io.Fonts->AddFontFromFileTTF(fp.c_str(), 27.f * fsc, nullptr, rng);
            gFSub = io.Fonts->AddFontFromFileTTF(fp.c_str(), 23.4f * fsc, nullptr, rng);
        }
    }
    ImGui_ImplGlfw_InitForOpenGL(gWin, true); ImGui_ImplOpenGL3_Init("#version 130");

    LoadConfig(); snprintf(bJava, sizeof(bJava), "%s", cfg.javaPath.c_str()); snprintf(bJvm, sizeof(bJvm), "%s", cfg.jvmArgs.c_str()); gLogOn = cfg.logsOn;
    if (!cfg.gameDir.empty()) { // своя папка игры из настроек
        std::error_code e2; fs::create_directories(P(cfg.gameDir), e2);
        if (!e2 && fs::is_directory(P(cfg.gameDir), e2)) gRoot = P(cfg.gameDir); else cfg.gameDir.clear();
    }
    MigrateInstances();
    std::thread(FetchVersions).detach();
    std::thread(FetchLoaderLists).detach();
    ScanShots();
    if (!cfg.bg.empty() && !cfg.slideshow) LoadBgAsync(cfg.bg); else NextShot();

    bool done = false; auto last = std::chrono::steady_clock::now();
    while (!done) {
        glfwPollEvents(); TrayPump();
        switch (gWinCmd.exchange(0)) { // команды из потока запуска игры и от значка в трее
            case 1: HideToTray(); break;
            case 2: TrayDel(); glfwShowWindow(gWin); glfwRestoreWindow(gWin); glfwFocusWindow(gWin); break;
            case 3: glfwSetWindowShouldClose(gWin, GLFW_TRUE); break;
        }
        if (glfwWindowShouldClose(gWin)) break;
        if (glfwGetWindowAttrib(gWin, GLFW_ICONIFIED) || !glfwGetWindowAttrib(gWin, GLFW_VISIBLE)) { Sleep(60); continue; }
        auto now = std::chrono::steady_clock::now(); float dt = std::chrono::duration<float>(now - last).count(); last = now; gTime += dt;

        { std::lock_guard<std::mutex> l(gMu); if (gNewAcc) {
            bool rep = false; for (auto& a : cfg.accs) if (a.type == gNewAcc->type && a.uuid == gNewAcc->uuid) { a = *gNewAcc; rep = true; }
            if (!rep) { cfg.accs.push_back(*gNewAcc); cfg.sel = (int)cfg.accs.size() - 1; }
            gNewAcc.reset(); SaveConfig(); } }
        { std::lock_guard<std::mutex> l(gVerMu); if (cfg.version.empty() && !gLatest.empty()) cfg.version = gLatest; }
        UpdateBackground(dt);

        { int sg = (cfg.light ? 1 : 0) | (std::clamp(cfg.color, 0, 4) << 1) | (cfg.rounded ? 16 : 0); if (sg != gThemeSig) { gThemeSig = sg; ApplyTheme(); } }
        ImGui_ImplOpenGL3_NewFrame(); ImGui_ImplGlfw_NewFrame(); ImGui::NewFrame();
        int cw = 0, ch = 0, bw = 0, bh = 0; glfwGetWindowSize(gWin, &cw, &ch); glfwGetFramebufferSize(gWin, &bw, &bh);
        DrawUI((float)cw, (float)ch);
        ImGui::Render();
        glViewport(0, 0, bw, bh); glClearColor(0.05f, 0.06f, 0.09f, 1.f); glClear(GL_COLOR_BUFFER_BIT);
        ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());
        glfwSwapBuffers(gWin);
    }
    SaveConfig();
    ImGui_ImplOpenGL3_Shutdown(); ImGui_ImplGlfw_Shutdown(); ImGui::DestroyContext();
    glfwDestroyWindow(gWin); glfwTerminate();
    fflush(nullptr); _exit(0); // фоновые потоки (curl) не ждём
}
