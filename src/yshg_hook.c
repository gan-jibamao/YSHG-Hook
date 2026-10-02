/* ============================================================================
 * yshg_hook — 阅姝阁 (com.box.dxgxx44) 增强插件
 *             视频抓取下载 / 内置播放器 / 记录面板
 *
 *   Author   : 鸡巴毛 (jibamao)
 *   Repo     : https://github.com/gan-jibamao/YSHG-Hook
 *   Version  : v4.14.6 （源码性能优化）
 *
 * 实现原理（自研，不依赖 Substrate/Frida）：
 *   · fishhook 式重绑 —— 遍历全部已加载镜像（Runner / App.framework Dart AOT /
 *     Flutter.framework VM）的 __la_symbol_ptr 与 __got，重绑 libc socket 系调用，
 *     从 connect() 起跟踪每个 fd，落盘明文流量日志；
 *   · ObjC 方法替换 —— AVPlayer/AVPlayerItem 播放链路、视图层级与手势微调
 *     （自绘控制层 / 记录面板 / 悬浮钮）；
 *   · 自研 HLS 下载器 —— m3u8 解析、AES-128 解密（EXT-X-KEY）、多任务多路并发
 *     分段下载、断点续传、TS→MP4 纯 C 重封装（内置 H.264 SPS/PPS 解析器）；
 *   · 常量段保护 —— 构建期把 __cstring/__const 搬入可写 __DATA 并加密，
 *     构造函数最前 deobf() 原地解密（密钥每次构建随机）。
 *
 * 日志：<app 容器>/Documents/yshg_net.log（超 8 MB 轮转，尽力 /var/mobile/Documents/）
 * 构建：clang -arch arm64 -target arm64-apple-ios12.0.0 -fblocks -O2 -fPIC
 *       -fno-objc-arc -c  →  ld64.lld -dylib（-rename_section __TEXT __cstring
 *       __DATA __cstr -rename_section __TEXT __const __DATA __tconst）
 *       →  ldid -S  →  llvm-strip -x  →  常量段加密
 * ========================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <dlfcn.h>
#include <unistd.h>
#include <fcntl.h>
#include <time.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netdb.h>

#include <stdarg.h>
// 栈保护哨兵: 8 字节值拷贝, 绝不能声明成指针
extern unsigned long __stack_chk_guard;
#include <strings.h>
#include <signal.h>
#include <sys/stat.h>
#include <unistd.h>

// ---------------- hand-written Mach-O 64 ----------------
typedef struct { uint32_t magic, cputype, cpusubtype, filetype, ncmds, sizeofcmds, flags, reserved; } mach_hdr64;
typedef struct { uint32_t cmd, cmdsize; char segname[16]; uint64_t vmaddr, vmsize, fileoff, filesize; uint32_t maxprot, initprot, nsects, flags; } seg_cmd64;
typedef struct { char sectname[16], segname[16]; uint64_t addr, size; uint32_t offset, align, reloff, nreloc, flags, reserved1, reserved2, reserved3; } sect_hdr64;
typedef struct { uint32_t cmd, cmdsize, symoff, nsyms, stroff, strsize; } symtab_cmd;
typedef struct { uint32_t cmd, cmdsize; uint32_t ilocalsym, nlocalsym, iextdefsym, nextdefsym, iundefsym, nundefsym;
                 uint32_t tocoff, ntoc, modtaboff, nmodtab, extrefsymoff, nextrefsyms;
                 uint32_t indirectsymoff, nindirectsyms, extreloff, nextrel, locreloff, nlocrel; } dysymtab_cmd;
typedef struct { uint32_t n_strx; uint8_t n_type, n_sect; uint16_t n_desc; uint64_t n_value; } nlist64;

#define LC_SEGMENT_64   0x19
#define LC_SYMTAB       0x2
#define LC_DYSYMTAB     0xb
#define IND_LOCAL       0x80000000u
#define IND_ABS         0x40000000u

typedef void *(*dlsym_fn)(void *, const char *);
// 直接用 extern 让 dyld 绑定 (本环境下 dlsym 对 objc/dispatch/CCCrypt 返回 0)
extern void *objc_msgSend(void);
extern void *objc_getClass(const char *);
extern void *sel_registerName(const char *);
extern void *objc_allocateClassPair(void *, const char *, size_t);
extern void *objc_retain(void *);
extern void *objc_autoreleasePoolPush(void);
extern void objc_autoreleasePoolPop(void *);
extern void *object_getClass(void *);
extern void *class_replaceMethod(void *, void *, void *, const char *);
extern signed char class_addMethod(void *, void *, void *, const char *);
extern void objc_registerClassPair(void *);
extern void *dispatch_semaphore_create(long);
extern long dispatch_semaphore_signal(void *);
extern long dispatch_semaphore_wait(void *, unsigned long long);
extern unsigned long long dispatch_time(unsigned long long, long long);
extern int getifaddrs(void **);
extern int CCCrypt(unsigned int, unsigned int, unsigned int, const void *, size_t, const void *,
                   const void *, size_t, void *, size_t, size_t *);
extern int _dyld_image_count(void);
extern const struct mach_header *_dyld_get_image_header(unsigned int);
extern const char *_dyld_get_image_name(unsigned int);
extern long _dyld_get_image_vmaddr_slide(unsigned int);
static int  (*dyld_img_count)(void);
static const struct mach_header *(*dyld_img_hdr)(uint32_t);
static const char *(*dyld_img_name)(uint32_t);
static intptr_t (*dyld_img_slide)(uint32_t);

// ---------------- logging ----------------
static pthread_mutex_t g_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t g_smu = PTHREAD_MUTEX_INITIALIZER;   /* seen_add 去重表 */
/* ★ v4.14.4 崩溃黑匣子: 直写 fd(绕开锁) + 每个下载线程的当前任务 */
static volatile int g_crashfd = -1;
static _Thread_local char g_tls_job[300];
static void *g_self_base;
static FILE *g_log = NULL, *g_log2 = NULL;

static void now_str(char *buf, size_t n) {
    struct timespec ts; clock_gettime(CLOCK_REALTIME, &ts);
    struct tm tm; time_t sec = ts.tv_sec + 8 * 3600;   /* ★ 北京时间 (UTC+8, 不随设备时区) */
    gmtime_r(&sec, &tm);
    snprintf(buf, n, "%02d:%02d:%02d.%03ld", tm.tm_hour, tm.tm_min, tm.tm_sec, ts.tv_nsec / 1000000);
}

static void log_open_locked(void) {
    if (g_log) return;
    const char *home = getenv("HOME");
    char p1[512];
    if (home && *home) {
        snprintf(p1, sizeof(p1), "%s/Documents/yshg_net.log", home);
        struct stat stt;
        if (!stat(p1, &stt) && stt.st_size > 8 * 1024 * 1024) {   // 超 8MB 轮转
            char old[540]; snprintf(old, sizeof(old), "%s.old", p1);
            remove(old); rename(p1, old);
        }
        g_log = fopen(p1, "a");
        if (!g_log) { snprintf(p1, sizeof(p1), "%s/Library/Caches/yshg_net.log", home); g_log = fopen(p1, "a"); }
        if (!g_log) { snprintf(p1, sizeof(p1), "%s/yshg_net.log", home); g_log = fopen(p1, "a"); }
    }
    if (!g_log) g_log = fopen("/var/mobile/Documents/yshg_net.log", "a");
    if (!g_log) g_log = fopen("/var/tmp/yshg_net.log", "a");
    if (!g_log) g_log = fopen("/tmp/yshg_net.log", "a");
    g_log2 = fopen("/var/mobile/Documents/yshg_net.log", "a"); // unsandboxed only
    if (g_log && g_crashfd < 0) g_crashfd = fileno(g_log);
}

static int g_flood_n; static time_t g_flood_t; static int g_flood_drop;
static void log_line(const char *fmt, ...) {
    pthread_mutex_lock(&g_mu);
    log_open_locked();
    time_t fnow = time(NULL);
    if (fnow != g_flood_t) {
        if (g_flood_drop && g_log) fprintf(g_log, "[%ld] …洪泛 %d 行已抑制\n", (long)fnow, g_flood_drop);
        g_flood_t = fnow; g_flood_n = 0; g_flood_drop = 0;
    }
    if (++g_flood_n > 300) { g_flood_drop++; pthread_mutex_unlock(&g_mu); return; }   // ★ 每秒 300 行封顶
    char ts[32]; now_str(ts, sizeof(ts));
    if (g_log || g_log2) {
        char msg[2200];
        va_list ap; va_start(ap, fmt);
        vsnprintf(msg, sizeof(msg), fmt, ap);
        va_end(ap);
        if (g_log)  { fprintf(g_log,  "[%s] %s\n", ts, msg); }
        if (g_log2) { fprintf(g_log2, "[%s] %s\n", ts, msg); }
        /* ★ v4.14.6: fflush 改为每 8 行一次 —— my_read/my_write 每次系统调用都过这里,
           高并发下载时逐行 fflush 在全局锁内变成串行 I/O 热点;
           崩溃兜底由黑匣子直写 fd(g_crashfd) 承担, 不依赖这条路径的实时 flush */
        static unsigned log_flush_n;
        if (++log_flush_n >= 8) {
            log_flush_n = 0;
            if (g_log)  fflush(g_log);
            if (g_log2) fflush(g_log2);
        }
    }
    pthread_mutex_unlock(&g_mu);
}

static void esc_payload(char *dst, size_t dstn, const void *data, size_t len) {
    size_t o = 0;
    const unsigned char *p = (const unsigned char *)data;
    size_t cap = len > 480 ? 480 : len;
    for (size_t i = 0; i < cap && o + 8 < dstn; i++) {
        unsigned char c = p[i];
        if (c >= 0x20 && c < 0x7f) { if (c == '\\' || c == '"') dst[o++] = '\\'; dst[o++] = (char)c; }
        else if (c == '\n') { dst[o++] = '\\'; dst[o++] = 'n'; }
        else if (c == '\r') { dst[o++] = '\\'; dst[o++] = 'r'; }
        else if (c == '\t') { dst[o++] = '\\'; dst[o++] = 't'; }
        else o += (size_t)snprintf(dst + o, dstn - o, "\\x%02x", c);
    }
    dst[o] = 0;
    if (len > cap) log_line("  (truncated %zu -> %zu bytes)", len, cap);
}

// ---------------- fd tracking ----------------
typedef struct { uint8_t used; uint8_t own; uint16_t port; char ip[46]; } fdinfo;
static fdinfo g_fds[4096];

static void fd_mark(int fd, const char *ip, uint16_t port) {
    if (fd < 0 || fd >= 4096) return;
    g_fds[fd].used = 1; g_fds[fd].port = port;
    snprintf(g_fds[fd].ip, sizeof(g_fds[fd].ip), "%s", ip);
}
static fdinfo *fd_get(int fd) { return (fd >= 0 && fd < 4096 && g_fds[fd].used) ? &g_fds[fd] : NULL; }
static void fd_clear(int fd) { if (fd >= 0 && fd < 4096) g_fds[fd].used = 0; }
static int g_hit_total, g_hit_imgs;
static int g_bind_hits[32];
// connect 目的去重(独立表, 不污染 m3u8 去重)
static char *g_cseen[2048];
static int cseen_add(const char *s) {
    uint32_t h = 2166136261u; const char *p = s;
    while (*p) { h ^= (uint8_t)*p++; h *= 16777619u; }
    uint32_t i = h & 2047;
    for (int n = 0; n < 8; n++, i = (i + 1) & 2047) {
        if (!g_cseen[i]) { g_cseen[i] = strdup(s); return 1; }
        if (!strcmp(g_cseen[i], s)) return 0;
    }
    return 0;
}
static void capture_scan(const char *buf, ssize_t n);
static void capture_request(int fd, const char *buf, ssize_t n);
static void dl_init(void);
static void dl_maybe_enqueue(const char *url, const char *reqbuf, size_t n);
static void dl_push_job(const char *url);
static void dl_grab_current(void);
static void dl_av_hook(void);
static int ts2mp4_file(const char *in, const char *out);   /* ★ v4.14.1 内部符号, 不导出 */
static const char *ns2utf8(void *obj);
static void dl_consider_url(const char *u);
static void ui_init(void);
static void ui_build(void);
static void tick_fn(void);
static void *ui_loop(void *);
static void imp_tick_build(void *, void *, void *);
static void *ui_loop(void *);
typedef unsigned char BOOL_;
struct tick_blk {
    void *isa; int flags; int reserved;
    void (*invoke)(struct tick_blk *);
    unsigned long desc[2];
};
static struct tick_blk g_tb, g_tb_store;
static const char *bounded_str(const char *h, size_t n, const char *needle);
static const char *bounded_str_impl(const char *h, size_t n, const char *needle) {
    size_t m = strlen(needle);
    if (n < m) return NULL;
    for (size_t i = 0; i + m <= n; i++)
        if (!memcmp(h + i, needle, m)) return h + i;
    return NULL;
}
#define bounded_str bounded_str_impl
static pthread_t g_worker_tid;

static int port_noisy(uint16_t p) { return p == 443; } // TLS ciphertext = noise

// ---------------- VPN 检测移除 (v0.9) ----------------
// vpn_connection_detector 靠 NetworkInterface.list() -> getifaddrs 枚举
// 接口名, 匹配 _commonVpnInterfaceNamePatterns (utun/tun/tap/ipsec/ppp...)。
// 把命中接口的名字整体抹成 'e', 前缀与子串匹配同时失效。
struct myifa {
    struct myifa *nxt;
    char *nm;
    unsigned int flg;
    void *a1, *a2, *a3, *a4;
};
static int (*o_getifaddrs)(struct myifa **);
static const char *g_vpnpat[] = { "utun", "tun", "tap", "ipsec", "ppp", "wg" };
static int my_getifaddrs(struct myifa **out) {
    int r = o_getifaddrs(out);
    if (r == 0 && out && *out) {
        for (struct myifa *p = *out; p; p = p->nxt) {
            if (!p->nm) continue;
            for (unsigned i = 0; i < sizeof(g_vpnpat) / sizeof(g_vpnpat[0]); i++) {
                size_t pl = strlen(g_vpnpat[i]);
                if (!strncmp(p->nm, g_vpnpat[i], pl)) {
                    size_t L = strlen(p->nm);
                    for (size_t j = 0; j < L; j++) p->nm[j] = 'e';
                    static char seen[16][32]; static unsigned seen_n;
                    int dup = 0;
                    for (unsigned k = 0; k < seen_n; k++) if (!strncmp(seen[k], p->nm, 31)) { dup = 1; break; }
                    if (!dup && seen_n < 16) { snprintf(seen[seen_n++], 32, "%s", p->nm); log_line("VPNHIDE %s -> %s (首次)", g_vpnpat[i], p->nm); }
                    break;
                }
            }
        }
    }
    return r;
}

// ---------------- originals ----------------
static int      (*o_connect)(int, const struct sockaddr *, socklen_t);
static int      (*o_close)(int);
static ssize_t  (*o_read)(int, void *, size_t);
static ssize_t  (*o_write)(int, const void *, size_t);
static ssize_t  (*o_recv)(int, void *, size_t, int);
static ssize_t  (*o_send)(int, const void *, size_t, int);
static int      (*o_getaddrinfo)(const char *, const char *, const struct addrinfo *, struct addrinfo **);

// ---------------- hooks ----------------
static int my_connect(int fd, const struct sockaddr *sa, socklen_t sl) {
    // ★ iOS 是 BSD 布局: sockaddr = { u8 sa_len; u8 sa_family; ... }
    //   Linux 头里 sa_family 是 16 位, 直接读会得到 0x0200/0x1E00 这类怪值。
    //   按字节手工解析, 不依赖结构体布局。
    if (sa && sl >= 8) {
        const unsigned char *p = (const unsigned char *)sa;
        unsigned char fam = p[1];
        if (fam == 2) { // AF_INET
            char ip[24];
            snprintf(ip, sizeof(ip), "%u.%u.%u.%u", p[4], p[5], p[6], p[7]);
            unsigned port = (unsigned)((p[2] << 8) | p[3]);
            fd_mark(fd, ip, (uint16_t)port);
            if (pthread_equal(pthread_self(), g_worker_tid)) g_fds[fd].own = 1;
            char key[64]; snprintf(key, sizeof(key), "%s:%u", ip, port);
            if (cseen_add(key)) log_line("C fd=%d -> %s:%u", fd, ip, port);
            return o_connect(fd, sa, sl);
        }
        if (fam == 30 && sl >= 24) { // AF_INET6
            char ip[80];
            snprintf(ip, sizeof(ip), "%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x",
                     p[8], p[9], p[10], p[11], p[12], p[13], p[14], p[15],
                     p[16], p[17], p[18], p[19], p[20], p[21], p[22], p[23]);
            unsigned port = (unsigned)((p[2] << 8) | p[3]);
            fd_mark(fd, ip, (uint16_t)port);
            if (pthread_equal(pthread_self(), g_worker_tid)) g_fds[fd].own = 1;
            char key[96]; snprintf(key, sizeof(key), "[%s]:%u", ip, port);
            if (cseen_add(key)) log_line("C fd=%d -> [%s]:%u", fd, ip, port);
            return o_connect(fd, sa, sl);
        }
        static int fam_dbg = 0;
        if (fam_dbg < 6) { log_line("CONNECT fam=%u len=%d fd=%d (非 INET)", fam, (int)sl, fd); fam_dbg++; }
    }
    fd_mark(fd, "unix", 0);
    return o_connect(fd, sa, sl);
}
static int my_close(int fd) { fd_clear(fd); return o_close(fd); }

static ssize_t my_read(int fd, void *buf, size_t n) {
    ssize_t r = o_read(fd, buf, n);
    fdinfo *f = fd_get(fd);
    if (f && f->own) return r;
    if (f && r > 0 && !port_noisy(f->port)) {
        char esc[1100]; esc_payload(esc, sizeof(esc), buf, (size_t)r);
        log_line("R fd=%d %s:%u n=%zd \"%s\"", fd, f->ip, f->port, r, esc);
    }
    if (r > 0) capture_scan((const char *)buf, r);
    return r;
}
static ssize_t my_write(int fd, const void *buf, size_t n) {
    fdinfo *f = fd_get(fd);
    if (f && !f->own && n > 16 && bounded_str((const char *)buf, n < 512 ? n : 512, "YSHG/")) f->own = 1;
    if (f && f->own) return o_write(fd, buf, n);
    if (f && n > 0 && !port_noisy(f->port)) {
        char esc[1100]; esc_payload(esc, sizeof(esc), buf, n);
        log_line("W fd=%d %s:%u n=%zu \"%s\"", fd, f->ip, f->port, n, esc);
    }
    if (n > 0) capture_request(fd, (const char *)buf, (ssize_t)n);
    return o_write(fd, buf, n);
}
static ssize_t my_recv(int fd, void *buf, size_t n, int flags) {
    ssize_t r = o_recv(fd, buf, n, flags);
    fdinfo *f = fd_get(fd);
    if (f && f->own) return r;
    if (f && r > 0 && !port_noisy(f->port)) {
        char esc[1100]; esc_payload(esc, sizeof(esc), buf, (size_t)r);
        log_line("R fd=%d %s:%u n=%zd \"%s\"", fd, f->ip, f->port, r, esc);
    }
    if (r > 0) capture_scan((const char *)buf, r);
    return r;
}
static ssize_t my_send(int fd, const void *buf, size_t n, int flags) {
    fdinfo *f = fd_get(fd);
    if (f && f->own) return o_send(fd, buf, n, flags);
    if (f && n > 0 && !port_noisy(f->port)) {
        char esc[1100]; esc_payload(esc, sizeof(esc), buf, n);
        log_line("W fd=%d %s:%u n=%zu \"%s\"", fd, f->ip, f->port, n, esc);
    }
    if (n > 0) capture_request(fd, (const char *)buf, (ssize_t)n);
    return o_send(fd, buf, n, flags);
}
static int my_getaddrinfo(const char *node, const char *svc, const struct addrinfo *hint, struct addrinfo **res) {
    if (node) log_line("DNS %s svc=%s", node, svc ? svc : "-");
    return o_getaddrinfo(node, svc, hint, res);
}

// ---------------- m3u8 capture (v0.2) ----------------
static FILE *g_m3u8 = NULL, *g_m3u82 = NULL;
#define HSLOTS 4096
static char *g_seen[HSLOTS];

static uint32_t fnv1a(const char *s) {
    uint32_t h = 2166136261u;
    while (*s) { h ^= (uint8_t)*s++; h *= 16777619u; }
    return h;
}
static int seen_add(const char *s) {
    pthread_mutex_lock(&g_smu);
    uint32_t i = fnv1a(s) & (HSLOTS - 1);
    int found = 0;
    for (int p = 0; p < 8; p++, i = (i + 1) & (HSLOTS - 1)) {
        if (!g_seen[i]) { g_seen[i] = strdup(s); break; }
        if (!strcmp(g_seen[i], s)) { found = 1; break; }
    }
    /* ★★ 关键修复: 原实现在"命中重复"分支直接 return 0 却没有 unlock ——
       g_smu 此后永久锁死, 所有后续 seen_add 全部阻塞:
         · 自动抓取(capture_request/dl_consider_url 走 seen_add)彻底失效
         · 下载 worker 卡死在 seen_add, 队列里的任务再也没人处理
       这正是"自动抓取不生效"与"抓两个后点抓没反应"的共同根因。 */
    pthread_mutex_unlock(&g_smu);
    return found ? 0 : 1;
}
/* ★ v4.14.2: 只读探测 (不改表) */
static int seen_has(const char *s) {
    pthread_mutex_lock(&g_smu);
    uint32_t i = fnv1a(s) & (HSLOTS - 1);
    int found = 0;
    for (int p = 0; p < 8; p++, i = (i + 1) & (HSLOTS - 1)) {
        if (!g_seen[i]) break;
        if (!strcmp(g_seen[i], s)) { found = 1; break; }
    }
    pthread_mutex_unlock(&g_smu);
    return found;
}

/* ★ v4.14.2: master → 变体 记忆 (4 槽轮转) + 上次处理时刻
   重复进入同一个 master 时, 若它的变体已经在下载/已下载 —— 直接跳过, 连网络都不碰。 */
#define MMC_N 4
static char   g_mmc_key[MMC_N][1300];
static char   g_mmc_val[MMC_N][1300];
static time_t g_mmc_t[MMC_N];
static int    g_mmc_rr;
static void mmc_put(const char *k, const char *v) {
    if (!k || !k[0] || !v || !v[0]) return;
    pthread_mutex_lock(&g_smu);
    int slot = -1;
    for (int i = 0; i < MMC_N; i++) if (g_mmc_key[i][0] && !strcmp(g_mmc_key[i], k)) { slot = i; break; }
    if (slot < 0) { slot = g_mmc_rr; g_mmc_rr = (g_mmc_rr + 1) % MMC_N; }
    snprintf(g_mmc_key[slot], 1300, "%s", k);
    snprintf(g_mmc_val[slot], 1300, "%s", v);
    g_mmc_t[slot] = time(NULL);
    pthread_mutex_unlock(&g_smu);
}
static int mmc_get(const char *k, char *out, size_t on, time_t *when) {
    int hit = 0;
    pthread_mutex_lock(&g_smu);
    for (int i = 0; i < MMC_N; i++)
        if (g_mmc_key[i][0] && !strcmp(g_mmc_key[i], k)) {
            if (out && on) snprintf(out, on, "%s", g_mmc_val[i]);
            if (when) *when = g_mmc_t[i];
            hit = 1; break;
        }
    pthread_mutex_unlock(&g_smu);
    return hit;
}

static void m3u8_line(const char *tag, const char *url) {
    if (!url || !*url || strlen(url) > 1500) return;
    if (!seen_add(url)) return;
    pthread_mutex_lock(&g_mu);
    log_open_locked();
    if (!g_m3u8) {
        const char *home = getenv("HOME");
        char p1[512];
        if (home && *home) { snprintf(p1, sizeof(p1), "%s/Documents/yshg_m3u8.log", home); g_m3u8 = fopen(p1, "a"); }
        g_m3u82 = fopen("/var/mobile/Documents/yshg_m3u8.log", "a");
    }
    if (g_m3u8)  { fprintf(g_m3u8,  "%s %s\n", tag, url); fflush(g_m3u8); }
    if (g_m3u82) { fprintf(g_m3u82, "%s %s\n", tag, url); fflush(g_m3u82); }
    pthread_mutex_unlock(&g_mu);
}
static int hexv(int c) { return c >= '0' && c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }
static size_t url_decode(const char *s, size_t n, char *out, size_t on) {
    size_t o = 0;
    for (size_t i = 0; i < n && o + 2 < on; i++) {
        if (s[i] == '%' && i + 2 < n &&
            ((s[i+1] >= '0' && s[i+1] <= '9') || ((s[i+1]|32) >= 'a' && (s[i+1]|32) <= 'f')) &&
            ((s[i+2] >= '0' && s[i+2] <= '9') || ((s[i+2]|32) >= 'a' && (s[i+2]|32) <= 'f'))) {
            out[o++] = (char)(hexv(s[i+1]) * 16 + hexv(s[i+2])); i += 2;
        } else if (s[i] == '+') out[o++] = ' ';
        else out[o++] = s[i];
    }
    out[o] = 0; return o;
}
// scan payload for m3u8 urls / parse?url= / EXT-X-KEY URIs
static void capture_scan(const char *buf, ssize_t n) {
    if (n < 8) return;
    size_t lim = n > 16384 ? 16384 : (size_t)n;
    char cand[1600], dec[1600];
    for (size_t i = 0; i + 7 < lim; i++) {
        if (!(buf[i]=='h' && buf[i+1]=='t' && buf[i+2]=='t' && buf[i+3]=='p' && (buf[i+4]==':' || (buf[i+4]=='s' && buf[i+5]==':')))) continue;
        size_t j = i;
        while (j < lim && j - i < sizeof(cand) - 1) {
            char c = buf[j];
            if (c <= 0x20 || c == '"' || c == '\'' || c == '\\' || c == '<' || c == '>') break;
            j++;
        }
        size_t cl = j - i;
        if (cl > 7 && cl < sizeof(cand)) {
            memcpy(cand, buf + i, cl); cand[cl] = 0;
            if (strstr(cand, ".m3u8")) m3u8_line("M3U8", cand);
            const char *pp = strstr(cand, "parse?url=");
            if (pp) {
                url_decode(pp + 10, strlen(pp + 10), dec, sizeof(dec));
                if (strstr(dec, ".m3u8")) m3u8_line("PARSE", dec);
            }
            if (strstr(cand, "/key/") || strstr(cand, "key?")) m3u8_line("KEY?", cand);
        }
        i = j;
    }
    // EXT-X-KEY URI inside playlist text
    const char *k = buf;
    while ((k = strstr(k, "URI=\"")) && k < buf + lim) {
        k += 5;
        const char *e = memchr(k, '"', (size_t)(buf + lim - k) > 1500 ? 1500 : (size_t)(buf + lim - k));
        if (e && e > k) {
            size_t kl = (size_t)(e - k);
            memcpy(cand, k, kl); cand[kl] = 0;
            if (strstr(cand, "http")) m3u8_line("KEY", cand);
            else if (kl > 1 && cand[0] == '/') { m3u8_line("KEYREL", cand); } // 相对路径, 需配 host
        }
    }
}
// outbound request line + Host -> full m3u8 url
static void capture_req_url(const char *url) {
    m3u8_line("REQ", url);
    const char *pp = strstr(url, "parse?url=");
    if (pp) {
        char dec[1200];
        url_decode(pp + 10, strlen(pp + 10), dec, sizeof(dec));
        if (strstr(dec, ".m3u8")) m3u8_line("PARSE", dec);
    }
}
static void capture_request(int fd, const char *buf, ssize_t n) {
    if (n < 16 || strncmp(buf, "GET ", 4) != 0) return;
    char path[800] = {0}, host[256] = {0};
    long lim = n < 900 ? n : 900;
    const char *sp = memchr(buf, ' ', (size_t)lim);
    if (!sp || sp == buf + 4) return;
    const char *le = memchr(sp + 1, ' ', (size_t)(buf + n - sp - 1) > 900 ? 900 : (size_t)(buf + n - sp - 1));
    if (!le || (size_t)(le - sp - 1) >= sizeof(path)) return;
    size_t pl = (size_t)(le - sp - 1); if (pl >= sizeof(path)) pl = sizeof(path) - 1;
    memcpy(path, sp + 1, pl); path[pl] = 0;
    char head[1024];
    size_t hl = (size_t)lim; if (hl >= sizeof(head)) hl = sizeof(head) - 1;
    memcpy(head, buf, hl); head[hl] = 0;
    const char *h = strstr(head, "\r\nHost:");
    if (!h) h = strstr(head, "\r\nhost:");
    if (h) { h += 7; while (*h == ' ') h++; size_t i = 0; while (h[i] && h[i] != '\r' && i < sizeof(host) - 1) { host[i] = h[i]; i++; } host[i] = 0; }
    if (!strstr(path, ".m3u8")) return;
    fdinfo *f = fd_get(fd);
    const char *scheme = (f && f->port == 443) ? "https" : "http";
    if (host[0]) {
        char url[1200];
        snprintf(url, sizeof(url), "%s://%s%s", scheme, host, path);
        capture_req_url(url);
        dl_maybe_enqueue(url, buf, (size_t)n);
    } else if (f && strcmp(f->ip, "unix")) {
        char url[1200];
        snprintf(url, sizeof(url), "%s://%s:%u%s", scheme, f->ip, f->port, path);
        capture_req_url(url);
    }
}
static void (*o_abort)(void);
typedef struct { int64_t value; int32_t timescale; uint32_t flags; int64_t epoch; int64_t duration; } CMTime;
static double cm_sec(CMTime t) { return t.timescale > 0 ? (double)t.value / (double)t.timescale : 0.0; }
CMTime CMTimeMakeWithSeconds(double seconds, int32_t prefTimescale);   /* CoreMedia, 加载期解析 */
static int g_ntask, g_jtail, g_jhead, g_dl_count;   /* 前置声明(定义在后) */
static void my_abort(void) {
    log_line("★ABORT 黑匣子: ntask=%d jdepth=%d dl_count=%d —— Dart 侧未捕获异常, 我方线程当时状态见线程栈",
             g_ntask, g_jtail - g_jhead, g_dl_count);
    o_abort();
}
struct bindent { const char *name; void *hook; void **orig; };
static struct bindent g_binds[] = {
    { "connect",      (void *)my_connect,      (void **)&o_connect },
    { "close",        (void *)my_close,        (void **)&o_close },
    { "read",         (void *)my_read,         (void **)&o_read },
    { "write",        (void *)my_write,        (void **)&o_write },
    { "recv",         (void *)my_recv,         (void **)&o_recv },
    { "send",         (void *)my_send,         (void **)&o_send },
    { "getaddrinfo",  (void *)my_getaddrinfo,  (void **)&o_getaddrinfo },
    { "getifaddrs",   (void *)my_getifaddrs,   (void **)&o_getifaddrs },
    { "abort",        (void *)my_abort,        (void **)&o_abort },
};
#define NBIND (sizeof(g_binds) / sizeof(g_binds[0]))

static void rebind_image(const struct mach_header *mh, intptr_t slide, const char *imgname) {
    if (!mh) return;
    if (imgname && strstr(imgname, "yshg_hook")) return;             // 不碰自己
    // 只钩 app 自带镜像: 系统镜像在共享缓存里, 页不可写, mprotect 必失败
    if (!imgname || !strstr(imgname, "/Runner.app/")) return;
    const uint8_t *base = (const uint8_t *)mh;
    const mach_hdr64 *hdr = (const mach_hdr64 *)base;
    if (hdr->magic != 0xfeedfacf) return;
    const seg_cmd64 *linkedit = NULL, *seg;
    const symtab_cmd *symcmd = NULL; const dysymtab_cmd *dysym = NULL;
    uint32_t off = sizeof(mach_hdr64);
    for (uint32_t i = 0; i < hdr->ncmds; i++) {
        const uint32_t cmd = *(const uint32_t *)(base + off);
        const uint32_t sz  = *(const uint32_t *)(base + off + 4);
        if (cmd == LC_SEGMENT_64) {
            seg = (const seg_cmd64 *)(base + off);
            if (!strcmp(seg->segname, "__LINKEDIT")) linkedit = seg;
        } else if (cmd == LC_SYMTAB) symcmd = (const symtab_cmd *)(base + off);
        else if (cmd == LC_DYSYMTAB) dysym = (const dysymtab_cmd *)(base + off);
        off += sz;
    }
    if (!linkedit || !symcmd || !dysym || !dysym->indirectsymoff) return;
    uintptr_t le_vm = linkedit->vmaddr + (uintptr_t)slide;
    uintptr_t le_fo = linkedit->fileoff;
    const nlist64 *symtab = (const nlist64 *)(le_vm + (symcmd->symoff - le_fo));
    const char *strtab    = (const char *)(le_vm + (symcmd->stroff - le_fo));
    const uint32_t *indsy = (const uint32_t *)(le_vm + (dysym->indirectsymoff - le_fo));

    int img_hits = 0;
    off = sizeof(mach_hdr64);
    for (uint32_t i = 0; i < hdr->ncmds; i++) {
        const uint32_t cmd = *(const uint32_t *)(base + off);
        const uint32_t sz  = *(const uint32_t *)(base + off + 4);
        if (cmd == LC_SEGMENT_64) {
            seg = (const seg_cmd64 *)(base + off);
            if (seg->initprot == 0 || !strcmp(seg->segname, "__PAGEZERO")) { off += sz; continue; }
            const sect_hdr64 *sects = (const sect_hdr64 *)((const uint8_t *)seg + sizeof(seg_cmd64));
            for (uint32_t s = 0; s < seg->nsects; s++) {
                const sect_hdr64 *st = &sects[s];
                int is_ptr = !strcmp(st->sectname, "__la_symbol_ptr") || !strcmp(st->sectname, "__nl_symbol_ptr")
                          || !strcmp(st->sectname, "__got") || !strcmp(st->sectname, "__auth_got");
                if (!is_ptr || !st->size) continue;
                uintptr_t addr = st->addr + (uintptr_t)slide;
                size_t cnt = (size_t)(st->size / 8);
                long pg = sysconf(_SC_PAGESIZE);
                uintptr_t pgstart = addr & ~(uintptr_t)(pg - 1);
                uintptr_t pgend   = (addr + st->size + pg - 1) & ~(uintptr_t)(pg - 1);
                if (mprotect((void *)pgstart, pgend - pgstart, PROT_READ | PROT_WRITE) != 0) {
                    log_line("REBIND skip %s/%s (mprotect 失败)", imgname, st->sectname);
                    continue;   // 写不了就别碰, 否则 SIGBUS
                }
                int hits_here = 0;
                for (size_t k = 0; k < cnt; k++) {
                    uint32_t idx = st->reserved1 + (uint32_t)k;
                    if (idx >= dysym->nindirectsyms) continue;
                    uint32_t isym = indsy[idx];
                    if (isym == 0 || (isym & (IND_LOCAL | IND_ABS)) || isym >= symcmd->nsyms) continue;
                    const char *name = strtab + symtab[isym].n_strx;
                    if (!name || !*name) continue;
                    if (name[0] == '_') name++;   // ★ 符号名带前导下划线, 必须去掉再比
                    for (unsigned b = 0; b < NBIND; b++) {
                        if (!strcmp(name, g_binds[b].name)) {
                            void **slot = (void **)(addr + k * 8);
                            if (*g_binds[b].orig == NULL) continue; // 无原函数指针 -> 不钩(防 stub 回环)
                            if (*slot != g_binds[b].hook) { *slot = g_binds[b].hook; hits_here++; img_hits++; g_hit_total++;
                                g_bind_hits[b]++; }
                            break;
                        }
                    }
                }
                mprotect((void *)pgstart, pgend - pgstart, PROT_READ);
            }
        }
        off += sz;
    }
    if (img_hits > 0) { g_hit_imgs++; log_line("REBIND %s: %d 槽", imgname ? imgname : "?", img_hits); }
}


/* ================= 成品保护: __cstring 运行时自解密 (ChaCha20) =================
   构建后用 protect.py 把 __cstring 整段加密; 本构造入口最先调用 deobf() 解密。
   密钥/偏移写在 __DATA 的 g_ck 里 (build 时被 protect.py 填好), 明文段带 CRC 校验。 */
typedef struct { uint64_t vmaddr, size; uint32_t crc, prot; } CkRange;
typedef struct {
    char          magic[8];
    uint32_t      nranges;
    uint32_t      flags;
    CkRange       r[4];
    unsigned char key[32];
    unsigned char nonce[12];
} CkBlob;
__attribute__((used, section("__DATA,__data")))
/* ★ v4.14.1 硬化: 魔数改非 ASCII (strings/hexdump 里看不到 'YSHGPRT2' 这种标记),
   key/nonce 落盘前按 CKMASK 掩码 —— 十六进制里不再是一眼可认的 ChaCha 密钥块。
   ★ 注意: 这两个数组必须留在可写的 __DATA (非 const), 否则会落进被加密的 __tconst,
     解密前读到的就是垃圾 -> 魔数校验失败 -> 常量段解得出来才怪。 */
static unsigned char kCkSig[8] = { 0x9E, 0x37, 0xC4, 0x51, 0xAB, 0x0F, 0x62, 0xD8 };
#define CKMASK(i) ((unsigned char)(kCkSig[(i) % 8] ^ (unsigned char)((i) * 0x5D + 0x3C)))
static CkBlob g_ck = { {'\x9E','\x37','\xC4','\x51','\xAB','\x0F','\x62','\xD8'}, 0, 0, {{0,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}}, {0}, {0} };

typedef struct { const char *fname; void *fbase; const char *sname; void *saddr; } DlInfoU;
extern unsigned int mach_task_self_;   /* dlfcn.h 已带 dladdr 原型 */
extern int vm_protect(unsigned int, void *, unsigned long, int, int);
#define MP_R 1
#define MP_W 2
#define MP_X 4
#define MP_CPY 0x10

#define ROTL32(v, c) ((uint32_t)(((v) << (c)) | ((uint32_t)(v) >> (32 - (c)))))
static void cc20_block(const unsigned char key[32], const unsigned char nonce[12],
                       uint32_t ctr, unsigned char out[64]) {
    uint32_t st[16];
    /* "expand 32-byte k" 由整数拼出 (不能用字面量: 本段自身正要被解密) */
    st[0] = 0x61707865u; st[1] = 0x3320646eu; st[2] = 0x79622d32u; st[3] = 0x6b206574u;
    for (int i = 0; i < 8; i++)
        st[4 + i] = (uint32_t)key[i*4] | ((uint32_t)key[i*4+1] << 8) | ((uint32_t)key[i*4+2] << 16) | ((uint32_t)key[i*4+3] << 24);
    st[12] = ctr;
    st[13] = (uint32_t)nonce[0] | ((uint32_t)nonce[1] << 8) | ((uint32_t)nonce[2] << 16) | ((uint32_t)nonce[3] << 24);
    st[14] = (uint32_t)nonce[4] | ((uint32_t)nonce[5] << 8) | ((uint32_t)nonce[6] << 16) | ((uint32_t)nonce[7] << 24);
    st[15] = (uint32_t)nonce[8] | ((uint32_t)nonce[9] << 8) | ((uint32_t)nonce[10] << 16) | ((uint32_t)nonce[11] << 24);
    uint32_t w[16];
    for (int i = 0; i < 16; i++) w[i] = st[i];
    for (int r = 0; r < 10; r++) {
        #define QR(a,b,c,d) \
            w[a] += w[b]; w[d] = ROTL32(w[d] ^ w[a], 16); \
            w[c] += w[d]; w[b] = ROTL32(w[b] ^ w[c], 12); \
            w[a] += w[b]; w[d] = ROTL32(w[d] ^ w[a], 8);  \
            w[c] += w[d]; w[b] = ROTL32(w[b] ^ w[c], 7);
        QR(0,4,8,12)  QR(1,5,9,13)   QR(2,6,10,14) QR(3,7,11,15)
        QR(0,5,10,15) QR(1,6,11,12)  QR(2,7,8,13)  QR(3,4,9,14)
        #undef QR
    }
    for (int i = 0; i < 16; i++) {
        uint32_t v = w[i] + st[i];
        out[i*4]   = (unsigned char)(v & 0xFF);
        out[i*4+1] = (unsigned char)((v >> 8) & 0xFF);
        out[i*4+2] = (unsigned char)((v >> 16) & 0xFF);
        out[i*4+3] = (unsigned char)((v >> 24) & 0xFF);
    }
}
static void cc20_xor(unsigned char *buf, size_t n, const unsigned char key[32],
                     const unsigned char nonce[12], uint32_t ctr) {
    unsigned char ks[64];
    size_t i = 0;
    while (i < n) {
        cc20_block(key, nonce, ctr++, ks);
        for (int j = 0; j < 64 && i < n; j++, i++) buf[i] ^= ks[j];
    }
}
static uint32_t crc32_of(const unsigned char *p, size_t n) {
    uint32_t c = 0xFFFFFFFFu;
    for (size_t i = 0; i < n; i++) {
        c ^= p[i];
        for (int k = 0; k < 8; k++) c = (c >> 1) ^ (0xEDB88320u & (~((c & 1) - 1)));
    }
    return ~c;
}
static int deobf(void) {
    if (memcmp(g_ck.magic, kCkSig, 8) != 0 || g_ck.nranges == 0 || g_ck.nranges > 4) return 0;  /* 未加密构建 */
    /* ★ v4.14.1: key/nonce 在文件里是掩码态, 先解出来再用 (栈上副本, 不落盘) */
    unsigned char key[32], nonce[12];
    for (int i = 0; i < 32; i++) key[i]   = (unsigned char)(g_ck.key[i]   ^ CKMASK(i));
    for (int i = 0; i < 12; i++) nonce[i] = (unsigned char)(g_ck.nonce[i] ^ CKMASK(i));
    DlInfoU di; di.fname = 0; di.fbase = 0; di.sname = 0; di.saddr = 0;
    if (!dladdr((const void *)&deobf, &di) || !di.fbase) return -1;
    int ok = 0;
    for (uint32_t i = 0; i < g_ck.nranges && i < 4; i++) {
        if (!g_ck.r[i].size) continue;
        /* 目标段已被链接器重命名到可写的 __DATA (构建时 -rename_section),
           因此直接原地解密即可 —— 不触碰任何可执行页, 免于 iOS W^X 限制 */
        unsigned char *p = (unsigned char *)di.fbase + g_ck.r[i].vmaddr;
        cc20_xor(p, (size_t)g_ck.r[i].size, key, nonce, (uint32_t)(i * 0x9E3779B9u));
        if (crc32_of(p, (size_t)g_ck.r[i].size) == g_ck.r[i].crc) ok++;
        else cc20_xor(p, (size_t)g_ck.r[i].size, key, nonce, (uint32_t)(i * 0x9E3779B9u));
        (void)g_ck.r[i].prot;
    }
    return ok;
}

/* ★★★ v4.14.4 崩溃黑匣子 ★★★
   致命信号时把 信号名/dylib基址/返回地址栈(含 dylib 内偏移)/当前任务 写进 yshg_net.log。
   全程 write(2) 直写(不碰 malloc/锁, 尽量异步信号安全); 写完 SIG_DFL + raise 照常死,
   iOS 系统崩溃报告不受影响。栈上地址给出相对 dylib 基址的偏移, llvm-objdump 可离线符号化。 */
extern int backtrace(void **, int);
static void crash_w(const char *s) {
    if (g_crashfd >= 0) { size_t n = 0; while (s[n]) n++; if (n) { ssize_t r = write(g_crashfd, s, n); (void)r; } }
}
static void crash_handler(int sig) {
    char ln[220];
    void *bt[48];
    int nbt = backtrace(bt, 48);
    const char *sn = sig == 11 ? "SEGV" : sig == 10 ? "BUS" : sig == 6 ? "ABRT"
                   : sig == 4 ? "ILL" : sig == 8 ? "FPE" : sig == 5 ? "TRAP" : "SIG?";
    snprintf(ln, sizeof(ln), "★★★ CRASH %s sig=%d base=%p 任务=%.120s ★★★\n",
             sn, sig, g_self_base, g_tls_job[0] ? g_tls_job : "(主线程/UI)");
    crash_w(ln);
    for (int i = 0; i < nbt && i < 32; i++) {
        unsigned long off = (unsigned long)((char *)bt[i] - (char *)g_self_base);
        snprintf(ln, sizeof(ln), "★CRASH bt[%d] %p (dylib+%#lx)%s\n", i, bt[i],
                 (off > 0 && off < 0x40000) ? off : 0, (off > 0 && off < 0x40000) ? "" : " (系统库)");
        crash_w(ln);
    }
    signal(sig, SIG_DFL);
    raise(sig);
}
static void crash_install(void) {
    DlInfoU di; di.fname = 0; di.fbase = 0; di.sname = 0; di.saddr = 0;
    if (dladdr((const void *)&crash_install, &di) && di.fbase) g_self_base = di.fbase;
    signal(SIGSEGV, crash_handler); signal(SIGBUS, crash_handler);
    signal(SIGABRT, crash_handler); signal(SIGILL, crash_handler);
    signal(SIGFPE, crash_handler);  signal(SIGTRAP, crash_handler);
}
__attribute__((constructor)) static void yshg_init(void) {
    int dr = deobf();       /* ★ 必须最先: 之后才能读任何字符串字面量 */
    log_line("=== yshg_hook v4.14.5 [鸡巴毛] CTOR ENTER (deobf=%d, HOME=%s) ===", dr, getenv("HOME") ? getenv("HOME") : "?");
    crash_install();
    {   DlInfoU di2; di2.fname = 0; di2.fbase = 0; di2.sname = 0; di2.saddr = 0;
        if (dladdr((const void *)&yshg_init, &di2) && di2.fbase) g_self_base = di2.fbase; }
    log_line("CRASH 黑匣子就绪 (base=%p)", g_self_base);
    // dyld API: 直接 extern 绑定 (dlsym 需要去掉下划线的裸名, 之前传了带下划线的名字 -> 全 0)
    dyld_img_count  = _dyld_image_count;
    dyld_img_hdr    = _dyld_get_image_header;
    dyld_img_name   = _dyld_get_image_name;
    dyld_img_slide  = _dyld_get_image_vmaddr_slide;
    log_line("dyld extern ok: images=%d", dyld_img_count());

    // originals first (before any slot rewrite)
    // 原函数: 直接 extern 绑定 (dlsym 在本环境不可靠)
    o_connect     = connect;
    o_close       = close;
    o_read        = read;
    o_write       = write;
    o_recv        = recv;
    o_send        = send;
    o_getaddrinfo = getaddrinfo;
    o_getifaddrs  = (int (*)(struct myifa **))getifaddrs;
    log_line("orig: connect=%p read=%p write=%p recv=%p send=%p getaddrinfo=%p",
             (void *)o_connect, (void *)o_read, (void *)o_write, (void *)o_recv,
             (void *)o_send, (void *)o_getaddrinfo);

    int32_t n = dyld_img_count();
    for (int32_t i = 0; i < n; i++) {
        const struct mach_header *h = dyld_img_hdr((uint32_t)i);
        rebind_image(h, (intptr_t)dyld_img_slide((uint32_t)i), dyld_img_name ? dyld_img_name((uint32_t)i) : "?");
    }
    log_line("=== yshg_hook v4.14.7 attached (%d images scanned, %d 镜像共 %d 槽重绑) ===", n, g_hit_imgs, g_hit_total);
    for (unsigned b = 0; b < NBIND; b++)
        if (g_bind_hits[b]) log_line("  HOOKED %-12s x%d", g_binds[b].name, g_bind_hits[b]);
    log_line("pid=%d HOME=%s", getpid(), getenv("HOME") ? getenv("HOME") : "?");
    dl_init();
}

// ================= v0.3 in-app downloader =================
// 播放即抓: app 内请求上游 m3u8 时自动入队, 本线程用 NSURLSession 下载
// (系统网络栈, https/重定向/cookie 全托管), CommonCrypto AES-128 解密,
// 流式写 Documents/yshg_dl/*.ts|mp4, 状态在 yshg_dl.log。STOP 文件 = 暂停开关。

// 纯 C 环境手写 ObjC 最小类型
typedef void *id;
typedef void *SEL;
typedef void *Class;
#define Nil ((void *)0)
#define nil ((void *)0)

// --- runtime API slots ---
static id    (*oc_ms)(id, SEL, ...);
static Class (*oc_getclass)(const char *);
static SEL   (*oc_sel)(const char *);
static Class (*oc_allocpair)(Class, const char *, size_t);
static int   (*oc_addmethod)(Class, SEL, void *, const char *);
static void  (*oc_register)(Class);
static id    (*dl_dsem_create)(long);
static long  (*dl_dsem_signal)(id);
static long  (*dl_dsem_wait)(id, uint64_t);
static uint64_t (*dl_dtime)(uint64_t, uint64_t);
static int   (*dl_cc)(uint32_t, uint32_t, uint32_t, const void *, size_t, const void *,
                      const void *, size_t, void *, size_t, size_t *);

static pthread_mutex_t g_dlm  = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t g_fmu  = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t g_hmu  = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  g_jcond;
static id g_fdeleg, g_sess;
static char g_hdrs[8192];
static size_t g_hn;
static pthread_t g_worker_tid;
static int g_dl_count;
static int g_dl_seq;   /* 文件命名序号(只增, 不参与配额) */
static int g_jhead, g_jtail;
static char g_jobs[16][1200];
static char g_cand[1200];
static char g_cand_pl[1200]; static time_t g_cand_pl_t;   /* ★ v4.14.7 最近播放列表候选 */
static volatile int g_ready, g_auto, g_act, g_cur, g_tot;
static time_t g_flash_until;

/* ★ v4.14.7 播放列表候选: 只收 m3u8 / parse?url= / mp4 / key 形态的 URL。
   播放期间分段请求持续覆盖 g_cand(最后一次出站请求), 点抓抓到的常是 .ts 分段
   → 封装器判"无分段"静默失败 = "点抓没反应"。此表让 tap 优先命中真正的播放列表。 */
static void cand_pl_set(const char *u) {
    if (!u || !*u) return;
    if (!strstr(u, ".m3u8") && !strstr(u, "parse?url=") && !strstr(u, ".mp4") && !strstr(u, "/key/")) return;
    pthread_mutex_lock(&g_dlm);
    snprintf(g_cand_pl, sizeof(g_cand_pl), "%s", u);
    g_cand_pl_t = time(NULL);
    pthread_mutex_unlock(&g_dlm);
}


// ============ 重建段: 日志/工具/取回/解析 (v1.6 等价) ============
#define DL_MAX 32

static void dl_log(const char *fmt, ...) {
    char ts[32]; now_str(ts, sizeof(ts));
    char msg[1200];
    va_list ap; va_start(ap, fmt);
    vsnprintf(msg, sizeof(msg), fmt, ap);
    va_end(ap);
    pthread_mutex_lock(&g_mu);
    const char *home = getenv("HOME");
    static FILE *a, *b;
    if (!a) {
        char p[512];
        if (home && *home) { snprintf(p, sizeof(p), "%s/Documents/yshg_dl.log", home); a = fopen(p, "a"); }
        b = fopen("/var/mobile/Documents/yshg_dl.log", "a");
    }
    if (a) { fprintf(a, "[%s] %s\n", ts, msg); fflush(a); }
    if (b) { fprintf(b, "[%s] %s\n", ts, msg); fflush(b); }
    pthread_mutex_unlock(&g_mu);
    log_line("DL %s", msg);
}

static id ns_str(const char *s) {
    return ((id (*)(id, SEL, const char *))oc_ms)((id)oc_getclass("NSString"), oc_sel("stringWithUTF8String:"), s);
}
static id oc_cls(const char *n) { return (id)oc_getclass(n); }
static id new_pool(void) {
    id p = ((id (*)(id, SEL))oc_ms)(oc_cls("NSAutoreleasePool"), oc_sel("alloc"));
    return ((id (*)(id, SEL))oc_ms)(p, oc_sel("init"));
}
static void pool_drain(id p) { ((void (*)(id, SEL))oc_ms)(p, oc_sel("drain")); }
static void set_hdr(id req, const char *k, const char *v) {
    ((id (*)(id, SEL, id, id))oc_ms)(req, oc_sel("setValue:forHTTPHeaderField:"), ns_str(v), ns_str(k));
}

static char *fetch_c(const char *url, const char *hdrs, int timeout_s, size_t *outn, int *status) {
    *outn = 0;
    if (status) *status = -1;
    if (!oc_ms || !url) return NULL;
    void *pool = objc_autoreleasePoolPush();
    char *out = NULL;
    id nurl = ((id (*)(id, SEL, id))oc_ms)(oc_cls("NSURL"), oc_sel("URLWithString:"), ns_str(url));
    if (nurl) {
        id req = ((id (*)(id, SEL, id))oc_ms)(oc_cls("NSMutableURLRequest"), oc_sel("requestWithURL:"), nurl);
        if (req) {
            ((void (*)(id, SEL, double))oc_ms)(req, oc_sel("setTimeoutInterval:"), (double)timeout_s);
            set_hdr(req, "User-Agent", "Mozilla/5.0 (iPhone; CPU iPhone OS 16_2 like Mac OS X) AppleWebKit/605.1.15");
            if (hdrs && *hdrs) {
                char *tmp = strdup(hdrs), *sp = tmp, *nl;
                while (sp && *sp) {
                    nl = strchr(sp, '\n'); if (nl) *nl = 0;
                    char *cp = strchr(sp, ':');
                    if (cp) {
                        *cp = 0; const char *k = sp, *v = cp + 1;
                        while (*v == ' ') v++;
                        if (strcasecmp(k, "Host") && strcasecmp(k, "Content-Length") &&
                            strcasecmp(k, "Accept-Encoding") && strcasecmp(k, "Connection"))
                            set_hdr(req, k, v);
                    }
                    sp = nl ? nl + 1 : NULL;
                }
                free(tmp);
            }
            id resp = NULL;
            id data = ((id (*)(id, SEL, id, id *, id *))oc_ms)(oc_cls("NSURLConnection"),
                        oc_sel("sendSynchronousRequest:returningResponse:error:"), req, &resp, Nil);
            if (status && resp) {
                long code = (long)((long (*)(id, SEL))oc_ms)(resp, oc_sel("statusCode"));
                *status = (int)code;
            }
            unsigned long len = data ? ((unsigned long (*)(id, SEL))oc_ms)(data, oc_sel("length")) : 0;
            if (len) {
                out = (char *)malloc(len + 1);
                const void *b = out ? ((const void *(*)(id, SEL))oc_ms)(data, oc_sel("bytes")) : NULL;
                if (out && b) { memcpy(out, b, len); out[len] = 0; *outn = len; }
                else { free(out); out = NULL; *outn = 0; }
            }
        }
    }
    objc_autoreleasePoolPop(pool);
    return out;
}

// ---- URL join ----
static void url_join(const char *base, const char *rel, char *out, size_t n) {
    if (!strncasecmp(rel, "http://", 7) || !strncasecmp(rel, "https://", 8)) { snprintf(out, n, "%s", rel); return; }
    const char *se = strstr(base, "://");
    if (!se) { snprintf(out, n, "%s", rel); return; }
    se += 3;
    const char *slash = strchr(se, '/');
    if (!slash) { snprintf(out, n, "%s/%s", base, rel); return; }
    if (rel[0] == '/') {
        size_t hl = (size_t)(slash - base);
        snprintf(out, n, "%.*s%s", (int)hl, base, rel);
        return;
    }
    char dir[800];
    snprintf(dir, sizeof(dir), "%s", base);
    char *q = strchr(dir, '?'); if (q) *q = 0;
    char *ls = strrchr(dir, '/'); if (ls) *ls = 0;
    snprintf(out, n, "%s/%s", dir, rel);
}

// ---- m3u8 解析 ----
typedef struct {
    char *segs[6000];
    int nsegs, enc, endlist, hasmap, byterange, mseq;
    char keyuri[1200], ivhex[40], mapuri[1200];
    char variant[1200]; long vbest;
    volatile int cur, tot;      /* 每任务进度 */
    char name[128];
    char url[1200];             /* ★ v4.14.0 任务 URL: 供入队去重比对 */
    void *dead_next;            /* v3.8.1 坟场链表 */
} MTX;
static MTX *g_task[8]; static int g_ntask;   /* 活动任务表 (g_dlm 内访问) */
static MTX *g_dead;                          /* 已完成任务坟场 (永不再 free) */
static pthread_mutex_t g_muxmu = PTHREAD_MUTEX_INITIALIZER;  /* 旧锁: 保留给老调用点, 见下 */
/* ★★★ v4.14.0: 封装器全程用全局状态 (mvs/mas/m_out/m_sps/m_pos...) + 静态读盘缓冲,
   必须严格串行。实测原 pthread 锁没拦住并发 (两条「转封装开始」只差 3ms) ->
   改用原子锁「等待式」串行: 第二个任务会等第一个做完, 而不是丢任务。 */
static volatile int g_mux_busy;
static void mux_lock(void)   { while (__sync_lock_test_and_set(&g_mux_busy, 1)) usleep(3000); }
static void mux_unlock(void) { __sync_lock_release(&g_mux_busy); }

static int line_attr(const char *ln, const char *key, char *out, size_t n) {
    const char *p = strstr(ln, key);
    if (!p) return 0;
    p += strlen(key);
    if (*p == '"') {
        p++;
        const char *e = strchr(p, '"');
        if (!e) return 0;
        size_t l = (size_t)(e - p); if (l >= n) l = n - 1;
        memcpy(out, p, l); out[l] = 0; return 1;
    }
    const char *e = p;
    while (*e && *e != ',' && *e != '\r' && *e != '\n') e++;
    size_t l = (size_t)(e - p); if (l >= n) l = n - 1;
    memcpy(out, p, l); out[l] = 0; return 1;
}

static void parse_m3u8(char *text, const char *base, MTX *mx) {
    char *save = text, *line;
    long best_bw = -1, pending_bw = -1;
    char best_uri[1200] = "";
    int have_pending = 0;
    while ((line = strsep(&save, "\n"))) {
        char *r = strchr(line, '\r'); if (r) *r = 0;
        if (!*line) continue;
        if (!strncmp(line, "#EXT-X-STREAM-INF", 17)) {
            char bw[32] = "";
            pending_bw = -1;
            if (line_attr(line, "BANDWIDTH=", bw, sizeof(bw))) pending_bw = atol(bw);
            continue;
        }
        if (!strncmp(line, "#EXT-X-KEY", 10)) {
            char m[32] = "";
            line_attr(line, "METHOD=", m, sizeof(m));
            if (!strcmp(m, "SAMPLE-AES")) continue;
            if (!strcmp(m, "AES-128")) {
                mx->enc = 1;
                char u[1000] = "";
                if (line_attr(line, "URI=", u, sizeof(u))) url_join(base, u, mx->keyuri, sizeof(mx->keyuri));
                char iv[40] = "";
                if (line_attr(line, "IV=0x", iv, sizeof(iv))) snprintf(mx->ivhex, sizeof(mx->ivhex), "%s", iv);
                else mx->ivhex[0] = 0;
            } else mx->enc = 0;
            continue;
        }
        if (!strncmp(line, "#EXT-X-MAP", 10)) {
            char u[1000] = "";
            if (line_attr(line, "URI=", u, sizeof(u))) { url_join(base, u, mx->mapuri, sizeof(mx->mapuri)); mx->hasmap = 1; }
            continue;
        }
        if (!strncmp(line, "#EXT-X-BYTERANGE", 16)) { mx->byterange = 1; continue; }
        if (!strncmp(line, "#EXT-X-ENDLIST", 14)) { mx->endlist = 1; continue; }
        if (!strncmp(line, "#EXT-X-MEDIA-SEQUENCE", 21)) { mx->mseq = atoi(line + 22); continue; }
        if (!strncmp(line, "#EXTINF", 7)) { have_pending = 1; continue; }
        if (line[0] == '#') continue;
        if (have_pending) {
            char full[1200];
            url_join(base, line, full, sizeof(full));
            if (mx->nsegs < 6000) mx->segs[mx->nsegs++] = strdup(full);
            have_pending = 0;
        } else if (pending_bw >= 0) {
            char cand[1200];
            url_join(base, line, cand, sizeof(cand));
            if (pending_bw > best_bw) { best_bw = pending_bw; snprintf(best_uri, sizeof(best_uri), "%s", cand); }
            pending_bw = -1;
        }
    }
    if (best_uri[0]) { snprintf(mx->variant, sizeof(mx->variant), "%s", best_uri); mx->vbest = best_bw; }
}

static void write_out_dir(char *dir, size_t n) {
    const char *home = getenv("HOME");
    snprintf(dir, n, "%s/Documents/yshg_dl", home && *home ? home : "/tmp");
    mkdir(dir, 0755);
    mkdir("/var/mobile/Documents/yshg_dl", 0755);
}

// ================= v3.6 下载记录 =================
#define HIST_MAX 200
static char g_hist[HIST_MAX][300];
static int g_histn = 0;
static pthread_mutex_t g_hst = PTHREAD_MUTEX_INITIALIZER;

static void hist_load(void) {
    char dir[512], p[600]; write_out_dir(dir, sizeof(dir));
    snprintf(p, sizeof(p), "%s/history.txt", dir);
    FILE *f = fopen(p, "rb");
    if (!f) return;
    char line[300];
    while (fgets(line, sizeof(line), f)) {
        size_t l = strlen(line);
        while (l && (line[l-1] == '\n' || line[l-1] == '\r')) line[--l] = 0;
        if (!l) continue;
        if (g_histn == HIST_MAX) { memmove(g_hist, g_hist + 1, (HIST_MAX - 1) * sizeof(g_hist[0])); g_histn--; }
        {   /* ★ 旧记录时间戳是 UTC 的 HH:MM:SS.mmm → 换算北京时间并补日期 */
            char *sp0 = strchr(line, ' ');
            if (sp0 && !strchr(line, '_') && sp0 - line >= 8) {
                int h = 0, mi = 0, se = 0;
                if (sscanf(line, "%d:%d:%d", &h, &mi, &se) == 3) {
                    h = (h + 8) % 24;
                    time_t nw = time(NULL); struct tm tm; localtime_r(&nw, &tm);
                    char nl2[300];
                    snprintf(nl2, sizeof(nl2), "%02d-%02d_%02d:%02d:%02d %s", tm.tm_mon + 1, tm.tm_mday, h, mi, se, sp0 + 1);
                    snprintf(line, 300, "%s", nl2);
                }
            }
        }
        snprintf(g_hist[g_histn++], sizeof(g_hist[0]), "%s", line);
    }
    fclose(f);
    dl_log("记录: 载入 %d 条历史", g_histn);
}

/* 完成时间戳: MM-DD_HH:MM:SS (无空格, 不破坏 hist_fields 的首空格切分) */
static void hist_ts(char *buf, size_t n) {
    time_t sec = time(NULL) + 8 * 3600;                /* ★ 北京时间 (UTC+8) */
    struct tm tm; gmtime_r(&sec, &tm);
    snprintf(buf, n, "%02d-%02d_%02d:%02d:%02d", tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec);
}
static void hist_add(const char *fmt, ...) {
    char body[240];
    va_list ap; va_start(ap, fmt);
    vsnprintf(body, sizeof(body), fmt, ap);
    va_end(ap);
    char ts[32]; hist_ts(ts, sizeof(ts));
    pthread_mutex_lock(&g_hst);
    if (g_histn == HIST_MAX) { memmove(g_hist, g_hist + 1, (HIST_MAX - 1) * sizeof(g_hist[0])); g_histn--; }
    snprintf(g_hist[g_histn++], sizeof(g_hist[0]), "%s %s", ts, body);
    char dir[512], p[600]; write_out_dir(dir, sizeof(dir));
    snprintf(p, sizeof(p), "%s/history.txt", dir);
    FILE *f = fopen(p, "wb");
    if (f) { for (int i = 0; i < g_histn; i++) fprintf(f, "%s\n", g_hist[i]); fclose(f); }
    pthread_mutex_unlock(&g_hst);
}

static void hexiv(const char *hex, uint8_t out[16]) {
    memset(out, 0, 16);
    for (int i = 0; i < 32 && hex[i]; i += 2) {
        int h = hex[i] <= '9' ? hex[i] - '0' : (hex[i] | 32) - 'a' + 10;
        int l = hex[i + 1] <= '9' ? hex[i + 1] - '0' : ((hex[i + 1] | 32) - 'a' + 10);
        if (i / 2 < 16) out[i / 2] = (uint8_t)(h * 16 + l);
    }
}

static void do_download_impl(const char *url, MTX *m);
static uint64_t g_mdur_ms;   /* 前置声明(定义在封装器段), 两处 tentative 合并 */
static int g_mw, g_mh;       /* 前置声明: 封装后分辨率 */

static void do_download(const char *url) {
    snprintf(g_tls_job, sizeof(g_tls_job), "%.200s", url ? url : "");
    MTX *m = (MTX *)calloc(1, sizeof(MTX));
    if (!m) { dl_log("FAIL ctx alloc (内存不足, 本次放弃)"); return; }
    m->vbest = -1;
    snprintf(m->url, sizeof(m->url), "%s", url);   /* ★ v4.14.0 供入队去重 */
    pthread_mutex_lock(&g_dlm);
    m->cur = 0; m->tot = 0;
    if (g_ntask < 8) g_task[g_ntask++] = m;
    int slot = g_ntask;
    pthread_mutex_unlock(&g_dlm);
    do_download_impl(url, m);
    pthread_mutex_lock(&g_dlm);
    for (int i = 0; i < g_ntask; i++) if (g_task[i] == m) {
        memmove(&g_task[i], &g_task[i+1], (g_ntask-i-1)*sizeof(MTX*));
        g_ntask--; break;
    }
    pthread_mutex_unlock(&g_dlm);
    (void)0;   /* g_dl_count 已在 dl_worker 内配对增减, 此处不再动 */
    for (int i = 0; i < m->nsegs; i++) { free(m->segs[i]); m->segs[i] = NULL; }
    /* ★ 保留坟场(防 tick 读到悬垂指针), 但必须封顶 —— 否则每完成一任务漏 ~48KB */
    pthread_mutex_lock(&g_dlm);
    m->dead_next = g_dead; g_dead = m;
    {
        static int g_deadn;
        g_deadn++;
        if (g_deadn > 12) {
            MTX *cur = (MTX *)g_dead, *prev = NULL;
            while (cur && cur->dead_next) { prev = cur; cur = (MTX *)cur->dead_next; }
            if (cur) { if (prev) prev->dead_next = NULL; else g_dead = NULL; free(cur); g_deadn--; }
        }
    }
    pthread_mutex_unlock(&g_dlm);
    (void)slot;
}

// ---- v3.8 段下载专用: NSURLSession (连接池/keep-alive/HTTP2), 真 block + 信号量 ----
static id g_dlsess;
static pthread_mutex_t g_dslm = PTHREAD_MUTEX_INITIALIZER;

static char *fetch_s(const char *url, const char *hdrs, int timeout_s, size_t *outn, int *status) {
    *outn = 0;
    if (status) *status = -1;
    if (!oc_ms || !url) return NULL;
    pthread_mutex_lock(&g_dslm);
    if (!g_dlsess) {
        id cfg = ((id(*)(id, SEL))oc_ms)(oc_cls("NSURLSessionConfiguration"), oc_sel("defaultSessionConfiguration"));
        if (cfg) {
            ((void(*)(id, SEL, double))oc_ms)(cfg, oc_sel("setTimeoutIntervalForRequest:"), 40.0);
            ((void(*)(id, SEL, double))oc_ms)(cfg, oc_sel("setTimeoutIntervalForResource:"), 120.0);
            g_dlsess = ((id(*)(id, SEL, id, id, id))oc_ms)(oc_cls("NSURLSession"),
                oc_sel("sessionWithConfiguration:delegate:delegateQueue:"), cfg, Nil, Nil);
            /* ★★ v4.14.5: 工厂方法返回 autoreleased 对象, 落在本调用的 autorelease pool 里,
               pool 在函数尾部排空 → 缓存进全局的 session 变成悬垂指针, 下一次段下载
               在它上面 objc_msgSend 直接崩 (iOS 崩溃报告 Thread 27 已证实)。
               与 UI session (g_sess) 同样处理: 创建即 retain。 */
            if (g_dlsess) g_dlsess = (id)objc_retain(g_dlsess);
        }
    }
    id sess = g_dlsess;
    pthread_mutex_unlock(&g_dslm);
    if (!sess) return NULL;
    void *pool = objc_autoreleasePoolPush();
    char *out = NULL;
    id nurl = ((id (*)(id, SEL, id))oc_ms)(oc_cls("NSURL"), oc_sel("URLWithString:"), ns_str(url));
    id req = NULL;
    if (nurl) {
        req = ((id (*)(id, SEL, id))oc_ms)(oc_cls("NSMutableURLRequest"), oc_sel("requestWithURL:"), nurl);
        if (req) {
            ((void (*)(id, SEL, double))oc_ms)(req, oc_sel("setTimeoutInterval:"), (double)timeout_s);
            set_hdr(req, "User-Agent", "Mozilla/5.0 (iPhone; CPU iPhone OS 16_2 like Mac OS X) AppleWebKit/605.1.15");
            if (hdrs && *hdrs) {
                char *tmp = strdup(hdrs), *sp = tmp, *nl;
                while (sp && *sp) {
                    nl = strchr(sp, '\n'); if (nl) *nl = 0;
                    char *cp = strchr(sp, ':');
                    if (cp) {
                        *cp = 0; const char *k = sp, *v = cp + 1;
                        while (*v == ' ') v++;
                        if (strcasecmp(k, "Host") && strcasecmp(k, "Content-Length") &&
                            strcasecmp(k, "Accept-Encoding") && strcasecmp(k, "Connection"))
                            set_hdr(req, k, v);
                    }
                    sp = nl ? nl + 1 : NULL;
                }
                free(tmp);
            }
        }
    }
    if (req) {
        __block char *rb = NULL; __block size_t rn = 0; __block int rst = -1;
        id sem = dl_dsem_create(0);
        id task = ((id (*)(id, SEL, id, void (^)(id, id, id)))oc_ms)(sess,
            oc_sel("dataTaskWithRequest:completionHandler:"), req,
            ^(id data, id resp, id err) {
                (void)err;
                rst = -1;
                if (resp) {
                    id hcls = oc_getclass("NSHTTPURLResponse");
                    if (hcls && ((unsigned char(*)(id, SEL, id))oc_ms)(resp, oc_sel("isKindOfClass:"), hcls))
                        rst = (int)(long)((long (*)(id, SEL))oc_ms)(resp, oc_sel("statusCode"));
                }
                unsigned long len = data ? ((unsigned long (*)(id, SEL))oc_ms)(data, oc_sel("length")) : 0;
                if (len) {
                    char *b2 = (char *)malloc(len + 1);
                    const void *b = b2 ? ((const void *(*)(id, SEL))oc_ms)(data, oc_sel("bytes")) : NULL;
                    if (b2 && b) { memcpy(b2, b, len); b2[len] = 0; rn = (size_t)len; rb = b2; }
                    else if (b2) { b2[0] = 0; rb = b2; }
                }
                dl_dsem_signal(sem);
            });
        if (task) {
            ((void(*)(id, SEL))oc_ms)(task, oc_sel("resume"));
            /* ★ dispatch_time 语义: 第二参是 dispatch_time_t 不是裸时长。
               v3.8 直接传 45e9 → 相对开机时刻早已过去 → 立即超时 → cancel 后
               迟到的完成回调写已释放的 __block 存储 → 堆损坏 → 全进程 alloc 失败。 */
            long w1 = dl_dsem_wait(sem, dl_dtime(0, (uint64_t)timeout_s * 1000000000ull + 5000000000ull));
            if (w1 != 0) {
                ((void(*)(id, SEL))oc_ms)(task, oc_sel("cancel"));   // 超时兜底取消
                dl_dsem_wait(sem, dl_dtime(0, 10000000000ull));      // ★ 等完成回调确认后才离场
            }
            if (rb) { out = rb; *outn = rn; if (status) *status = rst; }
        }
    }
    objc_autoreleasePoolPop(pool);
    return out;
}

static void url_penc(const char *s, char *out, size_t n) {
    size_t o = 0;
    for (; *s && o + 4 < n; s++) {
        unsigned char c = (unsigned char)*s;
        if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') ||
            c == '-' || c == '_' || c == '.' || c == '~') out[o++] = c;
        else o += (size_t)snprintf(out + o, n - o, "%%%02X", c);
    }
    out[o] = 0;
}
static int g_pxport = 6001;   /* 轮转: 每次调用只试一个端口, 降低对 app Dart 代理的惊扰 */
static char *fetch_via_proxy(const char *url, const char *hdrs, size_t *outn, int *status) {
    char pu[1800], enc[1500];
    url_penc(url, enc, sizeof(enc));
    snprintf(pu, sizeof(pu), "http://127.0.0.1:%d/parse?url=%s", g_pxport, enc);
    int used = g_pxport;
    g_pxport = g_pxport >= 6005 ? 6001 : g_pxport + 1;
    char *r = fetch_c(pu, hdrs, 30, outn, status);
    if (r && *outn) { dl_log("代理(%d) 取到 %zuB", used, *outn); return r; }
    free(r);
    dl_log("代理(%d) 未取到(st=%d)", used, status ? *status : -1);
    return NULL;
}

typedef struct {
    MTX *m;
    const uint8_t *key; int have_key;
    const char *wdir;
    const char *hdrs; int legacy;
    volatile int *next_seg, *done_ct, *fail_ct, *logct;
    size_t *tot;
    const char *name; int nsegs;
} SWARG;

static void *seg_worker(void *arg) {
    SWARG *w = (SWARG *)arg;
    MTX *m = w->m;
    uint8_t iv[16];
    char sfp[900];
    for (;;) {
        int i = __atomic_fetch_add(w->next_seg, 1, __ATOMIC_SEQ_CST);
        if (i >= w->nsegs) break;
        size_t sn = 0;
        char *sb = NULL;
        for (int tr = 0; tr < 3 && !sb; tr++) {
            sb = w->legacy ? fetch_c(m->segs[i], w->hdrs, 40, &sn, NULL)
                           : fetch_s(m->segs[i], w->hdrs, 40, &sn, NULL);
            if (!sb) sb = fetch_c(m->segs[i], w->hdrs, 40, &sn, NULL);   // ★ session 路径失败, NSURLConnection 保底
        }
        if (!sb) { __atomic_fetch_add(w->fail_ct, 1, __ATOMIC_SEQ_CST); continue; }
        size_t wn = sn;
        if (w->have_key) {
            if (m->ivhex[0]) hexiv(m->ivhex, iv);
            else { long seq = m->mseq + i; memset(iv, 0, 16);
                   iv[15] = (uint8_t)seq; iv[14] = (uint8_t)(seq >> 8);
                   iv[13] = (uint8_t)(seq >> 16); iv[12] = (uint8_t)(seq >> 24); }
            char *dec = (char *)malloc(sn + 32);
            if (!dec) { free(sb); __atomic_fetch_add(w->fail_ct, 1, __ATOMIC_SEQ_CST); continue; }
            size_t mv = 0;
            int rc = dl_cc(1, 0, 1, w->key, 16, iv, sb, sn, dec, sn + 32, &mv);
            free(sb);
            if (rc != 0) { dl_log("FAIL CCCrypt rc=%d 段 %d", rc, i); free(dec); __atomic_fetch_add(w->fail_ct, 1, __ATOMIC_SEQ_CST); continue; }
            sb = dec; wn = mv;
        }
        snprintf(sfp, sizeof(sfp), "%s/s%05d", w->wdir, i);
        FILE *sf = fopen(sfp, "wb");
        if (sf) { fwrite(sb, 1, wn, sf); fclose(sf); }
        free(sb);
        __atomic_fetch_add(w->tot, wn, __ATOMIC_SEQ_CST);
        int dc = __atomic_add_fetch(w->done_ct, 1, __ATOMIC_SEQ_CST);
        m->cur = dc;
        int lc = __atomic_add_fetch(w->logct, 1, __ATOMIC_SEQ_CST);
        if (lc % 25 == 0) dl_log("%s 段 %d/%d (%.1fMB)", w->name, dc, w->nsegs, __atomic_load_n(w->tot, __ATOMIC_SEQ_CST) / 1048576.0);
    }
    return NULL;
}

static void do_download_impl(const char *url, MTX *m) {
    if (!url || strlen(url) < 12 || !strstr(url, "http")) return;   // ★ 空坏 URL 直接拒绝
    if (g_dl_count >= DL_MAX) { dl_log("上限 %d 已到, 丢弃 %s", DL_MAX, url); return; }
    char dir[512]; write_out_dir(dir, sizeof(dir));
    char stopp[600]; snprintf(stopp, sizeof(stopp), "%s/STOP", dir);
    FILE *st = fopen(stopp, "r");
    if (st) { fclose(st); dl_log("STOP 开关打开, 跳过 %s", url); return; }

    pthread_mutex_lock(&g_hmu);
    char hdrs[4096];
    snprintf(hdrs, sizeof(hdrs), "%s", g_hdrs);
    pthread_mutex_unlock(&g_hmu);

    // final-url 去重: 同一视频的 master/variant 只下一次
    char dkey[1300]; snprintf(dkey, sizeof(dkey), "DL:%s", url);
    if (!seen_add(dkey)) {
        /* ★ v4.14.2: 重复进入先查记忆 —— 上次已解析出变体, 且该变体已在下载/已下载,
           就直接跳过, 连 master 都不再拉。(设备日志见过 16 秒重拉同一 master 472 次) */
        char cv[1300]; cv[0] = 0; time_t tprev = 0;
        if (mmc_get(url, cv, sizeof(cv), &tprev) && cv[0]) {
            char vk[1300]; snprintf(vk, sizeof(vk), "DL:%s", cv);
            if (seen_has(vk)) { dl_log("变体已在下/已下, 跳过"); return; }
        }
        if (tprev && (time(NULL) - tprev) < 5) {
            dl_log("重复视频: 5s 内已处理过同一地址, 忽略");
            return;
        }
        /* ★ 不再静默返回 —— 之前"点抓没反应"就是这里(第二次抓同一视频被去重吞掉)。
           改为允许重下, 文件名带秒级时间戳区分。 */
        dl_log("重复视频, 重新下载");
    }

    size_t n = 0;
    int st1 = 0;
    char *text = fetch_c(url, hdrs, 30, &n, &st1);
    if (!text) {
        dl_log("直连失败(st=%d), 走本地代理: %s", st1, url);
        text = fetch_via_proxy(url, hdrs, &n, &st1);
        if (!text) { dl_log("FAIL 代理也失败 %s", url); hist_add("✗ playlist取不到(st=%d) %s", st1, url); return; }
        dl_log("代理取到 playlist %zuB", n);
    }
    memset(m->segs,0,sizeof(m->segs)); m->nsegs=0; m->enc=0; m->endlist=0; m->hasmap=0; m->byterange=0; m->mseq=0;
    m->keyuri[0]=0; m->ivhex[0]=0; m->mapuri[0]=0; m->variant[0]=0; m->vbest=-1;
    parse_m3u8(text, url, m);
    free(text);
    if (m->variant[0]) {   // master → 二跳
        dl_log("master(%ldkbps) → %s", m->vbest / 1000, m->variant);
        mmc_put(url, m->variant);          /* ★ v4.14.2 记住 master → 变体 */
        char dk2[1300]; snprintf(dk2, sizeof(dk2), "DL:%s", m->variant);
        if (!seen_add(dk2)) { dl_log("变体已在下/已下, 跳过"); return; }
        text = fetch_c(m->variant, hdrs, 30, &n, NULL);
        if (!text) { dl_log("FAIL 取变体失败"); hist_add("✗ 变体取不到 %s", url); return; }
        m->nsegs = 0; m->enc = 0; m->endlist = 0; m->hasmap = 0; m->byterange = 0; m->mseq = 0;
        m->keyuri[0]=0; m->ivhex[0]=0; m->mapuri[0]=0;
        parse_m3u8(text, m->variant, m);
        free(text);
        url = m->variant;
    }
    if (m->byterange) { dl_log("BYTERANGE 不支持, 跳过"); hist_add("✗ BYTERANGE %s", url); return; }
    if (!m->nsegs) { dl_log("无分段 %s", url); hist_add("✗ 无分段 %s", url); return; }
    size_t cap = m->endlist ? 6000 : 500;
    if ((size_t)m->nsegs > cap) { m->nsegs = (int)cap; dl_log("无 ENDLIST, 截断 %zu 段", cap); }

    uint8_t key[16]; int have_key = 0;
    if (m->enc) {
        size_t kn = 0; char *kb = fetch_c(m->keyuri, hdrs, 30, &kn, NULL);
        if (!kb || kn != 16) { free(kb); kb = fetch_via_proxy(m->keyuri, hdrs, &kn, NULL); }
        if (!kb || kn != 16) { dl_log("FAIL key %s (%zu)", m->keyuri, kn); free(kb); hist_add("✗ key失败 %s", url); return; }
        memcpy(key, kb, 16); free(kb); have_key = 1;
        dl_log("key ok");
    }

    pthread_mutex_lock(&g_dlm); int dlno = ++g_dl_seq; pthread_mutex_unlock(&g_dlm);   /* 仅作文件命名序号 */
    time_t t = time(NULL);
    char name[128], path[700], part[750];
    snprintf(name, sizeof(name), "%ld_%02d.%s", (long)t, dlno % 100, m->hasmap ? "mp4" : "ts");
    snprintf(path, sizeof(path), "%s/%s", dir, name);
    snprintf(part, sizeof(part), "%s.part", path);
    FILE *out = fopen(part, "wb");
    if (!out) { dl_log("FAIL open %s", part); hist_add("✗ 文件打不开 %s", name); return; }
    m->tot = m->nsegs; m->cur = 0;

    // ===== v3.7 段级并行: 4 线程领段号, 每段落盘, 全完按序拼合 =====
    uint8_t iv[16];
    size_t total = 0;
    int broken = 0;
    char wdir[850];
    snprintf(wdir, sizeof(wdir), "%s/w_%s", dir, name);
    mkdir(wdir, 0755);
    fclose(out); remove(part);   // 拼合阶段重开
    volatile int next_seg = 0, done_ct = 0, fail_ct = 0, logct = 0;
    size_t tot_atomic = 0;

    char lgp[900]; snprintf(lgp, sizeof(lgp), "%s/LEGACY", dir);
    FILE *lg = fopen(lgp, "r"); int legacy = lg != NULL; if (lg) fclose(lg);
    SWARG sw = { m, key, have_key, wdir, hdrs, legacy, &next_seg, &done_ct, &fail_ct, &logct, &tot_atomic, name, m->nsegs };
    pthread_t ths[6]; int nth = 0;
    for (int w = 0; w < 6; w++) {
        if (pthread_create(&ths[w], NULL, seg_worker, &sw) == 0) nth++;
    }
    for (int w = 0; w < nth; w++) pthread_join(ths[w], NULL);
    m->cur = done_ct;
    total = tot_atomic;
    broken = fail_ct > 0;
    if (fail_ct) dl_log("FAIL 段 x%d (%d/%d 成功)", fail_ct, done_ct, m->nsegs);

    out = fopen(part, "wb");
    if (!out) { dl_log("FAIL open %s", part); hist_add("✗ 文件打不开 %s", name); return; }
    if (m->hasmap && !m->enc) {   // fMP4 init 段在最前
        size_t mn = 0; char *mb = fetch_c(m->mapuri, hdrs, 30, &mn, NULL);
        if (mb) { fwrite(mb, 1, mn, out); total += mn; free(mb); }
    }
    {   // 按序拼合
        char sfp[900];
        for (int i = 0; i < m->nsegs; i++) {
            snprintf(sfp, sizeof(sfp), "%s/s%05d", wdir, i);
            FILE *si = fopen(sfp, "rb");
            if (!si) continue;   // 失败段跳过 (中断)
            char cp[65536]; size_t r;
            while ((r = fread(cp, 1, sizeof(cp), si)) > 0) fwrite(cp, 1, r, out);
            fclose(si); remove(sfp);
        }
    }
    fclose(out);
    rmdir(wdir);
    if (total == 0) { remove(part); dl_log("FAIL 0 字节 %s", url); hist_add("✗ 0字节 %s", url); return; }
    rename(part, path);
    g_flash_until = time(NULL) + 2;
    dl_log("DONE %s (%.1fMB, %d 段%s) ← %s", path, total / 1048576.0, m->nsegs, m->enc ? " 已解密" : "", url);

    // .ts -> .mp4: 纯 C 封装器(自研 TS demux + MP4 mux), worker 线程直跑
    char finalname[160]; snprintf(finalname, sizeof(finalname), "%s", name);
    const char *sttag = broken ? "⚠中断" : "✓";
    mux_lock();                     /* ★ v4.14.0 原子锁: 严格串行 (等前一个做完) */
    {
        size_t L = strlen(path);
        if (L > 3 && !strcmp(path + L - 3, ".ts")) {
            char mp4p[700];
            snprintf(mp4p, sizeof(mp4p), "%s", path);
            strcpy(mp4p + L - 3, ".mp4");
            dl_log("转封装开始: %s", path);
            if (ts2mp4_file(path, mp4p)) {
                remove(path);
                dl_log("MP4 %s", mp4p);
                char base[128];
                const char *nm2 = strrchr(mp4p, '/');
                snprintf(base, sizeof(base), "%s", nm2 ? nm2 + 1 : mp4p);
                snprintf(finalname, sizeof(finalname), "%s", base);
                sttag = "✓mp4";
            } else dl_log("MP4 封装失败, 保留 ts: %s", path);
        }
    }
    mux_unlock();
    {   char durs[24] = "-";
        if (g_mdur_ms >= 1000) { unsigned sec = (unsigned)(g_mdur_ms / 1000);
            if (sec >= 3600) snprintf(durs, sizeof(durs), "%u:%02u:%02u", sec / 3600, (sec / 60) % 60, sec % 60);
            else snprintf(durs, sizeof(durs), "%02u:%02u", sec / 60, sec % 60); }
        char vinfo[48] = "-";
        if (durs[0] != '-') snprintf(vinfo, sizeof(vinfo), "%s", durs);
        if (g_mw > 0 && g_mh > 0) {
            if (vinfo[0] == '-') snprintf(vinfo, sizeof(vinfo), "%dx%d", g_mw, g_mh);
            else { char t2[40]; snprintf(t2, sizeof(t2), "· %dx%d", g_mw, g_mh);
                   size_t ol = strlen(vinfo); snprintf(vinfo + ol, sizeof(vinfo) - ol, " %s", t2); }
        }
        hist_add("%s %s | %.1fMB | %d段%s | %s | %s", sttag, finalname, total / 1048576.0,
                 m->nsegs, m->enc ? " 密" : "", vinfo, url);
    }
}

// --- 队列 + 线程 ---
static void *dl_worker(void *arg) {
    (void)arg;
    pthread_mutex_lock(&g_dlm);
    for (;;) {
        while (g_jhead == g_jtail) pthread_cond_wait(&g_jcond, &g_dlm);
        if (g_jhead > g_jtail) {                 /* ★ v4.14.2 队列索引自愈: 防失控空转 */
            log_line("QUEUE 索引异常 jhead=%d > jtail=%d, 已复位", g_jhead, g_jtail);
            g_jhead = g_jtail;
            continue;
        }
        char job[1200];
        snprintf(job, sizeof(job), "%s", g_jobs[g_jhead % 16]);
        g_jhead++;
        {   /* ★ v4.14.2 诊断: 连续派发同一任务 = 有失控来源, 每 20 次记一条 */
            static char lastjob[1200]; static int same;
            if (lastjob[0] && !strcmp(lastjob, job)) {
                if ((++same % 20) == 0) log_line("REPEAT 同一任务连续第 %d 次 (jhead=%d jtail=%d)", same, g_jhead, g_jtail);
            } else { same = 0; snprintf(lastjob, sizeof(lastjob), "%s", job); }
        }
        if (!job[0]) { log_line("空任务, 跳过"); continue; }   /* ★ v4.14.4 */
        {   /* ★ v4.14.4: 同一 URL 已在下载中 -> 跳过队列重复项 (堵重复派发) */
            int dup = 0;
            for (int i = 0; i < g_ntask; i++)
                if (g_task[i] && g_task[i]->url[0] && !strcmp(g_task[i]->url, job)) { dup = 1; break; }
            if (dup) { log_line("任务已在下载中, 跳过队列重复项"); continue; }
        }
        g_dl_count++;                       /* ★ 与下方递减严格配对 */
        pthread_mutex_unlock(&g_dlm);
        do_download(job);
        pthread_mutex_lock(&g_dlm);
        g_dl_count--;                       /* ★ 无论 do_download 走哪条早退路径都释放 */
    }
    return NULL;
}

void dl_maybe_enqueue(const char *url, const char *reqbuf, size_t n) {
    if (bounded_str(reqbuf, n < 512 ? n : 512, "YSHG/")) return; // 自己的请求
    // ★ 本地回环代理: 真实上游地址在 parse?url=<百分号编码> 里
    if (strstr(url, "127.0.0.1") || strstr(url, "localhost")) {
        const char *p = strstr(url, "parse?url=");
        if (!p) { log_line("LOOP %s", url); return; }   // vid= 形式无法直接还原, 只记录
        char dec[1400];
        url_decode(p + 10, strlen(p + 10), dec, sizeof(dec));
        if (!dec[0]) return;
        log_line("PARSE %s", dec);
        if (strstr(dec, ".m3u8") || strstr(dec, "m3u8") || strstr(dec, "http")) {
            pthread_mutex_lock(&g_dlm);
            snprintf(g_cand, sizeof(g_cand), "%s", dec);
            g_ready = 1;
            int auto_on = g_auto;
            pthread_mutex_unlock(&g_dlm);
            char qk[1400]; snprintf(qk, sizeof(qk), "Q:%s", dec);
            cand_pl_set(dec);   /* ★ v4.14.7 喂播放列表候选表 */
            if (auto_on && seen_add(qk)) dl_push_job(dec);   // ★ 自动去重: 同一视频只入队一次
        }
        return;
    }
    pthread_mutex_lock(&g_hmu);
    size_t hn = 0;
    const char *end = bounded_str(reqbuf, n, "\r\n\r\n");
    if (end) hn = (size_t)(end - reqbuf);
    else hn = n < sizeof(g_hdrs) - 2 ? n : sizeof(g_hdrs) - 2;
    if (hn >= sizeof(g_hdrs)) hn = sizeof(g_hdrs) - 1;
    memcpy(g_hdrs, reqbuf, hn); g_hdrs[hn] = 0; g_hn = hn;
    pthread_mutex_unlock(&g_hmu);
    // v0.4: 只挂候选, 按钮控制; 长按切全自动
    pthread_mutex_lock(&g_dlm);
    snprintf(g_cand, sizeof(g_cand), "%s", url);
    g_ready = 1;
    int auto_on = g_auto;
    pthread_mutex_unlock(&g_dlm);
    cand_pl_set(url);
    log_line("CAND %s", url);
    if (auto_on) dl_push_job(url);
}

// 统一候选判定: 回环 parse?url= 解出真实地址; 直接 m3u8/mp4 也认
// ★ absoluteString 返回的是 NSString 对象, 必须先 UTF8String 再当 char* 用
static const char *ns2utf8(void *obj) {
    if (!obj) return NULL;
    return (const char *)((id (*)(id, SEL))oc_ms)(obj, oc_sel("UTF8String"));
}

static void dl_consider_url(const char *u) {
    if (!u || !*u) return;
    { char dk[1400]; snprintf(dk, sizeof(dk), "P:%s", u);
      if (!seen_add(dk)) return; }          // 同一播放地址只处理一次
    log_line("PLAYURL %s", u);
    char real[1400]; real[0] = 0;
    const char *p = strstr(u, "parse?url=");
    if (p) { url_decode(p + 10, strlen(p + 10), real, sizeof(real)); }
    else if (!strstr(u, "127.0.0.1") && !strstr(u, "localhost")) snprintf(real, sizeof(real), "%s", u);
    if (!real[0]) return;
    if (!strstr(real, "http")) return;
    pthread_mutex_lock(&g_dlm);
    snprintf(g_cand, sizeof(g_cand), "%s", real);
    g_ready = 1;
    int auto_on = g_auto;
    pthread_mutex_unlock(&g_dlm);
    cand_pl_set(real);
    log_line("CAND %s", real);
    if (auto_on) dl_push_job(real);
}

// 悬浮钮 tap: 把当前候选压队列
static void dl_grab_current(void) {
    char u[1200];
    pthread_mutex_lock(&g_dlm);
    int ok = g_ready && g_cand[0];
    if (ok) snprintf(u, sizeof(u), "%s", g_cand);
    /* ★ v4.14.7: 播放列表候选优先 —— 播放中分段请求持续覆盖 g_cand,
       原来点抓抓到的常是 .ts 分段 → "无分段"静默失败 = "点抓没反应" */
    if (g_cand_pl[0]) { snprintf(u, sizeof(u), "%s", g_cand_pl); ok = 1; }
    pthread_mutex_unlock(&g_dlm);
    if (!ok) { dl_log("无候选: 先在 app 里播一下要抓的视频"); return; }
    dl_log("GRAB %s", u);   /* ★ 点抓落点: 设备日志可核对抓到的是列表还是分段 */
    dl_push_job(u);
}

static void dl_push_job(const char *url) {
    if (!url || strlen(url) < 12 || !strstr(url, "http")) return;   // ★ 无效任务一律不进队列
    pthread_mutex_lock(&g_dlm);
    /* ★ v4.14.0: 同一 URL 已在下载 / 已在队列 -> 忽略重复抓取。
       两个 578MB 的同片任务同时收尾会并发进封装器 (全局状态互踩) = 崩溃。 */
    for (int i = 0; i < g_ntask; i++)
        if (g_task[i] && g_task[i]->url[0] && !strcmp(g_task[i]->url, url)) {
            pthread_mutex_unlock(&g_dlm);
            dl_log("已在下载中, 忽略重复抓取");
            return;
        }
    for (int j = g_jhead; j < g_jtail; j++)
        if (!strcmp(g_jobs[j % 16], url)) {
            pthread_mutex_unlock(&g_dlm);
            dl_log("已在队列中, 忽略重复抓取");
            return;
        }
    int full = (g_jtail - g_jhead) >= 16;
    if (!full) { snprintf(g_jobs[g_jtail % 16], 1200, "%s", url); g_jtail++;
                 g_flash_until = time(NULL) + 2;   /* ★ v4.14.7 入队即闪 ✓: 点抓立刻有反馈 */
                 pthread_cond_signal(&g_jcond); }
    pthread_mutex_unlock(&g_dlm);
    if (full) dl_log("队列满, 丢 %s", url);
    else dl_log("ENQ %s", url);
}

// ---- AVFoundation 播放地址捕获 ----
// video_player_avfoundation 用 AVPlayer 播放; 其网络加载在系统独立进程,
// 本进程 socket 钩子看不到。但 AVURLAsset/AVPlayerItem 对象在本进程创建 ——
// 精确替换其方法的 IMP 即可拿到真实播放 URL。
// ★ 教训: class_replaceMethod 在方法不存在时会"添加"; 对元类盲用它会把
//   实例方法污染进元类 → 方法表损坏 → lookUpImpOrForward 崩溃。
//   必须先 class_getClassMethod / class_getInstanceMethod 判存在, 再
//   method_getImplementation 取原函数 + method_setImplementation 替换。
extern void *class_getClassMethod(void *, void *);
extern void *class_getInstanceMethod(void *, void *);
extern void *method_getImplementation(void *);
extern void *method_setImplementation(void *, void *);
extern void *dispatch_semaphore_create(long);
extern long dispatch_semaphore_signal(void *);
extern long dispatch_semaphore_wait(void *, unsigned long long);

static void *g_av_o[8];
static int g_av_done;

static id av_call(int slot, id self, SEL cmd, id a, id b) {
    // 统一按 4 参调用: ARM64 上被调用方忽略多余寄存器参数,
    // 对 initWithURL: 这类 2 参方法同样安全, 免去签名分支。
    if (!g_av_o[slot]) return nil;
    return ((id (*)(id, SEL, id, id))g_av_o[slot])(self, cmd, a, b);
}

static void av_grab_headers(id opts) {
    // options 里可能带 AVURLAssetHTTPHeaderFieldsKey (NSDictionary)
    if (!opts || !oc_ms) return;
    id d = ((id (*)(id, SEL, id, id))oc_ms)(opts, oc_sel("objectForKey:"), ns_str("AVURLAssetHTTPHeaderFieldsKey"), Nil);
    if (!d) return;
    id keys = ((id (*)(id, SEL))oc_ms)(d, oc_sel("allKeys"));
    unsigned long n = keys ? ((unsigned long (*)(id, SEL))oc_ms)(keys, oc_sel("count")) : 0;
    if (!n) return;
    char buf[4096]; size_t off = 0; buf[0] = 0;
    for (unsigned long i = 0; i < n && off + 256 < sizeof(buf); i++) {
        id k = ((id (*)(id, SEL, unsigned long))oc_ms)(keys, oc_sel("objectAtIndex:"), i);
        id v = ((id (*)(id, SEL, id))oc_ms)(d, oc_sel("objectForKey:"), k);
        const char *ks = ns2utf8(k), *vs = ns2utf8(v);
        if (ks && vs) off += (size_t)snprintf(buf + off, sizeof(buf) - off, "%s: %s\n", ks, vs);
    }
    if (off) {
        pthread_mutex_lock(&g_hmu);
        snprintf(g_hdrs, sizeof(g_hdrs), "%s", buf);
        pthread_mutex_unlock(&g_hmu);
        log_line("AVHDR %zu 字节", off);
    }
}
static id g_av_slot0(id s, SEL c, id u, id o) { const char *p = ns2utf8(((id (*)(id, SEL))oc_ms)(u, oc_sel("absoluteString"))); if (p) { av_grab_headers(o); dl_consider_url(p); } return av_call(0, s, c, u, o); }
static id g_av_slot1(id s, SEL c, id u, id o) { const char *p = ns2utf8(((id (*)(id, SEL))oc_ms)(u, oc_sel("absoluteString"))); if (p) { av_grab_headers(o); dl_consider_url(p); } return av_call(1, s, c, u, o); }
static id g_av_slot2(id s, SEL c, id u, id o) { const char *p = ns2utf8(((id (*)(id, SEL))oc_ms)(u, oc_sel("absoluteString"))); if (p) dl_consider_url(p); return av_call(2, s, c, u, o); }
static id g_av_slot3(id s, SEL c, id u, id o) { const char *p = ns2utf8(((id (*)(id, SEL))oc_ms)(u, oc_sel("absoluteString"))); if (p) dl_consider_url(p); return av_call(3, s, c, u, o); }

// 存在才替换; 返回 1 成功
static int av_hook_one(int slot, const char *clsname, const char *selname, void *imp, int is_class) {
    void *cls = (void *)oc_getclass(clsname);
    if (!cls) return 0;
    void *sel = oc_sel(selname);
    void *m = is_class ? class_getClassMethod(cls, sel) : class_getInstanceMethod(cls, sel);
    if (!m) return 0;
    if (g_av_o[slot]) return 0;                        // 已装
    g_av_o[slot] = method_getImplementation(m);
    if (!g_av_o[slot]) return 0;                       // 没有原函数就绝不替换
    method_setImplementation(m, imp);
    log_line("AVHOOK %s[%s %s]", is_class ? "+" : "-", clsname, selname);
    return 1;
}

static id g_player;   /* 前置声明 (定义在后) */

/* ★ 扫窗口树找其它 AVPlayerLayer 并暂停它们的播放器
   (不 hook 任何方法: v4.10 的 -[AVPlayer play] 全局钩子崩过, 已弃用) */
static void pause_other_players(void) {
    if (!oc_ms) return;
    id app = ((id(*)(id, SEL))oc_ms)(oc_cls("UIApplication"), oc_sel("sharedApplication"));
    if (!app) return;
    id wins = ((id(*)(id, SEL))oc_ms)(app, oc_sel("windows"));
    unsigned long wn = wins ? ((unsigned long(*)(id, SEL))oc_ms)(wins, oc_sel("count")) : 0;
    id avl = oc_cls("AVPlayerLayer");
    int n = 0;
    for (unsigned long i = 0; i < wn; i++) {
        id w = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), i);
        if (!w) continue;
        id stack[512]; int sp = 0;
        stack[sp++] = w;
        while (sp > 0) {
            id v = stack[--sp];
            if (!v) continue;
            id lyr = ((id(*)(id, SEL))oc_ms)(v, oc_sel("layer"));
            if (lyr && avl && ((unsigned char(*)(id, SEL, id))oc_ms)(lyr, oc_sel("isKindOfClass:"), avl)) {
                id pl = ((id(*)(id, SEL))oc_ms)(lyr, oc_sel("player"));
                if (pl && pl != g_player) {
                    ((void(*)(id, SEL))oc_ms)(pl, oc_sel("pause"));
                    ((void(*)(id, SEL, float))oc_ms)(pl, oc_sel("setVolume:"), 0.0f);
                    n++;
                }
            }
            id subs = ((id(*)(id, SEL))oc_ms)(v, oc_sel("subviews"));
            unsigned long sn = subs ? ((unsigned long(*)(id, SEL))oc_ms)(subs, oc_sel("count")) : 0;
            for (unsigned long k = 0; k < sn && sp < 512; k++) {
                id sv = ((id(*)(id, SEL, unsigned long))oc_ms)(subs, oc_sel("objectAtIndex:"), k);
                if (sv) stack[sp++] = sv;
            }
        }
    }
    dl_log("其它播放器 %d 个已暂停 (窗口树扫描)", n);
}
static void dl_av_hook(void) {
    if (g_av_done || !oc_ms) return;
    if (!oc_getclass("AVURLAsset")) return;    // AVFoundation 懒加载, 出现后再装
    g_av_done = 1;
    av_hook_one(0, "AVURLAsset",   "URLAssetWithURL:options:", (void *)g_av_slot0, 1);
    av_hook_one(1, "AVURLAsset",   "initWithURL:options:",     (void *)g_av_slot1, 0);
    av_hook_one(2, "AVPlayerItem", "playerItemWithURL:",       (void *)g_av_slot2, 1);
    av_hook_one(3, "AVPlayerItem", "initWithURL:",             (void *)g_av_slot3, 0);
    dl_log("AV hook 完毕 (o0..o3 = %p %p %p %p)", g_av_o[0], g_av_o[1], g_av_o[2], g_av_o[3]);
}

/* ★ 个人标识 (成品包归属) */
const char *yshg_owner(void) { return "é¸¡å·´æ¯"; }   /* 鸡巴毛 */

void dl_init(void) {
    oc_ms          = (id (*)(id, SEL, ...))objc_msgSend;
    oc_getclass    = (Class (*)(const char *))objc_getClass;
    oc_sel         = (SEL (*)(const char *))sel_registerName;
    oc_allocpair   = (Class (*)(Class, const char *, size_t))objc_allocateClassPair;
    oc_addmethod   = (int (*)(Class, SEL, void *, const char *))class_addMethod;
    oc_register    = (void (*)(Class))objc_registerClassPair;
    dl_dsem_create = (id (*)(long))dispatch_semaphore_create;
    dl_dsem_signal = (long (*)(id))dispatch_semaphore_signal;
    dl_dsem_wait   = (long (*)(id, uint64_t))dispatch_semaphore_wait;
    dl_dtime       = (uint64_t (*)(uint64_t, uint64_t))dispatch_time;
    dl_cc          = (int (*)(uint32_t, uint32_t, uint32_t, const void *, size_t, const void *,
                              const void *, size_t, void *, size_t, size_t *))CCCrypt;
    log_line("DL extern: msgSend=%p getClass=%p sel=%p allocPair=%p addMethod=%p reg=%p sem=%p CCCrypt=%p",
             (void *)oc_ms, (void *)oc_getclass, (void *)oc_sel, (void *)oc_allocpair,
             (void *)oc_addmethod, (void *)oc_register, (void *)dl_dsem_create, (void *)dl_cc);
    if (!oc_ms || !oc_getclass || !oc_sel || !dl_dsem_create) { log_line("DL runtime API 缺失, 下载禁用"); return; }
    pthread_cond_init(&g_jcond, NULL);
    hist_load();
    log_line("DL: UI 驱动 = performSelectorOnMainThread (免 block/dispatch/dlsym)");

    // NSURLSession 也推迟到主线程首 tick 建 (dyld 早期建会话是闪退源之一)
    for (int w = 0; w < 2; w++) {
        pthread_t th;
        pthread_create(&th, NULL, dl_worker, NULL);
        pthread_detach(th);
        if (w == 0) g_worker_tid = th;
    }
    dl_log("DL: 2 下载线程就绪");
    ui_init();
    dl_log("v4.14.5 armed (队列+记录点播+代理回退+6并行+连接复用+abort黑匣子, max=%d)", DL_MAX);
}



// ================= v0.8 悬浮钮 (全部 UI 在主线程构建) =================
// 两次闪退教训:
//  1) dyld 早期(构造函数里)建 UIKit 对象 -> unrecognized selector
//  2) [UITapGestureRecognizer initWithTarget:action:] 直接发给类对象 -> 同样炸
//     (initWithTarget:action: 是实例方法, 必须先 alloc)
// 现在: 构造函数只做绑定+hook; 后台线程轮询到 app 就绪 -> performSelectorOnMainThread
// 到主线程一次性 UI 构建; 之后每拍同样回主线程刷新。
typedef struct { double x, y; } Pnt;
typedef struct { double x, y, w, h; } MyRect;
typedef struct { double w, h; } MySize;
/* UIKit 绘图 (加载期解析, 同 CMTime 套路) */
extern void UIGraphicsBeginImageContextWithOptions(MySize, unsigned char, double);
extern void UIGraphicsEndImageContext(void);
extern void *UIGraphicsGetImageFromCurrentImageContext(void);
extern void *UIGraphicsGetCurrentContext(void);
extern void CGContextSetFillColorWithColor(void *, void *);
extern void CGContextFillEllipseInRect(void *, MyRect);
extern void CGContextSetShadowWithColor(void *, Pnt, double, void *);


static id g_btn, g_uideleg;
static volatile int g_uibuilt;

static id rgba(double r, double g, double b, double a) {
    return ((id(*)(id, SEL, double, double, double, double))oc_ms)(oc_cls("UIColor"),
            oc_sel("colorWithRed:green:blue:alpha:"), r, g, b, a);
}
static id g_btn_titleLabel(id btn) {
    return btn ? ((id (*)(id, SEL))oc_ms)(btn, oc_sel("titleLabel")) : NULL;
}
static void set_btn_style(const char *txt, double r, double g, double b) {
    if (!g_btn) return;
    /* ★ v4.14.6: 状态未变直接跳过 —— tick 每秒重设背景/标题/字体全套,
       空闲时每拍白白创建 UIColor + UIFont 对象; 文本或任一颜色变了才走全套 */
    static char last_txt[64]; static double last_r = -1.0, last_g = -1.0, last_b = -1.0;
    if (txt && !strcmp(txt, last_txt) && r == last_r && g == last_g && b == last_b) return;
    if (txt) { snprintf(last_txt, sizeof last_txt, "%s", txt); last_r = r; last_g = g; last_b = b; }
    ((void(*)(id, SEL, id))oc_ms)(g_btn, oc_sel("setBackgroundColor:"), rgba(r, g, b, 0.92));
    ((void(*)(id, SEL, id, unsigned long))oc_ms)(g_btn, oc_sel("setTitle:forState:"), ns_str(txt), 0);
    ((void(*)(id, SEL, id, unsigned long))oc_ms)(g_btn, oc_sel("setTitleColor:forState:"), rgba(1, 1, 1, 1), 0);
    // 进度文本("↓25/48")比单字长, 用小号字并允许缩排, 否则两位数显示不全
    double fs = strstr(txt, "/") ? 9.0 : 13.0;
    id tl = g_btn_titleLabel(g_btn);
    if (!tl) return;
    id font = ((id (*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("boldSystemFontOfSize:"), fs);
    if (font) ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setFont:"), font);
    ((void(*)(id, SEL, unsigned char))oc_ms)(tl, oc_sel("setAdjustsFontSizeToFitWidth:"), 1);
    ((void(*)(id, SEL, double))oc_ms)(tl, oc_sel("setMinimumScaleFactor:"), 0.5);
}
static void imp_tap(void *self, void *c, void *gr) { (void)self; (void)c; (void)gr; dl_grab_current(); }
static void imp_long(void *self, void *c, void *gr) {
    (void)self; (void)c;
    unsigned long st = ((unsigned long(*)(id, SEL))oc_ms)((id)gr, oc_sel("state"));
    if (st != 1) return;
    pthread_mutex_lock(&g_dlm);
    g_auto = !g_auto;
    int a = g_auto;
    pthread_mutex_unlock(&g_dlm);
    dl_log("AUTO %s", a ? "ON(播了就下)" : "OFF(只按按钮)");
}
static void imp_pan(void *self, void *c, void *gr) {
    (void)self; (void)c;
    if (!g_btn) return;
    Pnt t = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("translationInView:"), nil);
    Pnt ctr = ((Pnt(*)(id, SEL))oc_ms)(g_btn, oc_sel("center"));
    Pnt n; n.x = ctr.x + t.x; n.y = ctr.y + t.y;
    ((void(*)(id, SEL, Pnt))oc_ms)(g_btn, oc_sel("setCenter:"), n);
    Pnt z; z.x = 0; z.y = 0;
    ((void(*)(id, SEL, Pnt, id))oc_ms)((id)gr, oc_sel("setTranslation:inView:"), z, nil);
}
static void tick_fn(void);
static void imp_tick(void *self, void *c, void *o) { (void)self; (void)c; (void)o; tick_fn(); }
static void imp_tick_build(void *self, void *c, void *o) { (void)self; (void)c; (void)o; ui_build(); }

// ---- v3.6 历史面板 (双击钮) — v3.9 行可点播 ----
static id g_hpanel, g_htv, g_player, g_playvc, g_playlayer, g_playbtn, g_seeksl, g_seektlabel;
static void *g_pgtask[8]; static id g_pglabel[8], g_pgbar[8]; static int g_npg;
static id g_ppbtn, g_spdbtn, g_volsl;
static float g_rate = 1.0f; static int g_spdi = 1;
static volatile int g_seeking;
static float g_vol = 1.0f;
static int g_hshown = -1;
static id g_title, g_tcur, g_tdur, g_volicon, g_barbot, g_bartop, g_tapview, g_spdlbl;
static volatile int g_ctlvis = 1;
static time_t g_ctlshow;
static void player_ctl_apply(double a);
static void ctl_touch(void);
static long imp_gesdel(void *self, void *c, void *gr, void *touch);
static id mk_grad(float w, float y, float h);
static void player_ctl_apply(double a) {
    id *views[] = { g_seeksl, g_tcur, g_tdur, g_ppbtn, g_spdbtn, g_volsl, g_volicon, g_playbtn, g_title };
    for (unsigned k = 0; k < sizeof(views)/sizeof(views[0]); k++)
        if (views[k]) {
            ((void(*)(id, SEL, double))oc_ms)(views[k], oc_sel("setAlpha:"), a);
            /* 隐藏 = alpha 0 + hidden 1 + 禁触摸: hidden 视图绝不参与 hit-test, 不再吃点击 */
            ((void(*)(id, SEL, unsigned char))oc_ms)(views[k], oc_sel("setHidden:"), a < 0.5f);
            ((void(*)(id, SEL, unsigned char))oc_ms)(views[k], oc_sel("setUserInteractionEnabled:"), a > 0.5f);
        }
    /* ★ 渐变是 CALayer: 只有 setOpacity:, 调 setAlpha: 会 doesNotRecognizeSelector → NSException */
    if (g_barbot) ((void(*)(id, SEL, double))oc_ms)(g_barbot, oc_sel("setOpacity:"), a);
    if (g_bartop) ((void(*)(id, SEL, double))oc_ms)(g_bartop, oc_sel("setOpacity:"), a);
    g_ctlvis = a > 0.5f;
}
static id sym_img(const char *name) {
    return ((id(*)(id, SEL, id))oc_ms)(oc_cls("UIImage"), oc_sel("systemImageNamed:"), ns_str(name));
}
/* 指定点号的 SF 图标 */
static id sym_img_sz(const char *name, double pt) {
    id im = sym_img(name);
    if (!im) return NULL;
    id cfg = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIImageSymbolConfiguration"), oc_sel("configurationWithPointSize:"), pt);
    if (!cfg) return im;
    id im2 = ((id(*)(id, SEL, id))oc_ms)(im, oc_sel("imageWithConfiguration:"), cfg);
    return im2 ? im2 : im;
}
/* 统一图标按钮: 纯 SF 图标 + 半透明白底 + 圆角; 绝不设 title (title+image 会同时绘制) */
static id mk_icon_btn(MyRect f, const char *sym, double radius, double bg, double pt) {
    id b = ((id(*)(id, SEL))oc_ms)(oc_cls("UIButton"), oc_sel("alloc"));
    if (b) b = ((id(*)(id, SEL, MyRect))oc_ms)(b, oc_sel("initWithFrame:"), f);
    if (!b) return NULL;
    id im = sym_img_sz(sym, pt);
    if (im) ((void(*)(id, SEL, id, unsigned long))oc_ms)(b, oc_sel("setImage:forState:"), im, 0);
    ((void(*)(id, SEL, id))oc_ms)(b, oc_sel("setTintColor:"), rgba(1, 1, 1, 1));
    ((void(*)(id, SEL, id))oc_ms)(b, oc_sel("setBackgroundColor:"), rgba(1, 1, 1, bg));
    id l = ((id(*)(id, SEL))oc_ms)(b, oc_sel("layer"));
    if (l) ((void(*)(id, SEL, double))oc_ms)(l, oc_sel("setCornerRadius:"), radius);
    return b;
}
/* 倍速文本: 1x / 0.75x / 1.25x */
static void rate_txt(char *out, size_t n, float r) { snprintf(out, n, "%.3gx", r); }
/* 滑块统一样式: SF 圆点做圆润拇指 + 细轨 */
/* ── 自绘拇指: 白圆 + 1px 下柔影 (边缘干净, 比 SF 图标有体积感) ── */
static id mk_knob(double pt) {
    MySize sz = { pt, pt };
    UIGraphicsBeginImageContextWithOptions(sz, 0, 0.0);
    void *ctx = UIGraphicsGetCurrentContext();
    id img = NULL;
    if (ctx) {
        id cw = ((id(*)(id, SEL))oc_ms)(oc_cls("UIColor"), oc_sel("whiteColor"));
        if (cw) {
            void *cg = ((id(*)(id, SEL))oc_ms)(cw, oc_sel("CGColor"));
            Pnt off = { 0.0, 1.0 };
            CGContextSetShadowWithColor(ctx, off, 2.5, cg);
            CGContextSetFillColorWithColor(ctx, cg);
        }
        MyRect e = { 1.5, 1.5, pt - 3.0, pt - 3.0 };
        CGContextFillEllipseInRect(ctx, e);
        img = UIGraphicsGetImageFromCurrentImageContext();
    }
    UIGraphicsEndImageContext();
    return img;
}
static void style_slider(id sl, const char *thumb_sym, double pt,
                         double minr, double ming, double minb,
                         double maxr, double maxg, double maxb) {
    if (!sl) return;
    id tim = mk_knob(pt);          /* 自绘白圆点 (首选) */
    if (!tim) {                    /* 回退: SF 图标染白 */
        tim = sym_img_sz(thumb_sym, pt);
        if (tim) { id tw = ((id(*)(id, SEL, id, long))oc_ms)(tim, oc_sel("imageWithTintColor:renderingMode:"), rgba(1, 1, 1, 1), 1); if (tw) tim = tw; }
    }
    if (tim) {
        ((void(*)(id, SEL, id, unsigned long))oc_ms)(sl, oc_sel("setThumbImage:forState:"), tim, 0);
        ((void(*)(id, SEL, id, unsigned long))oc_ms)(sl, oc_sel("setThumbImage:forState:"), tim, 1);
    }
    ((void(*)(id, SEL, id))oc_ms)(sl, oc_sel("setMinimumTrackTintColor:"), rgba(minr, ming, minb, 1));
    ((void(*)(id, SEL, id))oc_ms)(sl, oc_sel("setMaximumTrackTintColor:"), rgba(maxr, maxg, maxb, 0.30));
    ((void(*)(id, SEL, id))oc_ms)(sl, oc_sel("setThumbTintColor:"), rgba(1, 1, 1, 1));
}
typedef struct { double t, l, b, r; } MyEdge;
static void ctl_touch(void) {
    g_ctlshow = time(NULL);
    if (!g_ctlvis) player_ctl_apply(1.0f);
}
static void imp_videotap(void *self, void *c, void *gr) {
    (void)self; (void)c; (void)gr;
    if (!oc_ms || !g_playvc) return;
    int pre = g_ctlvis;
    if (pre) { player_ctl_apply(0.0f); dl_log("VTOAP -> 隐藏"); }
    else {
        ctl_touch();
        double sa = -1; unsigned char sh = 1, en = 0;
        if (g_seeksl) {
            sa = ((double(*)(id, SEL))oc_ms)(g_seeksl, oc_sel("alpha"));
            sh = ((unsigned char(*)(id, SEL))oc_ms)(g_seeksl, oc_sel("isHidden"));
            en = ((unsigned char(*)(id, SEL))oc_ms)(g_seeksl, oc_sel("isUserInteractionEnabled"));
        }
        dl_log("VTOAP -> 显示 sl_a=%.2f hid=%d en=%d sup=%d", sa, sh, en, g_seeksl ? ((id(*)(id, SEL))oc_ms)(g_seeksl, oc_sel("superview")) != NULL : -1);
    }
}
static long imp_gesdel(void *self, void *c, void *gr, void *touch) {
    (void)self; (void)c; (void)gr;
    long r = 1;
    id tv = touch ? ((id(*)(id, SEL))oc_ms)((id)touch, oc_sel("view")) : NULL;
    if (tv) {
        id refs[] = { g_seeksl, g_ppbtn, g_spdbtn, g_volsl, g_playbtn };
        for (unsigned k = 0; k < sizeof(refs)/sizeof(refs[0]); k++)
            if (refs[k] && (tv == refs[k] || ((unsigned char(*)(id, SEL, id))oc_ms)(tv, oc_sel("isDescendantOfView:"), refs[k]))) { r = 0; break; }
    }
    if (!r) { const char *cn = tv ? ((const char *(*)(id))object_getClass)((id)object_getClass(tv)) : "nil";
              const char *gn = gr ? ((const char *(*)(id))object_getClass)((id)object_getClass((id)gr)) : "?";
              dl_log("GEST 拒绝 ges=%.24s t=%.28s", gn, cn); }
    return r;
}
static id mk_grad(float w, float y, float h) {
    id gl = ((id(*)(id, SEL))oc_ms)(oc_cls("CAGradientLayer"), oc_sel("alloc"));
    if (gl) gl = ((id(*)(id, SEL))oc_ms)(gl, oc_sel("init"));
    if (!gl) return NULL;
    MyRect gf = { 0, y, w, h };
    ((void(*)(id, SEL, MyRect))oc_ms)(gl, oc_sel("setFrame:"), gf);
    id c1 = rgba(0, 0, 0, 0.55), c2 = rgba(0, 0, 0, 0.0);
    id g1 = ((id(*)(id, SEL))oc_ms)(c1, oc_sel("CGColor"));
    id g2 = ((id(*)(id, SEL))oc_ms)(c2, oc_sel("CGColor"));
    id arr = ((id(*)(id, SEL, id, id, void *))oc_ms)(oc_cls("NSArray"), oc_sel("arrayWithObjects:"), g1, g2, NULL);
    ((void(*)(id, SEL, id))oc_ms)(gl, oc_sel("setColors:"), arr);
    Pnt p1 = { 0, 0 }, p2 = { 0, 1 };
    ((void(*)(id, SEL, Pnt))oc_ms)(gl, oc_sel("setStartPoint:"), p1);
    ((void(*)(id, SEL, Pnt))oc_ms)(gl, oc_sel("setEndPoint:"), p2);
    return gl;
}
static void fmt_mmss(double s, char *out, size_t n) {
    int sec = (int)(s < 0 ? 0 : s);
    snprintf(out, n, "%02d:%02d", sec / 60, sec % 60);
}
static void play_relayout(void);
static void imp_rot(void *self, void *c, void *n2) { (void)self; (void)c; (void)n2; play_relayout(); }

static void play_relayout(void) {
    if (!g_playvc || !oc_ms) return;
    id wv = ((id(*)(id, SEL))oc_ms)(g_playvc, oc_sel("view"));
    if (!wv) return;
    id wl = ((id(*)(id, SEL))oc_ms)(wv, oc_sel("window"));
    if (!wl) return;
    MyRect wb = ((MyRect(*)(id, SEL))oc_ms)(wl, oc_sel("bounds"));
    if (g_playlayer) ((void(*)(id, SEL, MyRect))oc_ms)(g_playlayer, oc_sel("setFrame:"), wb);
    if (g_tapview) ((void(*)(id, SEL, MyRect))oc_ms)(g_tapview, oc_sel("setFrame:"), wb);
    if (g_bartop) ((void(*)(id, SEL, MyRect))oc_ms)(g_bartop, oc_sel("setFrame:"), (MyRect){ 0, 0, wb.w, 92 });
    if (g_barbot) ((void(*)(id, SEL, MyRect))oc_ms)(g_barbot, oc_sel("setFrame:"), (MyRect){ 0, wb.h - 190, wb.w, 190 });
    if (g_title) ((void(*)(id, SEL, MyRect))oc_ms)(g_title, oc_sel("setFrame:"), (MyRect){ 20, 52, wb.w - 86, 20 });
    if (g_playbtn) ((void(*)(id, SEL, MyRect))oc_ms)(g_playbtn, oc_sel("setFrame:"), (MyRect){ wb.w - 54, 46, 34, 34 });
    if (g_tcur) ((void(*)(id, SEL, MyRect))oc_ms)(g_tcur, oc_sel("setFrame:"), (MyRect){ 18, wb.h - 113, 80, 15 });
    if (g_tdur) ((void(*)(id, SEL, MyRect))oc_ms)(g_tdur, oc_sel("setFrame:"), (MyRect){ wb.w - 98, wb.h - 113, 80, 15 });
    if (g_seeksl) ((void(*)(id, SEL, MyRect))oc_ms)(g_seeksl, oc_sel("setFrame:"), (MyRect){ 16, wb.h - 92, wb.w - 32, 26 });
    if (g_ppbtn) ((void(*)(id, SEL, MyRect))oc_ms)(g_ppbtn, oc_sel("setFrame:"), (MyRect){ 16, wb.h - 152, 58, 44 });
    if (g_spdbtn) ((void(*)(id, SEL, MyRect))oc_ms)(g_spdbtn, oc_sel("setFrame:"), (MyRect){ 82, wb.h - 152, 88, 44 });
    if (g_volicon) ((void(*)(id, SEL, MyRect))oc_ms)(g_volicon, oc_sel("setFrame:"), (MyRect){ wb.w - 152, wb.h - 143, 24, 24 });
    if (g_volsl) ((void(*)(id, SEL, MyRect))oc_ms)(g_volsl, oc_sel("setFrame:"), (MyRect){ wb.w - 124, wb.h - 148, 108, 30 });
}
static void hist_play_file(const char *path) {
    if (!oc_ms) return;
    id app = ((id(*)(id, SEL))oc_ms)(oc_cls("UIApplication"), oc_sel("sharedApplication"));
    if (!app) return;
    id wins = ((id(*)(id, SEL))oc_ms)(app, oc_sel("windows"));
    unsigned long wn = wins ? ((unsigned long(*)(id, SEL))oc_ms)(wins, oc_sel("count")) : 0;
    id win = NULL;
    for (unsigned long i = wn; i > 0; i--) {
        id w = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), i - 1);
        if (((unsigned char(*)(id, SEL))oc_ms)(w, oc_sel("isKeyWindow"))) { win = w; break; }
    }
    if (!win && wn) win = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), 0);
    if (!win) return;
    id rootvc = ((id(*)(id, SEL))oc_ms)(win, oc_sel("rootViewController"));
    if (!rootvc) return;
    id url = ((id(*)(id, SEL, id))oc_ms)(oc_cls("NSURL"), oc_sel("fileURLWithPath:"), ns_str(path));
    id player = url ? ((id(*)(id, SEL, id))oc_ms)(oc_cls("AVPlayer"), oc_sel("playerWithURL:"), url) : NULL;
    if (!player) { dl_log("记录播放: AVPlayer 建不出来 %s", path); return; }
    {
        id item = ((id(*)(id, SEL))oc_ms)(player, oc_sel("currentItem"));
        if (item) ((void(*)(id, SEL, id))oc_ms)(item, oc_sel("setAudioTimePitchAlgorithm:"), ns_str("AVAudioTimePitchAlgorithmSpectral"));
        ((void(*)(id, SEL, float))oc_ms)(player, oc_sel("setVolume:"), g_vol);
        {   /* 初始也建一次 mix, 保证后续音量有效 */
            id tr0 = ((id(*)(id, SEL))oc_ms)(player, oc_sel("currentItem"));
            if (tr0) {
                id as0 = ((id(*)(id, SEL))oc_ms)(tr0, oc_sel("asset"));
                id tk0 = as0 ? ((id(*)(id, SEL, id))oc_ms)(as0, oc_sel("tracksWithMediaType:"), ns_str("soun")) : NULL;
                unsigned long tn0 = tk0 ? ((unsigned long(*)(id, SEL))oc_ms)(tk0, oc_sel("count")) : 0;
                if (tn0) {
                    id mx0 = ((id(*)(id, SEL))oc_ms)(oc_cls("AVMutableAudioMix"), oc_sel("audioMix"));
                    id pa0 = ((id(*)(id, SEL))oc_ms)(oc_cls("NSMutableArray"), oc_sel("array"));
                    if (mx0 && pa0) {
                        for (unsigned long k = 0; k < tn0; k++) {
                            id trk = ((id(*)(id, SEL, unsigned long))oc_ms)(tk0, oc_sel("objectAtIndex:"), k);
                            id ap0 = trk ? ((id(*)(id, SEL, id))oc_ms)(oc_cls("AVMutableAudioMixInputParameters"), oc_sel("audioMixInputParametersWithTrack:"), trk) : NULL;
                            if (!ap0) continue;
                            CMTime z0 = { 0, 1, 1, 0, 0 };
                            ((void(*)(id, SEL, float, CMTime))oc_ms)(ap0, oc_sel("setVolume:atTime:"), g_vol, z0);
                            ((void(*)(id, SEL, id))oc_ms)(pa0, oc_sel("addObject:"), ap0);
                        }
                        ((void(*)(id, SEL, id))oc_ms)(mx0, oc_sel("setInputParameters:"), pa0);
                        ((void(*)(id, SEL, id))oc_ms)(tr0, oc_sel("setAudioMix:"), mx0);
                        dl_log("VOL 初始 %.2f (音轨 %lu 条)", g_vol, tn0);
                    }
                } else {
                    dl_log("VOL 初始: 该文件无音轨");
                }
            }
        }
        ((void(*)(id, SEL, float))oc_ms)(player, oc_sel("setDefaultRate:"), g_rate);
    }
    id vc = ((id(*)(id, SEL))oc_ms)(oc_cls("UIViewController"), oc_sel("alloc"));
    if (vc) vc = ((id(*)(id, SEL))oc_ms)(vc, oc_sel("init"));
    if (!vc) return;
    id v = ((id(*)(id, SEL))oc_ms)(vc, oc_sel("view"));
    ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("setBackgroundColor:"), rgba(0, 0, 0, 1));
    MyRect wb = ((MyRect(*)(id, SEL))oc_ms)(win, oc_sel("bounds"));
    id layer = ((id(*)(id, SEL, id))oc_ms)(oc_cls("AVPlayerLayer"), oc_sel("playerLayerWithPlayer:"), player);
    ((void(*)(id, SEL, MyRect))oc_ms)(layer, oc_sel("setFrame:"), wb);
    id vlay = ((id(*)(id, SEL))oc_ms)(v, oc_sel("layer"));
    ((id(*)(id, SEL, id))oc_ms)(vlay, oc_sel("addSublayer:"), layer);
    id nctr = ((id(*)(id, SEL))oc_ms)(oc_cls("NSNotificationCenter"), oc_sel("defaultCenter"));
    if (nctr) ((void(*)(id, SEL, id, SEL, id, id))oc_ms)(nctr, oc_sel("addObserver:selector:name:object:"),
        g_uideleg, oc_sel("yshgRot:"), ns_str("UIDeviceOrientationDidChangeNotification"), Nil);
    g_bartop = mk_grad(wb.w, 0, 92);           if (g_bartop) ((id(*)(id, SEL, id))oc_ms)(vlay, oc_sel("addSublayer:"), g_bartop);
    g_barbot = mk_grad(wb.w, wb.h - 190, 190); if (g_barbot) ((id(*)(id, SEL, id))oc_ms)(vlay, oc_sel("addSublayer:"), g_barbot);
    /* v4.10: 单一点击路径 = 下面挂 v 的手势(委托只放行空白区); 全屏按钮已移除(双路径互相踩) */
    {   /* v 级手势备用路径: 与 tapview 按钮双保险, 去抖防双触发 */
        id tg3 = ((id(*)(id, SEL))oc_ms)(oc_cls("UITapGestureRecognizer"), oc_sel("alloc"));
        if (tg3) { tg3 = ((id(*)(id, SEL, id, SEL))oc_ms)(tg3, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgVideotap:"));
                   ((void(*)(id, SEL, id))oc_ms)(tg3, oc_sel("setDelegate:"), g_uideleg);
                   ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addGestureRecognizer:"), tg3); objc_retain(tg3); }
    }
    g_ctlshow = time(NULL);  /* 开屏给满 3s 再自动隐藏 */
    /* ── 顶栏: 文件名 ── */
    id tl2 = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
    MyRect tf3 = { 20, 52, wb.w - 86, 20 };
    if (tl2) tl2 = ((id(*)(id, SEL, MyRect))oc_ms)(tl2, oc_sel("initWithFrame:"), tf3);
    if (tl2) {
        const char *bn = strrchr(path, '/'); bn = bn ? bn + 1 : path;
        ((void(*)(id, SEL, id))oc_ms)(tl2, oc_sel("setText:"), ns_str(bn));
        ((void(*)(id, SEL, id))oc_ms)(tl2, oc_sel("setTextColor:"), rgba(1, 1, 1, 0.94));
        id f0 = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("systemFontOfSize:"), 12.5);
        if (f0) ((void(*)(id, SEL, id))oc_ms)(tl2, oc_sel("setFont:"), f0);
        ((void(*)(id, SEL, unsigned char))oc_ms)(tl2, oc_sel("setUserInteractionEnabled:"), 0);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), tl2);
        g_title = (id)objc_retain(tl2);
    }
    /* ── 圆形关闭钮 (纯 SF xmark) ── */
    id cb = mk_icon_btn((MyRect){ wb.w - 54, 46, 34, 34 }, "xmark", 17.0, 0.16, 12.0);
    if (cb) {
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(cb, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgPlayClose:"), 64);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), cb);
        g_playbtn = (id)objc_retain(cb);
    }
    /* ── 时间标签: 进度条两端 ── */
    id t1 = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
    if (t1) t1 = ((id(*)(id, SEL, MyRect))oc_ms)(t1, oc_sel("initWithFrame:"), (MyRect){ 18, wb.h - 113, 80, 15 });
    if (t1) {
        ((void(*)(id, SEL, id))oc_ms)(t1, oc_sel("setText:"), ns_str("00:00"));
        ((void(*)(id, SEL, id))oc_ms)(t1, oc_sel("setTextColor:"), rgba(1, 1, 1, 0.72));
        id f8 = ((id(*)(id, SEL, id, double))oc_ms)(oc_cls("UIFont"), oc_sel("fontWithName:size:"), ns_str("Menlo-Regular"), 10.5);
        if (f8) ((void(*)(id, SEL, id))oc_ms)(t1, oc_sel("setFont:"), f8);
        ((void(*)(id, SEL, unsigned char))oc_ms)(t1, oc_sel("setUserInteractionEnabled:"), 0);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), t1);
        g_tcur = (id)objc_retain(t1);
    }
    id t2 = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
    if (t2) t2 = ((id(*)(id, SEL, MyRect))oc_ms)(t2, oc_sel("initWithFrame:"), (MyRect){ wb.w - 98, wb.h - 113, 80, 15 });
    if (t2) {
        ((void(*)(id, SEL, id))oc_ms)(t2, oc_sel("setText:"), ns_str("00:00"));
        ((void(*)(id, SEL, id))oc_ms)(t2, oc_sel("setTextColor:"), rgba(1, 1, 1, 0.72));
        id f8 = ((id(*)(id, SEL, id, double))oc_ms)(oc_cls("UIFont"), oc_sel("fontWithName:size:"), ns_str("Menlo-Regular"), 10.5);
        if (f8) ((void(*)(id, SEL, id))oc_ms)(t2, oc_sel("setFont:"), f8);
        ((void(*)(id, SEL, long))oc_ms)(t2, oc_sel("setTextAlignment:"), 2);
        ((void(*)(id, SEL, unsigned char))oc_ms)(t2, oc_sel("setUserInteractionEnabled:"), 0);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), t2);
        g_tdur = (id)objc_retain(t2);
    }
    /* ── 进度条 ── */
    id sl = ((id(*)(id, SEL))oc_ms)(oc_cls("UISlider"), oc_sel("alloc"));
    if (sl) sl = ((id(*)(id, SEL, MyRect))oc_ms)(sl, oc_sel("initWithFrame:"), (MyRect){ 16, wb.h - 92, wb.w - 32, 26 });
    if (sl) {
        style_slider(sl, "circle.fill", 18.0, 0.32, 0.85, 0.55, 1, 1, 1);
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(sl, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgSeekDown:"), 1);
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(sl, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgSeekChg:"), 4096);
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(sl, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgSeekUp:"), 320);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), sl);
        g_seeksl = (id)objc_retain(sl);
    }
    /* ── 控制行: 播放/暂停 · 倍速 ── */
    id pb = mk_icon_btn((MyRect){ 16, wb.h - 152, 58, 44 }, "pause.fill", 12.0, 0.16, 19.0);
    if (pb) {
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(pb, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgPlayPause:"), 64);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), pb);
        g_ppbtn = (id)objc_retain(pb);
    }
    id sb = mk_icon_btn((MyRect){ 82, wb.h - 152, 88, 44 }, "", 12.0, 0.16, 15.0);
    if (sb) {
        /* 图标 + 文字 = 两个独立子视图, 各占固定帧 —— 几何上永不相交 */
        id siv = ((id(*)(id, SEL))oc_ms)(oc_cls("UIImageView"), oc_sel("alloc"));
        if (siv) siv = ((id(*)(id, SEL, MyRect))oc_ms)(siv, oc_sel("initWithFrame:"), (MyRect){ 13, 12, 22, 22 });
        if (siv) {
            id sim = sym_img_sz("speedometer", 15.0);
            if (sim) ((void(*)(id, SEL, id))oc_ms)(siv, oc_sel("setImage:"), sim);
            ((void(*)(id, SEL, id))oc_ms)(siv, oc_sel("setTintColor:"), rgba(1, 1, 1, 0.92));
            ((void(*)(id, SEL, unsigned char))oc_ms)(siv, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(sb, oc_sel("addSubview:"), siv);
        }
        id rl = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (rl) rl = ((id(*)(id, SEL, MyRect))oc_ms)(rl, oc_sel("initWithFrame:"), (MyRect){ 40, 12, 44, 20 });
        if (rl) {
            char t3[16]; rate_txt(t3, sizeof(t3), g_rate);
            ((void(*)(id, SEL, id))oc_ms)(rl, oc_sel("setText:"), ns_str(t3));
            ((void(*)(id, SEL, id))oc_ms)(rl, oc_sel("setTextColor:"), rgba(1, 1, 1, 1));
            id f9 = ((id(*)(id, SEL, id, double))oc_ms)(oc_cls("UIFont"), oc_sel("fontWithName:size:"), ns_str("Menlo-Bold"), 11.5);
            if (f9) ((void(*)(id, SEL, id))oc_ms)(rl, oc_sel("setFont:"), f9);
            ((void(*)(id, SEL, long))oc_ms)(rl, oc_sel("setTextAlignment:"), 0);
            ((void(*)(id, SEL, unsigned char))oc_ms)(rl, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(sb, oc_sel("addSubview:"), rl);
            g_spdlbl = (id)objc_retain(rl);
        }
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(sb, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgSpeed:"), 64);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), sb);
        g_spdbtn = (id)objc_retain(sb);
    }
    /* ── 音量: SF 图标 + 细条 ── */
    id vi = ((id(*)(id, SEL))oc_ms)(oc_cls("UIImageView"), oc_sel("alloc"));
    if (vi) vi = ((id(*)(id, SEL, MyRect))oc_ms)(vi, oc_sel("initWithFrame:"), (MyRect){ wb.w - 152, wb.h - 143, 24, 24 });
    if (vi) {
        id vim = sym_img_sz("speaker.wave.2.circle.fill", 20.0);
        if (vim) ((void(*)(id, SEL, id))oc_ms)(vi, oc_sel("setImage:"), vim);
        ((void(*)(id, SEL, id))oc_ms)(vi, oc_sel("setTintColor:"), rgba(1, 1, 1, 0.85));
        ((void(*)(id, SEL, unsigned char))oc_ms)(vi, oc_sel("setUserInteractionEnabled:"), 0);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), vi);
        g_volicon = (id)objc_retain(vi);
    }
    id vs = ((id(*)(id, SEL))oc_ms)(oc_cls("UISlider"), oc_sel("alloc"));
    if (vs) vs = ((id(*)(id, SEL, MyRect))oc_ms)(vs, oc_sel("initWithFrame:"), (MyRect){ wb.w - 124, wb.h - 147, 108, 26 });
    if (vs) {
        ((void(*)(id, SEL, float))oc_ms)(vs, oc_sel("setValue:"), 1.0f);
        style_slider(vs, "circle.fill", 14.0, 1, 1, 1, 1, 1, 1);
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(vs, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgVolChg:"), 4096);
        ((void(*)(id, SEL, id))oc_ms)(v, oc_sel("addSubview:"), vs);
        g_volsl = (id)objc_retain(vs);
    }
    if (g_hpanel) ((void(*)(id, SEL, unsigned char))oc_ms)(g_hpanel, oc_sel("setHidden:"), 1);
    if (g_btn) ((void(*)(id, SEL, unsigned char))oc_ms)(g_btn, oc_sel("setHidden:"), 1);
    ctl_touch();
    ((void(*)(id, SEL, unsigned long))oc_ms)(vc, oc_sel("setModalPresentationStyle:"), 0);
    ((void(*)(id, SEL, id, unsigned char, id))oc_ms)(rootvc, oc_sel("presentViewController:animated:completion:"), vc, 0, Nil);
    ((void(*)(id, SEL))oc_ms)(player, oc_sel("play"));
    g_player = (id)objc_retain(player);
    /* ★ 暂停其它播放器: 它们会与我们的播放器并存, 抢占音频输出
       (证据: 音量回读 0.00 + muted=1 却仍有声音 → 声源不是我们) */
    pause_other_players();
    g_playvc = (id)objc_retain(vc);
    g_playlayer = (id)objc_retain(layer);
    dl_log("记录播放: %s", path);
}

static void imp_seekdown(void *self, void *c, void *b) { (void)self; (void)c; (void)b; g_seeking = 1; ctl_touch(); }
static void imp_seekchg(void *self, void *c, void *b) { (void)self; (void)c; (void)b; }
static void imp_seekup(void *self, void *c, void *b) {
    (void)self; (void)c; (void)b;
    g_seeking = 0;
    if (!g_player || !g_seeksl) return;
    float v = ((float(*)(id, SEL))oc_ms)((id)g_seeksl, oc_sel("value"));
    id item = ((id(*)(id, SEL))oc_ms)(g_player, oc_sel("currentItem"));
    if (!item) return;
    CMTime dt = ((CMTime(*)(id, SEL))oc_ms)(item, oc_sel("duration"));
    double dur = cm_sec(dt);
    if (dur <= 0) return;
    double sec = (double)v * dur;
    ((void(*)(id, SEL, CMTime))oc_ms)(g_player, oc_sel("seekToTime:"), CMTimeMakeWithSeconds(sec, 600));
}
static const float SPD[5] = {0.75f, 1.0f, 1.25f, 1.5f, 2.0f};
static void imp_playpause(void *self, void *c, void *b) {
    ctl_touch();
    (void)self; (void)c; (void)b;
    if (!g_player) return;
    float r = ((float(*)(id, SEL))oc_ms)(g_player, oc_sel("rate"));
    if (r > 0.01f) ((void(*)(id, SEL))oc_ms)(g_player, oc_sel("pause"));
    else ((void(*)(id, SEL))oc_ms)(g_player, oc_sel("play"));
}
static void imp_speed(void *self, void *c, void *b) {
    ctl_touch();
    (void)self; (void)c; (void)b;
    if (!g_player) return;
    g_spdi = (g_spdi + 1) % 5;
    g_rate = SPD[g_spdi];
    ((void(*)(id, SEL, float))oc_ms)(g_player, oc_sel("setRate:"), g_rate);
    ((void(*)(id, SEL, float))oc_ms)(g_player, oc_sel("setDefaultRate:"), g_rate);   /* iOS16: 暂停/继续保持倍速 */
    if (g_spdlbl) {
        char t2[16]; rate_txt(t2, sizeof(t2), g_rate);
        ((void(*)(id, SEL, id))oc_ms)(g_spdlbl, oc_sel("setText:"), ns_str(t2));
    }
}
/* ★ 音量双路: ① player.volume ② AVAudioMix 改音轨音量 (后者走渲染管线, 最可靠) */
static void vol_apply(float v) {
    g_vol = v;
    if (!g_player) return;
    ((void(*)(id, SEL, float))oc_ms)(g_player, oc_sel("setVolume:"), v);
    /* 拖到 0 = 硬静音(最彻底); 回读确认 AVPlayer 是否真的接受 */
    ((void(*)(id, SEL, unsigned char))oc_ms)(g_player, oc_sel("setMuted:"), v < 0.02f ? 1 : 0);
    float rb = ((float(*)(id, SEL))oc_ms)(g_player, oc_sel("volume"));
    id item = ((id(*)(id, SEL))oc_ms)(g_player, oc_sel("currentItem"));
    if (!item) { dl_log("VOL %.2f (回读 %.2f, 无 item)", v, rb); return; }
    id asset = ((id(*)(id, SEL))oc_ms)(item, oc_sel("asset"));
    if (!asset) { dl_log("VOL %.2f (无 asset)", v); return; }
    id tracks = ((id(*)(id, SEL, id))oc_ms)(asset, oc_sel("tracksWithMediaType:"), ns_str("soun"));
    unsigned long tn = tracks ? ((unsigned long(*)(id, SEL))oc_ms)(tracks, oc_sel("count")) : 0;
    id mix = ((id(*)(id, SEL))oc_ms)(oc_cls("AVMutableAudioMix"), oc_sel("audioMix"));
    id params = ((id(*)(id, SEL))oc_ms)(oc_cls("NSMutableArray"), oc_sel("array"));
    if (!mix || !params) { dl_log("VOL %.2f (mix 建不出)", v); return; }
    for (unsigned long k = 0; k < tn; k++) {
        id tr = ((id(*)(id, SEL, unsigned long))oc_ms)(tracks, oc_sel("objectAtIndex:"), k);
        if (!tr) continue;
        id ap = ((id(*)(id, SEL, id))oc_ms)(oc_cls("AVMutableAudioMixInputParameters"), oc_sel("audioMixInputParametersWithTrack:"), tr);
        if (!ap) continue;
        CMTime z = { 0, 1, 1, 0, 0 };
        ((void(*)(id, SEL, float, CMTime))oc_ms)(ap, oc_sel("setVolume:atTime:"), v, z);
        ((void(*)(id, SEL, id))oc_ms)(params, oc_sel("addObject:"), ap);
    }
    ((void(*)(id, SEL, id))oc_ms)(mix, oc_sel("setInputParameters:"), params);
    ((void(*)(id, SEL, id))oc_ms)(item, oc_sel("setAudioMix:"), mix);
    dl_log("VOL %.2f (回读 %.2f, 音轨 %lu 条已设)", v, rb, tn);
}
static void imp_volchg(void *self, void *c, void *b) {
    ctl_touch();
    (void)self; (void)c;
    if (!b) return;
    float v = ((float(*)(id, SEL))oc_ms)((id)b, oc_sel("value"));
    vol_apply(v);
}
static void imp_playclose(void *self, void *c, void *b) {
    (void)self; (void)c; (void)b;
    if (g_player) ((void(*)(id, SEL))oc_ms)(g_player, oc_sel("pause"));
    if (g_playvc) ((void(*)(id, SEL, unsigned char, id))oc_ms)(g_playvc, oc_sel("dismissViewControllerAnimated:completion:"), 0, Nil);
    g_playlayer = g_playbtn = NULL;
    g_seeksl = g_seektlabel = NULL;
    g_ppbtn = g_spdbtn = g_volsl = NULL;
    g_title = g_tcur = g_tdur = g_volicon = g_barbot = g_bartop = NULL;
    g_tapview = NULL; g_spdlbl = NULL;
    g_ctlvis = 1;
    if (g_hpanel) ((void(*)(id, SEL, unsigned char))oc_ms)(g_hpanel, oc_sel("setHidden:"), 0);
    if (g_btn) ((void(*)(id, SEL, unsigned char))oc_ms)(g_btn, oc_sel("setHidden:"), 0);
}
static void imp_histrow(void *self, void *c, void *b) {
    (void)self; (void)c;
    if (!b) return;
    long i = ((long(*)(id, SEL))oc_ms)((id)b, oc_sel("tag"));
    char line[300];
    pthread_mutex_lock(&g_hst);
    if (i < 0 || i >= g_histn) { pthread_mutex_unlock(&g_hst); return; }
    snprintf(line, sizeof(line), "%s", g_hist[i]);
    pthread_mutex_unlock(&g_hst);
    char *sp1 = strchr(line, ' '); if (!sp1) return;
    char *p = sp1 + 1;                       // tag
    char *sp2 = strchr(p, ' '); if (!sp2) return;
    size_t tl = (size_t)(sp2 - p); char tag[32] = "";
    if (tl >= sizeof(tag)) tl = sizeof(tag) - 1;
    memcpy(tag, p, tl); tag[tl] = 0;
    if (strncmp(tag, "✗", 3) == 0) return;   // 失败行不可播
    char *p2 = sp2 + 1;                      // 文件名
    char *sp3 = strchr(p2, ' ');
    size_t fl = sp3 ? (size_t)(sp3 - p2) : strlen(p2);
    char file[200] = "";
    if (fl >= sizeof(file)) fl = sizeof(file) - 1;
    memcpy(file, p2, fl); file[fl] = 0;
    if (!strstr(file, ".ts") && !strstr(file, ".mp4")) return;
    char dir[512], path[700]; write_out_dir(dir, sizeof(dir));
    snprintf(path, sizeof(path), "%s/%s", dir, file);
    FILE *t = fopen(path, "rb");
    if (!t) { dl_log("记录播放: 文件不在 %s", file); return; }
    fclose(t);
    hist_play_file(path);
}
// 行字段解析: "HH:MM:SS.mmm TAG file | size | segs | url"
static void hist_fields(const char *line, char *ts, char *tag, char *file, char *meta, int *play) {
    ts[0] = tag[0] = file[0] = meta[0] = 0; *play = 0;
    const char *sp1 = strchr(line, ' '); if (!sp1) return;
    size_t l1 = (size_t)(sp1 - line); if (l1 > 23) l1 = 23;
    memcpy(ts, line, l1); ts[l1] = 0;
    char *dot = strchr(ts, '.'); if (dot) *dot = 0;
    const char *p = sp1 + 1;
    const char *sp2 = strchr(p, ' '); if (!sp2) { snprintf(tag, 31, "%s", p); return; }
    size_t l2 = (size_t)(sp2 - p); if (l2 > 30) l2 = 30;
    memcpy(tag, p, l2); tag[l2] = 0;
    const char *bar = strstr(sp2, " | ");
    if (!bar) { snprintf(file, 199, "%s", sp2 + 1); return; }
    size_t l3 = (size_t)(bar - (sp2 + 1)); if (l3 > 199) l3 = 199;
    memcpy(file, sp2 + 1, l3); file[l3] = 0;
    snprintf(meta, 119, "%s", bar + 3);
    *play = strncmp(tag, "✗", 3) != 0;
}
/* 删除第 idx 条记录并落盘 */
static void hist_delete(int idx) {
    char dir[512], p[600];
    pthread_mutex_lock(&g_hst);
    if (idx < 0 || idx >= g_histn) { pthread_mutex_unlock(&g_hst); return; }
    for (int k = idx; k < g_histn - 1; k++) memcpy(g_hist[k], g_hist[k + 1], sizeof(g_hist[0]));
    g_histn--;
    write_out_dir(dir, sizeof(dir));
    snprintf(p, sizeof(p), "%s/history.txt", dir);
    FILE *f = fopen(p, "wb");
    if (f) { for (int i = 0; i < g_histn; i++) fprintf(f, "%s\n", g_hist[i]); fclose(f); }
    pthread_mutex_unlock(&g_hst);
    g_hshown = -1;              /* 强制下次 tick 重建面板 */
    dl_log("记录删除: idx=%d 剩 %d 条", idx, g_histn);
}
/* ★ 行横向拖拽: 慢拖也能露出删除底 —— 快甩 / 慢拖两条路都能出 */
static double g_rowbase;
static void imp_rowpan(void *self, void *c, void *gr) {
    (void)self; (void)c;
    if (!gr || !g_htv) return;
    id row = ((id(*)(id, SEL))oc_ms)((id)gr, oc_sel("view"));
    if (!row) return;
    unsigned long st = ((unsigned long(*)(id, SEL))oc_ms)((id)gr, oc_sel("state"));
    Pnt t = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("translationInView:"), g_htv);
    if (st == 1) {                                  /* Began: 记基准 x */
        MyRect f = ((MyRect(*)(id, SEL))oc_ms)(row, oc_sel("frame"));
        g_rowbase = f.x;
        return;
    }
    if (st == 2) {                                  /* Changed: 1:1 跟手, 钳位 [-60, 8] */
        double x = g_rowbase + t.x;
        if (x < -60.0) x = -60.0;
        if (x > 8.0)   x = 8.0;
        MyRect f = ((MyRect(*)(id, SEL))oc_ms)(row, oc_sel("frame"));
        f.x = x;
        ((void(*)(id, SEL, MyRect))oc_ms)(row, oc_sel("setFrame:"), f);
        return;
    }
    if (st == 3 || st == 4) {                       /* Ended/Cancelled: 过半或快甩 -> 露出, 否则归位 */
        Pnt v = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("velocityInView:"), g_htv);
        double x = g_rowbase + t.x;
        double tgt = (x < -34.0 || v.x < -300.0) ? -60.0 : 8.0;
        ((void(*)(id, SEL, id, void *))oc_ms)(oc_cls("UIView"), oc_sel("beginAnimations:context:"), ns_str("rowsnap"), NULL);
        ((void(*)(id, SEL, double))oc_ms)(oc_cls("UIView"), oc_sel("setAnimationDuration:"), 0.18);
        MyRect f = ((MyRect(*)(id, SEL))oc_ms)(row, oc_sel("frame"));
        f.x = tgt;
        ((void(*)(id, SEL, MyRect))oc_ms)(row, oc_sel("setFrame:"), f);
        ((void(*)(id, SEL))oc_ms)(oc_cls("UIView"), oc_sel("commitAnimations"));
        return;
    }
}
/* 左滑: 行左移 76pt 露出删除底 */
/* ★ 手势 action 的签名是 action:(UIGestureRecognizer*)sender —— 第一参是 target,
      行视图必须从 [sender view] 取 (v4.10 崩在 imp_rowswl+52 就是错把 self 当行) */
static void imp_rowswl(void *self, void *c, void *gr) {
    (void)self; (void)c;
    if (!gr) return;
    id row = ((id(*)(id, SEL))oc_ms)((id)gr, oc_sel("view"));
    if (!row) return;
    MyRect f = ((MyRect(*)(id, SEL))oc_ms)(row, oc_sel("frame"));
    f.x = -60.0;
    ((void(*)(id, SEL, MyRect))oc_ms)(row, oc_sel("setFrame:"), f);
    dl_log("ROWSWL 左滑露出删除 (tag=%ld)", ((long(*)(id, SEL))oc_ms)(row, oc_sel("tag")));
}
/* 右滑: 复原 */
static void imp_rowswr(void *self, void *c, void *gr) {
    (void)self; (void)c;
    if (!gr) return;
    id row = ((id(*)(id, SEL))oc_ms)((id)gr, oc_sel("view"));
    if (!row) return;
    MyRect f = ((MyRect(*)(id, SEL))oc_ms)(row, oc_sel("frame"));
    f.x = 8.0;
    ((void(*)(id, SEL, MyRect))oc_ms)(row, oc_sel("setFrame:"), f);
}
/* 点垃圾桶: 删除该行 */
static void imp_rowdel(void *self, void *c, void *b) {
    (void)self; (void)c;
    if (!b) return;
    long idx = ((long(*)(id, SEL))oc_ms)((id)b, oc_sel("tag"));
    hist_delete((int)idx);
}
/* ★ 面板滚动接管: 垂直平移直接改 contentOffset (按钮点击/左滑删除不受影响) */
static double g_pnbase;
static long imp_gesbegin(void *self, void *c, void *gr) {
    if (!gr) return 1;
    id v = ((id(*)(id, SEL))oc_ms)((id)gr, oc_sel("view"));
    if (v && g_htv && v == g_htv) {          /* 我方面板 pan: 仅垂直启动, 水平让给左滑删除 */
        Pnt t = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("translationInView:"), g_hpanel);
        double ax = t.x < 0 ? -t.x : t.x, ay = t.y < 0 ? -t.y : t.y;
        if (ay > 4.0 && ay > ax * 1.2) return 1;
        dl_log("PAN 横向让位 (ax=%.0f ay=%.0f)", ax, ay);   /* 让位日志: 确认左滑链路已放开 */
        return 0;
    }
    /* 行横向拖拽: 只管家面板内的行 (isDescendantOfView), 播放器 tap 不受影响 (它共用本 delegate) */
    if (v && g_htv && v != g_htv &&
        ((unsigned char(*)(id, SEL, id))oc_ms)(v, oc_sel("isDescendantOfView:"), g_htv)) {
        Pnt t = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("translationInView:"), g_htv);
        double ax = t.x < 0 ? -t.x : t.x, ay = t.y < 0 ? -t.y : t.y;
        if (ax > 4.0 && ax > ay * 1.2) return 1;
        return 0;                       /* 竖向让给面板滚动 */
    }
    return 1;
}
static void imp_hscroll(void *self, void *c, void *gr) {
    if (!gr || !g_htv) return;
    unsigned long st = ((unsigned long(*)(id, SEL))oc_ms)((id)gr, oc_sel("state"));
    Pnt t = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("translationInView:"), g_hpanel);
    Pnt cs = ((Pnt(*)(id, SEL))oc_ms)(g_htv, oc_sel("contentSize"));    /* x=宽, y=高 */
    MyRect f = ((MyRect(*)(id, SEL))oc_ms)(g_htv, oc_sel("frame"));
    double maxoff = cs.y + 56.0 - f.h;               /* contentInset 顶 56 */
    if (maxoff < 0) maxoff = 0;
    /* UIGestureRecognizerState: Possible=0 Began=1 Changed=2 Ended=3 Cancelled=4 Failed=5 */
    if (st == 1) {   /* Began: 记起点 */
        Pnt co = ((Pnt(*)(id, SEL))oc_ms)(g_htv, oc_sel("contentOffset"));
        g_pnbase = co.y;
        return;
    }
    if (st == 2) {   /* Changed: 1:1 跟手 + 边界橡皮筋 */
        double want = g_pnbase - t.y;
        double show = want;
        if (show < 0) show = want * 0.35;                                   /* 顶部回弹区 */
        else if (show > maxoff) show = maxoff + (want - maxoff) * 0.35;     /* 底部回弹区 */
        Pnt off = { 0, show };
        ((void(*)(id, SEL, Pnt))oc_ms)(g_htv, oc_sel("setContentOffset:"), off);
        return;
    }
    if (st == 3 || st == 4) {   /* Ended/Cancelled: 按松手速度惯性滑行, 越界弹回边界 */
        double want = g_pnbase - t.y;
        double tgt = want;
        if (want < 0) tgt = 0;
        else if (want > maxoff) tgt = maxoff;
        else {
            Pnt vel = ((Pnt(*)(id, SEL, id))oc_ms)((id)gr, oc_sel("velocityInView:"), g_hpanel);
            tgt = want - vel.y * 0.22;                 /* 惯性: 松手后继续滑行 */
            if (tgt < 0) tgt = 0;
            if (tgt > maxoff) tgt = maxoff;
        }
        Pnt off = { 0, tgt };
        ((void(*)(id, SEL, Pnt, unsigned char))oc_ms)(g_htv, oc_sel("setContentOffset:animated:"), off, 1);
        return;
    }
}
static void hist_panel_refresh(void) {
    if (!g_htv) return;
    id subs = ((id(*)(id, SEL))oc_ms)(g_htv, oc_sel("subviews"));
    unsigned long sn = subs ? ((unsigned long(*)(id, SEL))oc_ms)(subs, oc_sel("count")) : 0;
    for (unsigned long k = sn; k > 0; k--) {
        id s2 = ((id(*)(id, SEL, unsigned long))oc_ms)(subs, oc_sel("objectAtIndex:"), k - 1);
        ((void(*)(id, SEL))oc_ms)(s2, oc_sel("removeFromSuperview"));
    }
    float RW = 320.0;
    g_npg = 0;
    /* ── 进行中的任务 (实时进度, tick 里更新文字) ── */
    pthread_mutex_lock(&g_dlm);
    int na = g_ntask; id act[8];
    for (int i = 0; i < na && i < 8; i++) act[i] = g_task[i];
    pthread_mutex_unlock(&g_dlm);
    for (int i = 0; i < na && i < 8; i++) {
        MTX *m = (MTX *)act[i];
        if (!m) continue;
        float y = i * 66.0f;
        MyRect rf = { 8, y + 3, 304, 60 };
        id btn = ((id(*)(id, SEL))oc_ms)(oc_cls("UIButton"), oc_sel("alloc"));
        if (btn) btn = ((id(*)(id, SEL, MyRect))oc_ms)(btn, oc_sel("initWithFrame:"), rf);
        if (!btn) continue;
        ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("setBackgroundColor:"), rgba(0.10, 0.20, 0.14, 1));
        id bl2 = ((id(*)(id, SEL))oc_ms)(btn, oc_sel("layer"));
        if (bl2) ((void(*)(id, SEL, double))oc_ms)(bl2, oc_sel("setCornerRadius:"), 11.0);
        /* 主行: 文件名 */
        id tl = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (tl) tl = ((id(*)(id, SEL, MyRect))oc_ms)(tl, oc_sel("initWithFrame:"), (MyRect){ 14, 8, 216, 16 });
        if (tl) {
            ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setText:"), ns_str(m->name));
            ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setTextColor:"), rgba(0.55, 0.92, 0.68, 1));
            id f4 = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("systemFontOfSize:"), 12.0);
            if (f4) ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setFont:"), f4);
            ((void(*)(id, SEL, unsigned char))oc_ms)(tl, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), tl);
        }
        /* 次行: 实时进度 (由 tick 更新) */
        id pl = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (pl) pl = ((id(*)(id, SEL, MyRect))oc_ms)(pl, oc_sel("initWithFrame:"), (MyRect){ 14, 28, 220, 14 });
        if (pl) {
            ((void(*)(id, SEL, id))oc_ms)(pl, oc_sel("setText:"), ns_str("准备中…"));
            ((void(*)(id, SEL, id))oc_ms)(pl, oc_sel("setTextColor:"), rgba(0.45, 0.80, 0.55, 1));
            id f5 = ((id(*)(id, SEL, id, double))oc_ms)(oc_cls("UIFont"), oc_sel("fontWithName:size:"), ns_str("Menlo-Regular"), 9.5);
            if (f5) ((void(*)(id, SEL, id))oc_ms)(pl, oc_sel("setFont:"), f5);
            ((void(*)(id, SEL, unsigned char))oc_ms)(pl, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), pl);
        }
        /* 进度条 */
        id bar = ((id(*)(id, SEL))oc_ms)(oc_cls("UIView"), oc_sel("alloc"));
        if (bar) bar = ((id(*)(id, SEL, MyRect))oc_ms)(bar, oc_sel("initWithFrame:"), (MyRect){ 14, 48, 276, 4 });
        if (bar) {
            ((void(*)(id, SEL, id))oc_ms)(bar, oc_sel("setBackgroundColor:"), rgba(0.10, 0.75, 0.40, 1));
            id bl3 = ((id(*)(id, SEL))oc_ms)(bar, oc_sel("layer"));
            if (bl3) ((void(*)(id, SEL, double))oc_ms)(bl3, oc_sel("setCornerRadius:"), 2.0);
            ((void(*)(id, SEL, unsigned char))oc_ms)(bar, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), bar);
        }
        if (g_npg < 8) {
            g_pgtask[g_npg] = (void *)m; g_pglabel[g_npg] = (void *)objc_retain(pl); g_pgbar[g_npg] = (void *)objc_retain(bar);
            g_npg++;
        }
        ((void(*)(id, SEL, long))oc_ms)(btn, oc_sel("setTag:"), (long)-1);
        ((void(*)(id, SEL, id))oc_ms)(g_htv, oc_sel("addSubview:"), btn);
    }
    pthread_mutex_lock(&g_hst);
    if (g_histn == 0) {
        pthread_mutex_unlock(&g_hst);
        MyRect ef = { 0, 60, RW, 40 };
        id el = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (el) el = ((id(*)(id, SEL, MyRect))oc_ms)(el, oc_sel("initWithFrame:"), ef);
        if (el) {
            ((void(*)(id, SEL, id))oc_ms)(el, oc_sel("setText:"), ns_str("还没有记录\n点绿色「抓!」开始下载"));
            {
                id ei = ((id(*)(id, SEL))oc_ms)(oc_cls("UIImageView"), oc_sel("alloc"));
                if (ei) ei = ((id(*)(id, SEL, MyRect))oc_ms)(ei, oc_sel("initWithFrame:"), (MyRect){ 144, 14, 32, 32 });
                if (ei) {
                    id eim = sym_img_sz("tray", 26.0);
                    if (eim) ((void(*)(id, SEL, id))oc_ms)(ei, oc_sel("setImage:"), eim);
                    ((void(*)(id, SEL, id))oc_ms)(ei, oc_sel("setTintColor:"), rgba(0.42, 0.45, 0.50, 1));
                    ((void(*)(id, SEL, unsigned char))oc_ms)(ei, oc_sel("setUserInteractionEnabled:"), 0);
                    ((void(*)(id, SEL, id))oc_ms)(g_htv, oc_sel("addSubview:"), ei);
                }
            }
            ((void(*)(id, SEL, id))oc_ms)(el, oc_sel("setTextColor:"), rgba(0.55, 0.58, 0.62, 1));
            id f2 = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("systemFontOfSize:"), 11.0);
            if (f2) ((void(*)(id, SEL, id))oc_ms)(el, oc_sel("setFont:"), f2);
            ((void(*)(id, SEL, long))oc_ms)(el, oc_sel("setTextAlignment:"), 1);
            ((void(*)(id, SEL, unsigned char))oc_ms)(el, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(g_htv, oc_sel("addSubview:"), el);
        }
        MySize cs0 = { RW, 140 };   /* ★ setContentSize: 要 CGSize(2×double), 传 MyRect(4×double) 会按 ABI 错位成 {0,0} */
        ((void(*)(id, SEL, MySize))oc_ms)(g_htv, oc_sel("setContentSize:"), cs0);
        g_hshown = 0;
        return;
    }
    for (int k = 0; k < g_histn; k++) {
        int i = g_histn - 1 - k;              // 最新在上
        char ts[32], tag[32], file[200], meta[120]; int play = 0;
        hist_fields(g_hist[i], ts, tag, file, meta, &play);
        // meta: "size | segs | url" → "size · segs"
        char m2[120]; snprintf(m2, sizeof(m2), "%s", meta);
        char *b1 = strstr(m2, " | ");
        char segpart[80] = "", durp[24] = "";
        if (b1) { *b1 = 0; snprintf(segpart, sizeof(segpart), "%s", b1 + 3);
                  char *b2 = strstr(segpart, " | ");
                  if (b2) { *b2 = 0; char *r2 = b2 + 3; char *b3 = strstr(r2, " | ");
                            if (b3) *b3 = 0; snprintf(durp, sizeof(durp), "%s", r2); } }
        int good = strncmp(tag, "✓", 3) == 0 || strncmp(tag, "△", 3) == 0;
        int warn = strncmp(tag, "⚠", 3) == 0;
        int fail = strncmp(tag, "✗", 3) == 0;
        (void)good;
        float y = g_npg * 66.0f + k * 72.0f;
        /* 先铺删除底 (在行下面, 行左滑后露出) */
        {
            id dlbtn = ((id(*)(id, SEL))oc_ms)(oc_cls("UIButton"), oc_sel("alloc"));
            if (dlbtn) dlbtn = ((id(*)(id, SEL, MyRect))oc_ms)(dlbtn, oc_sel("initWithFrame:"), (MyRect){ 244, y + 3, 68, 68 });
            if (dlbtn) {
                ((void(*)(id, SEL, id))oc_ms)(dlbtn, oc_sel("setBackgroundColor:"), rgba(0.85, 0.23, 0.25, 1));
                id dbl = ((id(*)(id, SEL))oc_ms)(dlbtn, oc_sel("layer"));
                if (dbl) ((void(*)(id, SEL, double))oc_ms)(dbl, oc_sel("setCornerRadius:"), 11.0);
                id dim = sym_img_sz("trash", 20.0);
                if (dim) ((void(*)(id, SEL, id, unsigned long))oc_ms)(dlbtn, oc_sel("setImage:forState:"), dim, 0);
                ((void(*)(id, SEL, id))oc_ms)(dlbtn, oc_sel("setTintColor:"), rgba(1, 1, 1, 1));
                ((void(*)(id, SEL, long))oc_ms)(dlbtn, oc_sel("setTag:"), (long)i);
                ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(dlbtn, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgRowDel:"), 64);
                ((void(*)(id, SEL, id))oc_ms)(g_htv, oc_sel("addSubview:"), dlbtn);
            }
        }
        MyRect rf = { 8, y + 3, 304, 68 };
        id btn = ((id(*)(id, SEL))oc_ms)(oc_cls("UIButton"), oc_sel("alloc"));
        if (btn) btn = ((id(*)(id, SEL, MyRect))oc_ms)(btn, oc_sel("initWithFrame:"), rf);
        if (!btn) continue;
        /* ★ 必须不透明: 半透明卡会透出底层红色删除底 (表现为"按钮错位") */
        ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("setBackgroundColor:"), rgba(0.118, 0.118, 0.138, 1));
        id bl2 = ((id(*)(id, SEL))oc_ms)(btn, oc_sel("layer"));
        if (bl2) ((void(*)(id, SEL, double))oc_ms)(bl2, oc_sel("setCornerRadius:"), 11.0);
        /* 状态徽标: SF 图标 */
        id bd = ((id(*)(id, SEL))oc_ms)(oc_cls("UIImageView"), oc_sel("alloc"));
        if (bd) bd = ((id(*)(id, SEL, MyRect))oc_ms)(bd, oc_sel("initWithFrame:"), (MyRect){ 14, 24, 20, 20 });
        if (bd) {
            id bim = sym_img_sz(fail ? "xmark.circle.fill" : warn ? "exclamationmark.triangle.fill" : "checkmark.circle.fill", 15.0);
            if (bim) ((void(*)(id, SEL, id))oc_ms)(bd, oc_sel("setImage:"), bim);
            ((void(*)(id, SEL, id))oc_ms)(bd, oc_sel("setTintColor:"),
                fail ? rgba(0.52, 0.55, 0.60, 1) : warn ? rgba(0.98, 0.68, 0.22, 1) : rgba(0.30, 0.85, 0.48, 1));
            ((void(*)(id, SEL, unsigned char))oc_ms)(bd, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), bd);
        }
        /* 主行: 文件名 */
        id tl = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (tl) tl = ((id(*)(id, SEL, MyRect))oc_ms)(tl, oc_sel("initWithFrame:"), (MyRect){ 44, 7, 216, 17 });
        if (tl) {
            ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setText:"), ns_str(file));
            ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setTextColor:"), rgba(fail ? 0.48 : 0.96, fail ? 0.48 : 0.96, fail ? 0.52 : 0.96, 1));
            id f4b = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("boldSystemFontOfSize:"), 11.5);
            if (f4b) ((void(*)(id, SEL, id))oc_ms)(tl, oc_sel("setFont:"), f4b);
            ((void(*)(id, SEL, unsigned char))oc_ms)(tl, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), tl);
        }
        /* 第二行: 时长 · 分辨率 · 大小 · 段数 (视频信息主体) */
        id tm2 = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (tm2) tm2 = ((id(*)(id, SEL, MyRect))oc_ms)(tm2, oc_sel("initWithFrame:"), (MyRect){ 44, 28, 216, 14 });
        if (tm2) {
            char det2[160];
            if (durp[0] && strcmp(durp, "-") && strchr(durp, ':')) snprintf(det2, sizeof(det2), "%s · %s", durp, m2);
            else snprintf(det2, sizeof(det2), "%s", m2);
            ((void(*)(id, SEL, id))oc_ms)(tm2, oc_sel("setText:"), ns_str(det2));
            ((void(*)(id, SEL, id))oc_ms)(tm2, oc_sel("setTextColor:"), rgba(0.72, 0.75, 0.80, 1));
            id f5t = ((id(*)(id, SEL, id, double))oc_ms)(oc_cls("UIFont"), oc_sel("fontWithName:size:"), ns_str("Menlo-Regular"), 9.0);
            if (f5t) ((void(*)(id, SEL, id))oc_ms)(tm2, oc_sel("setFont:"), f5t);
            ((void(*)(id, SEL, unsigned char))oc_ms)(tm2, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), tm2);
        }
        /* 第三行: 完成时间 (北京时间) */
        id dl = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
        if (dl) dl = ((id(*)(id, SEL, MyRect))oc_ms)(dl, oc_sel("initWithFrame:"), (MyRect){ 44, 46, 216, 13 });
        if (dl) {
            char det[96];
            {   char disp[40]; snprintf(disp, sizeof(disp), "%s", ts);
                char *us = strchr(disp, '_'); if (us) *us = ' ';
                char *lc = strrchr(disp, ':'); if (lc) *lc = 0;   /* 去掉秒 */
                snprintf(det, sizeof(det), "完成 %s", disp);
            }
            ((void(*)(id, SEL, id))oc_ms)(dl, oc_sel("setText:"), ns_str(det));
            ((void(*)(id, SEL, id))oc_ms)(dl, oc_sel("setTextColor:"), rgba(0.55, 0.75, 0.62, 1));
            id f5 = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("systemFontOfSize:"), 9.5);
            if (f5) ((void(*)(id, SEL, id))oc_ms)(dl, oc_sel("setFont:"), f5);
            ((void(*)(id, SEL, unsigned char))oc_ms)(dl, oc_sel("setUserInteractionEnabled:"), 0);
            ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), dl);
        }
        /* 右侧: 播放角标 */
        if (!fail) {
            id pg = ((id(*)(id, SEL))oc_ms)(oc_cls("UIImageView"), oc_sel("alloc"));
            if (pg) pg = ((id(*)(id, SEL, MyRect))oc_ms)(pg, oc_sel("initWithFrame:"), (MyRect){ 268, 24, 20, 20 });
            if (pg) {
                id pim = sym_img_sz("play.circle.fill", 18.0);
                if (pim) ((void(*)(id, SEL, id))oc_ms)(pg, oc_sel("setImage:"), pim);
                ((void(*)(id, SEL, id))oc_ms)(pg, oc_sel("setTintColor:"), rgba(0.34, 0.86, 0.54, 1));
                ((void(*)(id, SEL, unsigned char))oc_ms)(pg, oc_sel("setUserInteractionEnabled:"), 0);
                ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addSubview:"), pg);
            }
        }
        ((void(*)(id, SEL, long))oc_ms)(btn, oc_sel("setTag:"), (long)i);
        {
            id rp = ((id(*)(id, SEL))oc_ms)(oc_cls("UIPanGestureRecognizer"), oc_sel("alloc"));
            if (rp) { rp = ((id(*)(id, SEL, id, SEL))oc_ms)(rp, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgRowPan:"));
                      ((void(*)(id, SEL, id))oc_ms)(rp, oc_sel("setDelegate:"), g_uideleg);
                      ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), rp); objc_retain(rp); }
            id sw1 = ((id(*)(id, SEL))oc_ms)(oc_cls("UISwipeGestureRecognizer"), oc_sel("alloc"));
            if (sw1) { sw1 = ((id(*)(id, SEL, id, SEL))oc_ms)(sw1, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgRowSwL:"));
                       ((void(*)(id, SEL, unsigned long))oc_ms)(sw1, oc_sel("setDirection:"), 2);   /* left */
                       ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), sw1); objc_retain(sw1); }
            id sw2 = ((id(*)(id, SEL))oc_ms)(oc_cls("UISwipeGestureRecognizer"), oc_sel("alloc"));
            if (sw2) { sw2 = ((id(*)(id, SEL, id, SEL))oc_ms)(sw2, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgRowSwR:"));
                       ((void(*)(id, SEL, unsigned long))oc_ms)(sw2, oc_sel("setDirection:"), 1);   /* right */
                       ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), sw2); objc_retain(sw2); }
        }
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(btn, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgHistRow:"), 64);
        ((void(*)(id, SEL, id))oc_ms)(g_htv, oc_sel("addSubview:"), btn);
    }
    pthread_mutex_unlock(&g_hst);
    MySize cs = { RW, g_npg * 66.0f + g_histn * 72.0f + 16 };
    ((void(*)(id, SEL, MySize))oc_ms)(g_htv, oc_sel("setContentSize:"), cs);
    MyRect off0 = { 0, 0, 0, 0 };
    ((void(*)(id, SEL, MyRect))oc_ms)(g_htv, oc_sel("setContentOffset:"), off0);
    g_hshown = g_histn;
    /* ★ 面板高度自适应: 内容少时收缩贴合, 多时封顶并可滑动 */
    {
        double ch = (double)g_npg * 66.0 + (double)g_histn * 72.0 + 16.0;
        double ph = 56.0 + (ch > 464.0 ? 464.0 : ch);
        if (ph < 190.0) ph = 190.0;
        MyRect pf = ((MyRect(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("frame"));
        id win = ((id(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("window"));
        if (win) {
            MyRect wb = ((MyRect(*)(id, SEL))oc_ms)(win, oc_sel("bounds"));
            pf.x = (wb.w - 320.0) / 2.0; pf.y = (wb.h - ph) / 2.0;
        }
        pf.w = 320.0; pf.h = ph;
        ((void(*)(id, SEL, MyRect))oc_ms)(g_hpanel, oc_sel("setFrame:"), pf);
        ((void(*)(id, SEL, MyRect))oc_ms)(g_htv, oc_sel("setFrame:"), (MyRect){ 0, 0, 320.0, ph });
    }
}
static void imp_histtap(void *self, void *c, void *gr) {
    (void)self; (void)c; (void)gr;
    if (g_hpanel) ((void(*)(id, SEL, unsigned char))oc_ms)(g_hpanel, oc_sel("setHidden:"), 1);
}
static void hist_toggle(void) {
    if (!oc_ms) return;
    if (g_hpanel) {
        unsigned char h = ((unsigned char(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("isHidden"));
        if (h) hist_panel_refresh();
        ((void(*)(id, SEL, unsigned char))oc_ms)(g_hpanel, oc_sel("setHidden:"), h ? 0 : 1);
        return;
    }
    id app = ((id(*)(id, SEL))oc_ms)(oc_cls("UIApplication"), oc_sel("sharedApplication"));
    if (!app) return;
    id wins = ((id(*)(id, SEL))oc_ms)(app, oc_sel("windows"));
    unsigned long n = wins ? ((unsigned long(*)(id, SEL))oc_ms)(wins, oc_sel("count")) : 0;
    id win = NULL;
    for (unsigned long i = n; i > 0; i--) {
        id w = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), i - 1);
        if (((unsigned char(*)(id, SEL))oc_ms)(w, oc_sel("isKeyWindow"))) { win = w; break; }
    }
    if (!win && n) win = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), 0);
    if (!win) return;
    MyRect wbb = ((MyRect(*)(id, SEL))oc_ms)(win, oc_sel("bounds"));
    id pv = ((id(*)(id, SEL))oc_ms)(oc_cls("UIView"), oc_sel("alloc"));
    MyRect f = { (wbb.w - 320) / 2, (wbb.h - 520) / 2, 320, 520 };
    if (pv) pv = ((id(*)(id, SEL, MyRect))oc_ms)(pv, oc_sel("initWithFrame:"), f);
    if (!pv) return;
    id lay = ((id(*)(id, SEL))oc_ms)(pv, oc_sel("layer"));
    if (lay) {
        ((void(*)(id, SEL, double))oc_ms)(lay, oc_sel("setCornerRadius:"), 18.0);
        ((void(*)(id, SEL, double))oc_ms)(lay, oc_sel("setZPosition:"), 99998.0);
    }
    ((void(*)(id, SEL, id))oc_ms)(pv, oc_sel("setBackgroundColor:"), rgba(0.06, 0.06, 0.08, 0.98));
    id tv = ((id(*)(id, SEL))oc_ms)(oc_cls("UIScrollView"), oc_sel("alloc"));
    MyRect tf = { 0, 0, 320, 520 };      /* ★ 铺满整个面板: 任何位置(含标题栏)都能滑动 */
    if (tv) tv = ((id(*)(id, SEL, MyRect))oc_ms)(tv, oc_sel("initWithFrame:"), tf);
    if (tv) {
        ((void(*)(id, SEL, unsigned char))oc_ms)(tv, oc_sel("setShowsHorizontalScrollIndicator:"), 0);
        ((void(*)(id, SEL, unsigned char))oc_ms)(tv, oc_sel("setShowsVerticalScrollIndicator:"), 1);
        ((void(*)(id, SEL, unsigned char))oc_ms)(tv, oc_sel("setScrollEnabled:"), 0);   /* ★ 滚动由我方 pan 接管 (v4.12) */
        ((void(*)(id, SEL, unsigned char))oc_ms)(tv, oc_sel("setAlwaysBounceVertical:"), 1);
        ((void(*)(id, SEL, unsigned char))oc_ms)(tv, oc_sel("setDelaysContentTouches:"), 1);   /* ★ 恢复原生化触摸延迟: 滑动更顺, 按钮仍可点 */
        ((void(*)(id, SEL, unsigned char))oc_ms)(tv, oc_sel("setDirectionalLockEnabled:"), 1);
        ((void(*)(id, SEL, id))oc_ms)(tv, oc_sel("setBackgroundColor:"), rgba(0, 0, 0, 0));
        /* ★ 顶部预留 56pt 给标题栏 (标题/关闭钮是浮层, 添加顺序在滚动视图之后) */
        ((void(*)(id, SEL, MyRect))oc_ms)(tv, oc_sel("setContentInset:"), (MyRect){ 56, 0, 0, 0 });
        ((void(*)(id, SEL, MyRect))oc_ms)(tv, oc_sel("setScrollIndicatorInsets:"), (MyRect){ 56, 0, 0, 0 });
        ((void(*)(id, SEL, id))oc_ms)(pv, oc_sel("addSubview:"), tv);
        g_htv = (id)objc_retain(tv);
        {   /* ★ 自管滚动: pan 直接驱动 contentOffset, 不依赖 UIScrollView 内部手势仲裁 */
            id pg = ((id(*)(id, SEL))oc_ms)(oc_cls("UIPanGestureRecognizer"), oc_sel("alloc"));
            if (pg) { pg = ((id(*)(id, SEL, id, SEL))oc_ms)(pg, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgPanelPan:"));
                      /* ★★ 根因修复: 不设 delegate 时 UIKit 永不调用 gestureRecognizerShouldBegin:,
                         面板 pan 就会对横竖任意方向都抢占手势 -> 行上的左滑删除被挤出竞技场 */
                      ((void(*)(id, SEL, id))oc_ms)(pg, oc_sel("setDelegate:"), g_uideleg);
                      ((void(*)(id, SEL, id))oc_ms)(tv, oc_sel("addGestureRecognizer:"), pg); objc_retain(pg); }
        }
    }
    ((void(*)(id, SEL, id))oc_ms)(win, oc_sel("addSubview:"), pv);
    ((void(*)(id, SEL, id))oc_ms)(win, oc_sel("bringSubviewToFront:"), pv);
    id xb = mk_icon_btn((MyRect){ 320 - 46, 14, 32, 32 }, "xmark", 16.0, 0.12, 12.0);
    if (xb) {
        {
            id ht = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
            MyRect hf = { 18, 16, 200, 20 };
            if (ht) ht = ((id(*)(id, SEL, MyRect))oc_ms)(ht, oc_sel("initWithFrame:"), hf);
            if (ht) {
                ((void(*)(id, SEL, id))oc_ms)(ht, oc_sel("setText:"), ns_str("下载记录"));
                ((void(*)(id, SEL, id))oc_ms)(ht, oc_sel("setTextColor:"), rgba(0.96, 0.96, 0.98, 1));
                id f7 = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("boldSystemFontOfSize:"), 15.0);
                if (f7) ((void(*)(id, SEL, id))oc_ms)(ht, oc_sel("setFont:"), f7);
                ((void(*)(id, SEL, unsigned char))oc_ms)(ht, oc_sel("setUserInteractionEnabled:"), 0);
                ((void(*)(id, SEL, id))oc_ms)(pv, oc_sel("addSubview:"), ht);
            }
            id hs = ((id(*)(id, SEL))oc_ms)(oc_cls("UILabel"), oc_sel("alloc"));
            if (hs) hs = ((id(*)(id, SEL, MyRect))oc_ms)(hs, oc_sel("initWithFrame:"), (MyRect){ 18, 36, 200, 14 });
            if (hs) {
                char cnt[48]; snprintf(cnt, sizeof(cnt), "%d 条记录", g_histn);
                ((void(*)(id, SEL, id))oc_ms)(hs, oc_sel("setText:"), ns_str(cnt));
                ((void(*)(id, SEL, id))oc_ms)(hs, oc_sel("setTextColor:"), rgba(0.52, 0.55, 0.60, 1));
                id f10 = ((id(*)(id, SEL, double))oc_ms)(oc_cls("UIFont"), oc_sel("systemFontOfSize:"), 10.0);
                if (f10) ((void(*)(id, SEL, id))oc_ms)(hs, oc_sel("setFont:"), f10);
                ((void(*)(id, SEL, unsigned char))oc_ms)(hs, oc_sel("setUserInteractionEnabled:"), 0);
                ((void(*)(id, SEL, id))oc_ms)(pv, oc_sel("addSubview:"), hs);
            }
        }
        ((void(*)(id, SEL, id, SEL, unsigned long))oc_ms)(xb, oc_sel("addTarget:action:forControlEvents:"), g_uideleg, oc_sel("yshgHistTap:"), 64);
        ((void(*)(id, SEL, id))oc_ms)(pv, oc_sel("addSubview:"), xb);
    }
    g_hpanel = (id)objc_retain(pv);
    hist_panel_refresh();
    dl_log("记录面板: 建立");
}
static void imp_dtap(void *self, void *c, void *gr) { (void)self; (void)c; (void)gr; hist_toggle(); }

// 主线程: 建类 + 建钮 + 建会话
static void ui_build(void) {
    if (g_uibuilt || !oc_ms) return;
    dl_log("UI build: 开始 (UIButton=%p)", (void *)oc_getclass("UIButton"));
    Class cls = oc_allocpair(oc_getclass("NSObject"), "YSHGUIObj", 0);
    if (!cls) { dl_log("UI build: 类创建失败"); return; }
    oc_addmethod(cls, oc_sel("yshgTap:"), (void *)imp_tap, "v@:@");
    oc_addmethod(cls, oc_sel("yshgLong:"), (void *)imp_long, "v@:@");
    oc_addmethod(cls, oc_sel("yshgPan:"), (void *)imp_pan, "v@:@");
    oc_addmethod(cls, oc_sel("yshgDtap:"), (void *)imp_dtap, "v@:@");
    oc_addmethod(cls, oc_sel("yshgHistTap:"), (void *)imp_histtap, "v@:@");
    oc_addmethod(cls, oc_sel("yshgHistRow:"), (void *)imp_histrow, "v@:@");
    oc_addmethod(cls, oc_sel("yshgRowPan:"), (void *)imp_rowpan, "v@:@");
    oc_addmethod(cls, oc_sel("yshgRowSwL:"), (void *)imp_rowswl, "v@:@");
    oc_addmethod(cls, oc_sel("yshgRowSwR:"), (void *)imp_rowswr, "v@:@");
    oc_addmethod(cls, oc_sel("yshgRowDel:"), (void *)imp_rowdel, "v@:@");
    oc_addmethod(cls, oc_sel("yshgPlayClose:"), (void *)imp_playclose, "v@:@");
    oc_addmethod(cls, oc_sel("yshgRot:"), (void *)imp_rot, "v@:@");
    oc_addmethod(cls, oc_sel("yshgVideotap:"), (void *)imp_videotap, "v@:@");
    oc_addmethod(cls, oc_sel("gestureRecognizerShouldBegin:"), (void *)imp_gesbegin, "B@:@");
    oc_addmethod(cls, oc_sel("yshgPanelPan:"), (void *)imp_hscroll, "v@:@");
    oc_addmethod(cls, oc_sel("gestureRecognizer:shouldReceiveTouch:"), (void *)imp_gesdel, "c@:@@");
    oc_addmethod(cls, oc_sel("yshgSeekDown:"), (void *)imp_seekdown, "v@:@");
    oc_addmethod(cls, oc_sel("yshgSeekChg:"), (void *)imp_seekchg, "v@:@");
    oc_addmethod(cls, oc_sel("yshgSeekUp:"), (void *)imp_seekup, "v@:@");
    oc_addmethod(cls, oc_sel("yshgPlayPause:"), (void *)imp_playpause, "v@:@");
    oc_addmethod(cls, oc_sel("yshgSpeed:"), (void *)imp_speed, "v@:@");
    oc_addmethod(cls, oc_sel("yshgVolChg:"), (void *)imp_volchg, "v@:@");
    oc_addmethod(cls, oc_sel("yshgTick:"), (void *)imp_tick, "v@:@");
    oc_register(cls);
    id d = ((id(*)(id, SEL))oc_ms)((id)cls, oc_sel("alloc"));
    g_uideleg = ((id(*)(id, SEL))oc_ms)(d, oc_sel("init"));
    if (!g_uideleg) { dl_log("UI build: deleg 创建失败"); return; }
    dl_log("UI build: cls=%p deleg=%p", (void *)cls, (void *)g_uideleg);

    // 必须自己持有: buttonWithType: 返回 autoreleased, 主线程 runloop 一排水就成野指针
    MyRect f = { 20, 120, 56, 56 };
    id btn = ((id(*)(id, SEL))oc_ms)(oc_cls("UIButton"), oc_sel("alloc"));
    if (btn) btn = ((id(*)(id, SEL, MyRect))oc_ms)(btn, oc_sel("initWithFrame:"), f);
    if (!btn) { dl_log("UI build: UIButton 为 nil"); return; }
    dl_log("UI build: btn=%p (alloc/init)", (void *)btn);
    id lay = ((id(*)(id, SEL))oc_ms)(btn, oc_sel("layer"));
    if (lay) {
        ((void(*)(id, SEL, double))oc_ms)(lay, oc_sel("setCornerRadius:"), 28.0);
        ((void(*)(id, SEL, double))oc_ms)(lay, oc_sel("setZPosition:"), 9999.0);
    }
    ((void(*)(id, SEL, double))oc_ms)(btn, oc_sel("setAlpha:"), 0.85);
    // 必须 alloc 再 initWithTarget:action:
    id tap = ((id(*)(id, SEL))oc_ms)(oc_cls("UITapGestureRecognizer"), oc_sel("alloc"));
    if (tap) { tap = ((id(*)(id, SEL, id, SEL))oc_ms)(tap, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgTap:"));
               ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), tap); }
    id lng = ((id(*)(id, SEL))oc_ms)(oc_cls("UILongPressGestureRecognizer"), oc_sel("alloc"));
    if (lng) { lng = ((id(*)(id, SEL, id, SEL))oc_ms)(lng, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgLong:"));
               ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), lng); }
    id pan = ((id(*)(id, SEL))oc_ms)(oc_cls("UIPanGestureRecognizer"), oc_sel("alloc"));
    if (pan) { pan = ((id(*)(id, SEL, id, SEL))oc_ms)(pan, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgPan:"));
               ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), pan); }
    id dtap = ((id(*)(id, SEL))oc_ms)(oc_cls("UITapGestureRecognizer"), oc_sel("alloc"));
    if (dtap) { dtap = ((id(*)(id, SEL, id, SEL))oc_ms)(dtap, oc_sel("initWithTarget:action:"), g_uideleg, oc_sel("yshgDtap:"));
                ((void(*)(id, SEL, unsigned long))oc_ms)(dtap, oc_sel("setNumberOfTapsRequired:"), 2);
                ((void(*)(id, SEL, id))oc_ms)(btn, oc_sel("addGestureRecognizer:"), dtap);
                if (tap) ((void(*)(id, SEL, id))oc_ms)(tap, oc_sel("requireGestureRecognizerToFail:"), dtap); }
    if (dtap) objc_retain(dtap);
    if (tap) objc_retain(tap);
    if (lng) objc_retain(lng);
    if (pan) objc_retain(pan);
    g_btn = btn;
    set_btn_style("抓", 0.30, 0.30, 0.36);
    dl_log("UI build: 钮=%p tap=%p lng=%p pan=%p", (void *)g_btn, (void *)tap, (void *)lng, (void *)pan);

    if (!g_sess) {
        id cfg = ((id(*)(id, SEL))oc_ms)(oc_cls("NSURLSessionConfiguration"), oc_sel("defaultSessionConfiguration"));
        if (cfg) {
            ((void(*)(id, SEL, double))oc_ms)(cfg, oc_sel("setTimeoutIntervalForRequest:"), 30.0);
            g_sess = ((id(*)(id, SEL, id, id, id))oc_ms)(oc_cls("NSURLSession"),
                     oc_sel("sessionWithConfiguration:delegate:delegateQueue:"), cfg, g_fdeleg, Nil);
            if (g_sess) g_sess = (id)objc_retain(g_sess);
            dl_log("UI build: session=%p", (void *)g_sess);
        } else dl_log("UI build: NSURLSessionConfiguration 为 nil");
    }
    g_uibuilt = 1;
    dl_log("UI build: 完成");
}

static void tick_fn(void) {
    if (!oc_ms || !g_btn) return;
    dl_av_hook();
    pthread_mutex_lock(&g_dlm);
    int nact = g_ntask, qd = g_jtail - g_jhead;
    int cur = 0, tot = 0;
    for (int i = 0; i < nact; i++) { cur += g_task[i]->cur; tot += g_task[i]->tot; }
    int ready = g_ready, autoo = g_auto;
    pthread_mutex_unlock(&g_dlm);
    int pend = nact + qd;
    char txt[32];
    double r = 0.30, g = 0.30, bb = 0.36;
    if (pend >= 2) { snprintf(txt, sizeof(txt), "↓%d", pend); r = 0.95; g = 0.58; bb = 0.10; }
    else if (nact == 1) { snprintf(txt, sizeof(txt), "↓%d/%d", cur, tot); r = 0.95; g = 0.58; bb = 0.10; }
    else if (time(NULL) < g_flash_until) { snprintf(txt, sizeof(txt), "✓"); r = 0.15; g = 0.72; bb = 0.35; }
    else if (autoo) { snprintf(txt, sizeof(txt), "自动"); r = 0.85; g = 0.28; bb = 0.28; }
    else if (ready) { snprintf(txt, sizeof(txt), "抓!"); r = 0.15; g = 0.72; bb = 0.35; }
    else { snprintf(txt, sizeof(txt), "抓"); }
    set_btn_style(txt, r, g, bb);
    if (g_hpanel && !((unsigned char(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("isHidden")) && g_npg > 0) {
        for (int i = 0; i < g_npg; i++) {
            MTX *m = (MTX *)g_pgtask[i];
            if (!m || !g_pglabel[i]) continue;
            int cur = m->cur, tot = m->tot;
            double pct = tot > 0 ? (double)cur / (double)tot : 0.0;
            char t2[160];
            snprintf(t2, sizeof(t2), "段 %d/%d · %d%%", cur, tot, (int)(pct * 100.0));
            ((void(*)(id, SEL, id))oc_ms)(g_pglabel[i], oc_sel("setText:"), ns_str(t2));
            if (g_pgbar[i]) ((void(*)(id, SEL, MyRect))oc_ms)(g_pgbar[i], oc_sel("setFrame:"), (MyRect){ 14, 48, 276.0 * pct, 4 });
        }
    }
    if (g_hpanel && g_histn != g_hshown) {
        unsigned char hp2 = ((unsigned char(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("isHidden"));
        if (!hp2) hist_panel_refresh();
    }
        if (g_player && g_seeksl && !g_seeking) {
        CMTime ct = ((CMTime(*)(id, SEL))oc_ms)(g_player, oc_sel("currentTime"));
        id item = ((id(*)(id, SEL))oc_ms)(g_player, oc_sel("currentItem"));
        double cur = cm_sec(ct), dur = 0;
        if (item) { CMTime dt = ((CMTime(*)(id, SEL))oc_ms)(item, oc_sel("duration")); dur = cm_sec(dt); }
        if (dur > 0) {
            float v = (float)(cur / dur); if (v < 0) v = 0; if (v > 1) v = 1;
            ((void(*)(id, SEL, float, unsigned char))oc_ms)(g_seeksl, oc_sel("setValue:animated:"), v, 0);
        }
        if (g_tcur) { char a[16]; fmt_mmss(cur, a, sizeof(a)); ((void(*)(id, SEL, id))oc_ms)(g_tcur, oc_sel("setText:"), ns_str(a)); }
        if (g_tdur) { char b2[16]; fmt_mmss(dur, b2, sizeof(b2)); ((void(*)(id, SEL, id))oc_ms)(g_tdur, oc_sel("setText:"), ns_str(b2)); }
        float r = ((float(*)(id, SEL))oc_ms)(g_player, oc_sel("rate"));
        if (g_ctlvis && r <= 0.01f) ctl_touch();
        if (g_ctlvis && r > 0.01f && time(NULL) - g_ctlshow > 3) { dl_log("CTLAUTO 隐藏"); player_ctl_apply(0.0f); }
        if (g_ppbtn) {
            /* ★ v4.14.6: 播放/暂停图标缓存 —— 原来每拍都走
               UIImageSymbolConfiguration + imageWithConfiguration 重新生成,
               常驻主线程每秒一次分配; UIImage 不可变, 可安全复用 */
            static id pim_play, pim_pause;
            if (!pim_play)  pim_play  = sym_img_sz("play.fill", 19.0);
            if (!pim_pause) pim_pause = sym_img_sz("pause.fill", 19.0);
            id pim = r > 0.01f ? pim_pause : pim_play;
            if (pim) ((void(*)(id, SEL, id, unsigned long))oc_ms)(g_ppbtn, oc_sel("setImage:forState:"), pim, 0);
        }
    }

    id sup = ((id(*)(id, SEL))oc_ms)(g_btn, oc_sel("superview"));
    if (g_hpanel) {
        unsigned char hp = ((unsigned char(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("isHidden"));
        id psup = ((id(*)(id, SEL))oc_ms)(g_hpanel, oc_sel("superview"));
        if (!hp && !psup && sup) {
            ((void(*)(id, SEL, id))oc_ms)(sup, oc_sel("addSubview:"), g_hpanel);
            ((void(*)(id, SEL, id))oc_ms)(sup, oc_sel("bringSubviewToFront:"), g_hpanel);
        }
    }
    if (sup) return;
    static int probe = 0;
    id app = ((id(*)(id, SEL))oc_ms)(oc_cls("UIApplication"), oc_sel("sharedApplication"));
    if (!app) { if (probe < 5) dl_log("UI tick: sharedApplication 为 nil"); probe++; return; }
    id key = NULL;
    id wins = ((id(*)(id, SEL))oc_ms)(app, oc_sel("windows"));
    unsigned long n = wins ? ((unsigned long(*)(id, SEL))oc_ms)(wins, oc_sel("count")) : 0;
    for (unsigned long i = n; i > 0; i--) {
        id w = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), i - 1);
        unsigned char k = ((unsigned char(*)(id, SEL))oc_ms)(w, oc_sel("isKeyWindow"));
        if (k) { key = w; break; }
    }
    if (!key) key = ((id(*)(id, SEL))oc_ms)(app, oc_sel("keyWindow"));
    if (!key && n > 0) key = ((id(*)(id, SEL, unsigned long))oc_ms)(wins, oc_sel("objectAtIndex:"), n - 1);
    if (!key) {
        id dlg = ((id(*)(id, SEL))oc_ms)(app, oc_sel("delegate"));
        if (dlg) key = ((id(*)(id, SEL))oc_ms)(dlg, oc_sel("window"));
    }
    if (key) {
        ((void(*)(id, SEL, id))oc_ms)(key, oc_sel("addSubview:"), g_btn);
        ((void(*)(id, SEL, id))oc_ms)(key, oc_sel("bringSubviewToFront:"), g_btn);
        dl_log("UI tick: 钮已挂载 win=%p (windows=%lu)", (void *)key, n);
    } else if (probe < 5) { dl_log("UI tick: 无可挂窗口 (windows=%lu)", n); probe++; }
}

// 后台线程: 轮询到 app 就绪 -> 回主线程构建; 之后每拍回主线程刷新
static void *ui_loop(void *a) {
    (void)a;
    for (;;) {
        sleep(1);
        if (!oc_ms || !g_uideleg) continue;
        if (!g_uibuilt) {
            id app = ((id(*)(id, SEL))oc_ms)(oc_cls("UIApplication"), oc_sel("sharedApplication"));
            if (!app) continue;
            ((void(*)(id, SEL, SEL, id, unsigned char))oc_ms)(g_uideleg,
                oc_sel("performSelectorOnMainThread:withObject:waitUntilDone:"), oc_sel("yshgBuild:"), Nil, 1);
        } else {
            ((void(*)(id, SEL, SEL, id, unsigned char))oc_ms)(g_uideleg,
                oc_sel("performSelectorOnMainThread:withObject:waitUntilDone:"), oc_sel("yshgTick:"), Nil, 0);
        }
    }
    return NULL;
}

static void ui_init(void) {
    if (!oc_ms) return;
    // 先建 delegate 类/实例(纯 NSObject, dyld 早期可安全创建), 好让轮询线程能 performSelector
    Class cls = oc_allocpair(oc_getclass("NSObject"), "YSHGDriverObj", 0);
    if (cls) {
        oc_addmethod(cls, oc_sel("yshgBuild:"), (void *)imp_tick_build, "v@:@");
        oc_addmethod(cls, oc_sel("yshgTick:"), (void *)imp_tick, "v@:@");
        oc_register(cls);
        id d = ((id(*)(id, SEL))oc_ms)((id)cls, oc_sel("alloc"));
        g_uideleg = ((id(*)(id, SEL))oc_ms)(d, oc_sel("init"));
    }
    dl_log("UI init: driver=%p", (void *)g_uideleg);
    static pthread_t th;
    if (pthread_create(&th, NULL, ui_loop, NULL) == 0) pthread_detach(th);
    else dl_log("UI init: 线程创建失败");
}

// ================= v2.3 TS -> MP4 重封装器 (纯 C, worker 线程直跑) =================
// AVFoundation 读不了本地 MPEG-TS(实测 passthrough/转码都 status=4), 自写:
// TS(PAT/PMT/PES) -> H.264 AnnexB->AVCC + ADTS->裸AAC -> MP4(ftyp/mdat/moov)。
// 流式读入(块大小 = 188 整数倍), 内存只占采样表。
typedef struct { uint32_t size; uint64_t dts; int64_t cts_off; int key; uint64_t off; } MVS;
typedef struct { uint32_t size; uint64_t off; } MAS;
static volatile int m_oom;   /* ★ v4.14.0: 任一 realloc 失败即置位, 封装体面放弃 */
static MVS *mvs; static long mnv, mvcap;
static MAS *mas; static long man, macap;
/* ★ v4.14.0: realloc 一律查 NULL —— 原来失败会把指针置 NULL, 下一句 mvs[mnv++] 直接崩 */
static void m_vpush(const MVS *s) {
    if (m_oom) return;
    if (mnv == mvcap) {
        long nc = mvcap ? mvcap * 2 : 8192;
        MVS *p = (MVS *)realloc(mvs, (size_t)nc * sizeof(MVS));
        if (!p) { m_oom = 1; return; }
        mvs = p; mvcap = nc;
    }
    mvs[mnv++] = *s;
}
static void m_apush(const MAS *s) {
    if (m_oom) return;
    if (man == macap) {
        long nc = macap ? macap * 2 : 8192;
        MAS *p = (MAS *)realloc(mas, (size_t)nc * sizeof(MAS));
        if (!p) { m_oom = 1; return; }
        mas = p; macap = nc;
    }
    mas[man++] = *s;
}

static unsigned char m_sps[512]; static int m_sps_len;
static int g_mw, g_mh;   /* 封装后分辨率 (MUXSTAT 同源), 供记录显示 */
static uint64_t g_mdur_ms;   /* 封装后的视频时长 (ms), ts2mp4_file 写入 */
static unsigned char m_pps[512]; static int m_pps_len;
static int m_a_ot = 2, m_a_freq = 4, m_a_ch = 2, m_a_freq_hz = 44100;
static int m_vw = 0, m_vh = 0;

static FILE *m_out; static uint64_t m_pos;
static void m_w(const void *d, size_t n) { if (n) fwrite(d, 1, n, m_out); m_pos += n; }
static void m_wu8(unsigned v) { unsigned char t = (unsigned char)v; m_w(&t, 1); }
static void m_wu16(unsigned v) { unsigned char t[2] = { (unsigned char)(v >> 8), (unsigned char)v }; m_w(t, 2); }
static void m_wu32(uint32_t v) { unsigned char t[4] = { (unsigned char)(v >> 24), (unsigned char)(v >> 16), (unsigned char)(v >> 8), (unsigned char)v }; m_w(t, 4); }

static void m_put16(unsigned char *p, unsigned v) { p[0] = (unsigned char)(v >> 8); p[1] = (unsigned char)v; }
static void m_put32(unsigned char *p, uint32_t v) { p[0] = (unsigned char)(v >> 24); p[1] = (unsigned char)(v >> 16); p[2] = (unsigned char)(v >> 8); p[3] = (unsigned char)v; }

typedef struct { unsigned char *p; size_t n, cap; } MBuf;
static void mb_need(MBuf *b, size_t add) {
    if (m_oom) return;
    if (b->n + add > b->cap) {
        size_t nc = (b->n + add) * 2 + 4096;
        unsigned char *p = (unsigned char *)realloc(b->p, nc);
        if (!p) { m_oom = 1; return; }
        b->p = p; b->cap = nc;
    }
}
static void mb_put(MBuf *b, const void *d, size_t n) { if (m_oom) return; mb_need(b, n); if (m_oom || !b->p) return; if (n) memcpy(b->p + b->n, d, n); b->n += n; }
static void mb_u8(MBuf *b, unsigned v)  { unsigned char t = (unsigned char)v; mb_put(b, &t, 1); }
static void mb_u16(MBuf *b, unsigned v) { unsigned char t[2]; m_put16(t, v); mb_put(b, t, 2); }
static void mb_u24(MBuf *b, unsigned v) { mb_u16(b, v >> 8); mb_u8(b, v); }
static void mb_u32(MBuf *b, uint32_t v) { unsigned char t[4]; m_put32(t, v); mb_put(b, t, 4); }
static size_t mb_open(MBuf *b, const char *type) { size_t pos = b->n; mb_u32(b, 0); mb_put(b, type, 4); return pos; }
static void mb_close(MBuf *b, size_t pos) { if (m_oom || !b->p) return; m_put32(b->p + pos, (uint32_t)(b->n - pos)); }
static void mb_matrix(MBuf *b) {
    static const unsigned char m[36] = { 0,1,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0, 0,1,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0, 0x40,0,0,0 };
    mb_put(b, m, 36);
}

// ---- 采样提取 ----
static void sps_wh(const unsigned char *s, int n, int *W, int *H);
static void m_video_pes(const unsigned char *d, size_t n, uint64_t dts90k, int64_t cts_off) {
    if (n < 5) return;
    unsigned char *tmp = NULL; size_t tn = 0, tc = 0;
    int key = 0;
    size_t i = 0;
    while (i + 3 <= n && !(d[i] == 0 && d[i + 1] == 0 && d[i + 2] == 1)) i++;
    if (i + 3 > n) return;
    size_t nal_start = i + 3;
    size_t k = nal_start;
    while (k + 3 <= n) {
        if (d[k] == 0 && d[k + 1] == 0 && d[k + 2] == 1) {
            size_t end = k;
            while (end > nal_start && d[end - 1] == 0) end--;
            size_t nlen = end - nal_start;
            if (nlen > 0) {
                const unsigned char *nal = d + nal_start;
                int type = nal[0] & 0x1F;
                if (type == 5) key = 1;
                if (type == 7 && nlen <= sizeof(m_sps)) {
                    memcpy(m_sps, nal, nlen); m_sps_len = (int)nlen;
                    int w2 = 0, h2 = 0; sps_wh(m_sps + 1, m_sps_len - 1, &w2, &h2);
                    if (w2 > 0 && h2 > 0) { m_vw = w2; m_vh = h2; }
                }
                if (type == 8 && nlen <= sizeof(m_pps)) { memcpy(m_pps, nal, nlen); m_pps_len = (int)nlen; }
                {
                    if (tn + 4 + nlen > tc) { size_t nc = (tn + 4 + nlen) * 2 + 4096;
                        unsigned char *np2 = (unsigned char *)realloc(tmp, nc);
                        if (!np2) { m_oom = 1; free(tmp); return; } tmp = np2; tc = nc; }
                    m_put32(tmp + tn, (uint32_t)nlen); tn += 4;
                    memcpy(tmp + tn, nal, nlen); tn += nlen;
                }
            }
            nal_start = k + 3; k += 3;
        } else k++;
    }
    if (nal_start < n) {
        size_t nlen = n - nal_start;
        const unsigned char *nal = d + nal_start;
        int type = nal[0] & 0x1F;
        if (type == 5) key = 1;
        if (type == 7 && nlen <= sizeof(m_sps)) { memcpy(m_sps, nal, nlen); m_sps_len = (int)nlen; }
        if (type == 8 && nlen <= sizeof(m_pps)) { memcpy(m_pps, nal, nlen); m_pps_len = (int)nlen; }
        {
            if (tn + 4 + nlen > tc) { size_t nc = (tn + 4 + nlen) * 2 + 4096;
                unsigned char *np2 = (unsigned char *)realloc(tmp, nc);
                if (!np2) { m_oom = 1; free(tmp); return; } tmp = np2; tc = nc; }
            m_put32(tmp + tn, (uint32_t)nlen); tn += 4;
            memcpy(tmp + tn, nal, nlen); tn += nlen;
        }
    }
    if (tn > 0) {
        MVS s; memset(&s, 0, sizeof s);
        s.size = (uint32_t)tn; s.dts = dts90k; s.cts_off = cts_off; s.key = key; s.off = m_pos;
        m_w(tmp, tn); m_vpush(&s);
    }
    free(tmp);
}
static void m_audio_pes(const unsigned char *d, size_t n, uint64_t pts90k) {
    size_t i = 0; uint64_t pts = pts90k;
    while (i + 7 <= n) {
        if (d[i] != 0xFF || (d[i + 1] & 0xF6) != 0xF0) { i++; continue; }
        int len = ((d[i + 3] & 3) << 11) | (d[i + 4] << 3) | ((d[i + 5] >> 5) & 7);
        if (len < 7 || i + (size_t)len > n) break;
        if (man == 0) {
            int prof = (d[i + 2] >> 6) & 3;
            m_a_ot = prof + 1;
            m_a_freq = (d[i + 2] >> 2) & 0xF;
            m_a_ch = ((d[i + 2] & 1) << 2) | (d[i + 3] >> 6);
            { static const int ft[16] = { 96000,88200,64000,48000,44100,32000,24000,22050,16000,12000,11025,8000,7350,0,0,0 };
              m_a_freq_hz = ft[m_a_freq & 15]; if (m_a_freq_hz <= 0) m_a_freq_hz = 44100; }
        }
        MAS s; memset(&s, 0, sizeof s);
        s.size = (uint32_t)(len - 7); s.off = m_pos;
        m_w(d + i + 7, len - 7); m_apush(&s);
        pts += (1024ULL * 90000) / (uint64_t)m_a_freq_hz;
        i += (size_t)len;
    }
}

// ---- PES 状态 ----
typedef struct { unsigned char *p; size_t n, cap; uint64_t pts; int64_t cts_off; int have; } MPes;
static MPes m_vc, m_ac;
static void m_flush(int is_video) {
    MPes *c = is_video ? &m_vc : &m_ac;
    if (c->have && c->n) {
        if (is_video) m_video_pes(c->p, c->n, c->pts, c->cts_off);
        else m_audio_pes(c->p, c->n, c->pts);
    }
    c->n = 0; c->have = 0;
}
static void m_collect(int is_video, const unsigned char *pl, int plen, int pusi) {
    MPes *c = is_video ? &m_vc : &m_ac;
    if (pusi) {
        m_flush(is_video);
        if (plen >= 9 && pl[0] == 0 && pl[1] == 0 && pl[2] == 1) {
            int flags2 = pl[7], hdrlen = pl[8];
            uint64_t pts = 0, dts = 0; int have_dts = 0;
            if ((flags2 >> 6) >= 2 && plen >= 14) {
                const unsigned char *q = pl + 9;
                pts = ((uint64_t)((q[0] >> 1) & 7) << 30) | ((uint64_t)q[1] << 22) |
                      ((uint64_t)(q[2] >> 1) << 15) | ((uint64_t)q[3] << 7) | (uint64_t)(q[4] >> 1);
                if ((flags2 >> 6) == 3 && plen >= 19) {          // DTS 也在
                    const unsigned char *r = q + 5;
                    dts = ((uint64_t)((r[0] >> 1) & 7) << 30) | ((uint64_t)r[1] << 22) |
                          ((uint64_t)(r[2] >> 1) << 15) | ((uint64_t)r[3] << 7) | (uint64_t)(r[4] >> 1);
                    have_dts = 1;
                }
            }
            c->cts_off = have_dts ? (int64_t)(pts - dts) : 0;   // ctts 用
            int ds = 9 + hdrlen;
            if (ds <= plen) {
                size_t add = (size_t)(plen - ds);
                if (c->n + add > c->cap) { size_t nc = (c->n + add) * 2 + 65536;
                    unsigned char *np2 = (unsigned char *)realloc(c->p, nc);
                    if (!np2) { m_oom = 1; return; } c->p = np2; c->cap = nc; }
                memcpy(c->p + c->n, pl + ds, add); c->n += add;
                c->pts = have_dts ? dts : pts; c->have = 1;   // 解码序
            }
        }
    } else if (c->have) {
        if (c->n + (size_t)plen > c->cap) { size_t nc = (c->n + (size_t)plen) * 2 + 65536;
            unsigned char *np2 = (unsigned char *)realloc(c->p, nc);
            if (!np2) { m_oom = 1; return; } c->p = np2; c->cap = nc; }
        memcpy(c->p + c->n, pl, (size_t)plen); c->n += (size_t)plen;
    }
}

// ---- 逐包处理(状态跨块保持) ----
static int m_vpid = -1, m_apid = -1, m_pmt_pid = -1, m_pmt_got = 0;
static void m_packet(const unsigned char *p) {
    if (p[0] != 0x47 || (p[1] & 0x80)) return;
    int pusi = (p[1] >> 6) & 1;
    int pid = ((p[1] & 0x1F) << 8) | p[2];
    int afc = (p[3] >> 4) & 3;
    int off = 4;
    if (afc & 2) off += 1 + p[4];
    if (!(afc & 1) || off >= 188) return;
    const unsigned char *pl = p + off;
    int plen = 188 - off;                       // ★ 到包尾 187
    if (m_pmt_pid < 0 && pid == 0 && pusi && plen > 2) {
        int pf = pl[0];
        if (pf < plen - 1) {
            const unsigned char *t = pl + 1 + pf;
            if (t[0] == 0x00 && plen - 1 - pf >= 12) {
                int i = 8, end = 3 + (((t[1] & 0x0F) << 8) | t[2]) - 4;
                if (end > plen - 1 - pf) end = plen - 1 - pf;
                while (i + 4 <= end) {
                    int prog = (t[i] << 8) | t[i + 1];
                    int p2 = ((t[i + 2] & 0x1F) << 8) | t[i + 3];
                    if (prog != 0 && p2 != 0x1FFF) { m_pmt_pid = p2; break; }
                    i += 4;
                }
            }
        }
        return;
    }
    if (m_pmt_pid > 0 && !m_pmt_got && pid == m_pmt_pid && pusi && plen > 2) {
        int pf = pl[0];
        if (pf < plen - 1) {
            const unsigned char *t = pl + 1 + pf;
            if (t[0] == 0x02 && plen - 1 - pf >= 14) {
                int pil = ((t[10] & 0x0F) << 8) | t[11];
                int i = 12 + pil, end = 3 + (((t[1] & 0x0F) << 8) | t[2]) - 4;
                if (end > plen - 1 - pf) end = plen - 1 - pf;
                while (i + 5 <= end) {
                    int st = t[i], ep = ((t[i + 1] & 0x1F) << 8) | t[i + 2];
                    if (st == 0x1B && m_vpid < 0) m_vpid = ep;
                    else if ((st == 0x0F || st == 0x11) && m_apid < 0) m_apid = ep;
                    i += 5 + ((t[i + 3] & 0x0F) << 8 | t[i + 4]);
                }
                if (m_vpid > 0) m_pmt_got = 1;
            }
        }
        return;
    }
    if (m_vpid < 0) return;
    if (pid == m_vpid) m_collect(1, pl, plen, pusi);
    else if (m_apid > 0 && pid == m_apid) m_collect(0, pl, plen, pusi);
}

// SPS 解析: 返回宽高 (失败 0)
static void sps_wh(const unsigned char *s, int n, int *W, int *H) {
    int bp = 0;
    unsigned char *cl = NULL;                        // 去 EP 的副本
    if (n > 2) {
        cl = (unsigned char *)malloc((size_t)n);
        int ci = 0, zr = 0;
        for (int i = 0; i < n; i++) {
            if (zr >= 2 && s[i] == 3) { zr = 0; continue; }   // 00 00 03 -> 00 00
            cl[ci++] = s[i];
            zr = s[i] == 0 ? zr + 1 : 0;
        }
        n = ci;
    }
    const unsigned char *sp = cl ? cl : s;
    #define GB() (bp < n * 8 ? ((sp[bp >> 3] >> (7 - (bp & 7))) & 1) : 0)
    #define U(nv2) do { res = 0; for (int q = 0; q < (nv2); q++) { res = (res << 1) | GB(); bp++; } } while (0)
    #define UE() do { int z = 0; while (bp < n * 8 && !GB()) { z++; bp++; } bp++; res = 0; for (int q = 0; q < z; q++) { res = (res << 1) | GB(); bp++; } res = z ? (int)((1u << z) - 1 + res) : 0; } while (0)
    int res;
    U(8);                 // profile_idc
    int prof = res;       // ★ 必须存下! res 马上被后续字段覆盖
    U(8); U(8);           // constraints + level
    UE();                 // seq_parameter_set_id
    int chroma = 1, scal = 0;
    if (prof == 100 || prof == 110 || prof == 122 || prof == 244 || prof == 44 || prof == 83 || prof == 86 || prof == 118 || prof == 128) {
        UE();             // chroma_format_idc
        chroma = res;
        if (res == 3) U(1);
        UE(); UE(); U(1); // bit_depth_luma/chroma, qpprime
        U(1); scal = res; // ★ seq_scaling_matrix_present_flag 是 1 位不是 UE
        if (scal) { free(cl); return; } /* 缩放表流不常见, 放弃宽高(保持 0, 不破坏流)
                                           ★ v4.14.6: 原来直接 return 泄漏去 EP 副本 cl */
    }
    UE();                 // log2_max_frame_num_minus4
    UE();                 // pic_order_cnt_type
    int pom = res;        /* ★ v4.14.3: 必须在 UE() 之后取值! 原来写在 UE() 之前,
                             pom 拿到的是 log2_max_frame_num_minus4 —— 只要它非 0,
                             poc_type 就错位, 宽高解析全崩 (128x32 那种) */
    if (pom == 0) UE();
    else if (pom == 1) { U(1); UE(); UE(); int cn = res; for (int i = 0; i < cn; i++) { if (bp < n*8) U(1); UE(); UE(); } }
    UE(); U(1);           // max_num_ref, gaps
    UE();                 // pic_width_in_mbs_minus1
    int wm1 = res;
    UE();                 // pic_height_in_map_units_minus1
    int hm1 = res;
    U(1);                 // frame_mbs_only_flag
    int fmo = res, mbaff = 0;
    if (!fmo) { U(1); mbaff = res; }   // mb_adaptive_frame_field_flag (仅场模式)
    U(1);                 // direct_8x8_inference_flag
    U(1);                 // frame_cropping_flag
    int crop = res;
    int ww = (wm1 + 1) * 16, hh = (hm1 + 1) * 16 * (fmo ? 1 : 2);
    if (crop) {
        UE(); int cl = res; UE(); int cr = res; UE(); int ct = res; UE(); int cb = res;
        /* ★ v4.14.3: 按 H.264 7.4.2.1.1 —— SubWidthC={1:2, 2:2, 3:1},
           SubHeightC={1:2, 2:1, 3:1}, CropUnitY = SubHeightC * (2 - frame_mbs_only_flag)
           (原来错用了 mbaff, 且 chroma=2/3 的单位是错的) */
        int swc = (chroma == 3) ? 1 : 2;
        int shc = (chroma >= 2) ? 1 : 2;
        int cux = chroma ? swc : 1;
        int cuy = chroma ? shc * (2 - fmo) : (2 - fmo);
        (void)mbaff;
        ww -= (cl + cr) * cux;
        hh -= (ct + cb) * cuy;
    }
    *W = ww; *H = hh;
    (void)chroma;
    free(cl);
    #undef GB
    #undef U
    #undef UE
}
static void build_m_avcc(MBuf *b) {
    size_t pos = mb_open(b, "avcC");
    mb_u8(b, 1);
    mb_u8(b, m_sps_len > 1 ? m_sps[1] : 66);
    mb_u8(b, m_sps_len > 2 ? m_sps[2] : 0);
    mb_u8(b, m_sps_len > 3 ? m_sps[3] : 30);
    mb_u8(b, 0xFF);
    mb_u8(b, 0xE0 | (m_sps_len ? 1 : 0));
    if (m_sps_len) { mb_u16(b, (unsigned)m_sps_len); mb_put(b, m_sps, (size_t)m_sps_len); }
    mb_u8(b, m_pps_len ? 1 : 0);
    if (m_pps_len) { mb_u16(b, (unsigned)m_pps_len); mb_put(b, m_pps, (size_t)m_pps_len); }
    mb_close(b, pos);
}
static void build_m_esds(MBuf *b) {
    size_t pos = mb_open(b, "esds");
    mb_u32(b, 0);
    size_t dsc = b->n;
    mb_u8(b, 0x03); mb_u8(b, 0);
    mb_u16(b, 1); mb_u8(b, 0);
    size_t dcd = b->n;
    mb_u8(b, 0x04); mb_u8(b, 0);
    mb_u8(b, 0x40); mb_u8(b, 0x15);
    mb_u24(b, 6144);
    mb_u32(b, 128000); mb_u32(b, 96000);
    mb_u8(b, 0x05); mb_u8(b, 2);
    mb_u8(b, (unsigned)((m_a_ot << 3) | (m_a_freq >> 1)));
    mb_u8(b, (unsigned)(((m_a_freq & 1) << 7) | (m_a_ch << 3)));
    mb_u8(b, 0x06); mb_u8(b, 1); mb_u8(b, 0x02);
    b->p[dcd + 1] = (unsigned char)(b->n - (dcd + 2));
    b->p[dsc + 1] = (unsigned char)(b->n - (dsc + 2));
    mb_close(b, pos);
}

static int ts2mp4_file(const char *in, const char *out) {
    FILE *in_f = fopen(in, "rb");
    if (!in_f) return 0;
    m_out = fopen(out, "wb");
    if (!m_out) { fclose(in_f); return 0; }
    m_pos = 0;
    mnv = man = 0; mvcap = macap = 0; mvs = NULL; mas = NULL;
    m_sps_len = m_pps_len = 0; m_vpid = m_apid = m_pmt_pid = -1; m_pmt_got = 0;
    m_oom = 0;
    memset(&m_vc, 0, sizeof m_vc); memset(&m_ac, 0, sizeof m_ac);

    { unsigned char ft[32];
      m_put32(ft, 32); memcpy(ft + 4, "ftyp", 4);
      memcpy(ft + 8, "isom", 4); m_put32(ft + 12, 512);
      memcpy(ft + 16, "isom", 4); memcpy(ft + 20, "iso2", 4);
      memcpy(ft + 24, "avc1", 4); memcpy(ft + 28, "mp41", 4);
      m_w(ft, 32); }
    uint64_t mdat_pos = m_pos;
    m_wu32(0);
    { unsigned char t[4] = { 'm','d','a','t' }; m_w(t, 4); }

    // 流式: 块 = 188 * 2000 (376KB), 状态跨块保持
    /* ★ v4.14.0: 原为 static —— 两个封装线程共用同一块缓冲, 数据互踩直接崩。
       改为每次调用独立分配 (376KB, 一次 malloc, 结束时释放)。 */
    unsigned char *chunk = (unsigned char *)malloc(188 * 2000);
    if (!chunk) { fclose(in_f); fclose(m_out); m_out = NULL; remove(out); return 0; }
    size_t got;
    long total_frames = 0;
    while ((got = fread(chunk, 1, 188 * 2000, in_f)) > 0) {
        size_t np = got / 188;
        for (size_t i = 0; i < np; i++) m_packet(chunk + i * 188);
    }
    fclose(in_f);
    m_flush(1); m_flush(0);
    total_frames = mnv + man;
    if (total_frames <= 0 || m_oom) {
        dl_log("MUX 放弃 (帧数=%ld%s)", total_frames, m_oom ? ", 内存不足" : "");
        fclose(m_out); m_out = NULL; remove(out); free(chunk); return 0;
    }

    uint64_t mdat_size = m_pos - mdat_pos;
    fseek(m_out, (long)mdat_pos, SEEK_SET);
    m_put32(chunk, (uint32_t)mdat_size); fwrite(chunk, 1, 4, m_out);
    fseek(m_out, 0, SEEK_END);
    free(chunk);                     /* ★ v4.14.0 回填 mdat 大小后即可释放 */

    uint64_t v_ms = 1000, a_ms = 1000, v_dur90 = 3000;
    if (mnv >= 2) { v_dur90 = mvs[mnv - 1].dts - mvs[0].dts; v_ms = v_dur90 / 90; }
    g_mdur_ms = v_ms;
    if (man) a_ms = (uint64_t)man * 1024ULL * 1000ULL / (uint64_t)m_a_freq_hz;
    if (!v_ms) v_ms = 1000; if (!a_ms) a_ms = 1000;

    MBuf moov; memset(&moov, 0, sizeof moov);
    size_t mpos0 = mb_open(&moov, "moov");
    size_t p1 = mb_open(&moov, "mvhd");
    mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, 0);
    mb_u32(&moov, 1000);
    uint64_t mv = v_ms > a_ms ? v_ms : a_ms; if (!mv) mv = 1000;
    mb_u32(&moov, (uint32_t)mv);
    mb_u32(&moov, 0x00010000); mb_u16(&moov, 0x0100);
    mb_u16(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, 0);
    mb_matrix(&moov);
    for (int i = 0; i < 6; i++) mb_u32(&moov, 0);
    mb_u32(&moov, 3);
    mb_close(&moov, p1);
    if (mnv) {
        size_t tk = mb_open(&moov, "trak");
        size_t tkh = mb_open(&moov, "tkhd");
        mb_u32(&moov, 3); mb_u32(&moov, 0); mb_u32(&moov, 0);   // ★ flags=3: enabled+in_movie (0=不渲染!)
        mb_u32(&moov, 1); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)v_ms);
        mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_u16(&moov, 0); mb_u16(&moov, 0); mb_u16(&moov, 0); mb_u16(&moov, 0);
        mb_matrix(&moov);
        mb_u32(&moov, (uint32_t)(m_vw << 16)); mb_u32(&moov, (uint32_t)(m_vh << 16));
        mb_close(&moov, tkh);
        {   // elst: 空编辑到首个 DTS + 正片 (ffmpeg 同款形态)
            size_t el = mb_open(&moov, "elst"); mb_u32(&moov, 0); mb_u32(&moov, 1);
            mb_u32(&moov, (uint32_t)v_ms); mb_u32(&moov, 0); mb_u32(&moov, 0x00010000);
            mb_close(&moov, el);
        }
        size_t md = mb_open(&moov, "mdia");
        size_t mh = mb_open(&moov, "mdhd");
        mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_u32(&moov, 90000); mb_u32(&moov, (uint32_t)v_dur90);
        mb_u16(&moov, 0x55C4); mb_u16(&moov, 0);
        mb_close(&moov, mh);
        size_t hl = mb_open(&moov, "hdlr");
        mb_u32(&moov, 0); mb_u32(&moov, 0); mb_put(&moov, "vide", 4);
        mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_put(&moov, "VideoHandler", 12); mb_u8(&moov, 0);
        mb_close(&moov, hl);
        size_t mi = mb_open(&moov, "minf");
        size_t v1 = mb_open(&moov, "vmhd"); mb_u32(&moov, 1);   /* flags=1 规范要求 */
        mb_u16(&moov, 0); mb_u16(&moov, 0); mb_u16(&moov, 0); mb_u16(&moov, 0);  /* graphicsmode + opcolor[3] = 4 个 u16, vmhd 必须 20 字节 */
        mb_close(&moov, v1);
        size_t di = mb_open(&moov, "dinf");
        size_t dr = mb_open(&moov, "dref");
        mb_u32(&moov, 0); mb_u32(&moov, 1);
        size_t u1 = mb_open(&moov, "url "); mb_u32(&moov, 1); mb_close(&moov, u1);
        mb_close(&moov, dr); mb_close(&moov, di);
        size_t st = mb_open(&moov, "stbl");
        size_t sd = mb_open(&moov, "stsd");
        mb_u32(&moov, 0); mb_u32(&moov, 1);
        size_t a1 = mb_open(&moov, "avc1");
        for (int i = 0; i < 6; i++) mb_u8(&moov, 0);
        mb_u16(&moov, 1);
        mb_u16(&moov, 0); mb_u16(&moov, 0);
        for (int i = 0; i < 12; i++) mb_u8(&moov, 0);
        mb_u16(&moov, (unsigned)m_vw); mb_u16(&moov, (unsigned)m_vh);
        mb_u32(&moov, 0x00480000); mb_u32(&moov, 0x00480000);
        mb_u32(&moov, 0); mb_u16(&moov, 1);
        for (int i = 0; i < 32; i++) mb_u8(&moov, 0);
        mb_u16(&moov, 0x0018); mb_u16(&moov, 0xFFFF);
        build_m_avcc(&moov);
        mb_close(&moov, a1);
        mb_close(&moov, sd);
        // stts
        size_t t1 = mb_open(&moov, "stts"); mb_u32(&moov, 0);
        if (mnv >= 2) {
            long runs = 1;
            uint64_t cd = mvs[1].dts - mvs[0].dts; if (!cd) cd = 1;
            for (long i = 2; i < mnv; i++) {
                uint64_t d2 = mvs[i].dts - mvs[i - 1].dts; if (!d2) d2 = 1;
                if (d2 != cd) runs++;
            }
            mb_u32(&moov, (uint32_t)runs);
            cd = mvs[1].dts - mvs[0].dts; if (!cd) cd = 1;
            long cn = 1;
            for (long i = 2; i < mnv; i++) {
                uint64_t d2 = mvs[i].dts - mvs[i - 1].dts; if (!d2) d2 = 1;
                if (d2 != cd) { mb_u32(&moov, (uint32_t)cn); mb_u32(&moov, (uint32_t)cd); cd = d2; cn = 1; }
                else cn++;
            }
            mb_u32(&moov, (uint32_t)(cn + 1)); mb_u32(&moov, (uint32_t)cd);   // ★ +1: 末样本沿用前一 delta, 否则 stts 少 1 与 stsz 不一致 → Apple 判轨无效
        } else { mb_u32(&moov, 1); mb_u32(&moov, (uint32_t)(mnv ? mnv : 1)); mb_u32(&moov, 3000); }
        mb_close(&moov, t1);
        long kc = 0;
        for (long i = 0; i < mnv; i++) if (mvs[i].key) kc++;
        if (kc > 0 && kc < mnv) {
            // ctts (B 帧显示序偏移)
        {
            int need = 0;
            for (long i = 0; i < mnv; i++) if (mvs[i].cts_off != 0) { need = 1; break; }
            if (need) {
                size_t c1 = mb_open(&moov, "ctts"); mb_u32(&moov, 0);
                long runs = 0, i = 0;
                while (i < mnv) {
                    long j = i; int64_t off0 = mvs[i].cts_off;
                    while (j < mnv && mvs[j].cts_off == off0) j++;
                    runs++; i = j;
                }
                mb_u32(&moov, (uint32_t)runs);
                i = 0;
                while (i < mnv) {
                    long j = i; int64_t off0 = mvs[i].cts_off;
                    while (j < mnv && mvs[j].cts_off == off0) j++;
                    mb_u32(&moov, (uint32_t)(j - i));
                    mb_u32(&moov, off0 >= 0 ? (uint32_t)off0 : (uint32_t)(-off0) | 0x80000000u);
                    i = j;
                }
                mb_close(&moov, c1);
            }
        }
        size_t s1 = mb_open(&moov, "stss"); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)kc);
            for (long i = 0; i < mnv; i++) if (mvs[i].key) mb_u32(&moov, (uint32_t)(i + 1));
            mb_close(&moov, s1);
        }
        size_t s2 = mb_open(&moov, "stsc"); mb_u32(&moov, 0); mb_u32(&moov, 1);
        mb_u32(&moov, 1); mb_u32(&moov, 1); mb_u32(&moov, 1);
        mb_close(&moov, s2);
        size_t s3 = mb_open(&moov, "stsz"); mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)mnv);
        for (long i = 0; i < mnv; i++) mb_u32(&moov, mvs[i].size);
        mb_close(&moov, s3);
        size_t s4 = mb_open(&moov, "stco"); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)mnv);
        for (long i = 0; i < mnv; i++) mb_u32(&moov, (uint32_t)mvs[i].off);
        mb_close(&moov, s4);
        mb_close(&moov, st); mb_close(&moov, mi); mb_close(&moov, md); mb_close(&moov, tk);
    }
    if (man) {
        size_t tk = mb_open(&moov, "trak");
        size_t tkh = mb_open(&moov, "tkhd");
        mb_u32(&moov, 3); mb_u32(&moov, 0); mb_u32(&moov, 0);   // ★ flags=3
        mb_u32(&moov, 2); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)a_ms);
        mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_u16(&moov, 0); mb_u16(&moov, 0); mb_u16(&moov, 0x0100); mb_u16(&moov, 0);
        mb_matrix(&moov);
        mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_close(&moov, tkh);
        {
            size_t el = mb_open(&moov, "elst"); mb_u32(&moov, 0); mb_u32(&moov, 1);
            mb_u32(&moov, (uint32_t)a_ms); mb_u32(&moov, 0); mb_u32(&moov, 0x00010000);
            mb_close(&moov, el);
        }
        size_t md = mb_open(&moov, "mdia");
        size_t mh = mb_open(&moov, "mdhd");
        mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_u32(&moov, (uint32_t)m_a_freq_hz); mb_u32(&moov, (uint32_t)((uint64_t)man * 1024ULL));
        mb_u16(&moov, 0x55C4); mb_u16(&moov, 0);
        mb_close(&moov, mh);
        size_t hl = mb_open(&moov, "hdlr");
        mb_u32(&moov, 0); mb_u32(&moov, 0); mb_put(&moov, "soun", 4);
        mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, 0);
        mb_put(&moov, "SoundHandler", 12); mb_u8(&moov, 0);
        mb_close(&moov, hl);
        size_t mi = mb_open(&moov, "minf");
        size_t v2 = mb_open(&moov, "smhd"); mb_u32(&moov, 0); mb_u16(&moov, 0); mb_u16(&moov, 0); mb_close(&moov, v2);
        size_t di = mb_open(&moov, "dinf");
        size_t dr = mb_open(&moov, "dref");
        mb_u32(&moov, 0); mb_u32(&moov, 1);
        size_t u1 = mb_open(&moov, "url "); mb_u32(&moov, 1); mb_close(&moov, u1);
        mb_close(&moov, dr); mb_close(&moov, di);
        size_t st = mb_open(&moov, "stbl");
        size_t sd = mb_open(&moov, "stsd");
        mb_u32(&moov, 0); mb_u32(&moov, 1);
        size_t a1 = mb_open(&moov, "mp4a");
        for (int i = 0; i < 6; i++) mb_u8(&moov, 0);
        mb_u16(&moov, 1);
        mb_u16(&moov, 0); mb_u16(&moov, 0); mb_u32(&moov, 0);
        mb_u16(&moov, (unsigned)m_a_ch); mb_u16(&moov, 16);
        mb_u16(&moov, 0); mb_u16(&moov, 0);
        mb_u32(&moov, ((uint32_t)m_a_freq_hz << 16));
        build_m_esds(&moov);
        mb_close(&moov, a1);
        mb_close(&moov, sd);
        size_t t1 = mb_open(&moov, "stts"); mb_u32(&moov, 0);
        mb_u32(&moov, 1); mb_u32(&moov, (uint32_t)man); mb_u32(&moov, 1024);
        mb_close(&moov, t1);
        size_t s2 = mb_open(&moov, "stsc"); mb_u32(&moov, 0); mb_u32(&moov, 1);
        mb_u32(&moov, 1); mb_u32(&moov, 1); mb_u32(&moov, 1);
        mb_close(&moov, s2);
        size_t s3 = mb_open(&moov, "stsz"); mb_u32(&moov, 0); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)man);
        for (long i = 0; i < man; i++) mb_u32(&moov, mas[i].size);
        mb_close(&moov, s3);
        size_t s4 = mb_open(&moov, "stco"); mb_u32(&moov, 0); mb_u32(&moov, (uint32_t)man);
        for (long i = 0; i < man; i++) mb_u32(&moov, (uint32_t)mas[i].off);
        mb_close(&moov, s4);
        mb_close(&moov, st); mb_close(&moov, mi); mb_close(&moov, md); mb_close(&moov, tk);
    }
    mb_close(&moov, mpos0);
    g_mw = m_vw; g_mh = m_vh;
    dl_log("MUXSTAT vf=%ld af=%ld %dx%d prof=%d vpid=%d apid=%d",
           (long)mnv, (long)man, m_vw, m_vh,
           m_sps_len > 1 ? m_sps[1] : 0, (int)m_vpid, (int)m_apid);
    if (m_oom || !moov.p) {
        dl_log("MUX 放弃: moov 组装内存不足");
        free(moov.p); fclose(m_out); m_out = NULL; remove(out);
        free(mvs); mvs = NULL; mnv = mvcap = 0;
        free(mas); mas = NULL; man = macap = 0;
        free(m_vc.p); memset(&m_vc, 0, sizeof m_vc);
        free(m_ac.p); memset(&m_ac, 0, sizeof m_ac);
        return 0;
    }
    m_w(moov.p, moov.n);
    free(moov.p);
    fclose(m_out); m_out = NULL;
    free(mvs); mvs = NULL; mnv = mvcap = 0;
    free(mas); mas = NULL; man = macap = 0;
    free(m_vc.p); memset(&m_vc, 0, sizeof m_vc);
    free(m_ac.p); memset(&m_ac, 0, sizeof m_ac);
    return 1;
}
