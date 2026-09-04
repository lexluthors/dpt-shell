//
// Created by luoyesiqiu
//

#include "dpt_risk.h"
#include <android/api-level.h>
#include <climits>
#include <cerrno>
#include <ctime>
#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <sys/socket.h>
#include <vector>
#include "mbedtls/sha256.h"
#include "mz_crypt.h"
#include "dpt.h"

extern ShellConfig g_shell_config;

DPT_ENCRYPT NO_INLINE void dpt_crash() {
#ifdef DEBUG
    abort();
#else
    asm volatile(
#ifdef __aarch64__
    "mov x30,#0\t\n"
#elif __arm__
    "mov lr,#0\t\n"
#elif __i386__
    "ret\t\n"
#elif __x86_64__
    "pop %rbp\t\n"
#endif
);
#endif
}

DPT_ENCRYPT void junkCodeDexProtect(JNIEnv *env) {
    const char *className = g_shell_config.junk_class_name.empty()
            ? AY_OBFUSCATE(JUNK_CLASS_FULL_NAME)
            : g_shell_config.junk_class_name.c_str();
    jclass klass = dpt::jni::FindClass(env, className);
    if(klass == nullptr) {
        dpt_crash();
    }
}

// Compare in-memory libc .text CRC with on-disk .text CRC; crash if mismatched.
DPT_ENCRYPT NO_INLINE void verifyLibcTextCrc() {
    Dl_info info = {};
    if (dladdr(reinterpret_cast<const void *>(&fopen), &info) == 0
        || info.dli_fbase == nullptr) {
        DLOGW("dladdr libc failed, skip text crc");
        return;
    }

    std::string libc_path;
    if (info.dli_fname != nullptr) {
        if (info.dli_fname[0] == '/') {
            libc_path.assign(info.dli_fname);
        } else {
            libc_path = find_so_path(info.dli_fname);
        }
    }
    if (libc_path.empty()) {
        libc_path = find_so_path(AY_OBFUSCATE("libc.so"));
    }
    if (libc_path.empty()) {
        DLOGW("cannot resolve libc path, skip text crc");
        return;
    }

    Elf_Shdr shdr = {};
    get_elf_section(&shdr, libc_path.c_str(), AY_OBFUSCATE(".text"));
    if (shdr.sh_size == 0) {
        DLOGW("libc .text section missing or empty, skip text crc");
        return;
    }

    FILE *fp = fopen(libc_path.c_str(), "r");
    if (fp == nullptr) {
        DLOGW("cannot open libc file: %s, skip text crc", libc_path.c_str());
        return;
    }

    if (fseek(fp, static_cast<long>(shdr.sh_offset), SEEK_SET) != 0) {
        DLOGW("fseek libc .text failed, skip text crc");
        fclose(fp);
        return;
    }

    auto *file_buf = static_cast<uint8_t *>(malloc(shdr.sh_size));
    if (file_buf == nullptr) {
        DLOGW("malloc for libc .text failed, skip text crc");
        fclose(fp);
        return;
    }

    size_t nread = fread(file_buf, 1, shdr.sh_size, fp);
    fclose(fp);
    if (nread != shdr.sh_size) {
        DLOGW("fread libc .text incomplete, skip text crc");
        DPT_FREE(file_buf);
        return;
    }

    const auto *mem_base = reinterpret_cast<const uint8_t *>(info.dli_fbase) + shdr.sh_addr;
    if (!isMemReadable(mem_base, shdr.sh_size)) {
        DLOGW("libc .text memory not readable, skip text crc");
        DPT_FREE(file_buf);
        return;
    }

    uint32_t crc_file = 0;
    uint32_t crc_mem = 0;
    size_t remaining = shdr.sh_size;
    size_t offset = 0;
    while (remaining > 0) {
        int32_t chunk = remaining > static_cast<size_t>(INT32_MAX)
                        ? INT32_MAX
                        : static_cast<int32_t>(remaining);
        crc_file = mz_crypt_crc32_update(crc_file, file_buf + offset, chunk);
        crc_mem = mz_crypt_crc32_update(crc_mem, mem_base + offset, chunk);
        offset += static_cast<size_t>(chunk);
        remaining -= static_cast<size_t>(chunk);
    }
    DPT_FREE(file_buf);

    DLOGD("libc .text crc file=%08x mem=%08x size=%u", crc_file, crc_mem,
          static_cast<unsigned>(shdr.sh_size));
    if (crc_file != crc_mem) {
        DLOGW("libc .text crc mismatch, file=%08x mem=%08x", crc_file, crc_mem);
        dpt_crash();
    }
}

// ======================= hardened risk detection =======================
// The checks below read /proc through raw syscalls (linux_syscall_support.h)
// so they keep working even when attackers hook libc open/read/readdir to
// fake /proc contents.

// Read a whole file (size bounded) using raw syscalls only.
DPT_ENCRYPT static std::vector<char> read_file_via_syscall(const char *path) {
    std::vector<char> buf;
    int fd = sys_open(path, O_RDONLY, 0);
    if (fd < 0) {
        return buf;
    }
    char tmp[4096];
    const size_t cap = 4 * 1024 * 1024;
    for (;;) {
        ssize_t n = sys_read(fd, tmp, sizeof(tmp));
        if (n <= 0) {
            break;
        }
        if (buf.size() + static_cast<size_t>(n) > cap) {
            break;
        }
        buf.insert(buf.end(), tmp, tmp + n);
    }
    sys_close(fd);
    buf.push_back('\0');
    return buf;
}

// Parse "TracerPid:\tNNN" from a /proc/self/status buffer.
DPT_ENCRYPT static int parse_tracer_pid(const char *status_buf) {
    const char *tracer_key = AY_OBFUSCATE("TracerPid:");
    const char *p = dpt_strstr(status_buf, tracer_key);
    if (p == nullptr) {
        return 0;
    }
    p += dpt_strlen(tracer_key);
    while (*p == ' ' || *p == '\t') {
        p++;
    }
    int tracer_pid = 0;
    while (*p >= '0' && *p <= '9') {
        tracer_pid = tracer_pid * 10 + (*p - '0');
        p++;
    }
    return tracer_pid;
}

// Cheap xorshift32 used to randomize the check schedule.
static uint32_t g_rng_state = 0;

DPT_ENCRYPT static uint32_t dpt_next_rand() {
    if (g_rng_state == 0) {
        struct timespec ts{};
        clock_gettime(CLOCK_MONOTONIC, &ts);
        g_rng_state = static_cast<uint32_t>(ts.tv_nsec)
                      ^ static_cast<uint32_t>(ts.tv_sec << 16)
                      ^ static_cast<uint32_t>(reinterpret_cast<uintptr_t>(&g_rng_state));
        if (g_rng_state == 0) {
            g_rng_state = 0x9e3779b9u;
        }
    }
    uint32_t x = g_rng_state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    g_rng_state = x;
    return x;
}

// frida-server / frida-gadget listen on 127.0.0.1:27042 by default.
DPT_ENCRYPT static bool probe_frida_port(int port) {
    int s = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0);
    if (s < 0) {
        return false;
    }
    sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_port = htons(static_cast<uint16_t>(port));
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);

    bool connected = false;
    int r = connect(s, reinterpret_cast<sockaddr *>(&addr), sizeof(addr));
    if (r == 0) {
        connected = true;
    } else if (errno == EINPROGRESS) {
        pollfd pfd{};
        pfd.fd = s;
        pfd.events = POLLOUT;
        if (poll(&pfd, 1, 150) > 0) {
            int soerr = 0;
            socklen_t len = sizeof(soerr);
            if (getsockopt(s, SOL_SOCKET, SO_ERROR, &soerr, &len) == 0 && soerr == 0) {
                connected = true;
            }
        }
    }
    close(s);
    return connected;
}

// Single-stepping or emulator-level tracing inflates a trivial integer loop
// by orders of magnitude. Require two consecutive anomalies so transient CPU
// throttling does not kill legitimate users.
DPT_ENCRYPT static void detectTimingAnomaly() {
    static int consecutive = 0;
    struct timespec t0{};
    struct timespec t1{};
    clock_gettime(CLOCK_MONOTONIC, &t0);
    volatile uint32_t acc = 0;
    for (uint32_t i = 0; i < 200000u; i++) {
        acc += i;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    long elapsed_ns = static_cast<long>(t1.tv_sec - t0.tv_sec) * 1000000000L
                      + static_cast<long>(t1.tv_nsec - t0.tv_nsec);
    if (elapsed_ns > 300L * 1000L * 1000L) {
        if (++consecutive >= 2) {
            DLOGW("timing anomaly detected, elapsed=%ldms", elapsed_ns / 1000000L);
            dpt_crash();
        }
    } else {
        consecutive = 0;
    }
}

DPT_ENCRYPT void detectFrida() {
    const char *frida_agent = AY_OBFUSCATE("frida-agent");
    const char *frida_gadget = AY_OBFUSCATE("frida-gadget");
    const char *frida_server = AY_OBFUSCATE("frida-server");
    const char *linjector = AY_OBFUSCATE("linjector");
    const char *pool_frida = AY_OBFUSCATE("pool-frida");
    const char *gmain = AY_OBFUSCATE("gmain");
    const char *gbus = AY_OBFUSCATE("gdbus");
    const char *gum_js_loop = AY_OBFUSCATE("gum-js-loop");

    // maps scan through raw syscalls (immune to libc open/read hooks)
    const char *maps_path = AY_OBFUSCATE("/proc/self/maps");
    std::vector<char> maps = read_file_via_syscall(maps_path);
    if (!maps.empty()) {
        const char *so_patterns[] = {frida_agent, frida_gadget, frida_server, linjector};
        for (const char *pattern : so_patterns) {
            if (dpt_strstr(maps.data(), pattern) != nullptr) {
                DLOGD("found frida pattern in maps");
                dpt_crash();
            }
        }
    } else if (find_in_maps(1, frida_agent) > 0) {
        DLOGD("found frida so");
        dpt_crash();
    }

    // frida-specific thread names must never appear in a clean process
    if (find_in_threads_list(2, pool_frida, gum_js_loop) > 0) {
        DLOGD("found frida-specific thread");
        dpt_crash();
    }
    if (find_in_threads_list(4, pool_frida, gmain, gbus, gum_js_loop) >= 2) {
        DLOGD("found frida threads");
        dpt_crash();
    }

    // default frida listening port
    if (probe_frida_port(27042)) {
        DLOGD("frida listening port detected");
        dpt_crash();
    }
}

DPT_ENCRYPT void detectDebugger() {
    // Primary path: read /proc/self/status via raw syscalls and parse it by
    // hand, so hooked libc open/read/sscanf cannot hide a tracer.
    const char *status_path = AY_OBFUSCATE("/proc/self/status");
    std::vector<char> status = read_file_via_syscall(status_path);
    if (!status.empty()) {
        int tracer_pid = parse_tracer_pid(status.data());
        if (tracer_pid != 0) {
            DLOGD("found tracer pid: %d", tracer_pid);
            dpt_crash();
        }
    } else {
        // Fallback to the stdio based check when raw syscalls are unavailable.
        FILE *fp = fopen(status_path, "r");
        if (fp != nullptr) {
            const char *tracer_key = AY_OBFUSCATE("TracerPid:");
            char line[256];
            while (fgets(line, sizeof(line), fp) != nullptr) {
                if (strncmp(line, tracer_key, strlen(tracer_key)) == 0) {
                    int tracer_pid = 0;
                    sscanf(line + strlen(tracer_key), "%d", &tracer_pid);
                    if (tracer_pid != 0) {
                        DLOGD("found tracer pid: %d", tracer_pid);
                        fclose(fp);
                        dpt_crash();
                    }
                    break;
                }
            }
            fclose(fp);
        }
    }

    // Cross-check: a release process must never host a JDWP thread.
    const char *jdwp_name = AY_OBFUSCATE("JDWP");
    if (find_in_threads_list(1, jdwp_name) > 0) {
        DLOGD("found JDWP thread");
        dpt_crash();
    }
}

[[noreturn]] DPT_ENCRYPT void *detectRiskOnThread(__unused void *args) {
    uint32_t round = 0;
    while (true) {
        bool run[4];
        run[0] = (g_shell_config.risk_check_flags & FLAG_DISABLE_FRIDA_DETECT) == 0;
        run[1] = (g_shell_config.risk_check_flags & FLAG_DISABLE_CRC_DETECT) == 0;
        run[2] = (g_shell_config.risk_check_flags & FLAG_DISABLE_ANTI_DEBUG) == 0;
        run[3] = run[2]; // timing check rides on the anti-debug flag

        // Rotate the check order every round so the schedule is not a fixed,
        // easy-to-anticipate sequence.
        for (uint32_t i = 0; i < 4; i++) {
            uint32_t idx = (round + i) & 3u;
            if (!run[idx]) {
                continue;
            }
            switch (idx) {
                case 0:
                    detectFrida();
                    break;
                case 1:
                    verifyLibcTextCrc();
                    break;
                case 2:
                    detectDebugger();
                    break;
                case 3:
                    detectTimingAnomaly();
                    break;
                default:
                    break;
            }
        }
        round++;

        // Randomized interval in [3, 9) seconds instead of a fixed 10s window.
        uint32_t delay = 3 + dpt_next_rand() % 6;
        sleep(delay);
    }
}

DPT_ENCRYPT void detectRisk() {
    pthread_t t;
    pthread_create(&t, nullptr, detectRiskOnThread, nullptr);
}

DPT_ENCRYPT void verifyAppSignature(JNIEnv *env, jobject context, const char *expectedSha256) {
    static std::string actual = {};
    if (context == nullptr || expectedSha256 == nullptr || strlen(expectedSha256) == 0) {
        DLOGW("signature check not configured, skip");
        return;
    }

    if(!actual.empty()) {
        if (dpt_strncasecmp(actual.c_str(), expectedSha256, 64) != 0) {
            DLOGW("signature cache verification failed, expected: %s actual: %s", expectedSha256, actual.c_str());
            dpt_crash();
        }
        return;
    }

    jobject pm = dpt::jni::CallObjectMethod(env, context,
            AY_OBFUSCATE("getPackageManager"),
            AY_OBFUSCATE("()Landroid/content/pm/PackageManager;"));
    if (pm == nullptr) {
        DLOGW("getPackageManager failed");
        dpt_crash();
        return;
    }

    jstring packageName = (jstring) dpt::jni::CallObjectMethod(env, context,
            AY_OBFUSCATE("getPackageName"),
            AY_OBFUSCATE("()Ljava/lang/String;"));
    if (packageName == nullptr) {
        DLOGW("getPackageName failed");
        dpt_crash();
        return;
    }

    int api = android_get_device_api_level();
    jint flags = (api >= 28) ? (jint)0x08000000 : (jint)0x40;

    jobject packageInfo = dpt::jni::CallObjectMethod(env, pm,
            AY_OBFUSCATE("getPackageInfo"),
            AY_OBFUSCATE("(Ljava/lang/String;I)Landroid/content/pm/PackageInfo;"),
            packageName, flags);
    if (packageInfo == nullptr) {
        DLOGW("getPackageInfo failed");
        dpt_crash();
        return;
    }

    jbyteArray certBytes = nullptr;
    if (api >= 28) {
        jobject signingInfo = dpt::jni::GetObjectField(env, packageInfo,
                AY_OBFUSCATE("signingInfo"),
                AY_OBFUSCATE("Landroid/content/pm/SigningInfo;"));
        if (signingInfo == nullptr) {
            DLOGW("signingInfo is null");
            dpt_crash();
            return;
        }
        jobjectArray signaturesArr = (jobjectArray) dpt::jni::CallObjectMethod(env, signingInfo,
                AY_OBFUSCATE("getApkContentsSigners"),
                AY_OBFUSCATE("()[Landroid/content/pm/Signature;"));
        if (signaturesArr == nullptr || env->GetArrayLength(signaturesArr) == 0) {
            DLOGW("getApkContentsSigners returned empty");
            dpt_crash();
            return;
        }
        jobject signature = env->GetObjectArrayElement(signaturesArr, 0);
        certBytes = (jbyteArray) dpt::jni::CallObjectMethod(env, signature,
                AY_OBFUSCATE("toByteArray"), AY_OBFUSCATE("()[B"));
    } else {
        jobjectArray signaturesArr = (jobjectArray) dpt::jni::GetObjectField(env, packageInfo,
                AY_OBFUSCATE("signatures"),
                AY_OBFUSCATE("[Landroid/content/pm/Signature;"));
        if (signaturesArr == nullptr || env->GetArrayLength(signaturesArr) == 0) {
            DLOGW("signatures field is empty");
            dpt_crash();
            return;
        }
        jobject signature = env->GetObjectArrayElement(signaturesArr, 0);
        certBytes = (jbyteArray) dpt::jni::CallObjectMethod(env, signature,
                AY_OBFUSCATE("toByteArray"), AY_OBFUSCATE("()[B"));
    }

    if (certBytes == nullptr) {
        DLOGW("certBytes is null");
        dpt_crash();
        return;
    }

    jsize certLen = env->GetArrayLength(certBytes);
    jbyte *certData = env->GetByteArrayElements(certBytes, nullptr);

    uint8_t sha256Output[32];
    mbedtls_sha256(reinterpret_cast<const unsigned char *>(certData),
                   static_cast<size_t>(certLen), sha256Output, 0);

    env->ReleaseByteArrayElements(certBytes, certData, JNI_ABORT);

    char sha256Hex[65] = {0};
    for (int i = 0; i < 32; i++) {
        snprintf(sha256Hex + i * 2, 3, "%02x", sha256Output[i]);
    }

    actual.assign(sha256Hex);

    if (dpt_strncasecmp(sha256Hex, expectedSha256, 64) != 0) {
        DLOGW("signature verification failed, expected: %s actual: %s", expectedSha256, sha256Hex);
        dpt_crash();
    }
}