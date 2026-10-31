/* SPDX-License-Identifier: GPL-2.0-only
 * Adapted from SpartanPort's differential tests:
 * https://github.com/FelipePrado0/SpartanPort/blob/main/tests/test_isa_emulate.c
 * Modified for Lantern Engine on 2026-10-31 to use its local emulator header and CPUID check. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "isa_emulate.h"
#include "isa_rewrite.h"
#include <cpuid.h>
#ifdef _WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#endif

static int host_has_required_isa(void) {
    unsigned a = 0, b = 0, c = 0, d = 0, leaf1 = 0, leaf7 = 0, ext1 = 0;
    if (__get_cpuid(1, &a, &b, &c, &d)) leaf1 = c;
    if (__get_cpuid_count(7, 0, &a, &b, &c, &d)) leaf7 = b;
    if (__get_cpuid(0x80000001u, &a, &b, &c, &d)) ext1 = c;
    return (leaf1 & (1u << 22)) && (leaf7 & (1u << 3)) && (ext1 & (1u << 5));
}

static const uint64_t EDGES[] = {0, 1, 2, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000, 0xffffffff,
                                 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff};
/* ctrl for BEXTR: start and len in {0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 255} crossed */
static const uint64_t BEXTR_FIELDS[] = {0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 255};
enum { EDGE_COUNT = sizeof EDGES / sizeof EDGES[0], FIELD_COUNT = sizeof BEXTR_FIELDS / sizeof BEXTR_FIELDS[0] };
enum { RANDOM_INPUTS = 20000 };
static const uint64_t RAX_START = 0x1122334455667788;
static const uint64_t FLAG_STARTS[] = {0, 0xcd5};

static uint64_t random_state = 0x9e3779b97f4a7c15;
static uint64_t xorshift64(void) {
    random_state ^= random_state << 13;
    random_state ^= random_state >> 7;
    random_state ^= random_state << 17;
    return random_state;
}

/* The red zone below rsp is stepped over before pushfq. */
#define FLAGS_OUT "\n\tleaq -128(%%rsp), %%rsp\n\tpushfq\n\tpopq %[f]\n\tleaq 128(%%rsp), %%rsp"
/* insn src, dst */
#define NATIVE1(mnemonic, size) \
    __asm__(mnemonic " %" size "[s1], %" size "[d]" FLAGS_OUT : [d] "+r"(dst), [f] "=r"(flags) : [s1] "r"(src1) : "cc")
/* insn src2, src1, dst (Intel: insn dst, src1, src2) */
#define NATIVE2(mnemonic, size) \
    __asm__(mnemonic " %" size "[s2], %" size "[s1], %" size "[d]" FLAGS_OUT \
            : [d] "+r"(dst), [f] "=r"(flags) : [s1] "r"(src1), [s2] "r"(src2) : "cc")
#define BY_WIDTH(macro, mnemonic) \
    do { if (width == 32) macro(mnemonic "l", "k"); else macro(mnemonic "q", "q"); } while (0)
#define BY_WIDTH16(macro, mnemonic) \
    do { if (width == 16) macro(mnemonic "w", "w"); else BY_WIDTH(macro, mnemonic); } while (0)

/* Runs the register form natively: dst = rax, src1 = rcx, src2 = rdx. Returns the new rax. */
static uint64_t native_register(uint8_t kind, int width, uint64_t src1, uint64_t src2, uint64_t *flags_out) {
    uint64_t dst = RAX_START, flags = 0;
    switch (kind) {
    case ISA_LZCNT: BY_WIDTH16(NATIVE1, "lzcnt"); break;
    case ISA_TZCNT: BY_WIDTH16(NATIVE1, "tzcnt"); break;
    case ISA_BLSI: BY_WIDTH(NATIVE1, "blsi"); break;
    case ISA_BLSMSK: BY_WIDTH(NATIVE1, "blsmsk"); break;
    case ISA_BLSR: BY_WIDTH(NATIVE1, "blsr"); break;
    case ISA_ANDN: BY_WIDTH(NATIVE2, "andn"); break;
    case ISA_BEXTR: BY_WIDTH(NATIVE2, "bextr"); break;
    default: abort();
    }
    *flags_out = flags;
    return dst;
}

static const char *kind_name(uint8_t kind) {
    static const char *const names[] = {
        "?", "MOVBE_LOAD", "MOVBE_STORE", "LZCNT", "TZCNT", "ANDN", "BEXTR", "BLSI", "BLSMSK", "BLSR",
        "VPMOVSXBW", "VPMOVSXBD", "VPMOVSXBQ", "VPMOVSXWD", "VPMOVSXWQ", "VPMOVSXDQ",
        "VPMOVZXBW", "VPMOVZXBD", "VPMOVZXBQ", "VPMOVZXWD", "VPMOVZXWQ", "VPMOVZXDQ"
    };
    return kind < sizeof names / sizeof names[0] ? names[kind] : "?";
}

static void fail(uint8_t kind, int width, uint64_t a, uint64_t b, const char *what, uint64_t expected, uint64_t got) {
    printf("isa-emulate-test FAILED: %s width %d input %#" PRIx64 ", %#" PRIx64 ": %s expected %#" PRIx64
           " got %#" PRIx64 "\n", kind_name(kind), width, a, b, what, expected, got);
    exit(1);
}

static IsaSite register_site(uint8_t kind, int width) {
    IsaSite site;
    memset(&site, 0, sizeof site);
    site.kind = kind;
    site.width = (uint8_t)width;
    site.dst = 0;
    site.src1 = 1;
    site.src2 = (kind == ISA_ANDN || kind == ISA_BEXTR) ? 2 : ISA_NO_REG;
    site.mem_slot = ISA_MEM_NONE;
    site.base = site.index = ISA_NO_REG;
    site.scale = 1;
    return site;
}

static void check_register(uint8_t kind, int width, uint64_t src1, uint64_t src2, unsigned round) {
    uint64_t native_flags;
    uint64_t expected = native_register(kind, width, src1, src2, &native_flags);
    IsaSite site = register_site(kind, width);
    IsaRegs regs;
    for (int r = 0; r < 16; r++) regs.gpr[r] = 0x0101010101010101ull * (uint64_t)r;
    regs.gpr[0] = RAX_START;
    regs.gpr[1] = src1;
    regs.gpr[2] = src2;
    uint64_t flags_start = FLAG_STARTS[round & 1];
    regs.rflags = flags_start;
    isa_emulate(&site, &regs);
    uint64_t defined = isa_defined_flags(kind);
    if (regs.gpr[0] != expected) fail(kind, width, src1, src2, "rax", expected, regs.gpr[0]);
    if ((regs.rflags ^ native_flags) & defined) fail(kind, width, src1, src2, "flags", native_flags & defined, regs.rflags & defined);
    if ((regs.rflags ^ flags_start) & ~defined) fail(kind, width, src1, src2, "undefined flags", flags_start, regs.rflags);
    if (regs.gpr[1] != src1 || regs.gpr[2] != src2) fail(kind, width, src1, src2, "sources", src1 ^ src2, regs.gpr[1] ^ regs.gpr[2]);
    for (int r = 3; r < 16; r++)
        if (regs.gpr[r] != 0x0101010101010101ull * (uint64_t)r) fail(kind, width, src1, src2, "other register", (uint64_t)r, regs.gpr[r]);
}

static void check_registers(void) {
    static const uint8_t kinds[] = {ISA_LZCNT, ISA_TZCNT, ISA_ANDN, ISA_BEXTR, ISA_BLSI, ISA_BLSMSK, ISA_BLSR};
    static const int widths[] = {16, 32, 64};
    unsigned round = 0;
    for (size_t k = 0; k < sizeof kinds; k++) {
        uint8_t kind = kinds[k];
        for (size_t w = 0; w < 3; w++) {
            int width = widths[w];
            if (width == 16 && kind != ISA_LZCNT && kind != ISA_TZCNT) continue;   /* VEX forms: 32/64 only */
            for (int a = 0; a < EDGE_COUNT; a++) {
                if (kind == ISA_BEXTR) {
                    for (int s = 0; s < FIELD_COUNT; s++)
                        for (int l = 0; l < FIELD_COUNT; l++)
                            check_register(kind, width, EDGES[a], BEXTR_FIELDS[s] | BEXTR_FIELDS[l] << 8, round++);
                } else {
                    for (int b = 0; b < EDGE_COUNT; b++) check_register(kind, width, EDGES[a], EDGES[b], round++);
                }
            }
            for (int i = 0; i < RANDOM_INPUTS; i++) {
                uint64_t a = xorshift64(), b = xorshift64();
                if (i & 1) a >>= a & 63;   /* leading zeros of every count */
                if (i & 2) a <<= b & 63;   /* trailing zeros of every count */
                if (kind == ISA_BEXTR && (i & 4)) b &= 0x7f7f;
                check_register(kind, width, a, b, round++);
            }
        }
    }
}

static IsaSite memory_site(uint8_t kind, int width) {
    IsaSite site = register_site(kind, width);
    site.base = 1;
    site.disp = 8;
    if (kind == ISA_MOVBE_LOAD) { site.src1 = ISA_NO_REG; site.mem_slot = ISA_MEM_SRC; }
    else { site.dst = ISA_NO_REG; site.src1 = 2; site.mem_slot = ISA_MEM_DST; }
    site.src2 = ISA_NO_REG;
    return site;
}

static void check_movbe(void) {
    static const int widths[] = {16, 32, 64};
    for (size_t w = 0; w < 3; w++) {
        int width = widths[w];
        for (int i = 0; i < RANDOM_INPUTS; i++) {
            unsigned char native_buffer[32], emulated_buffer[32];
            for (int j = 0; j < 32; j += 8) {
                uint64_t r = xorshift64();
                memcpy(native_buffer + j, &r, 8);
            }
            memcpy(emulated_buffer, native_buffer, sizeof emulated_buffer);
            uint64_t value = xorshift64(), dst = RAX_START;
            unsigned char *at = native_buffer + 8;
            /* load: rax <- [rcx + 8] */
            if (width == 16) __asm__("movbew %[m], %w[d]" : [d] "+r"(dst) : [m] "m"(*(uint16_t (*)[1])at));
            else if (width == 32) __asm__("movbel %[m], %k[d]" : [d] "+r"(dst) : [m] "m"(*(uint32_t (*)[1])at));
            else __asm__("movbeq %[m], %q[d]" : [d] "+r"(dst) : [m] "m"(*(uint64_t (*)[1])at));
            IsaSite site = memory_site(ISA_MOVBE_LOAD, width);
            IsaRegs regs = {.rflags = 0xcd5};
            regs.gpr[0] = RAX_START;
            regs.gpr[1] = (uint64_t)(uintptr_t)emulated_buffer;
            isa_emulate(&site, &regs);
            if (regs.gpr[0] != dst) fail(ISA_MOVBE_LOAD, width, regs.gpr[1], 0, "rax", dst, regs.gpr[0]);
            if (regs.rflags != 0xcd5) fail(ISA_MOVBE_LOAD, width, 0, 0, "flags", 0xcd5, regs.rflags);
            /* store: [rcx + 8] <- rdx */
            if (width == 16) __asm__("movbew %w[s], %[m]" : [m] "=m"(*(uint16_t (*)[1])at) : [s] "r"(value));
            else if (width == 32) __asm__("movbel %k[s], %[m]" : [m] "=m"(*(uint32_t (*)[1])at) : [s] "r"(value));
            else __asm__("movbeq %q[s], %[m]" : [m] "=m"(*(uint64_t (*)[1])at) : [s] "r"(value));
            site = memory_site(ISA_MOVBE_STORE, width);
            regs.gpr[2] = value;
            isa_emulate(&site, &regs);
            for (int j = 0; j < 32; j++)
                if (native_buffer[j] != emulated_buffer[j])
                    fail(ISA_MOVBE_STORE, width, value, (uint64_t)j, "byte", native_buffer[j], emulated_buffer[j]);
            if (regs.gpr[0] != dst || regs.gpr[2] != value) fail(ISA_MOVBE_STORE, width, value, 0, "rax", dst, regs.gpr[0]);
        }
    }
    /* Base, scaled index and negative displacement: rcx + rbx * 4 - 8. */
    unsigned char buffer[32];
    for (int j = 0; j < 32; j++) buffer[j] = (unsigned char)(j * 17 + 3);
    uint64_t dst = RAX_START;
    __asm__("movbel %[m], %k[d]" : [d] "+r"(dst) : [m] "m"(*(uint32_t (*)[1])(buffer + 12)));
    IsaSite site = memory_site(ISA_MOVBE_LOAD, 32);
    site.index = 3;
    site.scale = 4;
    site.disp = -8;
    IsaRegs regs = {.rflags = 0};
    regs.gpr[1] = (uint64_t)(uintptr_t)buffer;
    regs.gpr[3] = 5;
    isa_emulate(&site, &regs);
    if (regs.gpr[0] != dst) fail(ISA_MOVBE_LOAD, 32, 12, 0, "rax (indexed)", dst, regs.gpr[0]);
}

/* BEXTR r32, [rip + disp], r32: the address is image + disp. */
static void check_rip_relative(void) {
    static unsigned char image[256];
    enum { BUFFER_OFFSET = 100 };
    isa_emulate_set_image(image);
    for (int i = 0; i < RANDOM_INPUTS; i++) {
        uint32_t word = (uint32_t)xorshift64();
        uint64_t ctrl = xorshift64() & 0x3f3f, dst = RAX_START, flags = 0;
        memcpy(image + BUFFER_OFFSET, &word, 4);
        __asm__("bextrl %k[c], %[m], %k[d]" FLAGS_OUT
                : [d] "+r"(dst), [f] "=r"(flags) : [c] "r"(ctrl), [m] "m"(*(uint32_t (*)[1])(image + BUFFER_OFFSET)) : "cc");
        IsaSite site = register_site(ISA_BEXTR, 32);
        site.src1 = ISA_NO_REG;
        site.mem_slot = ISA_MEM_SRC;
        site.mem_flags = ISA_MEM_RIP_RELATIVE;
        site.disp = BUFFER_OFFSET;
        IsaRegs regs = {.rflags = FLAG_STARTS[i & 1]};
        regs.gpr[0] = RAX_START;
        regs.gpr[2] = ctrl;
        isa_emulate(&site, &regs);
        uint64_t defined = isa_defined_flags(ISA_BEXTR);
        if (regs.gpr[0] != dst) fail(ISA_BEXTR, 32, word, ctrl, "rax (rip)", dst, regs.gpr[0]);
        if ((regs.rflags ^ flags) & defined) fail(ISA_BEXTR, 32, word, ctrl, "flags (rip)", flags & defined, regs.rflags & defined);
    }
}

/* ANDN r, r, [rbx + 8] (32, 64) and BEXTR r32, [rbx - 4], r32: base + displacement memory sources. */
static void check_memory_sources(void) {
    for (int i = 0; i < RANDOM_INPUTS; i++) {
        unsigned char buffer[32];
        for (int j = 0; j < 32; j += 8) {
            uint64_t r = xorshift64();
            memcpy(buffer + j, &r, 8);
        }
        uint64_t src1 = xorshift64(), ctrl = xorshift64() & 0x3f3f, flags_start = FLAG_STARTS[i & 1];
        uint64_t defined = isa_defined_flags(ISA_ANDN);
        for (int width = 32; width <= 64; width += 32) {
            uint64_t dst = RAX_START, flags = 0;
            if (width == 32)
                __asm__("andnl %[m], %k[s1], %k[d]" FLAGS_OUT
                        : [d] "+r"(dst), [f] "=r"(flags) : [s1] "r"(src1), [m] "m"(*(uint32_t (*)[1])(buffer + 8)) : "cc");
            else
                __asm__("andnq %[m], %q[s1], %q[d]" FLAGS_OUT
                        : [d] "+r"(dst), [f] "=r"(flags) : [s1] "r"(src1), [m] "m"(*(uint64_t (*)[1])(buffer + 8)) : "cc");
            IsaSite site = register_site(ISA_ANDN, width);
            site.src2 = ISA_NO_REG;
            site.mem_slot = ISA_MEM_SRC;
            site.base = 3;
            site.disp = 8;
            IsaRegs regs = {.rflags = flags_start};
            regs.gpr[0] = RAX_START;
            regs.gpr[1] = src1;
            regs.gpr[3] = (uint64_t)(uintptr_t)buffer;
            isa_emulate(&site, &regs);
            if (regs.gpr[0] != dst) fail(ISA_ANDN, width, src1, 0, "rax (memory)", dst, regs.gpr[0]);
            if ((regs.rflags ^ flags) & defined) fail(ISA_ANDN, width, src1, 0, "flags (memory)", flags & defined, regs.rflags & defined);
        }
        uint64_t dst = RAX_START, flags = 0;
        __asm__("bextrl %k[c], %[m], %k[d]" FLAGS_OUT
                : [d] "+r"(dst), [f] "=r"(flags) : [c] "r"(ctrl), [m] "m"(*(uint32_t (*)[1])(buffer + 12)) : "cc");
        IsaSite site = register_site(ISA_BEXTR, 32);
        site.src1 = ISA_NO_REG;
        site.mem_slot = ISA_MEM_SRC;
        site.base = 3;
        site.disp = -4;
        IsaRegs regs = {.rflags = flags_start};
        regs.gpr[0] = RAX_START;
        regs.gpr[2] = ctrl;
        regs.gpr[3] = (uint64_t)(uintptr_t)(buffer + 16);
        isa_emulate(&site, &regs);
        defined = isa_defined_flags(ISA_BEXTR);
        if (regs.gpr[0] != dst) fail(ISA_BEXTR, 32, ctrl, 0, "rax (memory)", dst, regs.gpr[0]);
        if ((regs.rflags ^ flags) & defined) fail(ISA_BEXTR, 32, ctrl, 0, "flags (memory)", flags & defined, regs.rflags & defined);
    }
}



static int host_has_avx_state(void) {
    unsigned a = 0, b = 0, c = 0, d = 0;
    if (!__get_cpuid(1, &a, &b, &c, &d)) return 0;
    if (!(c & (1u << 27)) || !(c & (1u << 28))) return 0; /* OSXSAVE and AVX */
    unsigned lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    return (lo & 6) == 6;
}

static unsigned char *allocate_test_pages(size_t *page_size, size_t *allocation_size) {
#ifdef _WIN32
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    *page_size = info.dwPageSize;
    *allocation_size = *page_size * 2;
    return (unsigned char *)VirtualAlloc(NULL, *allocation_size, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
#else
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0) return NULL;
    *page_size = (size_t)page;
    *allocation_size = *page_size * 2;
    void *region = mmap(NULL, *allocation_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    return region == MAP_FAILED ? NULL : region;
#endif
}

static int protect_test_pages(unsigned char *region, size_t size, int writable) {
#ifdef _WIN32
    DWORD previous;
    return VirtualProtect(region, size, writable ? PAGE_READWRITE : PAGE_EXECUTE_READ, &previous) != 0;
#else
    return mprotect(region, size, writable ? PROT_READ | PROT_WRITE : PROT_READ | PROT_EXEC) == 0;
#endif
}

static void release_test_pages(unsigned char *region, size_t allocation_size) {
#ifdef _WIN32
    (void)allocation_size;
    VirtualFree(region, 0, MEM_RELEASE);
#else
    munmap(region, allocation_size);
#endif
}

/* Execute the generated AVX1 save/restore stub around a rewritten AVX2 instruction. */
static void check_vector_stub_execution(void) {
    if (!host_has_avx_state()) {
        puts("isa-emulate-test: vector stub execution skipped (OS AVX state unavailable)");
        return;
    }
    size_t page_size = 0, allocation_size = 0;
    unsigned char *region = allocate_test_pages(&page_size, &allocation_size);
    if (!region) {
        puts("isa-emulate-test FAILED: cannot allocate memory for vector stub");
        exit(1);
    }

    uint8_t source[32], source_after[32], destination_seed[32], result[32];
    for (unsigned i = 0; i < 32; ++i) {
        source[i] = (uint8_t)(0x80 + i * 7);
        destination_seed[i] = (uint8_t)(0x5a ^ i);
    }

    for (unsigned width = 16; width <= 32; width += 16) {
        if (!protect_test_pages(region, allocation_size, 1)) {
            puts("isa-emulate-test FAILED: mprotect writable");
            exit(1);
        }
        memset(region, 0x90, allocation_size);
        const uint8_t instruction[5] = {
            0xc4, 0x42, (uint8_t)(width == 16 ? 0x79 : 0x7d), 0x20, 0xca
        }; /* VPMOVSXBW xmm9/ymm9, xmm10 */
        memcpy(region, instruction, sizeof instruction);
        region[5] = 0xc3; /* ret */

        IsaSite site = {0};
        site.length = 5;
        site.kind = ISA_VPMOVSXBW;
        site.width = (uint8_t)width;
        site.mode = ISA_MODE_JMP;
        site.dst = 9;
        site.src1 = 10;
        site.src2 = ISA_NO_REG;
        site.mem_slot = ISA_MEM_NONE;
        site.base = site.index = ISA_NO_REG;
        site.scale = 1;
        memcpy(site.original, instruction, sizeof instruction);

        uint64_t hit = 0;
        IsaTable table = {0};
        table.sites = &site;
        table.hits = &hit;
        table.count = 1;
        IsaReport report = isa_rewrite_apply(&table, region, region + page_size, CPU_SET_AVX2);
        if (report.rewritten != 1 || report.unsupported_needed != 0) {
            puts("isa-emulate-test FAILED: AVX2 site was not rewritten");
            exit(1);
        }
        if (!protect_test_pages(region, allocation_size, 0)) {
            puts("isa-emulate-test FAILED: mprotect executable");
            exit(1);
        }

        __asm__ volatile("vmovdqu %0, %%ymm10" : : "m"(*(const uint8_t (*)[32])source) : "memory");
        __asm__ volatile("vmovdqu %0, %%ymm9" : : "m"(*(const uint8_t (*)[32])destination_seed) : "memory");
        ((void (*)(void))region)();
        __asm__ volatile("vmovdqu %%ymm9, %0" : "=m"(*(uint8_t (*)[32])result) : : "memory");
        __asm__ volatile("vmovdqu %%ymm10, %0" : "=m"(*(uint8_t (*)[32])source_after) : : "memory");

        unsigned elements = width / 2;
        for (unsigned i = 0; i < elements; ++i) {
            uint16_t expected = (uint16_t)(int16_t)(int8_t)source[i];
            if (result[i * 2] != (uint8_t)expected ||
                result[i * 2 + 1] != (uint8_t)(expected >> 8))
                fail(ISA_VPMOVSXBW, width, i, source[i], "generated stub result",
                     (uint8_t)expected, result[i * 2]);
        }
        if (width == 16) {
            for (unsigned i = 16; i < 32; ++i)
                if (result[i] != 0)
                    fail(ISA_VPMOVSXBW, width, i, 0, "generated stub upper YMM", 0, result[i]);
        }
        if (memcmp(source, source_after, sizeof source) != 0)
            fail(ISA_VPMOVSXBW, width, 0, 0, "generated stub source YMM preservation", source[0], source_after[0]);
    }
    release_test_pages(region, allocation_size);
}

static void vector_shape(uint8_t kind, unsigned *source_bytes, unsigned *destination_bytes, int *is_signed) {
    static const uint8_t source_sizes[6] = {1, 1, 1, 2, 2, 4};
    static const uint8_t destination_sizes[6] = {2, 4, 8, 4, 8, 8};
    unsigned index;
    if (kind >= ISA_VPMOVSXBW && kind <= ISA_VPMOVSXDQ) {
        index = kind - ISA_VPMOVSXBW;
        *is_signed = 1;
    } else {
        index = kind - ISA_VPMOVZXBW;
        *is_signed = 0;
    }
    *source_bytes = source_sizes[index];
    *destination_bytes = destination_sizes[index];
}

static void check_vector_extensions(void) {
    for (uint8_t kind = ISA_VPMOVSXBW; kind <= ISA_VPMOVZXDQ; ++kind) {
        unsigned source_size, destination_size;
        int is_signed;
        vector_shape(kind, &source_size, &destination_size, &is_signed);
        for (unsigned width = 16; width <= 32; width += 16) {
            unsigned elements = width / destination_size;
            unsigned input_size = elements * source_size;
            for (int memory = 0; memory <= 1; ++memory) {
                for (unsigned round = 0; round < 128; ++round) {
                    uint8_t source[32], memory_buffer[64], expected[32] = {0};
                    IsaRegs regs = {0};
                    IsaSite site = {0};
                    for (unsigned i = 0; i < sizeof source; ++i) source[i] = (uint8_t)xorshift64();
                    memset(memory_buffer, 0xa5, sizeof memory_buffer);
                    memcpy(memory_buffer + 5, source, input_size);

                    for (unsigned i = 0; i < 16; ++i) {
                        regs.gpr[i] = 0x0102030405060708ull * (i + 1);
                        for (unsigned b = 0; b < 32; ++b)
                            regs.ymm[i][b] = (uint8_t)(i * 19 + b * 7 + round);
                    }
                    regs.rflags = 0x8d5;
                    if (!memory) memcpy(regs.ymm[1], source, sizeof source);
                    regs.gpr[2] = (uint64_t)(uintptr_t)memory_buffer;

                    site.kind = kind;
                    site.width = (uint8_t)width; /* vector width is stored in bytes */
                    site.dst = 0;
                    site.src1 = memory ? ISA_NO_REG : 1;
                    site.src2 = ISA_NO_REG;
                    site.mem_slot = memory ? ISA_MEM_SRC : ISA_MEM_NONE;
                    site.base = memory ? 2 : ISA_NO_REG;
                    site.index = ISA_NO_REG;
                    site.scale = 1;
                    site.disp = 5;

                    for (unsigned element = 0; element < elements; ++element) {
                        uint64_t value = 0;
                        for (unsigned b = 0; b < source_size; ++b)
                            value |= (uint64_t)source[element * source_size + b] << (8 * b);
                        if (is_signed && (value & (1ull << (source_size * 8 - 1)))) {
                            uint64_t mask = (1ull << (source_size * 8)) - 1;
                            value |= ~mask;
                        }
                        for (unsigned b = 0; b < destination_size; ++b)
                            expected[element * destination_size + b] = (uint8_t)(value >> (8 * b));
                    }

                    uint8_t saved_vectors[16][32];
                    memcpy(saved_vectors, regs.ymm, sizeof saved_vectors);
                    uint64_t saved_flags = regs.rflags;
                    uint64_t saved_gprs[16];
                    memcpy(saved_gprs, regs.gpr, sizeof saved_gprs);
                    isa_emulate(&site, &regs);

                    for (unsigned b = 0; b < width; ++b) {
                        if (regs.ymm[0][b] != expected[b])
                            fail(kind, width, round, memory, "vector result", expected[b], regs.ymm[0][b]);
                    }
                    if (width == 16) {
                        for (unsigned b = 16; b < 32; ++b)
                            if (regs.ymm[0][b] != 0)
                                fail(kind, width, round, memory, "upper YMM zeroing", 0, regs.ymm[0][b]);
                    }
                    if (regs.rflags != saved_flags)
                        fail(kind, width, round, memory, "flags", saved_flags, regs.rflags);
                    for (unsigned i = 0; i < 16; ++i)
                        if (regs.gpr[i] != saved_gprs[i])
                            fail(kind, width, round, memory, "GPR preservation", saved_gprs[i], regs.gpr[i]);
                    for (unsigned i = 1; i < 16; ++i)
                        if (memcmp(regs.ymm[i], saved_vectors[i], 32) != 0)
                            fail(kind, width, round, memory, "vector preservation", saved_vectors[i][0], regs.ymm[i][0]);
                }
            }
        }
    }
}

int main(void) {
    check_vector_stub_execution();
    check_vector_extensions();
    if (!host_has_required_isa()) {
        puts("isa-emulate-test: native scalar differential tests skipped (CPU lacks BMI1, LZCNT or MOVBE)");
        return 0;
    }
    if (isa_defined_flags(ISA_MOVBE_LOAD) != 0 || isa_defined_flags(ISA_LZCNT) != (ISA_CF | ISA_ZF)
        || isa_defined_flags(ISA_BEXTR) != (ISA_ZF | ISA_CF | ISA_OF)
        || isa_defined_flags(ISA_BLSR) != (ISA_SF | ISA_ZF | ISA_CF | ISA_OF)) {
        puts("isa-emulate-test FAILED: isa_defined_flags table");
        return 1;
    }
    check_registers();
    check_movbe();
    check_rip_relative();
    check_memory_sources();
    puts("isa-emulate-test ok");
    return 0;
}
