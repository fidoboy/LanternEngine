/* SPDX-License-Identifier: GPL-2.0-only
 * Adapted from SpartanPort (https://github.com/FelipePrado0/SpartanPort).
 * Modified for Lantern Engine: MOVBE/BMI1/LZCNT and AVX2 integer extensions. */
#include "isa_emulate.h"

static unsigned char *isa_image;

void isa_emulate_set_image(unsigned char *image) { isa_image = image; }

static uint64_t width_mask(const IsaSite *site) {
    return site->width == 64 ? ~0ull : (1ull << site->width) - 1;
}

static unsigned char *effective_address(const IsaSite *site, const IsaRegs *regs) {
    if (site->mem_flags & ISA_MEM_RIP_RELATIVE) return isa_image + site->disp;
    uint64_t address = (uint64_t)site->disp;
    if (site->base != ISA_NO_REG) address += regs->gpr[site->base];
    if (site->index != ISA_NO_REG) address += regs->gpr[site->index] * site->scale;
    return (unsigned char *)(uintptr_t)address;
}

/* Unaligned accesses are valid on x86; the constant-size copies inline to plain moves. */
static uint64_t load(const IsaSite *site, const IsaRegs *regs) {
    unsigned char *at = effective_address(site, regs);
    if (site->width == 16) { uint16_t v; __builtin_memcpy(&v, at, 2); return v; }
    if (site->width == 32) { uint32_t v; __builtin_memcpy(&v, at, 4); return v; }
    uint64_t v;
    __builtin_memcpy(&v, at, 8);
    return v;
}

static void store(const IsaSite *site, const IsaRegs *regs, uint64_t value) {
    unsigned char *at = effective_address(site, regs);
    if (site->width == 16) { uint16_t v = (uint16_t)value; __builtin_memcpy(at, &v, 2); }
    else if (site->width == 32) { uint32_t v = (uint32_t)value; __builtin_memcpy(at, &v, 4); }
    else __builtin_memcpy(at, &value, 8);
}

/* The operand in a register slot; a slot left NO_REG holds the memory operand. */
static uint64_t read_operand(const IsaSite *site, const IsaRegs *regs, uint8_t reg) {
    if (reg == ISA_NO_REG) return load(site, regs);
    return regs->gpr[reg] & width_mask(site);
}

/* 64-bit writes replace the register, 32-bit ones zero-extend, 16-bit ones keep bits 16-63. */
static void write_dst(const IsaSite *site, IsaRegs *regs, uint64_t value) {
    if (site->dst == ISA_NO_REG) { store(site, regs, value); return; }
    uint64_t *reg = &regs->gpr[site->dst];
    if (site->width == 64) *reg = value;
    else if (site->width == 32) *reg = (uint32_t)value;
    else *reg = (*reg & ~0xffffull) | (value & 0xffff);
}

static void set_flags(IsaRegs *regs, uint64_t mask, uint64_t value) {
    regs->rflags = (regs->rflags & ~mask) | (value & mask);
}

static uint64_t byte_swap(const IsaSite *site, uint64_t value) {
    if (site->width == 16) return __builtin_bswap16((uint16_t)value);
    if (site->width == 32) return __builtin_bswap32((uint32_t)value);
    return __builtin_bswap64(value);
}

/* The VPMOVSX and VPMOVZX families differ only in source/destination element sizes
 * and whether the source element is sign-extended. All forms write XMM or YMM,
 * read only the low source bytes, and zero the upper YMM half for a 128-bit result. */
static void emulate_vector_extension(const IsaSite *site, IsaRegs *regs) {
    static const uint8_t source_bytes[6] = {1, 1, 1, 2, 2, 4};
    static const uint8_t destination_bytes[6] = {2, 4, 8, 4, 8, 8};
    uint8_t kind = site->kind;
    int is_signed;
    unsigned index;
    if (kind >= ISA_VPMOVSXBW && kind <= ISA_VPMOVSXDQ) {
        index = kind - ISA_VPMOVSXBW;
        is_signed = 1;
    } else if (kind >= ISA_VPMOVZXBW && kind <= ISA_VPMOVZXDQ) {
        index = kind - ISA_VPMOVZXBW;
        is_signed = 0;
    } else {
        return;
    }
    if (site->dst >= 16 || (site->width != 16 && site->width != 32)) return;

    unsigned src_size = source_bytes[index];
    unsigned dst_size = destination_bytes[index];
    unsigned elements = site->width / dst_size;
    unsigned input_size = elements * src_size;
    unsigned char input[16];
    unsigned char output[32] = {0};
    const unsigned char *source;

    if (site->mem_slot == ISA_MEM_SRC) {
        source = effective_address(site, regs);
    } else {
        if (site->src1 >= 16) return;
        source = regs->ymm[site->src1];
    }
    for (unsigned i = 0; i < input_size; ++i) input[i] = source[i];

    for (unsigned element = 0; element < elements; ++element) {
        uint64_t value = 0;
        for (unsigned byte = 0; byte < src_size; ++byte)
            value |= (uint64_t)input[element * src_size + byte] << (byte * 8);
        if (is_signed && (value & (1ull << (src_size * 8 - 1)))) {
            uint64_t mask = (1ull << (src_size * 8)) - 1;
            value |= ~mask;
        }
        for (unsigned byte = 0; byte < dst_size; ++byte)
            output[element * dst_size + byte] = (uint8_t)(value >> (byte * 8));
    }

    for (unsigned i = 0; i < site->width; ++i) regs->ymm[site->dst][i] = output[i];
    if (site->width == 16)
        for (unsigned i = 16; i < 32; ++i) regs->ymm[site->dst][i] = 0;
}

static uint64_t zf_sf(const IsaSite *site, uint64_t result) {
    return (result == 0 ? ISA_ZF : 0) | (result >> (site->width - 1) & 1 ? ISA_SF : 0);
}

uint64_t isa_defined_flags(uint8_t kind) {
    switch (kind) {
    case ISA_ANDN: case ISA_BLSI: case ISA_BLSMSK: case ISA_BLSR: return ISA_SF | ISA_ZF | ISA_CF | ISA_OF;
    case ISA_BEXTR: return ISA_ZF | ISA_CF | ISA_OF;
    case ISA_LZCNT: case ISA_TZCNT: return ISA_CF | ISA_ZF;
    default: return 0;
    }
}

void ABI isa_emulate(const IsaSite *site, IsaRegs *regs) {
    if (site->kind >= ISA_VPMOVSXBW && site->kind <= ISA_VPMOVZXDQ) {
        emulate_vector_extension(site, regs);
        return;
    }
    uint64_t mask = width_mask(site), defined = isa_defined_flags(site->kind);
    uint64_t width = site->width, source, result, flags;
    switch (site->kind) {
    case ISA_MOVBE_LOAD:
    case ISA_MOVBE_STORE:
        write_dst(site, regs, byte_swap(site, read_operand(site, regs, site->src1)));
        return;
    case ISA_LZCNT:
    case ISA_TZCNT:
        source = read_operand(site, regs, site->src1);
        if (source == 0) result = width;
        else if (site->kind == ISA_LZCNT) result = (uint64_t)__builtin_clzll(source) - (64 - width);
        else result = (uint64_t)__builtin_ctzll(source);
        flags = (source == 0 ? ISA_CF : 0) | (result == 0 ? ISA_ZF : 0);
        break;
    case ISA_ANDN:
        result = ~read_operand(site, regs, site->src1) & read_operand(site, regs, site->src2) & mask;
        flags = zf_sf(site, result);
        break;
    case ISA_BEXTR: {
        source = read_operand(site, regs, site->src1);
        uint64_t control = read_operand(site, regs, site->src2);
        uint64_t start = control & 0xff, length = control >> 8 & 0xff;
        result = 0;
        if (start < width && length != 0) {
            if (length > width - start) length = width - start;
            result = source >> start & (length == 64 ? ~0ull : (1ull << length) - 1);
        }
        flags = result == 0 ? ISA_ZF : 0;
        break;
    }
    case ISA_BLSI:
        source = read_operand(site, regs, site->src1);
        result = source & (0 - source) & mask;
        flags = zf_sf(site, result) | (source != 0 ? ISA_CF : 0);
        break;
    case ISA_BLSMSK:
        source = read_operand(site, regs, site->src1);
        result = (source ^ (source - 1)) & mask;
        flags = (zf_sf(site, result) & ISA_SF) | (source == 0 ? ISA_CF : 0);
        break;
    case ISA_BLSR:
        source = read_operand(site, regs, site->src1);
        result = source & (source - 1) & mask;
        flags = zf_sf(site, result) | (source == 0 ? ISA_CF : 0);
        break;
    default: return; /* Unknown kinds are never emulated. */
    }
    write_dst(site, regs, result);
    set_flags(regs, defined, flags);
}
