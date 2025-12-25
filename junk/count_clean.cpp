#include <arm_neon.h>
#include <array>
#include <cstddef>
#include <cstdint>

using cnt_t                        = uint32_t;
using vec_elem_t                   = cnt_t;
constexpr size_t vec_elem_sz_bytes = sizeof(vec_elem_t); // 4 bytes
typedef vec_elem_t vN_elem_t __attribute__((vector_size(128 / 8 /* N = 16 */)));
using val_t                          = uint32_t;
constexpr size_t num_bits            = sizeof(val_t) * 8; // 32 bits
using cnt_neon_t                     = vN_elem_t;
constexpr uint32_t vec_type_num_elem = sizeof(vN_elem_t) / sizeof(vec_elem_t);
using cnt_lst_t                      = std::array<cnt_t, num_bits>;
using cnt_neon_lst_t =
    std::array<vN_elem_t, num_bits / vec_type_num_elem>; // 8 SIMD regs, 128 bytes

static constexpr cnt_neon_t lut_nib[] = {{0, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, 1, 0}, {0, 0, 1, 1},
                                         {0, 1, 0, 0}, {0, 1, 0, 1}, {0, 1, 1, 0}, {0, 1, 1, 1},
                                         {1, 0, 0, 0}, {1, 0, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 1},
                                         {1, 1, 0, 0}, {1, 1, 0, 1}, {1, 1, 1, 0}, {1, 1, 1, 1}};

#if 0
void count_orig(val_t val, cnt_lst_t &cnt) {
    if (val & 0x00FFu) {
        if (val & 0x0001u)
            cnt[0]++;
        if (val & 0x0002u)
            cnt[1]++;
        if (val & 0x0004u)
            cnt[2]++;
        if (val & 0x0008u)
            cnt[3]++;
        if (val & 0x0010u)
            cnt[4]++;
        if (val & 0x0020u)
            cnt[5]++;
        if (val & 0x0040u)
            cnt[6]++;
        if (val & 0x0080u)
            cnt[7]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x0100u)
            cnt[8]++;
        if (val & 0x0200u)
            cnt[9]++;
        if (val & 0x0400u)
            cnt[10]++;
        if (val & 0x0800u)
            cnt[11]++;
        if (val & 0x1000u)
            cnt[12]++;
        if (val & 0x2000u)
            cnt[13]++;
        if (val & 0x4000u)
            cnt[14]++;
        if (val & 0x8000u)
            cnt[15]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00010000u)
            cnt[16]++;
        if (val & 0x00020000u)
            cnt[17]++;
        if (val & 0x00040000u)
            cnt[18]++;
        if (val & 0x00080000u)
            cnt[19]++;
        if (val & 0x00100000u)
            cnt[20]++;
        if (val & 0x00200000u)
            cnt[21]++;
        if (val & 0x00400000u)
            cnt[22]++;
        if (val & 0x00800000u)
            cnt[23]++;
    }
    if (val & 0xFF000000u) {
        if (val & 0x01000000u)
            cnt[24]++;
        if (val & 0x02000000u)
            cnt[25]++;
        if (val & 0x04000000u)
            cnt[26]++;
        if (val & 0x08000000u)
            cnt[27]++;
        if (val & 0x10000000u)
            cnt[28]++;
        if (val & 0x20000000u)
            cnt[29]++;
        if (val & 0x40000000u)
            cnt[30]++;
        if (val & 0x80000000u)
            cnt[31]++;
    }
}
#endif

void count_neon(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend;
    if (val & 0x00FFu) {
        addend[0] = lut_nib[(val >> 0) & 0xFu];
        addend[1] = lut_nib[(val >> 4) & 0xFu];
    }
    if (val & 0xFF00u) {
        addend[2] = lut_nib[(val >> 8) & 0xFu];
        addend[3] = lut_nib[(val >> 12) & 0xFu];
    }
    if (val & 0x00FF0000u) {
        addend[4] = lut_nib[(val >> 16) & 0xFu];
        addend[5] = lut_nib[(val >> 20) & 0xFu];
    }
    if (val & 0xFF000000u) {
        addend[6] = lut_nib[(val >> 24) & 0xFu];
        addend[7] = lut_nib[(val >> 28) & 0xFu];
    }
    for (int i = 0; i < vcnt.size(); ++i) {
        vcnt[i] += addend[i];
    }
}

[[gnu::always_inline]]
constexpr uint64_t expand_8_to_64(uint8_t v) {
    return (((v & 0x55u) * 0x02040810204081ull) | ((v & 0xAAu) * 0x02040810204081ull)) &
           0x0101010101010101ull;
}

constexpr auto frob(uint8_t v) {
    const auto v64    = expand_8_to_64(v);
    const auto v64_x2 = vdupq_n_u64(v64);
    return v64;
}

void count_swar(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend;
    uint64_t a, b, c, d = 0;
    if (const uint8_t bv = (val >> 0) & 0xFFu) {
        a = expand_8_to_64(bv);
    }
    if (const uint8_t bv = (val >> 8) & 0xFFu) {
        b = expand_8_to_64(bv);
    }
    if (const uint8_t bv = (val >> 16) & 0xFFu) {
        c = expand_8_to_64(bv);
    }
    if (const uint8_t bv = (val >> 24) & 0xFFu) {
        d = expand_8_to_64(bv);
    }
    for (int i = 0; i < vcnt.size(); ++i) {
        vcnt[i] += addend[i];
    }
}
