#include <array>
#include <cstddef>
#include <cstdint>

#include <arm_neon.h>

#define ALIGNMENT (4 * 4096)

typedef uint32_t vec_elem_t;

constexpr size_t vec_elem_sz_bytes = sizeof(vec_elem_t);

typedef vec_elem_t vN_elem_t __attribute__((vector_size(128 / 8)));
typedef vN_elem_t *aligned_vN_elem_ptr __attribute__((align_value(ALIGNMENT)));
typedef vN_elem_t *const const_aligned_vN_elem_ptr __attribute__((align_value(ALIGNMENT)));

typedef vec_elem_t *aligned_elem_ptr __attribute__((align_value(ALIGNMENT)));
typedef vec_elem_t *const const_aligned_elem_ptr __attribute__((align_value(ALIGNMENT)));

static_assert(ALIGNMENT % sizeof(vN_elem_t) == 0);

constexpr uint32_t vec_type_num_elem = sizeof(vN_elem_t) / sizeof(vec_elem_t);
constexpr size_t vec_sz_bytes        = 1024 * 16;
static_assert(vec_sz_bytes % ALIGNMENT == 0);
constexpr uint32_t vec_num_elem_max = UINT32_MAX / 2;
constexpr uint32_t vec_num_elem     = vec_sz_bytes / sizeof(vec_elem_t);
static_assert(vec_num_elem < vec_num_elem_max);

using val_t      = uint32_t;
using cnt_t      = uint32_t;
using cnt_neon_t = vN_elem_t;

constexpr size_t num_bits() {
    return sizeof(val_t) * 8;
}

using cnt_lst_t      = std::array<cnt_t, num_bits()>;
using cnt_neon_lst_t = std::array<vN_elem_t, num_bits() / vec_type_num_elem>;

static cnt_lst_t gcnt;

void count_v1(val_t val) {
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            gcnt[31]++;
        if (val & 0x40000000u)
            gcnt[30]++;
        if (val & 0x20000000u)
            gcnt[29]++;
        if (val & 0x10000000u)
            gcnt[28]++;
        if (val & 0x08000000u)
            gcnt[27]++;
        if (val & 0x04000000u)
            gcnt[26]++;
        if (val & 0x02000000u)
            gcnt[25]++;
        if (val & 0x01000000u)
            gcnt[24]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            gcnt[23]++;
        if (val & 0x00400000u)
            gcnt[22]++;
        if (val & 0x00200000u)
            gcnt[21]++;
        if (val & 0x00100000u)
            gcnt[20]++;
        if (val & 0x00080000u)
            gcnt[19]++;
        if (val & 0x00040000u)
            gcnt[18]++;
        if (val & 0x00020000u)
            gcnt[17]++;
        if (val & 0x00010000u)
            gcnt[16]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            gcnt[15]++;
        if (val & 0x4000u)
            gcnt[14]++;
        if (val & 0x2000u)
            gcnt[13]++;
        if (val & 0x1000u)
            gcnt[12]++;
        if (val & 0x0800u)
            gcnt[11]++;
        if (val & 0x0400u)
            gcnt[10]++;
        if (val & 0x0200u)
            gcnt[9]++;
        if (val & 0x0100u)
            gcnt[8]++;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            gcnt[7]++;
        if (val & 0x0040u)
            gcnt[6]++;
        if (val & 0x0020u)
            gcnt[5]++;
        if (val & 0x0010u)
            gcnt[4]++;
        if (val & 0x0008u)
            gcnt[3]++;
        if (val & 0x0004u)
            gcnt[2]++;
        if (val & 0x0002u)
            gcnt[1]++;
        if (val & 0x0001u)
            gcnt[0]++;
    }
}

void count_v2(val_t val, cnt_t *cnt) {
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            cnt[31]++;
        if (val & 0x40000000u)
            cnt[30]++;
        if (val & 0x20000000u)
            cnt[29]++;
        if (val & 0x10000000u)
            cnt[28]++;
        if (val & 0x08000000u)
            cnt[27]++;
        if (val & 0x04000000u)
            cnt[26]++;
        if (val & 0x02000000u)
            cnt[25]++;
        if (val & 0x01000000u)
            cnt[24]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            cnt[23]++;
        if (val & 0x00400000u)
            cnt[22]++;
        if (val & 0x00200000u)
            cnt[21]++;
        if (val & 0x00100000u)
            cnt[20]++;
        if (val & 0x00080000u)
            cnt[19]++;
        if (val & 0x00040000u)
            cnt[18]++;
        if (val & 0x00020000u)
            cnt[17]++;
        if (val & 0x00010000u)
            cnt[16]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            cnt[15]++;
        if (val & 0x4000u)
            cnt[14]++;
        if (val & 0x2000u)
            cnt[13]++;
        if (val & 0x1000u)
            cnt[12]++;
        if (val & 0x0800u)
            cnt[11]++;
        if (val & 0x0400u)
            cnt[10]++;
        if (val & 0x0200u)
            cnt[9]++;
        if (val & 0x0100u)
            cnt[8]++;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            cnt[7]++;
        if (val & 0x0040u)
            cnt[6]++;
        if (val & 0x0020u)
            cnt[5]++;
        if (val & 0x0010u)
            cnt[4]++;
        if (val & 0x0008u)
            cnt[3]++;
        if (val & 0x0004u)
            cnt[2]++;
        if (val & 0x0002u)
            cnt[1]++;
        if (val & 0x0001u)
            cnt[0]++;
    }
}

void count_v3(val_t val, cnt_lst_t &cnt) {
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            cnt[31]++;
        if (val & 0x40000000u)
            cnt[30]++;
        if (val & 0x20000000u)
            cnt[29]++;
        if (val & 0x10000000u)
            cnt[28]++;
        if (val & 0x08000000u)
            cnt[27]++;
        if (val & 0x04000000u)
            cnt[26]++;
        if (val & 0x02000000u)
            cnt[25]++;
        if (val & 0x01000000u)
            cnt[24]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            cnt[23]++;
        if (val & 0x00400000u)
            cnt[22]++;
        if (val & 0x00200000u)
            cnt[21]++;
        if (val & 0x00100000u)
            cnt[20]++;
        if (val & 0x00080000u)
            cnt[19]++;
        if (val & 0x00040000u)
            cnt[18]++;
        if (val & 0x00020000u)
            cnt[17]++;
        if (val & 0x00010000u)
            cnt[16]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            cnt[15]++;
        if (val & 0x4000u)
            cnt[14]++;
        if (val & 0x2000u)
            cnt[13]++;
        if (val & 0x1000u)
            cnt[12]++;
        if (val & 0x0800u)
            cnt[11]++;
        if (val & 0x0400u)
            cnt[10]++;
        if (val & 0x0200u)
            cnt[9]++;
        if (val & 0x0100u)
            cnt[8]++;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            cnt[7]++;
        if (val & 0x0040u)
            cnt[6]++;
        if (val & 0x0020u)
            cnt[5]++;
        if (val & 0x0010u)
            cnt[4]++;
        if (val & 0x0008u)
            cnt[3]++;
        if (val & 0x0004u)
            cnt[2]++;
        if (val & 0x0002u)
            cnt[1]++;
        if (val & 0x0001u)
            cnt[0]++;
    }
}

void count_v3_rev(val_t val, cnt_lst_t &cnt) {
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

void count_autovec_v1(val_t val) {
    cnt_t addend[num_bits()] = {};
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            addend[31]++;
        if (val & 0x40000000u)
            addend[30]++;
        if (val & 0x20000000u)
            addend[29]++;
        if (val & 0x10000000u)
            addend[28]++;
        if (val & 0x08000000u)
            addend[27]++;
        if (val & 0x04000000u)
            addend[26]++;
        if (val & 0x02000000u)
            addend[25]++;
        if (val & 0x01000000u)
            addend[24]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            addend[23]++;
        if (val & 0x00400000u)
            addend[22]++;
        if (val & 0x00200000u)
            addend[21]++;
        if (val & 0x00100000u)
            addend[20]++;
        if (val & 0x00080000u)
            addend[19]++;
        if (val & 0x00040000u)
            addend[18]++;
        if (val & 0x00020000u)
            addend[17]++;
        if (val & 0x00010000u)
            addend[16]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            addend[15]++;
        if (val & 0x4000u)
            addend[14]++;
        if (val & 0x2000u)
            addend[13]++;
        if (val & 0x1000u)
            addend[12]++;
        if (val & 0x0800u)
            addend[11]++;
        if (val & 0x0400u)
            addend[10]++;
        if (val & 0x0200u)
            addend[9]++;
        if (val & 0x0100u)
            addend[8]++;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            addend[7]++;
        if (val & 0x0040u)
            addend[6]++;
        if (val & 0x0020u)
            addend[5]++;
        if (val & 0x0010u)
            addend[4]++;
        if (val & 0x0008u)
            addend[3]++;
        if (val & 0x0004u)
            addend[2]++;
        if (val & 0x0002u)
            addend[1]++;
        if (val & 0x0001u)
            addend[0]++;
    }
    for (int i = 0; i < num_bits(); ++i) {
        gcnt[i] += addend[i];
    }
}

void count_autovec_v1_r(val_t val, cnt_lst_t &cnt) {
    cnt_lst_t addend{};
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            addend[31]++;
        if (val & 0x40000000u)
            addend[30]++;
        if (val & 0x20000000u)
            addend[29]++;
        if (val & 0x10000000u)
            addend[28]++;
        if (val & 0x08000000u)
            addend[27]++;
        if (val & 0x04000000u)
            addend[26]++;
        if (val & 0x02000000u)
            addend[25]++;
        if (val & 0x01000000u)
            addend[24]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            addend[23]++;
        if (val & 0x00400000u)
            addend[22]++;
        if (val & 0x00200000u)
            addend[21]++;
        if (val & 0x00100000u)
            addend[20]++;
        if (val & 0x00080000u)
            addend[19]++;
        if (val & 0x00040000u)
            addend[18]++;
        if (val & 0x00020000u)
            addend[17]++;
        if (val & 0x00010000u)
            addend[16]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            addend[15]++;
        if (val & 0x4000u)
            addend[14]++;
        if (val & 0x2000u)
            addend[13]++;
        if (val & 0x1000u)
            addend[12]++;
        if (val & 0x0800u)
            addend[11]++;
        if (val & 0x0400u)
            addend[10]++;
        if (val & 0x0200u)
            addend[9]++;
        if (val & 0x0100u)
            addend[8]++;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            addend[7]++;
        if (val & 0x0040u)
            addend[6]++;
        if (val & 0x0020u)
            addend[5]++;
        if (val & 0x0010u)
            addend[4]++;
        if (val & 0x0008u)
            addend[3]++;
        if (val & 0x0004u)
            addend[2]++;
        if (val & 0x0002u)
            addend[1]++;
        if (val & 0x0001u)
            addend[0]++;
    }
    for (int i = 0; i < num_bits(); ++i) {
        cnt[i] += addend[i];
    }
}

void count_autovec_v1_r_rev(val_t val, cnt_lst_t &cnt) {
    cnt_lst_t addend{};
    if (val & 0x00FFu) {
        if (val & 0x0001u)
            addend[0]++;
        if (val & 0x0002u)
            addend[1]++;
        if (val & 0x0004u)
            addend[2]++;
        if (val & 0x0008u)
            addend[3]++;
        if (val & 0x0010u)
            addend[4]++;
        if (val & 0x0020u)
            addend[5]++;
        if (val & 0x0040u)
            addend[6]++;
        if (val & 0x0080u)
            addend[7]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x0100u)
            addend[8]++;
        if (val & 0x0200u)
            addend[9]++;
        if (val & 0x0400u)
            addend[10]++;
        if (val & 0x0800u)
            addend[11]++;
        if (val & 0x1000u)
            addend[12]++;
        if (val & 0x2000u)
            addend[13]++;
        if (val & 0x4000u)
            addend[14]++;
        if (val & 0x8000u)
            addend[15]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00010000u)
            addend[16]++;
        if (val & 0x00020000u)
            addend[17]++;
        if (val & 0x00040000u)
            addend[18]++;
        if (val & 0x00080000u)
            addend[19]++;
        if (val & 0x00100000u)
            addend[20]++;
        if (val & 0x00200000u)
            addend[21]++;
        if (val & 0x00400000u)
            addend[22]++;
        if (val & 0x00800000u)
            addend[23]++;
    }
    if (val & 0xFF000000u) {
        if (val & 0x01000000u)
            addend[24]++;
        if (val & 0x02000000u)
            addend[25]++;
        if (val & 0x04000000u)
            addend[26]++;
        if (val & 0x08000000u)
            addend[27]++;
        if (val & 0x10000000u)
            addend[28]++;
        if (val & 0x20000000u)
            addend[29]++;
        if (val & 0x40000000u)
            addend[30]++;
        if (val & 0x80000000u)
            addend[31]++;
    }
    for (int i = 0; i < num_bits(); ++i) {
        cnt[i] += addend[i];
    }
}

void count_autovec_v2(val_t val) {
    cnt_lst_t addend{};
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            addend[31] = 1;
        if (val & 0x40000000u)
            addend[30] = 1;
        if (val & 0x20000000u)
            addend[29] = 1;
        if (val & 0x10000000u)
            addend[28] = 1;
        if (val & 0x08000000u)
            addend[27] = 1;
        if (val & 0x04000000u)
            addend[26] = 1;
        if (val & 0x02000000u)
            addend[25] = 1;
        if (val & 0x01000000u)
            addend[24] = 1;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            addend[23] = 1;
        if (val & 0x00400000u)
            addend[22] = 1;
        if (val & 0x00200000u)
            addend[21] = 1;
        if (val & 0x00100000u)
            addend[20] = 1;
        if (val & 0x00080000u)
            addend[19] = 1;
        if (val & 0x00040000u)
            addend[18] = 1;
        if (val & 0x00020000u)
            addend[17] = 1;
        if (val & 0x00010000u)
            addend[16] = 1;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            addend[15] = 1;
        if (val & 0x4000u)
            addend[14] = 1;
        if (val & 0x2000u)
            addend[13] = 1;
        if (val & 0x1000u)
            addend[12] = 1;
        if (val & 0x0800u)
            addend[11] = 1;
        if (val & 0x0400u)
            addend[10] = 1;
        if (val & 0x0200u)
            addend[9] = 1;
        if (val & 0x0100u)
            addend[8] = 1;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            addend[7] = 1;
        if (val & 0x0040u)
            addend[6] = 1;
        if (val & 0x0020u)
            addend[5] = 1;
        if (val & 0x0010u)
            addend[4] = 1;
        if (val & 0x0008u)
            addend[3] = 1;
        if (val & 0x0004u)
            addend[2] = 1;
        if (val & 0x0002u)
            addend[1] = 1;
        if (val & 0x0001u)
            addend[0] = 1;
    }
    for (int i = 0; i < num_bits(); ++i) {
        gcnt[i] += addend[i];
    }
}

void count_neon_v1(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend{};
    if (val & 0x00FFu) {
        if (val & 0x0001u)
            addend[0][0] = 1;
        if (val & 0x0002u)
            addend[0][1] = 1;
        if (val & 0x0004u)
            addend[0][2] = 1;
        if (val & 0x0008u)
            addend[0][3] = 1;
        if (val & 0x0010u)
            addend[1][4] = 1;
        if (val & 0x0020u)
            addend[1][5] = 1;
        if (val & 0x0040u)
            addend[1][6] = 1;
        if (val & 0x0080u)
            addend[1][7] = 1;
    }
    if (val & 0xFF00u) {
        if (val & 0x0100u)
            addend[2][0] = 1;
        if (val & 0x0200u)
            addend[2][1] = 1;
        if (val & 0x0400u)
            addend[2][2] = 1;
        if (val & 0x0800u)
            addend[2][3] = 1;
        if (val & 0x1000u)
            addend[3][4] = 1;
        if (val & 0x2000u)
            addend[3][5] = 1;
        if (val & 0x4000u)
            addend[3][6] = 1;
        if (val & 0x8000u)
            addend[3][7] = 1;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00010000u)
            addend[4][0] = 1;
        if (val & 0x00020000u)
            addend[4][1] = 1;
        if (val & 0x00040000u)
            addend[4][2] = 1;
        if (val & 0x00080000u)
            addend[4][3] = 1;
        if (val & 0x00100000u)
            addend[5][4] = 1;
        if (val & 0x00200000u)
            addend[5][5] = 1;
        if (val & 0x00400000u)
            addend[5][6] = 1;
        if (val & 0x00800000u)
            addend[5][7] = 1;
    }
    if (val & 0xFF000000u) {
        if (val & 0x01000000u)
            addend[6][0] = 1;
        if (val & 0x02000000u)
            addend[6][1] = 1;
        if (val & 0x04000000u)
            addend[6][2] = 1;
        if (val & 0x08000000u)
            addend[6][3] = 1;
        if (val & 0x10000000u)
            addend[7][4] = 1;
        if (val & 0x20000000u)
            addend[7][5] = 1;
        if (val & 0x40000000u)
            addend[7][6] = 1;
        if (val & 0x80000000u)
            addend[7][7] = 1;
    }
    for (int i = 0; i < vcnt.size(); ++i) {
        vcnt[i] += addend[i];
    }
}

void count_neon_v1_rev(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend{};
    if (val & 0xFF000000u) {
        if (val & 0x01000000u)
            addend[6][0] = 1;
        if (val & 0x02000000u)
            addend[6][1] = 1;
        if (val & 0x04000000u)
            addend[6][2] = 1;
        if (val & 0x08000000u)
            addend[6][3] = 1;
        if (val & 0x10000000u)
            addend[7][4] = 1;
        if (val & 0x20000000u)
            addend[7][5] = 1;
        if (val & 0x40000000u)
            addend[7][6] = 1;
        if (val & 0x80000000u)
            addend[7][7] = 1;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00010000u)
            addend[4][0] = 1;
        if (val & 0x00020000u)
            addend[4][1] = 1;
        if (val & 0x00040000u)
            addend[4][2] = 1;
        if (val & 0x00080000u)
            addend[4][3] = 1;
        if (val & 0x00100000u)
            addend[5][4] = 1;
        if (val & 0x00200000u)
            addend[5][5] = 1;
        if (val & 0x00400000u)
            addend[5][6] = 1;
        if (val & 0x00800000u)
            addend[5][7] = 1;
    }
    if (val & 0xFF00u) {
        if (val & 0x0100u)
            addend[2][0] = 1;
        if (val & 0x0200u)
            addend[2][1] = 1;
        if (val & 0x0400u)
            addend[2][2] = 1;
        if (val & 0x0800u)
            addend[2][3] = 1;
        if (val & 0x1000u)
            addend[3][4] = 1;
        if (val & 0x2000u)
            addend[3][5] = 1;
        if (val & 0x4000u)
            addend[3][6] = 1;
        if (val & 0x8000u)
            addend[3][7] = 1;
    }
    if (val & 0x00FFu) {
        if (val & 0x0001u)
            addend[0][0] = 1;
        if (val & 0x0002u)
            addend[0][1] = 1;
        if (val & 0x0004u)
            addend[0][2] = 1;
        if (val & 0x0008u)
            addend[0][3] = 1;
        if (val & 0x0010u)
            addend[1][4] = 1;
        if (val & 0x0020u)
            addend[1][5] = 1;
        if (val & 0x0040u)
            addend[1][6] = 1;
        if (val & 0x0080u)
            addend[1][7] = 1;
    }
    for (int i = 0; i < vcnt.size(); ++i) {
        vcnt[i] += addend[i];
    }
}

void count_neon_v1_rev_full(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend{};
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            addend[7][7] = 1;
        if (val & 0x40000000u)
            addend[7][6] = 1;
        if (val & 0x20000000u)
            addend[7][5] = 1;
        if (val & 0x10000000u)
            addend[7][4] = 1;
        if (val & 0x08000000u)
            addend[6][3] = 1;
        if (val & 0x04000000u)
            addend[6][2] = 1;
        if (val & 0x02000000u)
            addend[6][1] = 1;
        if (val & 0x01000000u)
            addend[6][0] = 1;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            addend[5][7] = 1;
        if (val & 0x00400000u)
            addend[5][6] = 1;
        if (val & 0x00200000u)
            addend[5][5] = 1;
        if (val & 0x00100000u)
            addend[5][4] = 1;
        if (val & 0x00080000u)
            addend[4][3] = 1;
        if (val & 0x00040000u)
            addend[4][2] = 1;
        if (val & 0x00020000u)
            addend[4][1] = 1;
        if (val & 0x00010000u)
            addend[4][0] = 1;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            addend[3][7] = 1;
        if (val & 0x4000u)
            addend[3][6] = 1;
        if (val & 0x2000u)
            addend[3][5] = 1;
        if (val & 0x1000u)
            addend[3][4] = 1;
        if (val & 0x0800u)
            addend[2][3] = 1;
        if (val & 0x0400u)
            addend[2][2] = 1;
        if (val & 0x0200u)
            addend[2][1] = 1;
        if (val & 0x0100u)
            addend[2][0] = 1;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            addend[1][7] = 1;
        if (val & 0x0040u)
            addend[1][6] = 1;
        if (val & 0x0020u)
            addend[1][5] = 1;
        if (val & 0x0010u)
            addend[1][4] = 1;
        if (val & 0x0008u)
            addend[0][3] = 1;
        if (val & 0x0004u)
            addend[0][2] = 1;
        if (val & 0x0002u)
            addend[0][1] = 1;
        if (val & 0x0001u)
            addend[0][0] = 1;
    }
    for (int i = 0; i < vcnt.size(); ++i) {
        vcnt[i] += addend[i];
    }
}

void count_neon_v1_rev_full_inc(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend{};
    if (val & 0xFF000000u) {
        if (val & 0x80000000u)
            addend[7][7]++;
        if (val & 0x40000000u)
            addend[7][6]++;
        if (val & 0x20000000u)
            addend[7][5]++;
        if (val & 0x10000000u)
            addend[7][4]++;
        if (val & 0x08000000u)
            addend[6][3]++;
        if (val & 0x04000000u)
            addend[6][2]++;
        if (val & 0x02000000u)
            addend[6][1]++;
        if (val & 0x01000000u)
            addend[6][0]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00800000u)
            addend[5][7]++;
        if (val & 0x00400000u)
            addend[5][6]++;
        if (val & 0x00200000u)
            addend[5][5]++;
        if (val & 0x00100000u)
            addend[5][4]++;
        if (val & 0x00080000u)
            addend[4][3]++;
        if (val & 0x00040000u)
            addend[4][2]++;
        if (val & 0x00020000u)
            addend[4][1]++;
        if (val & 0x00010000u)
            addend[4][0]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x8000u)
            addend[3][7]++;
        if (val & 0x4000u)
            addend[3][6]++;
        if (val & 0x2000u)
            addend[3][5]++;
        if (val & 0x1000u)
            addend[3][4]++;
        if (val & 0x0800u)
            addend[2][3]++;
        if (val & 0x0400u)
            addend[2][2]++;
        if (val & 0x0200u)
            addend[2][1]++;
        if (val & 0x0100u)
            addend[2][0]++;
    }
    if (val & 0x00FFu) {
        if (val & 0x0080u)
            addend[1][7]++;
        if (val & 0x0040u)
            addend[1][6]++;
        if (val & 0x0020u)
            addend[1][5]++;
        if (val & 0x0010u)
            addend[1][4]++;
        if (val & 0x0008u)
            addend[0][3]++;
        if (val & 0x0004u)
            addend[0][2]++;
        if (val & 0x0002u)
            addend[0][1]++;
        if (val & 0x0001u)
            addend[0][0]++;
    }
    for (int i = 0; i < vcnt.size(); ++i) {
        vcnt[i] += addend[i];
    }
}

[[gnu::always_inline]]
cnt_neon_t count_neon_single(uint8_t nib) {
    cnt_neon_t r{};
    nib &= 0xF;
    r = vdupq_n_u32(nib);
    return r;
}

static constexpr cnt_neon_t lut_nib[] = {{0, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, 1, 0}, {0, 0, 1, 1},
                                         {0, 1, 0, 0}, {0, 1, 0, 1}, {0, 1, 1, 0}, {0, 1, 1, 1},
                                         {1, 0, 0, 0}, {1, 0, 0, 1}, {1, 0, 1, 0}, {1, 0, 1, 1},
                                         {1, 1, 0, 0}, {1, 1, 0, 1}, {1, 1, 1, 0}, {1, 1, 1, 1}};

void count_neon_v2(val_t val, cnt_neon_lst_t &vcnt) {
    cnt_neon_lst_t addend{};
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
