#include <arm_neon.h>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <type_traits>

// clang-format off
#include <fmt/format.h>
#include <fmt/color.h>
#include <fmt/ranges.h>
#include <fmt/std.h>
// clang-format on

using std::literals::string_view_literals::operator""sv;

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

struct vec128_array_t {
    alignas(uint8x16_t) uint8_t vals[sizeof(uint8x16_t)];
};

static constexpr std::array<cnt_neon_t, 16> lut_nib{{{0, 0, 0, 0},
                                                     {0, 0, 0, 1},
                                                     {0, 0, 1, 0},
                                                     {0, 0, 1, 1},
                                                     {0, 1, 0, 0},
                                                     {0, 1, 0, 1},
                                                     {0, 1, 1, 0},
                                                     {0, 1, 1, 1},
                                                     {1, 0, 0, 0},
                                                     {1, 0, 0, 1},
                                                     {1, 0, 1, 0},
                                                     {1, 0, 1, 1},
                                                     {1, 1, 0, 0},
                                                     {1, 1, 0, 1},
                                                     {1, 1, 1, 0},
                                                     {1, 1, 1, 1}}};

void print_counts(const cnt_lst_t &cnt) {
    for (size_t i = 0; i < cnt.size(); ++i) {
        fmt::print("cnt[{:02d}] = {:4d}\n", i, cnt[i]);
    }
}

static constexpr uint8_t vec_nelem(const uint8x16_t v) {
    return 16;
}
static constexpr uint8_t vec_nelem(const int8x16_t v) {
    return 16;
}
static constexpr uint8_t vec_nelem(const uint16x8_t v) {
    return 8;
}
static constexpr uint8_t vec_nelem(const int16x8_t v) {
    return 8;
}
static constexpr uint8_t vec_nelem(const uint32x4_t v) {
    return 4;
}
static constexpr uint8_t vec_nelem(const int32x4_t v) {
    return 4;
}
static constexpr uint8_t vec_nelem(const uint64x2_t v) {
    return 2;
}
static constexpr uint8_t vec_nelem(const int64x2_t v) {
    return 2;
}

struct corner_t {
    const std::string_view tl;  /// top left
    const std::string_view tr;  /// top right
    const std::string_view bl;  /// bottom left
    const std::string_view br;  /// bottom right
    const std::string_view tds; /// top down space
    const std::string_view bus; /// bottom up space
    const std::string_view tdb; /// top down bar
    const std::string_view bub; /// bottom up bar
    const std::string_view x;   /// cross
};

struct edge_t {
    const std::string_view oh; /// outer horizontal
    const std::string_view ov; /// outer vertical
    const std::string_view ih; /// inner horizontal
    const std::string_view iv; /// inner vertical
};

struct box_t {
    const corner_t c; /// corner
    const edge_t e;   /// edge
};

enum class box_type_t {
    ASCII,
    HEAVY_LIGHT,
    HEAVY,
    LIGHT,
    ROUNDED,
};

// clang-format off
static constexpr box_t box_ascii      {{"+", "+", "+", "+", "", "", "", "", "+"}, {"-", "|", "-", "|"}};
static constexpr box_t box_heavy_light{{"┏", "┓", "┗", "┛", "╂", "", "", "", "+"}, {"━", "┃", "─", "│"}};
static constexpr box_t box_heavy      {{"┏", "┓", "┗", "┛", "╋", "", "", "", "+"}, {"━", "┃", "━", "┃"}};
static constexpr box_t box_light      {{"┌", "┐", "└", "┘", "┼", "", "", "", "+"}, {"─", "│", "─", "│"}};
static constexpr box_t box_rounded    {{"╭", "╮", "╰", "╯", "┼", "", "", "", "+"}, {"─", "│", "─", "│"}};
// clang-format on

static constexpr const box_t &get_box(const box_type_t bt) {
    using btt = box_type_t;
    switch (bt) {
    case btt::ASCII:
        return box_ascii;
    case btt::HEAVY_LIGHT:
        return box_heavy_light;
    case btt::HEAVY:
        return box_heavy;
    case btt::LIGHT:
        return box_light;
    case btt::ROUNDED:
        return box_rounded;
    }
}

std::string format_vec128(const auto v, const box_type_t bt = box_type_t::ROUNDED) {
    const auto nelem = vec_nelem(v);
    const auto b     = get_box(bt);
    return fmt::format("{0}{1}{2}{1}{3}\n"
                       "{4}x{5}y{6}\n"
                       "{4}a{5}b{6}\n"
                       "{7}{8}{9}{8}{10}",
                       b.c.tr, b.e.oh, b.c.td, b.c.tds);
}

void print_vec128(const auto v) {
    static_assert(sizeof(v) == sizeof(vec128_array_t) &&
                  alignof(decltype(v)) == alignof(vec128_array_t));
    vec128_array_t vec{};
    memcpy(&vec.vals, &v, sizeof(v));
    for (size_t i = 0; i < sizeof(vec.vals); ++i) {
        fmt::print("v[{:2d}] = {:#04x}\n", i, vec.vals[i]);
    }
}

void count_orig(val_t val, cnt_lst_t &cnt) {
    // clang-format off
    if (val & 0x00FFu) {
        if (val & 0x0001u) cnt[0]++;
        if (val & 0x0002u) cnt[1]++;
        if (val & 0x0004u) cnt[2]++;
        if (val & 0x0008u) cnt[3]++;
        if (val & 0x0010u) cnt[4]++;
        if (val & 0x0020u) cnt[5]++;
        if (val & 0x0040u) cnt[6]++;
        if (val & 0x0080u) cnt[7]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x0100u) cnt[8]++;
        if (val & 0x0200u) cnt[9]++;
        if (val & 0x0400u) cnt[10]++;
        if (val & 0x0800u) cnt[11]++;
        if (val & 0x1000u) cnt[12]++;
        if (val & 0x2000u) cnt[13]++;
        if (val & 0x4000u) cnt[14]++;
        if (val & 0x8000u) cnt[15]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00010000u) cnt[16]++;
        if (val & 0x00020000u) cnt[17]++;
        if (val & 0x00040000u) cnt[18]++;
        if (val & 0x00080000u) cnt[19]++;
        if (val & 0x00100000u) cnt[20]++;
        if (val & 0x00200000u) cnt[21]++;
        if (val & 0x00400000u) cnt[22]++;
        if (val & 0x00800000u) cnt[23]++;
    }
    if (val & 0xFF000000u) {
        if (val & 0x01000000u) cnt[24]++;
        if (val & 0x02000000u) cnt[25]++;
        if (val & 0x04000000u) cnt[26]++;
        if (val & 0x08000000u) cnt[27]++;
        if (val & 0x10000000u) cnt[28]++;
        if (val & 0x20000000u) cnt[29]++;
        if (val & 0x40000000u) cnt[30]++;
        if (val & 0x80000000u) cnt[31]++;
    }
    // clang-format on
}

void count_autovec(val_t val, cnt_lst_t &cnt) {
    uint32_t addend[32] = {};
    // clang-format off
    if (val & 0x00FFu) {
        if (val & 0x0001u) addend[0]++;
        if (val & 0x0002u) addend[1]++;
        if (val & 0x0004u) addend[2]++;
        if (val & 0x0008u) addend[3]++;
        if (val & 0x0010u) addend[4]++;
        if (val & 0x0020u) addend[5]++;
        if (val & 0x0040u) addend[6]++;
        if (val & 0x0080u) addend[7]++;
    }
    if (val & 0xFF00u) {
        if (val & 0x0100u) addend[8]++;
        if (val & 0x0200u) addend[9]++;
        if (val & 0x0400u) addend[10]++;
        if (val & 0x0800u) addend[11]++;
        if (val & 0x1000u) addend[12]++;
        if (val & 0x2000u) addend[13]++;
        if (val & 0x4000u) addend[14]++;
        if (val & 0x8000u) addend[15]++;
    }
    if (val & 0x00FF0000u) {
        if (val & 0x00010000u) addend[16]++;
        if (val & 0x00020000u) addend[17]++;
        if (val & 0x00040000u) addend[18]++;
        if (val & 0x00080000u) addend[19]++;
        if (val & 0x00100000u) addend[20]++;
        if (val & 0x00200000u) addend[21]++;
        if (val & 0x00400000u) addend[22]++;
        if (val & 0x00800000u) addend[23]++;
    }
    if (val & 0xFF000000u) {
        if (val & 0x01000000u) addend[24]++;
        if (val & 0x02000000u) addend[25]++;
        if (val & 0x04000000u) addend[26]++;
        if (val & 0x08000000u) addend[27]++;
        if (val & 0x10000000u) addend[28]++;
        if (val & 0x20000000u) addend[29]++;
        if (val & 0x40000000u) addend[30]++;
        if (val & 0x80000000u) addend[31]++;
    }
    // clang-format on
    for (int i = 0; i < cnt.size(); ++i) {
        cnt[i] += addend[i];
    }
}

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

using counts_t = std::array<uint32x4x4_t, 2>;

void add_counts(const counts_t &addend, counts_t &accum) {
    for (size_t io = 0; io < accum.size(); ++io) {
        for (size_t ii = 0; ii < std::size(accum[io].val); ++ii) {
            accum[io].val[ii] += addend[io].val[ii];
        }
    }
}

int main(void) {
    fmt::print("main\n");
    for (size_t i = 0; i < lut_nib.size(); ++i) {
        fmt::print("lut_nib[{:2d}]:\n", i);
        fmt::print("{:s}\n", format_vec128(lut_nib[i]));
        print_vec128(lut_nib[i]);
    }
    return 0;
}
