
#undef NDEBUG
#include <cassert>

#include "instdec/utils.hpp"

#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <string_view>
#include <vector>

#include <fmt/format.h>
#include <fmt/ranges.h>
#include <fmt/std.h>
#include <nlohmann/json.hpp>
#include <scn/scan.h>
#include <structopt/app.hpp>

using namespace instdec;

namespace fs = std::filesystem;

struct Args {
    std::optional<fs::path> inst_freq_file;
    std::optional<fs::path> espresso_file;
    std::optional<bool> treegy  = false;
    std::optional<bool> naive   = false;
    std::optional<bool> verbose = false;
};
STRUCTOPT(Args, inst_freq_file, espresso_file, treegy, naive, verbose);

struct IFreq {
    uint32_t iword;
    uint32_t freq;
};

static_assert(sizeof(IFreq) == 2 * sizeof(uint32_t));

static std::vector<IFreq> parse_inst_freq(const fs::path &ifreq_file) {
    return read_file_pod<IFreq>(ifreq_file);
}

static void print_inst_freqs(const std::vector<IFreq> &ifreqs) {
    const auto ninstr = std::min(32zu, ifreqs.size());
    for (size_t i = 0; i < ninstr; ++i) {
        fmt::print("iword: {:08x} freq: {:d}\n", ifreqs[i].iword, ifreqs[i].freq);
    }
}

struct Pattern {
    uint32_t mask;
    uint32_t value;
};

struct Node {
    int bit_pos;
    int child0;
    int child1;
};

using Leaf = std::array<uint32_t, 4>;

Pattern parse_pattern(const std::string_view s) {
    assert(s.length() == 32);
    uint32_t m = 0;
    uint32_t v = 0;
    for (int i = 0; i < 32; ++i) {
        const char c = s[31 - i];
        if (c == '0') {
            m |= (1u << i);
        } else if (c == '1') {
            m |= (1u << i);
            v |= (1u << i);
        } else {
            assert(c == '-');
        }
    }
    return {m, v};
}

std::vector<Pattern> parse_patterns(const std::vector<std::string> &pattern_strings) {
    std::vector<Pattern> pats;
    pats.reserve(pattern_strings.size());
    std::transform(pattern_strings.cbegin(), pattern_strings.cend(), std::back_inserter(pats),
                   [](const std::string &s) {
                       return parse_pattern(s);
                   });
    return pats;
}

std::vector<Pattern> parse_patterns_alt(const std::vector<std::string> &pattern_strings) {
    std::vector<Pattern> pats;
    pats.reserve(pattern_strings.size());
    for (const auto &s : pattern_strings) {
        pats.push_back(parse_pattern(s));
    }
    return pats;
}

void build_tree(int node, int depth, const std::vector<int> &pattern_idxs,
                const std::vector<Pattern> &all_patterns, std::vector<Node> &tree,
                std::vector<Leaf> &leaf_masks, std::vector<Leaf> &leaf_values) {
    if (depth == 10) {
        int block_idx = node - 1023;
        Leaf masks    = {0, 0, 0, 0};
        Leaf values   = {1, 1, 1, 1};
        int count     = std::min(4, static_cast<int>(pattern_idxs.size()));
        for (int i = 0; i < count; i++) {
            int idx   = pattern_idxs[i];
            masks[i]  = all_patterns[idx].mask;
            values[i] = all_patterns[idx].value;
        }
        leaf_masks[block_idx]  = masks;
        leaf_values[block_idx] = values;
    } else {
        std::array<int, 32> d_k{};
        for (int idx : pattern_idxs) {
            const auto &p = all_patterns[idx];
            for (int k = 0; k < 32; k++) {
                if ((p.mask & (1 << k)) == 0)
                    d_k[k]++;
            }
        }
        int best_k  = 0;
        int min_d_k = d_k[0];
        for (int k = 1; k < 32; k++) {
            if (d_k[k] < min_d_k) {
                min_d_k = d_k[k];
                best_k  = k;
            }
        }
        tree[node].bit_pos = best_k;
        tree[node].child0  = 2 * node + 1;
        tree[node].child1  = 2 * node + 2;
        std::vector<int> left_idxs, right_idxs;
        uint32_t bit_mask = 1 << best_k;
        for (int idx : pattern_idxs) {
            const auto &p = all_patterns[idx];
            if ((p.mask & bit_mask) == 0 || (p.value & bit_mask) == 0)
                left_idxs.push_back(idx);
            if ((p.mask & bit_mask) == 0 || (p.value & bit_mask) != 0)
                right_idxs.push_back(idx);
        }
        build_tree(tree[node].child0, depth + 1, left_idxs, all_patterns, tree, leaf_masks,
                   leaf_values);
        build_tree(tree[node].child1, depth + 1, right_idxs, all_patterns, tree, leaf_masks,
                   leaf_values);
    }
}

void generate_decision_tree(const std::vector<Pattern> &all_patterns, std::vector<Node> &tree,
                            std::vector<Leaf> &leaf_masks, std::vector<Leaf> &leaf_values) {
    tree.resize(2047);
    leaf_masks.resize(1024);
    leaf_values.resize(1024);

    std::vector<int> init_idxs(all_patterns.size());
    std::iota(init_idxs.begin(), init_idxs.end(), 0);

    build_tree(0, 0, init_idxs, all_patterns, tree, leaf_masks, leaf_values);
}

int evaluate_function(const uint32_t iword, const std::vector<Node> &tree,
                      const std::vector<Leaf> &leaf_masks, const std::vector<Leaf> &leaf_values) {
    int node = 0;
    for (int i = 0; i < 10; ++i) {
        int bit_pos = tree[node].bit_pos;
        node        = (iword & (1 << bit_pos)) ? tree[node].child1 : tree[node].child0;
    }
    int block_index = node - 1023;
    for (int i = 0; i < 4; ++i) {
        if ((iword & leaf_masks[block_index][i]) == leaf_values[block_index][i]) {
            return 1;
        }
    }
    return 0;
}

std::vector<Pattern> parse_espresso_file(const fs::path path) {
    const auto file_str                      = read_file_string(path);
    std::vector<std::string> pattern_strings = split_lines(file_str);
    return parse_patterns(pattern_strings);
}

void get_treegy_wif_it(const fs::path &espresso_path) {
    const std::vector<Pattern> patterns = parse_espresso_file(espresso_path);
    std::vector<Node> tree;
    std::vector<Leaf> leaf_masks;
    std::vector<Leaf> leaf_values;
    generate_decision_tree(patterns, tree, leaf_masks, leaf_values);
    while (const auto iwordr = scn::input<uint32_t>("{:08x}")) {
        const auto iword = iwordr.value().value();
        const auto r     = evaluate_function(iword, tree, leaf_masks, leaf_values);
        fmt::print("iword: {:08x} r: {}\n", iword, r);
    }
}

bool matches_pattern(const uint32_t iword, const Pattern pat) {
    return (iword & pat.mask) == pat.value;
}

bool matches_patterns(const uint32_t iword, const std::vector<Pattern> &pats) {
    for (const auto pat : pats) {
        if (matches_pattern(iword, pat)) {
            return true;
        }
    }
    return false;
}

void naive_repl(const fs::path &espresso_path) {
    const std::vector<Pattern> patterns = parse_espresso_file(espresso_path);
    while (const auto iwordr = scn::input<uint32_t>("{:08x}")) {
        const auto iword = iwordr.value().value();
        const auto r     = static_cast<int>(matches_patterns(iword, patterns));
        fmt::print("iword: {:08x} r: {}\n", iword, r);
    }
}

int main_task(const Args &args) {
    if (args.inst_freq_file) {
        const auto ifreqs = parse_inst_freq(*args.inst_freq_file);
        print_inst_freqs(ifreqs);
    }
    if (args.espresso_file) {
        if (*args.treegy) {
            fmt::print("treegy\n");
            get_treegy_wif_it(*args.espresso_file);
        }
        if (*args.naive) {
            fmt::print("naive\n");
            naive_repl(*args.espresso_file);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    try {
        const auto options = structopt::app("instdec-util").parse<Args>(argc, argv);
        return main_task(options);
    } catch (const structopt::exception &e) {
        fmt::print("{}\n", e);
        fmt::print("{}\n", e.help());
        return 1;
    }
}
