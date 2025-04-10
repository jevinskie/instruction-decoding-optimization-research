#undef NDEBUG
#include <cassert>

#include "instdec/utils.hpp"

#include <algorithm>
#include <cstdint>
#include <filesystem>
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
    std::optional<bool> verbose = false;
};
STRUCTOPT(Args, inst_freq_file, verbose);

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

static int main_task(const Args &args) {
    if (args.inst_freq_file) {
        const auto ifreqs = parse_inst_freq(*args.inst_freq_file);
        print_inst_freqs(ifreqs);
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
