#pragma once

#include "common.hpp"

#include <cstdint>
#include <filesystem>
#include <span>
#include <string>
#include <sys/fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#include <vector>

#pragma push_macro("NDEBUG")
#undef NDEBUG
#include <cassert>

namespace instdec {

void write_file(const std::filesystem::path &path, const std::string &str);

void write_file(const std::filesystem::path &path, const std::span<const uint8_t> buf);

template <typename T> void write_file(const std::filesystem::path &path, const std::span<T> buf) {
    return write_file(
        path, std::span{reinterpret_cast<const uint8_t *const>(buf.data()), buf.size_bytes()});
}

template <typename T>
void write_file(const std::filesystem::path &path, const std::vector<T> &buf) {
    return write_file(path, std::span{reinterpret_cast<const uint8_t *const>(buf.data()),
                                      buf.size() * sizeof(T)});
}

std::vector<uint8_t> read_file_bytes(const std::filesystem::path &path);
std::string read_file_string(const std::filesystem::path &path);

template <typename T>
    requires POD<T>
std::vector<T> read_file_pod(const std::filesystem::path &path) {
    const auto fd = ::open(path.c_str(), O_RDONLY);
    assert(fd >= 0);
    struct stat st;
    assert(!::fstat(fd, &st));
    const auto sz = static_cast<size_t>(st.st_size);
    if (!sz) {
        assert(!::close(fd));
        return {};
    }
    const size_t nelem = sz / sizeof(T);
    assert(sizeof(T) * nelem == sz);
    std::vector<T> res(nelem);
    assert(sz == ::read(fd, res.data(), sz));
    assert(!::close(fd));
    return res;
}

} // namespace instdec

#pragma pop_macro("NDEBUG")
