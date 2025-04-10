#pragma once

#include <cstdint>
#include <filesystem>
#include <span>
#include <string>
#include <vector>

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

} // namespace instdec
