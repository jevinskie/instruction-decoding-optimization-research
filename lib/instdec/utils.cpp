#undef NDEBUG
#include <cassert>

#include "instdec/utils.hpp"

namespace fs = std::filesystem;

namespace instdec {

void write_file(const fs::path &path, const std::span<const uint8_t> buf) {
    const int fd = ::open(path.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
    assert(fd >= 0);
    const auto wrote_len = ::write(fd, buf.data(), buf.size_bytes());
    assert(!::close(fd));
    assert(wrote_len == static_cast<ssize_t>(buf.size_bytes()));
}

void write_file(const fs::path &path, const std::string &str) {
    const int fd = ::open(path.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
    assert(fd >= 0);
    const auto wrote_len = ::write(fd, str.data(), str.size());
    assert(!::close(fd));
    assert(wrote_len == static_cast<ssize_t>(str.size()));
}

std::vector<uint8_t> read_file_bytes(const std::filesystem::path &path) {
    return read_file_pod<uint8_t>(path);
}

std::string read_file_string(const std::filesystem::path &path) {
    const auto fd = ::open(path.c_str(), O_RDONLY);
    assert(fd >= 0);
    struct stat st;
    assert(!::fstat(fd, &st));
    const auto sz = static_cast<size_t>(st.st_size);
    if (!sz) {
        assert(!::close(fd));
        return {};
    }
    std::string res(sz, '\0');
    assert(sz == ::read(fd, res.data(), res.size()));
    assert(!::close(fd));
    return res;
}

} // namespace instdec
