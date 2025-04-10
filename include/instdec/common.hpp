#pragma once

#include <type_traits>

namespace instdec {

template <typename T>
concept POD = std::is_trivial_v<T> && std::is_standard_layout_v<T>;

}
