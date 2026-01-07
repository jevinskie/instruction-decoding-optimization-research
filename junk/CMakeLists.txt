add_executable(count count.cpp)
target_link_libraries(count fmt benchmark)

add_library(count-rambling count-rambling.cpp)
