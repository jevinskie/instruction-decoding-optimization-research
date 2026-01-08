add_executable(count count.cpp)
target_link_libraries(count fmt benchmark)
target_compile_definitions(count PRIVATE USE_BENCH=1)

add_library(count-rambling count-rambling.cpp)
