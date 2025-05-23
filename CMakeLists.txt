cmake_minimum_required(VERSION 3.31)

project(instdec CXX)

option(FORCE_COLORED_OUTPUT "Always produce ANSI-colored output (GNU/Clang only)." ON)

if (${FORCE_COLORED_OUTPUT})
    if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
       add_compile_options(-fdiagnostics-color=always)
    elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang" OR "${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang")
       add_compile_options(-fcolor-diagnostics)
    endif ()
endif ()

add_compile_options(-ggdb3)
add_compile_options(-O0 -fno-omit-frame-pointer -mno-omit-leaf-frame-pointer)
# add_compile_options(-Os -fvisibility=hidden -fvisibility-inlines-hidden -ffunction-sections -fdata-sections)
# add_link_options(-Os -Wl,-dead_strip)

add_compile_options(-fsanitize=address)
add_link_options(-fsanitize=address)

# add_compile_options(-fsanitize=memory)
# add_link_options(-fsanitize=memory)

set(CMAKE_CXX_STANDARD 23)

add_subdirectory(3rdparty)
add_subdirectory(lib)
add_subdirectory(tools)
