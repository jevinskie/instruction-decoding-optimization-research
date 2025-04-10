set(INSTDEC_SRC
    utils.cpp
)

set(INSTDEC_HDR_STANDALONE
    instdec.hpp
    common.hpp
)

set(INSTDEC_HDR_STANDALONE_PRIVATE
)

set(INSTDEC_HDR)
foreach(HDR ${INSTDEC_HDR_STANDALONE})
    set(RELHDR "${CMAKE_CURRENT_SOURCE_DIR}/../../include/instdec/${HDR}")
    if(NOT EXISTS ${RELHDR})
        message(ERROR "INSTDEC_HDR_STANDALONE missing: ${HDR} ${RELHDR}")
    endif()
    list(APPEND INSTDEC_HDR ${RELHDR})
endforeach()

foreach(HDR ${INSTDEC_HDR_STANDALONE_PRIVATE})
    set(RELHDR "${CMAKE_CURRENT_SOURCE_DIR}/${HDR}")
    if(NOT EXISTS ${RELHDR})
        message(ERROR "INSTDEC_HDR_STANDALONE_PRIVATE missing: ${HDR} ${RELHDR}")
    endif()
    list(APPEND INSTDEC_HDR ${RELHDR})
endforeach()

foreach(SRC ${INSTDEC_SRC})
    get_filename_component(HDR_NAME ${SRC} NAME_WLE)
    set(HDR "${CMAKE_CURRENT_SOURCE_DIR}/../../include/instdec/${HDR_NAME}.hpp")
    if(EXISTS ${HDR})
        list(APPEND INSTDEC_HDR ${HDR})
    endif()
endforeach()

set(INSTDEC_PUBLIC_LIBS
)

set(INSTDEC_PRIVATE_LIBS
    fmt::fmt
)

# INSTDEC_HDR added for IDE project generation
add_library(instdec ${INSTDEC_SRC} ${INSTDEC_HDR})
set_target_properties(instdec PROPERTIES PUBLIC_HEADER "${INSTDEC_HDR}")

target_link_libraries(instdec
PUBLIC
    ${INSTDEC_PUBLIC_LIBS}
PRIVATE
    ${INSTDEC_PRIVATE_LIBS}
)

target_include_directories(instdec
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../include
    PRIVATE ${CMAKE_CURRENT_BINARY_DIR}
)

set_target_properties(instdec PROPERTIES
    CXX_STANDARD 23
    CXX_EXTENSIONS ON
    CXX_STANDARD_REQUIRED ON
    CXX_VISIBILITY_PRESET hidden
    VISIBILITY_INLINES_HIDDEN ON
)
