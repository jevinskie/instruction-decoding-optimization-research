add_executable(instdec-util instdec-util.cpp)
target_link_libraries(instdec-util PRIVATE fmt::fmt nlohmann_json::nlohmann_json scn::scn)
set_target_properties(instdec-util PROPERTIES
    CXX_STANDARD 23
    CXX_EXTENSIONS ON
    CXX_STANDARD_REQUIRED ON
    CXX_VISIBILITY_PRESET hidden
    VISIBILITY_INLINES_HIDDEN ON
)
