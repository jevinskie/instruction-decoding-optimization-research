set(FMT_DOC OFF CACHE INTERNAL "")
set(FMT_TEST OFF CACHE INTERNAL "")
add_subdirectory(fmt)

set(JSON_BuildTests OFF CACHE INTERNAL "")
set(JSON_Install OFF CACHE INTERNAL "")
add_subdirectory(json)

set(SCN_USE_NATIVE_ARCH ON CACHE INTERNAL "")
add_subdirectory(scnlib)
set_target_properties(scn PROPERTIES EXCLUDE_FROM_ALL ON)

add_subdirectory(structopt)
