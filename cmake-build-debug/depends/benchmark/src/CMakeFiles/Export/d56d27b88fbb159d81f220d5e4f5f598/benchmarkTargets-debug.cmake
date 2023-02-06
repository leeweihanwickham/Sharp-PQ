#----------------------------------------------------------------
# Generated CMake target import file for configuration "Debug".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "benchmark::benchmark" for configuration "Debug"
set_property(TARGET benchmark::benchmark APPEND PROPERTY IMPORTED_CONFIGURATIONS DEBUG)
set_target_properties(benchmark::benchmark PROPERTIES
  IMPORTED_LINK_INTERFACE_LANGUAGES_DEBUG "CXX"
  IMPORTED_LOCATION_DEBUG "${_IMPORT_PREFIX}/lib/libbenchmark.a"
  )

list(APPEND _cmake_import_check_targets benchmark::benchmark )
list(APPEND _cmake_import_check_files_for_benchmark::benchmark "${_IMPORT_PREFIX}/lib/libbenchmark.a" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
