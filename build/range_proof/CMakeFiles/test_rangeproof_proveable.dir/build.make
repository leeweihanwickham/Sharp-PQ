# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.5

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = "/home/leeweihan/Desktop/range proof"

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = "/home/leeweihan/Desktop/range proof/build"

# Include any dependencies generated for this target.
include range_proof/CMakeFiles/test_rangeproof_proveable.dir/depend.make

# Include the progress variables for this target.
include range_proof/CMakeFiles/test_rangeproof_proveable.dir/progress.make

# Include the compile flags for this target's objects.
include range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make

range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o: ../range_proof/tests/test_rangeproof_proveable.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/c++   $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o -c "/home/leeweihan/Desktop/range proof/range_proof/tests/test_rangeproof_proveable.cpp"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.i"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E "/home/leeweihan/Desktop/range proof/range_proof/tests/test_rangeproof_proveable.cpp" > CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.i

range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.s"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S "/home/leeweihan/Desktop/range proof/range_proof/tests/test_rangeproof_proveable.cpp" -o CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.s

range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o: ../range_proof/bcs/BLAKE3/blake3.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_2) "Building C object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o   -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3.c"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.i"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3.c" > CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.i

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.s"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3.c" -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.s

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o: ../range_proof/bcs/BLAKE3/blake3_dispatch.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_3) "Building C object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o   -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_dispatch.c"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.i"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_dispatch.c" > CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.i

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.s"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_dispatch.c" -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.s

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o: ../range_proof/bcs/BLAKE3/blake3_portable.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_4) "Building C object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o   -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_portable.c"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.i"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_portable.c" > CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.i

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.s"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_portable.c" -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.s

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o: ../range_proof/bcs/BLAKE3/blake3_sse2_x86-64_unix.S
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_5) "Building ASM object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(ASM_DEFINES) $(ASM_INCLUDES) $(ASM_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_sse2_x86-64_unix.S"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o: ../range_proof/bcs/BLAKE3/blake3_sse41_x86-64_unix.S
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_6) "Building ASM object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(ASM_DEFINES) $(ASM_INCLUDES) $(ASM_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_sse41_x86-64_unix.S"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o: ../range_proof/bcs/BLAKE3/blake3_avx2_x86-64_unix.S
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_7) "Building ASM object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(ASM_DEFINES) $(ASM_INCLUDES) $(ASM_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_avx2_x86-64_unix.S"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o


range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o: range_proof/CMakeFiles/test_rangeproof_proveable.dir/flags.make
range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o: ../range_proof/bcs/BLAKE3/blake3_avx512_x86-64_unix.S
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_8) "Building ASM object range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && /usr/bin/cc  $(ASM_DEFINES) $(ASM_INCLUDES) $(ASM_FLAGS) -o CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o -c "/home/leeweihan/Desktop/range proof/range_proof/bcs/BLAKE3/blake3_avx512_x86-64_unix.S"

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.requires:

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.provides: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.requires
	$(MAKE) -f range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.provides.build
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.provides

range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.provides.build: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o


# Object files for target test_rangeproof_proveable
test_rangeproof_proveable_OBJECTS = \
"CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o" \
"CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o"

# External object files for target test_rangeproof_proveable
test_rangeproof_proveable_EXTERNAL_OBJECTS =

range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/build.make
range_proof/test_rangeproof_proveable: range_proof/librange_proof.a
range_proof/test_rangeproof_proveable: depends/libff/libff/libff.a
range_proof/test_rangeproof_proveable: /usr/lib/x86_64-linux-gnu/libgmp.so
range_proof/test_rangeproof_proveable: depends/libzm.a
range_proof/test_rangeproof_proveable: /usr/lib/x86_64-linux-gnu/libsodium.so
range_proof/test_rangeproof_proveable: range_proof/CMakeFiles/test_rangeproof_proveable.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir="/home/leeweihan/Desktop/range proof/build/CMakeFiles" --progress-num=$(CMAKE_PROGRESS_9) "Linking CXX executable test_rangeproof_proveable"
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_rangeproof_proveable.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
range_proof/CMakeFiles/test_rangeproof_proveable.dir/build: range_proof/test_rangeproof_proveable

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/build

range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/tests/test_rangeproof_proveable.cpp.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3.c.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_dispatch.c.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_portable.c.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse2_x86-64_unix.S.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_sse41_x86-64_unix.S.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx2_x86-64_unix.S.o.requires
range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires: range_proof/CMakeFiles/test_rangeproof_proveable.dir/bcs/BLAKE3/blake3_avx512_x86-64_unix.S.o.requires

.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/requires

range_proof/CMakeFiles/test_rangeproof_proveable.dir/clean:
	cd "/home/leeweihan/Desktop/range proof/build/range_proof" && $(CMAKE_COMMAND) -P CMakeFiles/test_rangeproof_proveable.dir/cmake_clean.cmake
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/clean

range_proof/CMakeFiles/test_rangeproof_proveable.dir/depend:
	cd "/home/leeweihan/Desktop/range proof/build" && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" "/home/leeweihan/Desktop/range proof" "/home/leeweihan/Desktop/range proof/range_proof" "/home/leeweihan/Desktop/range proof/build" "/home/leeweihan/Desktop/range proof/build/range_proof" "/home/leeweihan/Desktop/range proof/build/range_proof/CMakeFiles/test_rangeproof_proveable.dir/DependInfo.cmake" --color=$(COLOR)
.PHONY : range_proof/CMakeFiles/test_rangeproof_proveable.dir/depend

