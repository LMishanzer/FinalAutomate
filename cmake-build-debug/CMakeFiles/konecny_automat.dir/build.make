# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.17

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Disable VCS-based implicit rules.
% : %,v


# Disable VCS-based implicit rules.
% : RCS/%


# Disable VCS-based implicit rules.
% : RCS/%,v


# Disable VCS-based implicit rules.
% : SCCS/s.%


# Disable VCS-based implicit rules.
% : s.%


.SUFFIXES: .hpux_make_needs_suffix_list


# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

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
CMAKE_COMMAND = /home/mike/.local/share/JetBrains/Toolbox/apps/CLion/ch-0/202.7660.37/bin/cmake/linux/bin/cmake

# The command to remove a file.
RM = /home/mike/.local/share/JetBrains/Toolbox/apps/CLion/ch-0/202.7660.37/bin/cmake/linux/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/mike/Projects/konecny_automat

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/mike/Projects/konecny_automat/cmake-build-debug

# Include any dependencies generated for this target.
include CMakeFiles/konecny_automat.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/konecny_automat.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/konecny_automat.dir/flags.make

CMakeFiles/konecny_automat.dir/sample.cpp.o: CMakeFiles/konecny_automat.dir/flags.make
CMakeFiles/konecny_automat.dir/sample.cpp.o: ../sample.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mike/Projects/konecny_automat/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/konecny_automat.dir/sample.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/konecny_automat.dir/sample.cpp.o -c /home/mike/Projects/konecny_automat/sample.cpp

CMakeFiles/konecny_automat.dir/sample.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/konecny_automat.dir/sample.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mike/Projects/konecny_automat/sample.cpp > CMakeFiles/konecny_automat.dir/sample.cpp.i

CMakeFiles/konecny_automat.dir/sample.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/konecny_automat.dir/sample.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mike/Projects/konecny_automat/sample.cpp -o CMakeFiles/konecny_automat.dir/sample.cpp.s

# Object files for target konecny_automat
konecny_automat_OBJECTS = \
"CMakeFiles/konecny_automat.dir/sample.cpp.o"

# External object files for target konecny_automat
konecny_automat_EXTERNAL_OBJECTS =

konecny_automat: CMakeFiles/konecny_automat.dir/sample.cpp.o
konecny_automat: CMakeFiles/konecny_automat.dir/build.make
konecny_automat: CMakeFiles/konecny_automat.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/mike/Projects/konecny_automat/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable konecny_automat"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/konecny_automat.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/konecny_automat.dir/build: konecny_automat

.PHONY : CMakeFiles/konecny_automat.dir/build

CMakeFiles/konecny_automat.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/konecny_automat.dir/cmake_clean.cmake
.PHONY : CMakeFiles/konecny_automat.dir/clean

CMakeFiles/konecny_automat.dir/depend:
	cd /home/mike/Projects/konecny_automat/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/mike/Projects/konecny_automat /home/mike/Projects/konecny_automat /home/mike/Projects/konecny_automat/cmake-build-debug /home/mike/Projects/konecny_automat/cmake-build-debug /home/mike/Projects/konecny_automat/cmake-build-debug/CMakeFiles/konecny_automat.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/konecny_automat.dir/depend

