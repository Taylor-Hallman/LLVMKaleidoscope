cmake_minimum_required(VERSION 3.15)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")

# Project name and language
project(MyLang LANGUAGES CXX)

# Set C++ standard
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(LLVM_DIR "/home/taylor/llvm-project/build-Debug/lib/cmake/llvm")
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

# Add the executable
add_executable(MyLang my-lang.cpp)
#add_executable(MyLang their-code.cpp)

target_link_options(MyLang PRIVATE -rdynamic)

# Link against the full set of LLVM libs (or choose specific components)

llvm_map_components_to_libnames(LLVM_LIBS
  support
  core
  irreader
  analysis
  target
  executionengine
  orcjit
  orcshared
  orctargetprocess
  x86asmparser
  x86targetmca
  x86codegen
)

target_include_directories(MyLang PRIVATE ${LLVM_INCLUDE_DIRS})
target_compile_definitions(MyLang PRIVATE ${LLVM_DEFINITIONS})
target_link_libraries(MyLang PRIVATE ${LLVM_LIBS})

message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
