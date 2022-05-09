cmake_minimum_required(VERSION 2.9)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -std=c2x -Wno-unknown-attributes")

project(page_table_walker)

include_directories(${PROJECT_SOURCE_DIR} _opam/lib/refinedc/include/)
