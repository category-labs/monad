cmake_minimum_required(VERSION 3.20)

project(rpmalloc LANGUAGES C)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED True)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_library(
    rpmallocwrap STATIC
    "rpmalloc.c"
    "rpmalloc.h"
    "malloc.c"
    "rpnew.h")
