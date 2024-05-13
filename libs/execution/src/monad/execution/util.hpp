#pragma once

#include <monad/config.hpp>

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

MONAD_NAMESPACE_BEGIN

inline int64_t get_proc_rss()
{
    std::ifstream stat_file("/proc/self/statm");
    if (!stat_file.is_open()) {
        std::cerr << "Failed to open /proc/self/statm" << std::endl;
        return -1;
    }

    std::string line;
    std::getline(stat_file, line);
    stat_file.close();

    std::istringstream iss(line);
    // RSS is the 2nd field in /proc/[pid]/statm
    std::string discard;
    iss >> discard;

    int64_t rss_pages = 0;
    iss >> rss_pages;

    return rss_pages * 4;
}

MONAD_NAMESPACE_END
