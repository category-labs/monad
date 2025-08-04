#pragma once

#include <category/vm/core/assert.h>
#include <category/vm/utils/load_program.hpp>
#include <category/vm/utils/parser.hpp>
#include <stopwatch.hpp>

#include <valgrind/cachegrind.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace fs = std::filesystem;

template <bool instrument>
class InstrumentableDecoder
{
public:
    std::vector<uint8_t>
    decode(fs::path const &filename, InstrumentationDevice const device)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return decode<InstrumentationDevice::Cachegrind>(filename);
        case InstrumentationDevice::WallClock:
            return decode<InstrumentationDevice::WallClock>(filename);
        }
        std::unreachable();
    }

    template <InstrumentationDevice device>
    std::vector<uint8_t> decode(fs::path const &filename)
    {
        std::vector<char> const bytes = this->read_file(filename);
        if (filename.extension() == ".mevm") {
            std::string contents(bytes.begin(), bytes.end());
            monad::vm::utils::parser_config config{false, false};
            if constexpr (instrument) {
                if constexpr (device == InstrumentationDevice::Cachegrind) {
                    CACHEGRIND_START_INSTRUMENTATION;
                    std::vector<uint8_t> const code =
                        monad::vm::utils::parse_opcodes(config, contents);
                    CACHEGRIND_STOP_INSTRUMENTATION;
                    return code;
                }
                else {
                    timer.start();
                    std::vector<uint8_t> const code =
                        monad::vm::utils::parse_opcodes(config, contents);
                    timer.pause();
                    return code;
                }
            }
            else {
                return monad::vm::utils::parse_opcodes(config, contents);
            }
        }

        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {

                CACHEGRIND_START_INSTRUMENTATION;
                std::vector<uint8_t> const code =
                    monad::vm::utils::parse_hex_program(bytes);
                CACHEGRIND_STOP_INSTRUMENTATION;

                return code;
            }
            else {
                timer.start();

                std::vector<uint8_t> const code =
                    monad::vm::utils::parse_hex_program(bytes);

                timer.pause();
                return code;
            }
        }
        else {
            return monad::vm::utils::parse_hex_program(bytes);
        }
    }

private:
    std::vector<char> read_file(std::string const &filename)
    {
        if (filename == "-") {
            std::streamsize size = 65536; // 64K
            std::vector<char> contents;
            contents.reserve(static_cast<size_t>(size));

            char c;
            while (std::cin >> c) {
                contents.push_back(c);
            }
            return contents;
        }

        std::ifstream file(filename.c_str(), std::ios::binary | std::ios::ate);
        if (!file) {
            throw std::runtime_error("Failed to open file: " + filename);
        }

        // Get the file size
        std::streamsize size = file.tellg();
        file.seekg(0, std::ios::beg);
        MONAD_VM_ASSERT(size >= 0);

        // Allocate buffer and read file contents
        std::vector<char> contents(static_cast<size_t>(size), 0);
        if (!file.read(contents.data(), size)) {
            throw std::runtime_error("Failed to read file: " + filename);
        }
        return contents;
    }
};
