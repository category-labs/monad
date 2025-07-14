#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/compiler/ir/local_stacks.hpp>
#include <monad/vm/compiler/ir/poly_typed.hpp>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

namespace fs = std::filesystem;

using namespace monad::vm::compiler;

void usage_exit [[noreturn]] (char *prog)
{
    std::cerr << "usage: " << prog << " CONTRACT_DIRECTORY" << std::endl;
    exit(1);
}

void io_error_exit [[noreturn]] (std::string msg)
{
    std::cerr << "IO error: " << msg << std::endl;
    exit(1);
}

bool read_contract(fs::path const &path, std::vector<uint8_t> &result)
{
    std::ifstream s{path, std::ifstream::binary};
    if (s.good()) {
        s.seekg(0, s.end);
        result = std::vector<uint8_t>(static_cast<size_t>(s.tellg()));
        s.seekg(0, s.beg);
        s.read(
            reinterpret_cast<char *>(&result[0]),
            static_cast<std::streamsize>(result.size()));
    }
    return s.good();
}

void type_check_contract(
    fs::path const &path, std::vector<uint8_t> const &contract)
{
    basic_blocks::BasicBlocksIR const ir2{std::move(contract)};
    local_stacks::LocalStacksIR const ir3{std::move(ir2)};

    auto start_time = std::chrono::high_resolution_clock::now();
    poly_typed::PolyTypedIR ir{std::move(ir3)};
    auto elapsed_time = std::chrono::high_resolution_clock::now() - start_time;
    int64_t us =
        std::chrono::duration_cast<std::chrono::microseconds>(elapsed_time)
            .count();

    // std::cout << std::format("{}", ir) << std::endl;

    if (!ir.type_check()) {
        std::cerr << std::format("{} : {} us : failed", path.string(), us)
                  << std::endl;
    }
    else {
        if (ir.blocks.empty()) {
            std::cout << std::format(
                             "{} : {} us : s0 -> Exit", path.string(), us)
                      << std::endl;
        }
        else {
            std::cout << std::format(
                             "{} : {} us : {}",
                             path.string(),
                             us,
                             ir.blocks[0].kind)
                      << std::endl;
        }
    }
}

int main(int argc, char **argv)
{
    if (argc != 2) {
        usage_exit(argv[0]);
    }
    fs::path const dir{argv[1]};
    std::error_code ec;
    if (!fs::is_directory(dir, ec)) {
        usage_exit(argv[0]);
    }
    if (ec) {
        io_error_exit(ec.message());
    }
    for (auto const &file : fs::recursive_directory_iterator{dir, ec}) {
        if (!file.is_regular_file()) {
            continue;
        }
        std::vector<uint8_t> contract;
        if (!read_contract(file.path(), contract)) {
            io_error_exit("failed reading contract " + file.path().string());
        }
        type_check_contract(file.path(), contract);
    }
    if (ec) {
        io_error_exit(ec.message());
    }
}
