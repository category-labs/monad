#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <vector>

#include <category/core/small_prng.hpp>
#include <category/core/unordered_map.hpp>

/*
We know from analysing Ethereum chain history that:

- Under 2% of all accounts are recipients of 65% of all transactions.
- Under 5% of all accounts are recipients of 75% of all transactions.
- Around one third of all accounts are recipients of 90% of all
transactions.
- Around two thirds of all accounts are recipients of 95% of all
transactions.

Or put another way:
- One third of all accounts are recipients of 5% of all transactions.
- Two thirds of all accounts are recipients of 10% of all transactions.
- 95% of all accounts are recipients of 25% of all transactions.
- 98% of all accounts are recipients of 35% of all transactions.
- So just under 2% of all accounts are recipients of two thirds of all
transactions.

- The regression line for this is (6 ^ (6 * ratio)) / (6 ^ 6)

We can't have duplicate keys per SLICE_LEN, and we fill 100000 SLICE_LENs
per prepare_keccak(). 65% of each SLICE_LEN needs to use the same
keys each upsert. 10% of each SLICE_LEN needs to be unique across
upserts.


*/

static constexpr uint32_t SLICE_LEN = 100000;
static constexpr uint32_t SLICES = 50000;
static constexpr double MULTIPLIER = 3.7;
static double const DIVISOR = pow(MULTIPLIER, MULTIPLIER);
static constexpr uint32_t BUCKETS = 20;
static constexpr uint32_t TOTAL_KEYS = 500000000;
static double const MAX_RAND = double(monad::small_prng::max());

int main()
{
    std::vector<uint32_t> arr;
    if (!std::filesystem::exists("array_sorted.bin") &&
        !std::filesystem::exists("array_unsorted.bin")) {
        monad::unordered_flat_map<uint32_t, uint32_t> map;
        monad::unordered_flat_set<uint32_t> seen;
        std::cout << "Generating map ..." << std::endl;
        monad::small_prng rand;
        for (uint32_t x = 0; x < SLICES; x++) {
            seen.clear();
            for (uint64_t y = 0; y < SLICE_LEN; y++) {
                double r = double(rand()) / MAX_RAND;
                r = pow(MULTIPLIER, MULTIPLIER * r) / DIVISOR;
                uint32_t const j = uint32_t(double(TOTAL_KEYS) * r);
                if (!seen.contains(j)) {
                    auto &v = map[j];
                    v += 1;
                    seen.insert(j);
                }
            }
        }
        std::cout << "Generating array from map ..." << std::endl;
        arr.reserve(map.size());
        for (auto &i : map) {
            arr.push_back(i.second);
        }
        map.clear();
        std::cout << "Writing into 'array_unsorted.bin' ..." << std::endl;
        std::ofstream s("array_unsorted.bin");
        s.write(
            (char const *)arr.data(),
            std::streamsize(arr.size() * sizeof(uint32_t)));
    }

    if (!std::filesystem::exists("array_sorted.bin")) {
        if (arr.empty()) {
            std::ifstream s("array_unsorted.bin");
            s.seekg(0, std::ios::end);
            arr.resize(size_t(s.tellg()) / sizeof(uint32_t));
            s.seekg(0, std::ios::beg);
            s.read(
                (char *)arr.data(),
                std::streamsize(arr.size() * sizeof(uint32_t)));
        }
        std::cout << "Starting array sort of " << arr.size()
                  << " integers, this is the slowest part ..." << std::endl;
        std::sort(arr.begin(), arr.end());
        std::cout << "\n"
                  << arr.size() << " " << (SLICE_LEN * SLICES) << std::endl;
        std::cout << "Writing into 'array_sorted.bin' ..." << std::endl;
        std::ofstream s("array_sorted.bin");
        s.write(
            (char const *)arr.data(),
            std::streamsize(arr.size() * sizeof(uint32_t)));
        std::filesystem::remove("array_unsorted.bin");
    }
    if (arr.empty()) {
        std::ifstream s("array_sorted.bin");
        s.seekg(0, std::ios::end);
        arr.resize(size_t(s.tellg()) / sizeof(uint32_t));
        s.seekg(0, std::ios::beg);
        s.read(
            (char *)arr.data(), std::streamsize(arr.size() * sizeof(uint32_t)));
    }
    uint32_t largest = 0;
    for (auto &i : arr) {
        if (i > largest) {
            largest = i;
        }
    }
    std::cout << "highest frequency = " << largest << std::endl;
    std::vector<uint32_t> counts(largest);
    {
        uint64_t sum = 0;
        for (auto &i : arr) {
            counts[i - 1]++;
            sum++;
        }
        for (auto &i : counts) {
            std::cout << (100.0 * double(&i - counts.data() + 1) /
                          double(counts.size()))
                      << "%: " << i << " " << (100.0 * i / double(sum))
                      << "%\n";
        }
        std::cout << "\nNormalised to 5% bucket increments:\n" << std::flush;
    }
    // Need to normalise the histogram so they become comparable
    std::vector<float> histogram(1000000);
    for (size_t n = 0, step = histogram.size() / counts.size();
         n < counts.size();
         n++) {
        histogram[n * step] = float(counts[n]);
    }
    size_t sidx = 0;
    size_t eidx = 0;
    for (bool done = false; !done;) {
        done = true;
        for (;;) {
            while (histogram[eidx] != 0 && eidx < histogram.size()) {
                eidx++;
            }
            sidx = eidx - 1;
            while (histogram[eidx] == 0 && eidx < histogram.size()) {
                eidx++;
            }
            if (eidx == histogram.size()) {
                eidx--;
                if (eidx - sidx < 2) {
                    sidx = eidx = 0;
                    break;
                }
            }
            if (eidx - sidx > 1) {
                histogram[(sidx + eidx) / 2] =
                    (histogram[sidx] + histogram[eidx]) / 2;
                done = false;
            }
            sidx = eidx;
        }
    }
    float sum = 0;
    for (size_t n = 0; n < histogram.size(); n += histogram.size() / BUCKETS) {
        sum += histogram[n];
    }
    for (size_t n = 0; n < histogram.size(); n += histogram.size() / BUCKETS) {
        std::cout << "\n"
                  << histogram[n] << " " << (100.0 * histogram[n] / sum) << "%";
    }
    std::cout << std::endl;
    return 0;
}
