# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Generate a guest-only header with 64-bit buckets and integer capacity
# thresholds. A 40% load factor (upstream: 80%) reduces insertion collisions
# at the cost of more buckets. Iteration still follows the dense value vector.
# Skip the initial bucket clear only after a fresh allocation (checked below).
# Write the derived header in the build tree; leave the submodule unchanged.

function(monad_zkvm_unordered_dense_derive target third_party_dir out_dir)
    set(_src "${third_party_dir}/unordered_dense/include/ankerl/unordered_dense.h")
    set(_out "${out_dir}/ankerl/unordered_dense.h")

    if(NOT EXISTS "${_src}")
        message(FATAL_ERROR
            "unordered_dense submodule not populated: ${_src} is missing. "
            "Run `git submodule update --init third_party/unordered_dense`.")
    endif()

    file(READ "${_src}" _text)

    # Keep the pinned 0.8 default as an upstream-change guard.
    # The rewritten thresholds use a fixed 0.4 ratio; guest callers must not
    # change max_load_factor(), whose setter is not covered by this check.
    string(FIND "${_text}"
        "static constexpr float default_max_load_factor = 0.8F;" _pos)
    if(_pos EQUAL -1)
        message(FATAL_ERROR
            "unordered_dense's default_max_load_factor is no longer 0.8F. The "
            "substitution in ${CMAKE_CURRENT_LIST_FILE} overrides it with a "
            "ratio of its own, so re-read the two expressions and confirm they "
            "are still the load-factor sites before bumping the submodule.")
    endif()

    # Require both expected expressions so upstream changes cannot skip the patch.
    set(_from_shifts
        "static_cast<size_t>(static_cast<float>(calc_num_buckets(shifts)) * max_load_factor())")
    set(_to_shifts
        "static_cast<size_t>((static_cast<uint64_t>(calc_num_buckets(shifts)) * 2) / 5)")
    set(_from_capacity
        "static_cast<value_idx_type>(static_cast<float>(m_num_buckets) * max_load_factor())")
    set(_to_capacity
        "static_cast<value_idx_type>((static_cast<uint64_t>(m_num_buckets) * 2) / 5)")

    # ZisK charges less for aligned 64-bit accesses and native index arithmetic
    # than for 32-bit operations. Buckets grow from 8 to 16 bytes, and
    # value_idx_type widens with m_value_idx. alignas(8) alone gave no measured
    # gain: it did not widen the individual loads and stores.
    set(_from_bucket [==[    uint32_t m_dist_and_fingerprint; // upper 3 byte: distance to original bucket. lower byte: fingerprint from hash
    uint32_t m_value_idx;            // index into the m_values vector.]==])
    set(_to_bucket [==[    uint64_t m_dist_and_fingerprint; // upper bits: probe distance; low byte: hash fingerprint
    uint64_t m_value_idx;            // index into the m_values vector.]==])

    # increase_size(), rehash() and reserve() refill freshly allocated buckets.
    # The guest's bump allocator never reuses memory; on ZisK, reads before
    # any write are constrained to zero. Only this initial clear is redundant;
    # clear_buckets() must still clear reused arrays.
    #
    # Remove allocation/refill pairs from a temporary copy, then reject any
    # remaining refill call. Bracket arguments preserve regex escapes; matching
    # pairs avoids CMake's semicolon splitting of MATCHALL result lists.
    string(REGEX REPLACE
        [=[allocate_buckets_from_shift\(\)[^;]*;[^;]*clear_and_fill_buckets_from_values\(\)[^;]*;]=]
        "" _cf_probe "${_text}")
    string(FIND "${_cf_probe}" "clear_and_fill_buckets_from_values();" _cf_leftover)
    if(NOT _cf_leftover EQUAL -1)
        message(FATAL_ERROR
            "unordered_dense: a call of clear_and_fill_buckets_from_values() no "
            "longer follows allocate_buckets_from_shift(). Dropping its "
            "clear_buckets() in ${CMAKE_CURRENT_LIST_FILE} is sound only while "
            "every caller has just allocated fresh bump memory, which ZisK's "
            "memory AIR then constrains to read zero. Re-read the new caller.")
    endif()

    set(_from_fill [==[    void clear_and_fill_buckets_from_values() {
        clear_buckets();
        for (value_idx_type value_idx = 0,]==])
    set(_to_fill [==[    void clear_and_fill_buckets_from_values() {
        for (value_idx_type value_idx = 0,]==])

    foreach(_pair "_from_shifts;_to_shifts" "_from_capacity;_to_capacity"
                  "_from_bucket;_to_bucket" "_from_fill;_to_fill")
        list(GET _pair 0 _from_var)
        list(GET _pair 1 _to_var)
        string(FIND "${_text}" "${${_from_var}}" _found)
        if(_found EQUAL -1)
            message(FATAL_ERROR
                "unordered_dense rewrite site not found:\n  ${${_from_var}}\n"
                "The header changed under ${CMAKE_CURRENT_LIST_FILE}. Re-derive "
                "the substitution against the new pinned revision.")
        endif()
        string(REPLACE "${${_from_var}}" "${${_to_var}}" _text "${_text}")
    endforeach()

    # load_factor() and the max_load_factor setter retain float arithmetic;
    # neither is used by the guest. Check the final ELF for soft-float helpers:
    #   riscv64-unknown-elf-nm <elf> | grep -E '__(floatundisf|mulsf3|fixunssfdi)'
    # Expected: no matches.
    # Preserve the output's mtime when unchanged to avoid needless recompilation.
    file(WRITE "${_out}.tmp" "${_text}")
    execute_process(COMMAND "${CMAKE_COMMAND}" -E copy_if_different "${_out}.tmp" "${_out}")
    file(REMOVE "${_out}.tmp")

    # Regenerate when the submodule header changes.
    set_property(DIRECTORY APPEND
        PROPERTY CMAKE_CONFIGURE_DEPENDS "${_src}")

    # Prefer the derived header for every consumer of this target.
    target_include_directories(${target} BEFORE INTERFACE "${out_dir}")
endfunction()
