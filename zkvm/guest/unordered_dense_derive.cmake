# Copyright (C) 2025 Category Labs, Inc.
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

# Two derivations of the pinned ankerl::unordered_dense header, both guest-only.
#
# One. Compute 80% bucket-capacity thresholds with integers to avoid soft-float
# calls in the guest. From 2^24 buckets, thresholds can differ from float rounding.
# Generate a guest-only header in the build tree; leave the submodule unchanged.

function(monad_zkvm_unordered_dense_derive target third_party_dir out_dir)
    set(_src "${third_party_dir}/unordered_dense/include/ankerl/unordered_dense.h")
    set(_out "${out_dir}/ankerl/unordered_dense.h")

    if(NOT EXISTS "${_src}")
        message(FATAL_ERROR
            "unordered_dense submodule not populated: ${_src} is missing. "
            "Run `git submodule update --init third_party/unordered_dense`.")
    endif()

    file(READ "${_src}" _text)

    # Require the 0.8 default assumed by the integer formulas.
    # Guest callers must not change max_load_factor: this guard checks only
    # the upstream default, not calls to the public setter.
    string(FIND "${_text}"
        "static constexpr float default_max_load_factor = 0.8F;" _pos)
    if(_pos EQUAL -1)
        message(FATAL_ERROR
            "unordered_dense's default_max_load_factor is no longer 0.8F. The "
            "integer substitution in ${CMAKE_CURRENT_LIST_FILE} assumes it. "
            "Re-derive the numerator/denominator before bumping the submodule.")
    endif()

    # Require both expected expressions so upstream changes cannot skip the patch.
    set(_from_shifts
        "static_cast<size_t>(static_cast<float>(calc_num_buckets(shifts)) * max_load_factor())")
    set(_to_shifts
        "static_cast<size_t>((static_cast<uint64_t>(calc_num_buckets(shifts)) * 4) / 5)")
    set(_from_capacity
        "static_cast<value_idx_type>(static_cast<float>(m_num_buckets) * max_load_factor())")
    set(_to_capacity
        "static_cast<value_idx_type>((static_cast<uint64_t>(m_num_buckets) * 4) / 5)")

    # Two. bucket_type::standard holds its two fields as uint32_t, and ZisK
    # charges a 4-byte read 122 cells and a 4-byte write 193, against 17 and 18
    # for an aligned 8-byte one -- anything narrower than a word is a sub-word
    # access there. A probe reads one field and place_and_shift_up reads and
    # writes both per displacement, so a bucket costs hundreds of cells where a
    # word would cost seventeen. The narrow fields also put value_idx_type's
    # arithmetic on the 32-bit path, priced at 60 against a native add's 15.3,
    # and make every widening a `sll 32` + `srl 32` pair at 56 apiece.
    #
    # Alignment is not the blocker and alignas(8) alone changes nothing: gcc
    # interleaves the second field's load between the two stores, so it cannot
    # merge them however aligned they are.
    #
    # Sixteen bytes a bucket rather than eight. Buckets run about 1.25x the
    # element count, so the guest's largest map costs a few hundred kilobytes
    # more against 42 MB of RAM in use. value_idx_type follows m_value_idx, and
    # the bucket count stays bounded by calc_num_buckets' `1 << (64 - shifts)`
    # rather than by max_bucket_count.
    set(_from_bucket [==[    uint32_t m_dist_and_fingerprint; // upper 3 byte: distance to original bucket. lower byte: fingerprint from hash
    uint32_t m_value_idx;            // index into the m_values vector.]==])
    set(_to_bucket [==[    uint64_t m_dist_and_fingerprint; // upper 3 byte: distance to original bucket. lower byte: fingerprint from hash
    uint64_t m_value_idx;            // index into the m_values vector.]==])

    foreach(_pair "_from_shifts;_to_shifts" "_from_capacity;_to_capacity"
                  "_from_bucket;_to_bucket")
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
