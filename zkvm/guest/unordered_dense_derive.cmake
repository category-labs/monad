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
# One. ankerl::unordered_dense stores max_load_factor as a `float` and computes
# `num_buckets * 0.8f` on every rehash and every size query. The guest has no
# FPU, so each one is a call to __floatundisf and __mulsf3. For the
# power-of-two bucket counts this map uses, `(n * 4) / 5` is the same integer.
# Worth 0.236 % of block 25551991 -- 477,650 steps, 47,309,128 COST -- measured
# against an otherwise identical build.
#
# The change belongs in the header, and the header is in a submodule pinned at
# martinus/unordered_dense. A submodule is a separate repository: no commit
# here can carry its file contents, and mutating its working tree leaves a
# dirty submodule that records nothing.
#
# So don't mutate it. Read the pinned header, rewrite the two expressions, and
# write a derived copy into the build tree, then put that copy ahead of the
# submodule on the include path. The submodule stays pristine, the
# transformation is versioned here, and it applies to the guest only -- the
# host build never sees it.
#
# This replaces the second half of third_party/patches/. The first half, the
# immer popcount hunk, went the same way for the same reason: see
# zkvm/core/builtin_popcount.hpp.

function(monad_zkvm_unordered_dense_derive target third_party_dir out_dir)
    set(_src "${third_party_dir}/unordered_dense/include/ankerl/unordered_dense.h")
    set(_out "${out_dir}/ankerl/unordered_dense.h")

    if(NOT EXISTS "${_src}")
        message(FATAL_ERROR
            "unordered_dense submodule not populated: ${_src} is missing. "
            "Run `git submodule update --init third_party/unordered_dense`.")
    endif()

    file(READ "${_src}" _text)

    # `(n * 4) / 5` is only the same number as `n * max_load_factor()` at the
    # default 0.8. The setter is public, so guard on the default being what we
    # think it is -- if upstream changes it, fail loudly rather than silently
    # mis-sizing every map in the guest.
    #
    # Nothing in category/ or zkvm/ calls the setter; if that ever changes, the
    # caller gets 0.8 regardless and this guard will not catch it. Grep before
    # introducing one.
    string(FIND "${_text}"
        "static constexpr float default_max_load_factor = 0.8F;" _pos)
    if(_pos EQUAL -1)
        message(FATAL_ERROR
            "unordered_dense's default_max_load_factor is no longer 0.8F. The "
            "integer substitution in ${CMAKE_CURRENT_LIST_FILE} assumes it. "
            "Re-derive the numerator/denominator before bumping the submodule.")
    endif()

    # Two sites, each rewritten exactly once. Both are `private:` members of
    # table<>, so the expressions are unique in the file -- but check anyway,
    # because a silent no-match costs 0.236 % and changes nothing observable.
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
    # merge them however aligned they are. Measured -- identical steps, COST and
    # every memory row.
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

    # Two float conversions survive on purpose, and there is deliberately no
    # warning about them: `load_factor()` at ~1738 and the `max_load_factor`
    # setter at ~1748, both public API the guest never calls. Rewriting dead
    # code buys nothing, and a warning that fires on every configure for code
    # that is provably unreached is how warnings get ignored.
    #
    # The invariant that matters is not "no float in the header", it is "no
    # soft-float in the image", and that is a link-time property this function
    # cannot see. Check it on the shipped ELF:
    #
    #   riscv64-unknown-elf-nm <elf> | grep -E '__(floatundisf|mulsf3|fixunssfdi)'
    #
    # Zero matches is the pass. If the setter ever acquires a caller those
    # symbols come back, the guest keeps working, and 0.236 % quietly is not
    # saved -- the same failure mode as the popcount override, and the same
    # remedy.
    file(WRITE "${_out}" "${_text}")

    # Re-run cmake if the pinned header moves under us -- a submodule bump
    # otherwise leaves a stale generated copy in the build tree.
    set_property(DIRECTORY APPEND
        PROPERTY CMAKE_CONFIGURE_DEPENDS "${_src}")

    # BEFORE, so every consumer of the target resolves <ankerl/unordered_dense.h>
    # to the rewritten copy rather than the submodule's.
    target_include_directories(${target} BEFORE INTERFACE "${out_dir}")
endfunction()
