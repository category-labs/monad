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
# FPU, so each one is a call to __floatundisf and __mulsf3. Replacing it with an
# integer ratio is worth 0.236 % of block 25551991 -- 477,650 steps, 47,309,128
# COST -- measured against an otherwise identical build.
#
# The ratio here is `(n * 2) / 5`, a load factor of 0.4, and it is a CHOICE, not
# the arithmetic equivalent of upstream's 0.8: `(n * 4) / 5` would be that. The
# guest keeps twice the buckets for a given size, which halves how often the
# rehash refill runs and shortens every run `place_and_shift_up` walks. The
# payer is the insert side, not the find side -- `do_find` visits two buckets
# whatever the load factor, and the priced-opcode delta agrees, with `eq` and
# `add` falling while `ltu` barely moves.
#
# Iteration order does not move: this map iterates its dense value vector in
# insertion order, so no digest can observe the bucket count.
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

function(monad_zkvm_unordered_dense_derive target third_party_dir out_dir)
    set(_src "${third_party_dir}/unordered_dense/include/ankerl/unordered_dense.h")
    set(_out "${out_dir}/ankerl/unordered_dense.h")

    if(NOT EXISTS "${_src}")
        message(FATAL_ERROR
            "unordered_dense submodule not populated: ${_src} is missing. "
            "Run `git submodule update --init third_party/unordered_dense`.")
    endif()

    file(READ "${_src}" _text)

    # The substituted ratio replaces `n * max_load_factor()` outright, so the
    # header's own default stops being consulted. Guard on it anyway: it is the
    # anchor that says this file is still rewriting the expressions it thinks it
    # is, and a bump that moved the default almost certainly moved them too.
    #
    # Nothing in category/ or zkvm/ calls the setter; if that ever changes, the
    # caller gets 0.8 regardless and this guard will not catch it. Grep before
    # introducing one.
    string(FIND "${_text}"
        "static constexpr float default_max_load_factor = 0.8F;" _pos)
    if(_pos EQUAL -1)
        message(FATAL_ERROR
            "unordered_dense's default_max_load_factor is no longer 0.8F. The "
            "substitution in ${CMAKE_CURRENT_LIST_FILE} overrides it with a "
            "ratio of its own, so re-read the two expressions and confirm they "
            "are still the load-factor sites before bumping the submodule.")
    endif()

    # Two sites, each rewritten exactly once. Both are `private:` members of
    # table<>, so the expressions are unique in the file -- but check anyway,
    # because a silent no-match costs 0.236 % and changes nothing observable.
    set(_from_shifts
        "static_cast<size_t>(static_cast<float>(calc_num_buckets(shifts)) * max_load_factor())")
    set(_to_shifts
        "static_cast<size_t>((static_cast<uint64_t>(calc_num_buckets(shifts)) * 2) / 5)")
    set(_from_capacity
        "static_cast<value_idx_type>(static_cast<float>(m_num_buckets) * max_load_factor())")
    set(_to_capacity
        "static_cast<value_idx_type>((static_cast<uint64_t>(m_num_buckets) * 2) / 5)")

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

    # Three. clear_and_fill_buckets_from_values() drops its clear_buckets(). All
    # three of its call sites -- increase_size, rehash and reserve -- run
    # allocate_buckets_from_shift() on the line before, the guest's operator new
    # is a bump pointer whose delete is a no-op, and ZisK's memory AIR constrains
    # a first-access read to zero. So those buckets have never been written and
    # the memset is provably dead.
    #
    # clear_buckets() itself is untouched: clear(), move-assign and replace()'s
    # non-reallocating path all clear buckets that are NOT fresh.
    #
    # The check below is that argument mechanised: if a submodule bump moves a
    # call away from its allocation, the fill stops being dead and this fails the
    # configure instead of the state root. Its form matters twice over. Bracket arguments, because
    # `\(` is not a CMake escape in a quoted one. And a pairing test rather than
    # two counts, because `list(LENGTH)` over a MATCHALL whose matches contain a
    # `;` splits every match into several list elements -- three calls read as
    # six. Delete every call that DOES follow an allocation, then assert none is
    # left. Verified both ways: it passes on the pinned header and fires on a
    # copy with one call moved one line away from its allocation.
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
    # copy_if_different, not file(WRITE): file(WRITE) rewrites unconditionally, so the derived
    # header's mtime moved on every configure -- and cmake-rs configures on every cargo build.
    # Everything including unordered_dense.h then rebuilt, execute.cpp among them, which is the
    # single most expensive translation unit here: 33 s of a 47 s build, every commit, for a file
    # whose bytes had not changed.
    file(WRITE "${_out}.tmp" "${_text}")
    execute_process(COMMAND "${CMAKE_COMMAND}" -E copy_if_different "${_out}.tmp" "${_out}")
    file(REMOVE "${_out}.tmp")

    # Re-run cmake if the pinned header moves under us -- a submodule bump
    # otherwise leaves a stale generated copy in the build tree.
    set_property(DIRECTORY APPEND
        PROPERTY CMAKE_CONFIGURE_DEPENDS "${_src}")

    # BEFORE, so every consumer of the target resolves <ankerl/unordered_dense.h>
    # to the rewritten copy rather than the submodule's.
    target_include_directories(${target} BEFORE INTERFACE "${out_dir}")
endfunction()
