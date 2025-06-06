#include <monad/mpt/compute.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/merkle/compact_encode.hpp>
#include <monad/mpt/merkle/node_reference.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/rlp/encode.hpp>

#include <cstddef>
#include <cstring>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

unsigned encode_two_pieces(
    unsigned char *const dest, NibblesView const path,
    byte_string_view const second, bool const has_value)
{
    constexpr size_t max_compact_encode_size = KECCAK256_SIZE + 1;

    MONAD_DEBUG_ASSERT(path.data_size() <= KECCAK256_SIZE);

    unsigned char path_arr[max_compact_encode_size];
    auto const first = compact_encode(path_arr, path, has_value);
    MONAD_ASSERT_PRINTF(
        first.size() <= max_compact_encode_size,
        "size being encoded %zu maximum %zu",
        first.size(),
        max_compact_encode_size);
    // leaf and hashed node ref requires rlp encoding,
    // rlp encoded but unhashed branch node ref doesn't
    bool const need_encode_second =
        has_value || second.size() >= KECCAK256_SIZE;
    auto const concat_len =
        rlp::string_length(first) +
        (need_encode_second ? rlp::string_length(second) : second.size());
    byte_string concat_rlp(concat_len, 0);
    auto result = rlp::encode_string(concat_rlp, first);
    result = need_encode_second ? rlp::encode_string(result, second) : [&] {
        memcpy(result.data(), second.data(), second.size());
        return result.subspan(second.size());
    }();
    MONAD_DEBUG_ASSERT(
        (unsigned long)(result.data() - concat_rlp.data()) == concat_len);

    byte_string rlp(rlp::list_length(concat_len), 0);
    rlp::encode_list(rlp, {concat_rlp.data(), concat_rlp.size()});
    auto ret = to_node_reference({rlp.data(), rlp.size()}, dest);
    // free any long array allocated on heap
    return ret;
}

std::span<unsigned char> encode_empty_string(std::span<unsigned char> result)
{
    result[0] = RLP_EMPTY_STRING;
    return result.subspan(1);
}

std::span<unsigned char> encode_16_children(
    std::span<ChildData> const children, std::span<unsigned char> result)
{
    unsigned i = 0;
    for (auto &child : children) {
        if (child.is_valid()) {
            MONAD_DEBUG_ASSERT(child.branch < 16);
            while (child.branch != i) {
                result[0] = RLP_EMPTY_STRING;
                result = result.subspan(1);
                ++i;
            }
            MONAD_DEBUG_ASSERT(i == child.branch);
            result = (child.len < KECCAK256_SIZE)
                         ? [&] {
                               memcpy(result.data(), child.data, child.len);
                               return result.subspan(child.len);
                           }()
                         : rlp::encode_string(result, {child.data, child.len});
            ++i;
        }
    }
    // encode empty value string
    for (; i < 16; ++i) {
        result = encode_empty_string(result);
    }
    return result;
}

std::span<unsigned char>
encode_16_children(Node *node, std::span<unsigned char> result)
{

    for (unsigned i = 0, bit = 1; i < 16; ++i, bit <<= 1) {
        if (node->mask & bit) {
            auto const child_index = node->to_child_index(i);
            MONAD_DEBUG_ASSERT(
                node->child_data_len(child_index) <= KECCAK256_SIZE);
            result =
                (node->child_data_len(child_index) < KECCAK256_SIZE)
                    ? [&] {
                          memcpy(
                              result.data(),
                              node->child_data(child_index),
                              node->child_data_len(child_index));
                          return result.subspan(
                              node->child_data_len(child_index));
                      }()
                    : rlp::encode_string(result, node->child_data_view(child_index));
        }
        else {
            result = encode_empty_string(result);
        }
    }
    return result;
}

MONAD_MPT_NAMESPACE_END
