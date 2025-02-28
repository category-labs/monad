#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt2/config.hpp>
#include <monad/mpt2/rlp/item.hpp>
#include <monad/rlp/config.hpp>

MONAD_MPT2_NAMESPACE_BEGIN

using RawList = rlp::RawList;
using RawString = rlp::RawString;
using RawNode = RawList;

inline bool is_branch_node(RawNode const &node)
{
    return node.size() == 17;
}

inline bool is_extension_node(RawNode const &node)
{
    if (node.size() != 2) {
        return false;
    }
    if (auto const *path = std::get_if<RawString>(&node[0].value);
        path != nullptr) {
        return ~(*path)[0] & 0x20;
    }
    return false;
}

inline bool is_leaf_node(RawNode const &node)
{
    if (node.size() != 2) {
        return false;
    }
    if (auto const *path = std::get_if<RawString>(&node[0].value);
        path != nullptr) {
        return (*path)[0] & 0x20;
    }
    return false;
}

// Decodes nibbles. However, it does not add the nibbles terminator for leaves
inline mpt::NibblesView decode_path(RawString const &nibbles)
{
    bool const is_odd_len = nibbles[0] & 0x10;
    if (is_odd_len) {
        return mpt::NibblesView{nibbles}.substr(1);
    }
    else {
        return mpt::NibblesView{nibbles}.substr(2);
    }
}

MONAD_MPT2_NAMESPACE_END
