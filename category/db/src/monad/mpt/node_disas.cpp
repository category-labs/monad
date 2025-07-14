#include <monad/mpt/node.hpp>

MONAD_MPT_NAMESPACE_BEGIN

uint16_t child_mask_disas(Node const &node)
{
    return child_mask(node);
}

bool child_test_disas(Node const &node, unsigned const i)
{
    return child_test(node, i);
}

bool child_all_disas(Node const &node)
{
    return child_all(node);
}

bool child_any_disas(Node const &node)
{
    return child_any(node);
}

bool child_none_disas(Node const &node)
{
    return child_none(node);
}

unsigned child_count_disas(Node const &node)
{
    return child_count(node);
}

unsigned child_index_disas(Node const &node, unsigned const i)
{
    return child_index(node, i);
}

std::pair<unsigned char const *, unsigned char>
child_path_disas(Node const &node, unsigned const i)
{
    return child_path(node, i);
}

MONAD_MPT_NAMESPACE_END
