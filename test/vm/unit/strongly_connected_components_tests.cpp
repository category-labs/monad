#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed/block.hpp>
#include <category/vm/compiler/ir/poly_typed/infer_state.hpp>
#include <category/vm/compiler/ir/poly_typed/strongly_connected_components.hpp>
#include <category/vm/compiler/types.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <iostream>
#include <unordered_map>
#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::poly_typed;

namespace
{
    void assert_components(
        std::vector<Component> const &x, std::vector<Component> const &y)
    {
        ASSERT_EQ(x.size(), y.size());
        for (size_t i = 0; i < x.size(); ++i) {
            auto const &x1 = x[i];
            auto const &y1 = y[i];
            ASSERT_EQ(x1.size(), y1.size());
            for (block_id const bid : x1) {
                ASSERT_TRUE(y1.contains(bid));
            }
            for (block_id const bid : y1) {
                ASSERT_TRUE(x1.contains(bid));
            }
        }
    }

    __attribute__((unused)) void
    debug_print(std::vector<Component> const &components)
    {
        std::cout << "{";
        for (auto const &c : components) {
            std::cout << "{";
            for (auto x : c) {
                std::cout << x << ",";
            }
            std::cout << "},";
        }
        std::cout << "}\n";
    }
}

TEST(poly_typed, strongly_connected_components_1)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {};
    std::vector<local_stacks::Block> const pre_blocks = {local_stacks::Block{
        .min_params = 0,
        .output = {},
        .instrs = {},
        .terminator = basic_blocks::Terminator::Stop,
        .fallthrough_dest = 0,
        .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{0}});
}

TEST(poly_typed, strongly_connected_components_2)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {1, 1}, {2, 2}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 1}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 2}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 1}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{2, 1}, {0}});
}

TEST(poly_typed, strongly_connected_components_3)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {0, 0}, {1, 1}, {2, 2}, {3, 3}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 2}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 1,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 3}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 2}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{3, 2}, {1, 0}});
}

TEST(poly_typed, strongly_connected_components_4)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {0, 0}, {1, 1}, {2, 2}, {3, 3}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 2}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 1,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 3,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 2}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 4,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Stop,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{4}, {1, 3, 2, 0}});
}

TEST(poly_typed, strongly_connected_components_5)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {0, 0}, {1, 1}, {2, 2}, {4, 4}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 4}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 1,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 2,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 1}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 3,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Stop,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{3}, {2, 1, 4, 0}});
}

TEST(poly_typed, strongly_connected_components_6)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {0, 0}, {1, 1}, {2, 2}, {3, 3}, {4, 4}, {5, 5}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 3}, Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 1,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::COMPUTED, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::FallThrough,
            .fallthrough_dest = 2,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 1}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::COMPUTED, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::FallThrough,
            .fallthrough_dest = 4,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 5}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 3}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{2, 1}, {5, 4, 3}, {0}});
}

TEST(poly_typed, strongly_connected_components_7)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {0, 0}, {1, 1}, {2, 2}, {3, 3}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output =
                {Value{ValueIs::LITERAL, 2},
                 Value{ValueIs::COMPUTED, 0},
                 Value{ValueIs::LITERAL, 3}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 1,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output =
                {Value{ValueIs::LITERAL, 4},
                 Value{ValueIs::COMPUTED, 0},
                 Value{ValueIs::LITERAL, 0},
                 Value{ValueIs::COMPUTED, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{1, 2, 3, 0}});
}

TEST(poly_typed, strongly_connected_components_8)
{
    std::unordered_map<byte_offset, block_id> const jumpdests = {
        {0, 0}, {1, 1}};
    std::vector<local_stacks::Block> const pre_blocks = {
        local_stacks::Block{
            .min_params = 0,
            .output =
                {Value{ValueIs::LITERAL, 3},
                 Value{ValueIs::COMPUTED, 0},
                 Value{ValueIs::LITERAL, 2}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::JumpI,
            .fallthrough_dest = 1,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0},
        local_stacks::Block{
            .min_params = 0,
            .output = {Value{ValueIs::LITERAL, 0}},
            .instrs = {},
            .terminator = basic_blocks::Terminator::Jump,
            .fallthrough_dest = 0,
            .offset = 0}};
    std::vector<Component> const components =
        strongly_connected_components(InferState(jumpdests, pre_blocks));
    assert_components(components, {{1, 0}, {2}});
}
