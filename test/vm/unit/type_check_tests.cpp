#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/evm/opcodes.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <variant>
#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::poly_typed;

TEST(type_check, test_1)
{
    auto ir = PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR({ADD})));

    std::vector<Kind> const front = ir.blocks[0].kind->front;

    ir.blocks[0].kind->front.at(1) = kind_var(0);
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = front;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front.push_back(word);
    ASSERT_TRUE(ir.type_check()); // Less general type will work here

    ir.blocks[0].kind->front = front;
    ASSERT_TRUE(ir.type_check()); // sanity check
}

TEST(type_check, test_2)
{
    auto ir = PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR({JUMP})));

    std::vector<Kind> const front = ir.blocks[0].kind->front;
    ContKind const jump = std::get<Jump>(ir.blocks[0].terminator).jump_kind;

    ir.blocks[0].kind->front.at(0) = word;
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = front;
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<Jump>(ir.blocks[0].terminator).jump_kind =
        cont_kind({word}, ir.blocks[0].kind->tail);
    ASSERT_FALSE(ir.type_check());

    std::get<Jump>(ir.blocks[0].terminator).jump_kind = jump;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front.push_back(word);
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = front;
    ASSERT_TRUE(ir.type_check()); // sanity check
}

TEST(type_check, test_3)
{
    auto ir = PolyTypedIR(local_stacks::LocalStacksIR(
        basic_blocks::BasicBlocksIR({// Word,Word,Word,s -> Exit
                                     PUSH1,
                                     12,
                                     DUP1,
                                     SWAP2,
                                     ADD,
                                     PUSH1,
                                     9,
                                     JUMPI,
                                     // (s -> Exit),s -> Exit
                                     JUMP,
                                     JUMPDEST, // a,Word,Word,s -> Exit
                                     POP,
                                     RETURN,
                                     JUMPDEST, // Word,Word,s -> Exit
                                     RETURN})));

    ASSERT_TRUE(
        alpha_equal(ir.blocks[0].kind, cont_kind({word, word, word}, 0)));
    ASSERT_TRUE(alpha_equal(
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind,
        cont_kind({cont(cont_kind({word, word}, 0)), word, word}, 0)));
    ASSERT_TRUE(
        alpha_equal(ir.blocks[1].kind, cont_kind({cont(cont_kind({}, 0))}, 0)));
    ASSERT_TRUE(alpha_equal(
        ir.blocks[2].kind, cont_kind({kind_var(0), word, word}, 0)));
    ASSERT_TRUE(alpha_equal(ir.blocks[3].kind, cont_kind({word, word}, 0)));

    ContTailKind tail0 = ir.blocks[0].kind->tail;
    std::vector<Kind> const front0 = ir.blocks[0].kind->front;
    ContTailKind fallthrough_tail0 =
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->tail;
    std::vector<Kind> const fallthrough_front0 =
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front;
    Kind const jump_literal_var0 =
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front.at(0);

    ASSERT_TRUE(std::holds_alternative<LiteralVar>(*jump_literal_var0));

    ir.blocks[0].kind->tail = ContVar{std::get<ContVar>(tail0).var + 1};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = ContWords{};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check
                                  //
    ir.blocks[0].kind->front = {word, word};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = front0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front = {
        word, word, word};
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front =
        fallthrough_front0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->tail =
        ContVar{std::get<ContVar>(fallthrough_tail0).var + 1};
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->tail =
        fallthrough_tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front.at(0) =
        literal_var(
            std::get<LiteralVar>(*jump_literal_var0).var,
            cont_kind(
                {word}, std::get<LiteralVar>(*jump_literal_var0).cont->tail));
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front.at(0) =
        jump_literal_var0;
    ASSERT_TRUE(ir.type_check()); // sanity check
}

TEST(type_check, test_4)
{
    auto ir =
        PolyTypedIR(local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR(
            {// Word,(s -> Exit),((s -> Exit),s -> Exit),s -> Exit
             PUSH1,
             12,
             ADD,
             SWAP1,
             SWAP2,
             JUMPI,
             // (s -> Exit),s -> Exit
             JUMP})));

    ASSERT_TRUE(alpha_equal(
        ir.blocks[0].kind,
        cont_kind(
            {word,
             cont(cont_kind({}, 0)),
             cont(cont_kind({cont(cont_kind({}, 0))}, 0))},
            0)));
    ASSERT_TRUE(
        alpha_equal(ir.blocks[1].kind, cont_kind({cont(cont_kind({}, 0))}, 0)));

    ContTailKind tail0 = ir.blocks[0].kind->tail;

    ir.blocks[0].kind->tail = ContVar{std::get<ContVar>(tail0).var + 1};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    VarName const v =
        std::get<ContVar>(
            std::get<Cont>(*ir.blocks[0].kind->front[2]).cont->tail)
            .var;
    ir.blocks[0].kind->front[2] =
        cont(cont_kind({cont(cont_kind({}, v + 1))}, v));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[2] =
        cont(cont_kind({cont(cont_kind({}, v))}, v + 1));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[2] =
        cont(cont_kind({cont(cont_kind({word}, v))}, v));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[2] =
        cont(cont_kind({cont(cont_kind({word}, v + 1))}, v));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[2] = cont(cont_kind({cont(cont_kind({}, v))}, v));
    ASSERT_TRUE(ir.type_check()); // sanity check

    VarName const w =
        std::get<ContVar>(
            std::get<Cont>(*ir.blocks[0].kind->front[1]).cont->tail)
            .var;

    ir.blocks[0].kind->front[1] = cont(cont_kind({}, w + 1));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[1] = cont(cont_kind({word}, w + 1));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[1] = cont(cont_kind({word}, w));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[1] = cont(cont_kind({}, w));
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front[0] = cont(cont_kind({}, w));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] = any;
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] = word;
    ASSERT_TRUE(ir.type_check()); // sanity check
}

TEST(type_check, test_5)
{
    auto ir =
        PolyTypedIR(local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR({
            // (Word : (Word : Word,s -> Exit),(Word : Word,s -> Exit),s ->
            // Exit),(Word : Word,s -> Exit),s -> Exit
            DUP2, // a1,a0,a1,s1 -> Exit
            SWAP1, // a0,a1,a1,s1 -> Exit
            DUP2, // a1,a0,a1,a1,s1 -> Exit
            DUP2, // a0,a1,a0,a1,a1,s1 -> Exit
            ADD, // Word,a0,a1,a1,s1 -> Exit
            SWAP1, // a0,Word,a1,a1,s1 -> Exit
            JUMPI, // a1,a1,s1 -> Exit
            // Word,(Word,s -> Exit),s -> Exit
            PUSH1,
            1, // Word,Word,(Word,s -> Exit),s -> Exit
            ADD, // Word,(Word,s -> Exit),s -> Exit
            SWAP1, // (Word,s -> Exit),Word,s -> Exit
            JUMP // Word,s -> Exit
        })));

    ASSERT_TRUE(alpha_equal(
        ir.blocks[0].kind,
        cont_kind(
            {word_cont(cont_kind(
                 {word_cont(cont_kind({word}, 0)),
                  word_cont(cont_kind({word}, 0))},
                 0)),
             word_cont(cont_kind({word}, 0))},
            0)));
    ASSERT_TRUE(alpha_equal(
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind,
        cont_kind(
            {word_cont(cont_kind({word}, 0)), word_cont(cont_kind({word}, 0))},
            0)));
    ASSERT_TRUE(alpha_equal(
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind,
        cont_kind({word, cont(cont_kind({word}, 0))}, 0)));

    ASSERT_TRUE(alpha_equal(
        ir.blocks[1].kind, cont_kind({word, cont(cont_kind({word}, 0))}, 0)));

    std::vector<Kind> front0 = ir.blocks[0].kind->front;
    ContTailKind tail0 = ir.blocks[0].kind->tail;
    std::vector<Kind> jump_front0 =
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front;
    std::vector<Kind> fallthrough_front0 =
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front;

    ir.blocks[0].kind->tail = ContVar{std::get<ContVar>(tail0).var + 1};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->tail = ContWords{};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front[0] = word;
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] = front0[0];
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front[1] = word;
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[1] = front0[1];
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front[0] = cont(std::get<WordCont>(*front0[0]).cont);
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] = front0[0];
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front[1] = cont(std::get<WordCont>(*front0[1]).cont);
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[1] = front0[1];
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[0] =
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[0];
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[0] =
        jump_front0[0];
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[1] =
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[1];
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[1] =
        jump_front0[1];
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[0] =
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[0];
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[0] =
        fallthrough_front0[0];
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[1] =
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[1];
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[1] =
        fallthrough_front0[1];
    ASSERT_TRUE(ir.type_check()); // sanity check
}

TEST(type_check, test_6)
{
    auto ir = PolyTypedIR(local_stacks::LocalStacksIR(
        basic_blocks::BasicBlocksIR({// (Any,Any,s -> Exit),Word,s -> Exit
                                     DUP1, // a,a,Word,s -> Exit
                                     SWAP2, // Word,a,a,s -> Exit
                                     DUP2, // a,Word,a,a,s -> Exit
                                     JUMPI, // a,a,s -> Exit
                                     POP,
                                     STOP})));

    ASSERT_TRUE(alpha_equal(
        ir.blocks[0].kind,
        cont_kind({cont(cont_kind({any, any}, 0)), word}, 0)));
    ASSERT_TRUE(alpha_equal(
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind,
        cont_kind({any, any}, 0)));
    ASSERT_TRUE(alpha_equal(
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind,
        cont_kind(
            {cont(cont_kind({any, any}, 0)), cont(cont_kind({any, any}, 0))},
            0)));

    std::vector<Kind> const front0 = ir.blocks[0].kind->front;
    std::vector<Kind> const fallthrough_front0 =
        std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front;
    std::vector<Kind> jump_front0 =
        std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front;

    ir.blocks[0].kind->front[0] =
        cont(cont_kind({any, any, any}, ir.blocks[0].kind->tail));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] =
        cont(cont_kind({any}, ir.blocks[0].kind->tail));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] =
        cont(cont_kind({any, kind_var(100)}, ir.blocks[0].kind->tail));
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front[0] =
        cont(cont_kind({any, any}, ir.blocks[0].kind->tail));
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[0] =
        ir.blocks[0].kind->front[0];
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).jump_kind->front[0] =
        jump_front0[0];
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[0] =
        cont(cont_kind({any}, ir.blocks[0].kind->tail));
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[0] =
        cont(cont_kind({any, any}, ir.blocks[0].kind->tail));
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[1] =
        cont(cont_kind({kind_var(100), any}, ir.blocks[0].kind->tail));
    ASSERT_FALSE(ir.type_check());

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[1] =
        cont(cont_kind({any, any}, ir.blocks[0].kind->tail));
    ASSERT_TRUE(ir.type_check()); // sanity check

    std::get<JumpI>(ir.blocks[0].terminator).fallthrough_kind->front[1] = any;
    ASSERT_TRUE(ir.type_check()); // should still type check

    ir.blocks[0].kind->front[0] =
        word_cont(cont_kind({any, any}, ir.blocks[0].kind->tail));
    ASSERT_TRUE(ir.type_check()); // should still type check
}

TEST(type_check, test_7)
{
    auto ir =
        PolyTypedIR(local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR(
            {DUP1, ADD, JUMPDEST, DUP1, PUSH1, 1, ADD, JUMP})));

    ASSERT_TRUE(alpha_equal(ir.blocks[0].kind, cont_kind({word})));
    ASSERT_TRUE(alpha_equal(
        std::get<FallThrough>(ir.blocks[0].terminator).fallthrough_kind,
        cont_kind({word})));

    ASSERT_TRUE(alpha_equal(ir.blocks[1].kind, cont_words));
    ASSERT_TRUE(alpha_equal(
        std::get<Jump>(ir.blocks[1].terminator).jump_kind, cont_words));

    ASSERT_TRUE(ir.type_check());

    ir.blocks[0].kind->front = {};
    ASSERT_TRUE(ir.type_check());

    ir.blocks[0].kind->front = {word, word};
    ASSERT_TRUE(ir.type_check());

    ir.blocks[0].kind->front = {word, word, word, word};
    ASSERT_TRUE(ir.type_check());

    ir.blocks[1].kind->front = {word};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {word, word};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {any};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {word, any};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {kind_var(100)};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {word, kind_var(100)};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {any};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {word, any};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {kind_var(100)};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {word, kind_var(100)};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {any};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {word, any};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {kind_var(100)};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {word, kind_var(100)};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->front = {word};
    ir.blocks[1].kind->front = {};
    ASSERT_TRUE(ir.type_check()); // sanity check

    ContTailKind const tail0 = ir.blocks[0].kind->tail;
    ContTailKind const tail1 = ir.blocks[1].kind->tail;

    ir.blocks[0].kind->tail = ContVar{0};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[1].kind->front = {word};
    ir.blocks[1].kind->tail = ContVar{0};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {};
    ir.blocks[1].kind->tail = tail1;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front = {word};
    ir.blocks[1].kind->front = {word};
    ir.blocks[0].kind->tail = ContVar{0};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[1].kind->front = {};
    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check

    ir.blocks[0].kind->front = {word, word};
    ir.blocks[0].kind->tail = ContVar{0};
    ASSERT_FALSE(ir.type_check());

    ir.blocks[0].kind->tail = tail0;
    ASSERT_TRUE(ir.type_check()); // sanity check
}

TEST(type_check, error_1)
{
    auto ir = PolyTypedIR(local_stacks::LocalStacksIR(
        basic_blocks::BasicBlocksIR({DUP3, DUP4, JUMPI})));
    ASSERT_TRUE(ir.type_check());
}

TEST(type_check, error_2)
{
    auto ir1 = std::vector<std::uint8_t>{
        POP,      CALLER,   CALLER,   PUSH14,   0x61,     0x6b,     0x61,
        0x6b,     0x65,     0x5f,     0x73,     0x68,     0x61,     0x72,
        0x65,     0x64,     0x5f,     0x74,     PUSH2,    0x01,     0x01,
        ADD,      PUSH6,    0x5b,     0x5b,     0x5b,     0x5b,     0x5b,
        0x5b,     JUMPDEST, JUMPDEST, JUMPDEST, JUMPDEST, JUMPDEST, JUMPDEST,
        PUSH0,    PUSH20,   0x33,     0x86,     0x96,     0x96,     0x96,
        0x96,     0x96,     0x96,     0x96,     0x96,     0x96,     0x96,
        0x96,     0x96,     0x96,     0x96,     0x68,     0x91,     0x91,
        0x11,     JUMPDEST, JUMPDEST, JUMPDEST, JUMPDEST, JUMPDEST, JUMPDEST,
        JUMPDEST, PUSH0,    PUSH20,   0x33,     0x86,     0x96,     0x96,
        0x96,     0x96,     0x96,     0x96,     0x96,     0x96,     0x96,
        0x96,     0x96,     0x96,     0x96,     0x5b,     0x5b,     0xaa,
        0x5b,     0xb5,     MULMOD,   MULMOD,   MULMOD,   MULMOD,   JUMPDEST,
        JUMPDEST, PUSH1,    0x5b,     JUMPDEST, DUP5};

    auto ir = PolyTypedIR(local_stacks::LocalStacksIR(
        basic_blocks::BasicBlocksIR(std::move(ir1))));

    ASSERT_TRUE(ir.type_check());
}

TEST(type_check, error_3)
{
    auto ir1 = std::vector<std::uint8_t>(
        {0x80, 0x81, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x7c, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x57,
         0x57, 0x57, 0x57, 0x8a, 0x57, 0x30, 0x89, 0xff});
    auto ir = PolyTypedIR(local_stacks::LocalStacksIR(
        basic_blocks::BasicBlocksIR(std::move(ir1))));
    ASSERT_TRUE(ir.type_check());
}

TEST(type_check, error_4)
{
    auto ir1 = std::vector<std::uint8_t>(
        {0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5b,
         0x60, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
         0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x64, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
         0x57, 0x57, 0x57, 0x57, 0x57, 0x30, 0xb5, 0x30, 0x30, 0x30, 0x30, 0x30,
         0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5b, 0x60, 0x30, 0x8e,
         0x56, 0x5b, 0x60, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
         0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x57});
    auto ir2 = basic_blocks::BasicBlocksIR(std::move(ir1));
    auto ir3 = local_stacks::LocalStacksIR(std::move(ir2));
    auto ir = PolyTypedIR(std::move(ir3));
    ASSERT_TRUE(ir.type_check());
}
