#include <monad/vm/compiler/ir/poly_typed/kind.hpp>

#include <gtest/gtest.h>

#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::poly_typed;

TEST(kind, weak_equal_test)
{
    ASSERT_TRUE(weak_equal(word, word));

    ASSERT_FALSE(weak_equal(word, any));

    ASSERT_FALSE(weak_equal(word, cont(cont_kind({}))));
    ASSERT_FALSE(weak_equal(cont_kind({}, 0), cont_kind({})));
    ASSERT_FALSE(weak_equal(cont(cont_kind({}, 0)), cont(cont_kind({}))));
    ASSERT_FALSE(
        weak_equal(word_cont(cont_kind({}, 0)), word_cont(cont_kind({}))));

    ASSERT_TRUE(weak_equal(cont_kind({word}), cont_kind({})));
    ASSERT_TRUE(weak_equal(cont_kind({}), cont_kind({word})));

    ASSERT_TRUE(weak_equal(cont_kind({}), cont_kind({})));
    ASSERT_TRUE(weak_equal(cont(cont_kind({})), cont(cont_kind({}))));
    ASSERT_TRUE(weak_equal(word_cont(cont_kind({})), word_cont(cont_kind({}))));

    ASSERT_TRUE(weak_equal(cont_kind({}, 0), cont_kind({}, 0)));
    ASSERT_TRUE(weak_equal(cont(cont_kind({}, 0)), cont(cont_kind({}, 0))));
    ASSERT_TRUE(
        weak_equal(word_cont(cont_kind({}, 0)), word_cont(cont_kind({}, 0))));

    ASSERT_FALSE(weak_equal(cont_kind({}, 0), cont_kind({}, 1)));
    ASSERT_FALSE(weak_equal(cont(cont_kind({}, 0)), cont(cont_kind({}, 1))));
    ASSERT_FALSE(
        weak_equal(word_cont(cont_kind({}, 0)), word_cont(cont_kind({}, 1))));

    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));
    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 0),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 0)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 1)), word}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0)), any}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, word}, 0)), word}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({word, word}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));

    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0))}),
        cont_kind({cont(cont_kind({word, any}, 0))})));
    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0))}),
        cont_kind({cont(cont_kind({word, any}, 0)), word})));
    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0))}),
        cont_kind({cont(cont_kind({word, any}, 0)), word})));
    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0))}),
        cont_kind({cont(cont_kind({word, any}, 0)), word, word})));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0))}),
        cont_kind({cont(cont_kind({word, any}, 0)), any})));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0))}),
        cont_kind({cont(cont_kind({word, any}, 0)), kind_var(100)})));

    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any})), word}, 1),
        cont_kind({cont(cont_kind({word, any})), word}, 1)));
    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any})), word}, 1),
        cont_kind({cont(cont_kind({word, any, word})), word}, 1)));
    ASSERT_TRUE(weak_equal(
        cont_kind({cont(cont_kind({word, any})), word}, 1),
        cont_kind({cont(cont_kind({word, any, word, word})), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any})), word}, 1),
        cont_kind({cont(cont_kind({word, word, word, word})), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any})), word}, 1),
        cont_kind({cont(cont_kind({word})), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any})), word}, 1),
        cont_kind({cont(cont_kind({})), word}, 1)));
    ASSERT_FALSE(weak_equal(
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1),
        cont_kind({cont(cont_kind({word, any})), word}, 1)));
}

TEST(kind, can_specialize_test_basic)
{
    ASSERT_TRUE(can_specialize(any, any));
    ASSERT_TRUE(can_specialize(kind_var(0), kind_var(0)));
    ASSERT_TRUE(can_specialize(kind_var(0), kind_var(1)));

    ASSERT_TRUE(can_specialize(kind_var(0), word));
    ASSERT_FALSE(can_specialize(word, kind_var(0)));

    ASSERT_TRUE(can_specialize(kind_var(0), cont(cont_kind({}, 0))));
    ASSERT_TRUE(can_specialize(kind_var(0), cont(cont_kind({}, 1))));
    ASSERT_TRUE(can_specialize(kind_var(0), word_cont(cont_kind({}, 0))));
    ASSERT_TRUE(can_specialize(kind_var(0), word_cont(cont_kind({}, 1))));
    ASSERT_FALSE(can_specialize(cont(cont_kind({}, 0)), kind_var(0)));
    ASSERT_FALSE(can_specialize(cont(cont_kind({}, 1)), kind_var(0)));
    ASSERT_FALSE(can_specialize(word_cont(cont_kind({}, 0)), kind_var(0)));
    ASSERT_FALSE(can_specialize(cont(cont_kind({}, 1)), kind_var(0)));
}

TEST(kind, can_specialize_test_cont_var)
{
    ASSERT_TRUE(can_specialize(cont_kind({}, 0), cont_kind({}, 0)));
    ASSERT_TRUE(can_specialize(cont_kind({}, 0), cont_kind({}, 1)));

    ASSERT_TRUE(can_specialize(cont_kind({}, 0), cont_kind({word}, 1)));
    ASSERT_TRUE(can_specialize(cont_kind({}, 0), cont_kind({word}, 0)));
    ASSERT_FALSE(can_specialize(cont_kind({word}, 1), cont_kind({}, 0)));

    ASSERT_TRUE(
        can_specialize(cont_kind({word}, 0), cont_kind({word, word}, 0)));
    ASSERT_TRUE(can_specialize(cont_kind({word}, 0), cont_kind({word}, 0)));

    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1),
        cont_kind(
            {cont(cont_kind({word, any}, 0)), word, cont(cont_kind({}, 0))},
            1)));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));

    ASSERT_TRUE(can_specialize(
        cont_kind({kind_var(1), kind_var(0)}, 1),
        cont_kind({kind_var(0), kind_var(1)}, 0)));
    ASSERT_TRUE(can_specialize(
        cont_kind({kind_var(0), kind_var(1)}, 0),
        cont_kind({kind_var(0), kind_var(1)}, 0)));
    ASSERT_FALSE(can_specialize(
        cont_kind({kind_var(0), kind_var(0)}, 0),
        cont_kind({kind_var(0), kind_var(1)}, 0)));
    ASSERT_FALSE(can_specialize(
        cont_kind({kind_var(1), kind_var(1)}, 0),
        cont_kind({kind_var(0), kind_var(1)}, 0)));
    ASSERT_TRUE(can_specialize(
        cont_kind({kind_var(0), kind_var(0)}, 0),
        cont_kind({kind_var(1), kind_var(1)}, 0)));
    ASSERT_TRUE(can_specialize(
        cont_kind({kind_var(0), kind_var(0)}, 0),
        cont_kind({kind_var(1), kind_var(1)}, 1)));

    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({word}, 0)), word}, 1),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1)));
    ASSERT_FALSE(can_specialize(
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 1),
        cont_kind({cont(cont_kind({word}, 0)), word}, 1)));
    ASSERT_FALSE(can_specialize(
        cont_kind({cont(cont_kind({word}, 0)), word}, 0),
        cont_kind({cont(cont_kind({word, any}, 0)), word}, 0)));

    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind(
            {cont(cont_kind({word}, 0)), cont(cont_kind({word}, 0))}, 1)));
    ASSERT_FALSE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind(
            {cont(cont_kind({word}, 0)), cont(cont_kind({word}, 1))}, 1)));
    ASSERT_FALSE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind(
            {cont(cont_kind({word}, 0)), cont(cont_kind({word}, 2))}, 1)));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0))}, 0),
        cont_kind({cont(cont_kind({word}, 0)), word}, 0)));
}

TEST(kind, can_specialize_test_cont_words)
{
    ASSERT_TRUE(can_specialize(cont_words, cont_words));

    ASSERT_TRUE(can_specialize(cont_kind({word}), cont_words));
    ASSERT_TRUE(can_specialize(cont_words, cont_kind({word})));

    ASSERT_FALSE(can_specialize(cont_words, cont_kind({}, 0)));
    ASSERT_FALSE(can_specialize(cont_words, cont_kind({word}, 0)));

    ASSERT_TRUE(can_specialize(cont_kind({}, 0), cont_words));
    ASSERT_TRUE(can_specialize(cont_kind({word}, 0), cont_words));

    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({word}))}, 1)));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({}))}, 1)));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({word}, 0))}, 1),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({}))}, 1)));
    ASSERT_TRUE(can_specialize(
        cont_kind(
            {cont(cont_kind({word, word}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind({cont(cont_kind({})), cont(cont_kind({word}))}, 1)));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}))}, 0),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({word}))})));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({})), cont(cont_kind({}))}, 0),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({word}))})));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 0),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({word}))})));
    ASSERT_FALSE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({word}, 1))}, 1)));
    ASSERT_FALSE(can_specialize(
        cont_kind({cont(cont_kind({}, 0)), cont(cont_kind({}, 0))}, 1),
        cont_kind({cont(cont_kind({word})), cont(cont_kind({word}, 2))}, 1)));
    ASSERT_TRUE(can_specialize(
        cont_kind({cont(cont_kind({}))}),
        cont_kind({cont(cont_kind({word})), word})));
}

TEST(kind, alpha_equal_test_1)
{
    ASSERT_TRUE(alpha_equal(word, word));
    ASSERT_FALSE(alpha_equal(word, any));
    ASSERT_FALSE(alpha_equal(word, cont(cont_kind({}))));
}

TEST(kind, alpha_equal_test_2)
{
    auto mk = [](VarName s) { return cont_kind({word}, s); };
    ContKind const left = mk(0);
    ASSERT_TRUE(alpha_equal(left, left));
    ASSERT_TRUE(alpha_equal(left, mk(1)));
    ASSERT_FALSE(alpha_equal(left, cont_kind({word})));
    ASSERT_FALSE(alpha_equal(left, cont_kind({word, word}, 0)));
    ASSERT_FALSE(alpha_equal(left, cont_kind({any}, 0)));
}

TEST(kind, alpha_equal_test_3)
{
    auto mk = [](VarName s1, VarName s2, VarName v1, VarName v2, VarName l1) {
        return cont(cont_kind(
            {kind_var(v1),
             cont(cont_kind({}, s2)),
             kind_var(v1),
             kind_var(v2),
             literal_var(l1, cont_kind({kind_var(v1)}, s1))},
            s1));
    };
    Kind const left = mk(0, 1, 0, 1, 0);
    ASSERT_TRUE(alpha_equal(left, left));
    ASSERT_TRUE(alpha_equal(left, mk(10, 20, 30, 40, 0)));
    ASSERT_FALSE(alpha_equal(left, mk(10, 20, 30, 40, 1)));
    ASSERT_FALSE(alpha_equal(left, mk(10, 10, 30, 40, 0)));
    ASSERT_FALSE(alpha_equal(left, mk(10, 20, 30, 30, 0)));
}

TEST(kind, alpha_equal_test_4)
{
    ASSERT_TRUE(alpha_equal(
        cont_kind({kind_var(0), kind_var(1)}, 0),
        cont_kind({kind_var(1), kind_var(0)}, 0)));
    ASSERT_TRUE(alpha_equal(
        cont_kind({kind_var(0), kind_var(1)}, 0),
        cont_kind({kind_var(1), kind_var(0)}, 1)));
    ASSERT_TRUE(alpha_equal(
        cont_kind({kind_var(0), kind_var(1)}, 0),
        cont_kind({kind_var(0), kind_var(1)}, 0)));
    ASSERT_TRUE(alpha_equal(
        cont_kind({kind_var(0), kind_var(1)}, 0),
        cont_kind({kind_var(0), kind_var(1)}, 1)));
    ASSERT_FALSE(alpha_equal(
        cont_kind({kind_var(0), kind_var(0)}, 0),
        cont_kind({kind_var(1), kind_var(0)}, 0)));
    ASSERT_FALSE(alpha_equal(
        cont_kind({kind_var(0), kind_var(0)}, 0),
        cont_kind({kind_var(1), kind_var(0)}, 1)));
    ASSERT_FALSE(alpha_equal(
        cont_kind({kind_var(0), kind_var(0)}, 1),
        cont_kind({kind_var(1), kind_var(0)}, 1)));
}
