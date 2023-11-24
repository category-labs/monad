#include <monad/analysis/ssa.hpp>

MONAD_ANALYSIS_NAMESPACE_BEGIN

StackValue::StackValue(StackValue::Variant value)
    : value{value}
{
}

MONAD_ANALYSIS_NAMESPACE_END
