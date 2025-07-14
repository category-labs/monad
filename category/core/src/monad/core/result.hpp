#pragma once

#include <monad/config.hpp>

#include <boost/outcome/experimental/status_result.hpp>

MONAD_NAMESPACE_BEGIN

namespace outcome = BOOST_OUTCOME_V2_NAMESPACE;
namespace outcome_e = outcome::experimental;

template <typename T>
using Result = outcome_e::status_result<T>;

MONAD_NAMESPACE_END
