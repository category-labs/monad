#pragma once

#include <boost/describe/enum.hpp>

#define MONAD_DEFINE_NESTED_ENUM_CLASS(E, ...) enum class E { __VA_ARGS__ }; BOOST_DESCRIBE_NESTED_ENUM(E, ##__VA_ARGS__)
