#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/signature.hpp>
#include <monad/rlp/config.hpp>

#include <optional>

MONAD_RLP_NAMESPACE_BEGIN

byte_string_view decode_sc(SignatureAndChain &, byte_string_view);

MONAD_RLP_NAMESPACE_END
