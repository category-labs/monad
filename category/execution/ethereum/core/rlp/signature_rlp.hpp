#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/signature.hpp>

MONAD_RLP_NAMESPACE_BEGIN

Result<SignatureAndChain> decode_sc(byte_string_view &);

MONAD_RLP_NAMESPACE_END
