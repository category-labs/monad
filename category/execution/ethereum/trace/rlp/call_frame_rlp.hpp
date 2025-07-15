#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/core/rlp/config.hpp>

#include <span>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_call_frame(CallFrame const &);

byte_string encode_call_frames(std::span<CallFrame const>);

Result<CallFrame> decode_call_frame(byte_string_view &);

Result<std::vector<CallFrame>> decode_call_frames(byte_string_view &);

MONAD_RLP_NAMESPACE_END
