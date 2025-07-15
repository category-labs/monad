#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/signature_rlp.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>

MONAD_RLP_NAMESPACE_BEGIN

Result<SignatureAndChain> decode_sc(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const v, decode_unsigned<uint256_t>(enc));

    SignatureAndChain sc;
    sc.from_v(v);
    return sc;
}

MONAD_RLP_NAMESPACE_END
