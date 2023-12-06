#include <monad/core/byte_string.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/result.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/signature_rlp.hpp>
#include <monad/rlp/config.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>

MONAD_RLP_NAMESPACE_BEGIN

Result<byte_string_view>
decode_sc(SignatureAndChain &sc, byte_string_view const enc)
{
    uint64_t v{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, decode_unsigned<uint64_t>(v, enc));

    sc.from_v(v);
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
