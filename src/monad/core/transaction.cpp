#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/transaction_rlp.hpp>

#include <silkpre/ecdsa.h>

#include <evmc/evmc.hpp>

#include <ethash/hash_types.hpp>
#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <secp256k1.h>

#include <cstdint>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Address> recover_sender(Transaction const &txn)
{
    if (txn.from.has_value()) {
        return txn.from;
    }

    byte_string const txn_encoding = rlp::encode_transaction_for_signing(txn);
    ethash::hash256 const txn_encoding_hash{
        ethash::keccak256(txn_encoding.data(), txn_encoding.size())};

    uint8_t signature[sizeof(txn.sc.r) * 2];
    intx::be::unsafe::store(signature, txn.sc.r);
    intx::be::unsafe::store(signature + sizeof(txn.sc.r), txn.sc.s);

    std::optional<Address> res = evmc::address{};
    static std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        context(
            secp256k1_context_create(SILKPRE_SECP256K1_CONTEXT_FLAGS),
            &secp256k1_context_destroy);
    if (!silkpre_recover_address(
            res->bytes,
            txn_encoding_hash.bytes,
            signature,
            txn.sc.odd_y_parity,
            context.get())) {
        return std::nullopt;
    }

    return res;
}

MONAD_NAMESPACE_END
