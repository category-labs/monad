#include <monad/core/transaction.hpp>

#include <monad/rlp/encode_helpers.hpp>

#include <ethash/keccak.hpp>

#include <silkpre/ecdsa.h>

#include <memory>

MONAD_NAMESPACE_BEGIN

std::optional<address_t> recover_sender(Transaction const &t)
{
    if (t.from.has_value()) {
        return t.from;
    }

    byte_string const txn_encoding = rlp::encode_transaction_for_signing(t);
    ethash::hash256 const txn_encoding_hash{
        ethash::keccak256(txn_encoding.data(), txn_encoding.size())};

    uint8_t signature[sizeof(t.sc.r) * 2];
    intx::be::unsafe::store(signature, t.sc.r);
    intx::be::unsafe::store(signature + sizeof(t.sc.r), t.sc.s);

    std::optional<address_t> res = evmc::address{};
    std::unique_ptr<secp256k1_context, decltype(&secp256k1_context_destroy)>
        context(
            secp256k1_context_create(SILKPRE_SECP256K1_CONTEXT_FLAGS),
            &secp256k1_context_destroy);
    if (!silkpre_recover_address(
            res->bytes,
            txn_encoding_hash.bytes,
            signature,
            t.sc.odd_y_parity,
            context.get())) {
        return std::nullopt;
    }

    return res;
}

MONAD_NAMESPACE_END