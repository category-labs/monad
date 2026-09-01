// Copyright (C) 2026 Category Labs, Inc.

#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/dkg/dkg_contract.hpp>
#include <category/execution/monad/dkg/dkg_error.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace dkg
{

    namespace
    {

        constexpr uint32_t REGISTER_SELECTOR =
            abi_encode_selector("register(uint64,(address,(uint8,bytes32),"
                                "uint32,bytes32,bytes32))");
        constexpr uint32_t POST_PC_QC_SELECTOR = abi_encode_selector(
            "postPcQc(uint64,(uint32,bytes32,(uint32,bytes32,bytes32)[]))");
        constexpr uint32_t POST_BVE_QC_SELECTOR =
            abi_encode_selector("postBveQc(uint64,(uint32,bytes32,bytes32,("
                                "uint32,bytes32,bytes32)[]))");
        constexpr uint32_t SUBMIT_RESULT_SELECTOR =
            abi_encode_selector("submitResult(uint64,(bytes32,bytes32[18],("
                                "uint32,bytes32,bytes32)[]))");
        constexpr uint32_t REGISTRATION_OF_SELECTOR =
            abi_encode_selector("registrationOf(uint64,uint64)");
        constexpr uint32_t PC_QCS_SELECTOR =
            abi_encode_selector("pcQcs(uint64,uint64,uint32)");
        constexpr uint32_t BVE_QCS_SELECTOR =
            abi_encode_selector("bveQcs(uint64,uint64,uint32)");
        constexpr uint32_t DKG_RESULT_SELECTOR =
            abi_encode_selector("dkgResult(uint64)");

        static_assert(REGISTER_SELECTOR == 0x737ddc1d);
        static_assert(POST_PC_QC_SELECTOR == 0x95588efd);
        static_assert(POST_BVE_QC_SELECTOR == 0x38a59810);
        static_assert(SUBMIT_RESULT_SELECTOR == 0x58b2030e);
        static_assert(REGISTRATION_OF_SELECTOR == 0x40275c7a);
        static_assert(PC_QCS_SELECTOR == 0x2053219b);
        static_assert(BVE_QCS_SELECTOR == 0x510ef97c);
        static_assert(DKG_RESULT_SELECTOR == 0x8491dd57);

        constexpr uint64_t MAX_PARTIES = staking::limits::active_valset_size();
        constexpr uint32_t MAX_PAGE_RECORDS = 16;
        constexpr uint32_t MAX_PAGE_SIGNATURES = 512;

        // Native execution does not charge for State accesses automatically.
        // These costs conservatively account for the bounded scans, signature
        // work and trie writes performed below. Calldata-sized methods add a
        // per-word component in precompile_dispatch.
        constexpr uint64_t REGISTER_GAS = 600'000;
        constexpr uint64_t POST_QC_BASE_GAS = 900'000;
        constexpr uint64_t SUBMIT_RESULT_GAS = 4'000'000;
        constexpr uint64_t READ_REGISTRATION_GAS = 100'000;
        constexpr uint64_t READ_PAGE_GAS = 4'000'000;
        constexpr uint64_t READ_RESULT_GAS = 1'000'000;
        constexpr uint64_t FALLBACK_GAS = 40'000;
        constexpr uint64_t GAS_PER_INPUT_WORD = 12'000;

        enum class ValidatorSetKind : uint8_t
        {
            Consensus,
            Snapshot,
        };

#pragma pack(push, 1)

        struct GlobalState
        {
            u8_be initialized;
            u8_be active_index;
        };

        struct StateMeta
        {
            u64_be epoch;
            u64_be pc_qc_count;
            u64_be bve_qc_count;
            u8_be result_recorded;
        };

        struct Registration
        {
            Address qc_verifier;
            u8_be receiver_prefix;
            bytes32_t receiver_x;
            u32_be receiver_proof_nonce;
            bytes32_t receiver_proof_r;
            bytes32_t receiver_proof_s;
        };

        struct RegisteredParty
        {
            u64_be epoch;
            Address address;
            Registration registration;
        };

        struct QcSignature
        {
            u32_be signer;
            bytes32_t r;
            bytes32_t s;
        };

        struct PcQcRecord
        {
            u32_be dealer;
            bytes32_t digest;
            u32_be signature_count;
        };

        struct BveQcRecord
        {
            u32_be dealer;
            bytes32_t digest;
            bytes32_t commitment_digest;
            u32_be signature_count;
        };

        struct ResultRecord
        {
            u64_be recorded_block;
            bytes32_t session_id;
            bytes32_t bte_key[18];
            u32_be signature_count;
        };

#pragma pack(pop)

        static_assert(std::has_unique_object_representations_v<GlobalState>);
        static_assert(std::has_unique_object_representations_v<StateMeta>);
        static_assert(std::has_unique_object_representations_v<Registration>);
        static_assert(
            std::has_unique_object_representations_v<RegisteredParty>);
        static_assert(std::has_unique_object_representations_v<QcSignature>);
        static_assert(std::has_unique_object_representations_v<PcQcRecord>);
        static_assert(std::has_unique_object_representations_v<BveQcRecord>);
        static_assert(std::has_unique_object_representations_v<ResultRecord>);

        struct PcQc
        {
            uint32_t dealer;
            bytes32_t digest;
            std::vector<QcSignature> signatures;
        };

        struct BveQc
        {
            uint32_t dealer;
            bytes32_t digest;
            bytes32_t commitment_digest;
            std::vector<QcSignature> signatures;
        };

        struct DkgResult
        {
            bytes32_t session_id;
            std::array<bytes32_t, 18> bte_key;
            std::vector<QcSignature> signatures;
        };

        struct Party
        {
            Address address;
            uint64_t validator_id;
            uint256_t voting_weight;
        };

        struct AbiItem
        {
            bool dynamic;
            byte_string data;
        };

        void
        append(byte_string &target, void const *const data, size_t const size)
        {
            auto const *const begin = static_cast<uint8_t const *>(data);
            target.insert(target.end(), begin, begin + size);
        }

        void append_word(byte_string &target, bytes32_t const &word)
        {
            append(target, word.bytes, sizeof(word.bytes));
        }

        template <BigEndianType T>
        byte_string static_uint(T const &value)
        {
            return byte_string{abi_encode_uint(value)};
        }

        byte_string static_bool(bool const value)
        {
            return byte_string{abi_encode_bool(value)};
        }

        byte_string static_address(Address const &value)
        {
            return byte_string{abi_encode_address(value)};
        }

        byte_string static_bytes32(bytes32_t const &value)
        {
            return byte_string{value};
        }

        AbiItem static_item(byte_string data)
        {
            return AbiItem{false, std::move(data)};
        }

        AbiItem dynamic_item(byte_string data)
        {
            return AbiItem{true, std::move(data)};
        }

        byte_string encode_tuple(std::vector<AbiItem> const &items)
        {
            size_t head_size = 0;
            for (auto const &item : items) {
                head_size +=
                    item.dynamic ? sizeof(bytes32_t) : item.data.size();
            }

            byte_string head;
            byte_string tail;
            head.reserve(head_size);
            for (auto const &item : items) {
                if (item.dynamic) {
                    append_word(
                        head,
                        abi_encode_uint(u64_be{
                            static_cast<uint64_t>(head_size + tail.size())}));
                    tail += item.data;
                }
                else {
                    head += item.data;
                }
            }
            return std::move(head) + std::move(tail);
        }

        byte_string
        encode_signatures(std::vector<QcSignature> const &signatures)
        {
            byte_string result;
            append_word(
                result,
                abi_encode_uint(
                    u64_be{static_cast<uint64_t>(signatures.size())}));
            for (auto const &signature : signatures) {
                append_word(result, abi_encode_uint(signature.signer));
                append_word(result, signature.r);
                append_word(result, signature.s);
            }
            return result;
        }

        byte_string encode_pc_qc(
            PcQcRecord const &record,
            std::vector<QcSignature> const &signatures)
        {
            return encode_tuple({
                static_item(static_uint(record.dealer)),
                static_item(static_bytes32(record.digest)),
                dynamic_item(encode_signatures(signatures)),
            });
        }

        byte_string encode_bve_qc(
            BveQcRecord const &record,
            std::vector<QcSignature> const &signatures)
        {
            return encode_tuple({
                static_item(static_uint(record.dealer)),
                static_item(static_bytes32(record.digest)),
                static_item(static_bytes32(record.commitment_digest)),
                dynamic_item(encode_signatures(signatures)),
            });
        }

        byte_string
        encode_dynamic_array(std::vector<byte_string> const &elements)
        {
            byte_string result;
            append_word(
                result,
                abi_encode_uint(
                    u64_be{static_cast<uint64_t>(elements.size())}));
            std::vector<AbiItem> items;
            items.reserve(elements.size());
            for (auto const &element : elements) {
                items.push_back(dynamic_item(element));
            }
            result += encode_tuple(items);
            return result;
        }

        bool all_zero(uint8_t const *const begin, uint8_t const *const end)
        {
            return std::all_of(
                begin, end, [](uint8_t const value) { return value == 0; });
        }

        bool word_at(
            byte_string_view const input, size_t const offset, bytes32_t &word)
        {
            if (offset > input.size() || input.size() - offset < sizeof(word)) {
                return false;
            }
            std::memcpy(word.bytes, input.data() + offset, sizeof(word));
            return true;
        }

        template <typename T>
            requires(std::unsigned_integral<T>)
        bool
        uint_at(byte_string_view const input, size_t const offset, T &value)
        {
            bytes32_t word;
            if (!word_at(input, offset, word) ||
                !all_zero(word.bytes, word.bytes + sizeof(word) - sizeof(T))) {
                return false;
            }
            value = load_be_unsafe<T>(word.bytes + sizeof(word) - sizeof(T));
            return true;
        }

        bool address_at(
            byte_string_view const input, size_t const offset, Address &value)
        {
            bytes32_t word;
            if (!word_at(input, offset, word) ||
                !all_zero(word.bytes, word.bytes + 12)) {
                return false;
            }
            std::memcpy(value.bytes, word.bytes + 12, sizeof(value.bytes));
            return true;
        }

        bool offset_at(
            byte_string_view const input, size_t const offset, size_t &value)
        {
            uint64_t decoded;
            if (!uint_at(input, offset, decoded) || decoded % 32 != 0 ||
                decoded > input.size()) {
                return false;
            }
            value = static_cast<size_t>(decoded);
            return true;
        }

        bool signatures_at(
            byte_string_view const input, size_t const offset,
            std::vector<QcSignature> &signatures)
        {
            uint64_t count;
            if (!uint_at(input, offset, count) || count == 0 ||
                count > MAX_PARTIES) {
                return false;
            }
            constexpr size_t words_per_signature = 3;
            if (count > (std::numeric_limits<size_t>::max() - 32) /
                            (words_per_signature * 32)) {
                return false;
            }
            size_t const end =
                offset + 32 +
                static_cast<size_t>(count) * words_per_signature * 32;
            // Signatures are the final ABI field. Requiring exact consumption
            // keeps the native decoder canonical and prevents ignored calldata
            // suffixes from creating a second encoding of the same call.
            if (end != input.size()) {
                return false;
            }

            signatures.clear();
            signatures.reserve(static_cast<size_t>(count));
            size_t cursor = offset + 32;
            for (uint64_t i = 0; i < count; ++i) {
                uint32_t signer;
                QcSignature signature{};
                if (!uint_at(input, cursor, signer) ||
                    !word_at(input, cursor + 32, signature.r) ||
                    !word_at(input, cursor + 64, signature.s)) {
                    return false;
                }
                signature.signer = signer;
                signatures.push_back(signature);
                cursor += words_per_signature * 32;
            }
            return true;
        }

        bool decode_registration(
            byte_string_view const input, uint64_t &epoch,
            Registration &registration)
        {
            uint8_t prefix;
            uint32_t nonce;
            return input.size() == 7 * 32 && uint_at(input, 0, epoch) &&
                   address_at(input, 32, registration.qc_verifier) &&
                   uint_at(input, 64, prefix) &&
                   word_at(input, 96, registration.receiver_x) &&
                   uint_at(input, 128, nonce) &&
                   word_at(input, 160, registration.receiver_proof_r) &&
                   word_at(input, 192, registration.receiver_proof_s) &&
                   ((registration.receiver_prefix = prefix), true) &&
                   ((registration.receiver_proof_nonce = nonce), true);
        }

        bool
        decode_pc_qc(byte_string_view const input, uint64_t &epoch, PcQc &qc)
        {
            size_t tuple_offset;
            size_t signature_offset;
            uint32_t dealer;
            if (!uint_at(input, 0, epoch) ||
                !offset_at(input, 32, tuple_offset) || tuple_offset != 2 * 32 ||
                input.size() - tuple_offset < 3 * 32 ||
                !uint_at(input, tuple_offset, dealer) ||
                !word_at(input, tuple_offset + 32, qc.digest) ||
                !offset_at(input, tuple_offset + 64, signature_offset) ||
                signature_offset != 3 * 32) {
                return false;
            }
            qc.dealer = dealer;
            return signatures_at(
                input, tuple_offset + signature_offset, qc.signatures);
        }

        bool
        decode_bve_qc(byte_string_view const input, uint64_t &epoch, BveQc &qc)
        {
            size_t tuple_offset;
            size_t signature_offset;
            uint32_t dealer;
            if (!uint_at(input, 0, epoch) ||
                !offset_at(input, 32, tuple_offset) || tuple_offset != 2 * 32 ||
                input.size() - tuple_offset < 4 * 32 ||
                !uint_at(input, tuple_offset, dealer) ||
                !word_at(input, tuple_offset + 32, qc.digest) ||
                !word_at(input, tuple_offset + 64, qc.commitment_digest) ||
                !offset_at(input, tuple_offset + 96, signature_offset) ||
                signature_offset != 4 * 32) {
                return false;
            }
            qc.dealer = dealer;
            return signatures_at(
                input, tuple_offset + signature_offset, qc.signatures);
        }

        bool decode_result(
            byte_string_view const input, uint64_t &epoch, DkgResult &result)
        {
            size_t tuple_offset;
            size_t signature_offset;
            if (!uint_at(input, 0, epoch) ||
                !offset_at(input, 32, tuple_offset) || tuple_offset != 2 * 32 ||
                input.size() - tuple_offset < 20 * 32 ||
                !word_at(input, tuple_offset, result.session_id)) {
                return false;
            }
            for (size_t i = 0; i < result.bte_key.size(); ++i) {
                if (!word_at(
                        input,
                        tuple_offset + (i + 1) * 32,
                        result.bte_key[i])) {
                    return false;
                }
            }
            if (!offset_at(input, tuple_offset + 19 * 32, signature_offset) ||
                signature_offset != 20 * 32) {
                return false;
            }
            return signatures_at(
                input, tuple_offset + signature_offset, result.signatures);
        }

        bool signatures_are_canonical(
            std::vector<QcSignature> const &signatures,
            size_t const party_count)
        {
            if (signatures.empty() || signatures.size() > party_count) {
                return false;
            }
            uint32_t previous = 0;
            for (size_t i = 0; i < signatures.size(); ++i) {
                uint32_t const signer = signatures[i].signer.native();
                if (signer >= party_count || (i != 0 && signer <= previous)) {
                    return false;
                }
                previous = signer;
            }
            return true;
        }

        bytes32_t storage_key(
            uint8_t const domain, uint8_t const state_index = 0,
            byte_string_view const suffix = {})
        {
            // Follow staking's storage convention: every logical mapping owns
            // one explicit namespace byte. The second byte selects one of the
            // two reusable epoch slots and the remaining bytes contain the
            // packed, big-endian mapping key.
            MONAD_ASSERT(domain != 0);
            MONAD_ASSERT(state_index < 2);
            MONAD_ASSERT(suffix.size() <= 30);
            bytes32_t key{};
            key.bytes[0] = domain;
            key.bytes[1] = state_index;
            if (!suffix.empty()) {
                std::memcpy(key.bytes + 2, suffix.data(), suffix.size());
            }
            return key;
        }

        byte_string suffix_u64(uint64_t const value)
        {
            u64_be const encoded{value};
            byte_string result;
            append(result, encoded.bytes, sizeof(encoded.bytes));
            return result;
        }

        byte_string suffix_u32(uint32_t const value)
        {
            u32_be const encoded{value};
            byte_string result;
            append(result, encoded.bytes, sizeof(encoded.bytes));
            return result;
        }

        byte_string suffix_index(uint64_t const index, uint32_t const subindex)
        {
            byte_string result = suffix_u64(index);
            u32_be const encoded{subindex};
            append(result, encoded.bytes, sizeof(encoded.bytes));
            return result;
        }

        // A typed view over one of the two reusable epoch slots. Logically each
        // slot has the same five mappings as Solidity: registered parties, two
        // QC collections, and two submission-marker collections. Dynamic QC
        // signatures require separate trie domains in the native encoding. The
        // captured slot index prevents mixing metadata and records across
        // slots.
        class DkgState
        {
            State *state_;
            uint8_t index_;

            template <typename T>
            T load(uint8_t const domain, byte_string_view suffix = {}) const
            {
                return StorageVariable<T>{
                    *state_, DKG_CA, storage_key(domain, index_, suffix)}
                    .load();
            }

            template <typename T>
            void store(
                uint8_t const domain, byte_string_view suffix,
                T const &value) const
            {
                StorageVariable<T>{
                    *state_, DKG_CA, storage_key(domain, index_, suffix)}
                    .store(value);
            }

        public:
            DkgState(State &state, uint8_t const index)
                : state_{&state}
                , index_{index}
            {
                MONAD_ASSERT(index_ < 2);
            }

            StateMeta meta() const
            {
                return load<StateMeta>(2);
            }

            void meta(StateMeta const &value) const
            {
                store(2, {}, value);
            }

            RegisteredParty registered_party(uint64_t validator_id) const
            {
                auto suffix = suffix_u64(validator_id);
                return load<RegisteredParty>(4, suffix);
            }

            void registered_party(
                uint64_t validator_id, RegisteredParty const &value) const
            {
                auto suffix = suffix_u64(validator_id);
                store(4, suffix, value);
            }

            uint64_t pc_dedup(uint32_t const dealer) const
            {
                auto suffix = suffix_u32(dealer);
                return load<u64_be>(5, suffix).native();
            }

            void pc_dedup(
                uint32_t const dealer, uint64_t const epoch) const
            {
                auto suffix = suffix_u32(dealer);
                store(5, suffix, u64_be{epoch});
            }

            uint64_t bve_dedup(uint32_t const dealer) const
            {
                auto suffix = suffix_u32(dealer);
                return load<u64_be>(6, suffix).native();
            }

            void bve_dedup(
                uint32_t const dealer, uint64_t const epoch) const
            {
                auto suffix = suffix_u32(dealer);
                store(6, suffix, u64_be{epoch});
            }

            PcQcRecord pc(uint64_t const record_index) const
            {
                auto suffix = suffix_u64(record_index);
                return load<PcQcRecord>(7, suffix);
            }

            void pc(uint64_t const record_index, PcQcRecord const &value) const
            {
                auto suffix = suffix_u64(record_index);
                store(7, suffix, value);
            }

            QcSignature pc_signature(
                uint64_t const record_index,
                uint32_t const signature_index) const
            {
                auto suffix = suffix_index(record_index, signature_index);
                return load<QcSignature>(8, suffix);
            }

            void pc_signature(
                uint64_t const record_index, uint32_t const signature_index,
                QcSignature const &value) const
            {
                auto suffix = suffix_index(record_index, signature_index);
                store(8, suffix, value);
            }

            BveQcRecord bve(uint64_t const record_index) const
            {
                auto suffix = suffix_u64(record_index);
                return load<BveQcRecord>(9, suffix);
            }

            void
            bve(uint64_t const record_index, BveQcRecord const &value) const
            {
                auto suffix = suffix_u64(record_index);
                store(9, suffix, value);
            }

            QcSignature bve_signature(
                uint64_t const record_index,
                uint32_t const signature_index) const
            {
                auto suffix = suffix_index(record_index, signature_index);
                return load<QcSignature>(10, suffix);
            }

            void bve_signature(
                uint64_t const record_index, uint32_t const signature_index,
                QcSignature const &value) const
            {
                auto suffix = suffix_index(record_index, signature_index);
                store(10, suffix, value);
            }

            ResultRecord result() const
            {
                return load<ResultRecord>(11);
            }

            void result(ResultRecord const &value) const
            {
                store(11, {}, value);
            }

            QcSignature result_signature(uint32_t const signature_index) const
            {
                auto suffix = suffix_index(0, signature_index);
                return load<QcSignature>(12, suffix);
            }

            void result_signature(
                uint32_t const signature_index, QcSignature const &value) const
            {
                auto suffix = suffix_index(0, signature_index);
                store(12, suffix, value);
            }
        };

        class Store
        {
            State &state_;

        public:
            explicit Store(State &state)
                : state_{state}
            {
                // Native methods access both storage owners directly rather
                // than through EvmcHost. Populate State's original-account
                // cache before StorageVariable performs its first read.
                MONAD_ASSERT(state_.account_exists(DKG_CA));
                MONAD_ASSERT(state_.account_exists(staking::STAKING_CA));
            }

            GlobalState global() const
            {
                return StorageVariable<GlobalState>{
                    state_, DKG_CA, storage_key(1)}
                    .load();
            }

            void global(GlobalState const &value)
            {
                StorageVariable<GlobalState>{state_, DKG_CA, storage_key(1)}
                    .store(value);
            }

            DkgState dkg_state(uint8_t const index) const
            {
                return DkgState{state_, index};
            }
        };

        Result<void> reset_state(DkgState state, uint64_t const epoch)
        {
            StateMeta next{};
            next.epoch = epoch;
            state.meta(next);
            return outcome::success();
        }

        // This mutates lifecycle metadata and is called only by execution
        // prelude or authenticated staking system calls. User transactions use
        // synchronized_states() below and fail closed on any mismatch.
        Result<void>
        transition_states(Store &store, uint64_t const current_epoch)
        {
            if (current_epoch == std::numeric_limits<uint64_t>::max()) {
                return DkgError::StakingLookupFailed;
            }
            uint64_t const following_epoch = current_epoch + 1;

            GlobalState global = store.global();
            if (global.initialized.native() == 0) {
                global.initialized = 1;
                global.active_index = 0;
                BOOST_OUTCOME_TRY(
                    reset_state(store.dkg_state(0), current_epoch));
                BOOST_OUTCOME_TRY(
                    reset_state(store.dkg_state(1), following_epoch));
                store.global(global);
                return outcome::success();
            }

            uint8_t const active_index = global.active_index.native();
            if (active_index > 1) {
                return DkgError::StakingLookupFailed;
            }
            uint8_t const next_index = active_index ^ 1;
            DkgState const active_state = store.dkg_state(active_index);
            DkgState const next_state = store.dkg_state(next_index);
            StateMeta const active = active_state.meta();
            StateMeta const next = next_state.meta();
            if (current_epoch == active.epoch.native()) {
                if (next.epoch.native() != following_epoch) {
                    BOOST_OUTCOME_TRY(reset_state(next_state, following_epoch));
                }
                return outcome::success();
            }
            if (current_epoch == next.epoch.native()) {
                global.active_index = next_index;
                store.global(global);
                BOOST_OUTCOME_TRY(reset_state(active_state, following_epoch));
                return outcome::success();
            }
            if (current_epoch > next.epoch.native()) {
                global.active_index = 0;
                store.global(global);
                BOOST_OUTCOME_TRY(
                    reset_state(store.dkg_state(0), current_epoch));
                BOOST_OUTCOME_TRY(
                    reset_state(store.dkg_state(1), following_epoch));
                return outcome::success();
            }
            return DkgError::StakingLookupFailed;
        }

        Result<std::pair<uint64_t, bool>>
        synchronized_states(Store &store, State &state)
        {
            staking::StakingContract::Variables staking_vars{state};
            uint64_t const current_epoch = staking_vars.epoch.load().native();
            bool const in_delay = staking_vars.in_epoch_delay_period.load();
            if (current_epoch == std::numeric_limits<uint64_t>::max()) {
                return DkgError::StakingLookupFailed;
            }

            GlobalState const global = store.global();
            uint8_t const active_index = global.active_index.native();
            if (global.initialized.native() == 0 || active_index > 1) {
                return DkgError::EpochStateUnavailable;
            }
            DkgState const active = store.dkg_state(active_index);
            DkgState const next =
                store.dkg_state(static_cast<uint8_t>(active_index ^ 1));
            if (active.meta().epoch.native() != current_epoch ||
                next.meta().epoch.native() != current_epoch + 1) {
                return DkgError::EpochStateUnavailable;
            }
            return std::pair{current_epoch, in_delay};
        }

        std::optional<DkgState>
        retained_state(Store &store, uint64_t const epoch)
        {
            GlobalState const global = store.global();
            if (global.initialized.native() == 0) {
                return std::nullopt;
            }
            DkgState const first = store.dkg_state(0);
            if (first.meta().epoch.native() == epoch) {
                return first;
            }
            DkgState const second = store.dkg_state(1);
            if (second.meta().epoch.native() == epoch) {
                return second;
            }
            return std::nullopt;
        }

        struct ProtocolState
        {
            DkgState state;
            ValidatorSetKind kind;
        };

        Result<ProtocolState>
        protocol_state(Store &store, State &state, uint64_t const epoch)
        {
            BOOST_OUTCOME_TRY(
                auto const synchronized, synchronized_states(store, state));
            auto const [current_epoch, in_delay] = synchronized;
            uint8_t const active_index = store.global().active_index.native();
            if (epoch == current_epoch) {
                return ProtocolState{
                    store.dkg_state(active_index),
                    in_delay ? ValidatorSetKind::Snapshot
                             : ValidatorSetKind::Consensus};
            }
            if (in_delay && epoch == current_epoch + 1) {
                return ProtocolState{
                    store.dkg_state(static_cast<uint8_t>(active_index ^ 1)),
                    ValidatorSetKind::Consensus};
            }
            return DkgError::PartySetUnavailable;
        }

        Result<std::vector<Party>> party_set(
            DkgState const &dkg_state, State &state,
            ValidatorSetKind const kind)
        {
            StateMeta const meta = dkg_state.meta();
            uint64_t const epoch = meta.epoch.native();
            staking::StakingContract::Variables staking_vars{state};
            auto const valset = kind == ValidatorSetKind::Consensus
                                    ? staking_vars.valset_consensus
                                    : staking_vars.valset_snapshot;
            // MAX_PARTIES is derived directly from native staking's active-set
            // limit. Solidity relies on the same staking invariant because the
            // current staking ABI does not expose the bound.
            uint64_t const count = valset.length();
            if (count == 0 || count > MAX_PARTIES) {
                return DkgError::PartySetUnavailable;
            }

            std::vector<Party> parties;
            parties.reserve(static_cast<size_t>(count));
            for (uint64_t i = 0; i < count; ++i) {
                uint64_t const validator_id = valset.get(i).load().native();
                if (validator_id == 0) {
                    return DkgError::StakingLookupFailed;
                }
                RegisteredParty const registered =
                    dkg_state.registered_party(validator_id);
                if (registered.epoch.native() != epoch) {
                    continue;
                }
                uint256_t const stake =
                    (kind == ValidatorSetKind::Consensus
                         ? staking_vars.consensus_view(u64_be{validator_id})
                               .stake()
                               .load()
                         : staking_vars.snapshot_view(u64_be{validator_id})
                               .stake()
                               .load())
                        .native();
                if (stake == 0) {
                    return DkgError::StakingLookupFailed;
                }
                // Verify Done-QC quorum in the exact staking-weight domain.
                // The Rust runner reduces the same vector by its GCD only to
                // fit the engine's u64 API; that preserves all ratios exactly.
                parties.push_back(
                    Party{registered.address, validator_id, stake});
            }
            if (parties.empty()) {
                return DkgError::PartySetUnavailable;
            }
            return parties;
        }

        std::optional<uint32_t>
        party_id(std::vector<Party> const &parties, Address const &sender)
        {
            for (size_t i = 0; i < parties.size(); ++i) {
                if (parties[i].address == sender) {
                    MONAD_ASSERT(i <= std::numeric_limits<uint32_t>::max());
                    return static_cast<uint32_t>(i);
                }
            }
            return std::nullopt;
        }

        std::vector<QcSignature> load_pc_signatures(
            DkgState const &state, uint64_t const record_index,
            uint32_t const count)
        {
            std::vector<QcSignature> result;
            result.reserve(count);
            for (uint32_t i = 0; i < count; ++i) {
                result.push_back(state.pc_signature(record_index, i));
            }
            return result;
        }

        std::vector<QcSignature> load_bve_signatures(
            DkgState const &state, uint64_t const record_index,
            uint32_t const count)
        {
            std::vector<QcSignature> result;
            result.reserve(count);
            for (uint32_t i = 0; i < count; ++i) {
                result.push_back(state.bve_signature(record_index, i));
            }
            return result;
        }

        std::vector<QcSignature>
        load_result_signatures(DkgState const &state, uint32_t const count)
        {
            std::vector<QcSignature> result;
            result.reserve(count);
            for (uint32_t i = 0; i < count; ++i) {
                result.push_back(state.result_signature(i));
            }
            return result;
        }

        void append_big_u64(byte_string &target, uint64_t const value)
        {
            for (size_t i = sizeof(value); i > 0; --i) {
                target.push_back(static_cast<uint8_t>(value >> ((i - 1) * 8)));
            }
        }

        bytes32_t done_digest(uint64_t const epoch, DkgResult const &result)
        {
            static constexpr std::string_view statement_domain =
                "BTX-DKG/protocol/qc-signature/v1";
            static constexpr std::string_view done_domain =
                "BTX-DKG/protocol/dkg-done-qc/v1";
            byte_string transcript;
            append(
                transcript, statement_domain.data(), statement_domain.size());
            append_big_u64(transcript, done_domain.size());
            append(transcript, done_domain.data(), done_domain.size());
            append_big_u64(transcript, epoch);
            append_big_u64(transcript, sizeof(bytes32_t));
            append(
                transcript,
                result.session_id.bytes,
                sizeof(result.session_id.bytes));
            for (auto const &word : result.bte_key) {
                append(transcript, word.bytes, sizeof(word.bytes));
            }
            bytes32_t digest;
            auto const sha = sha256_execute(transcript);
            MONAD_ASSERT(sha.status_code == EVMC_SUCCESS);
            MONAD_ASSERT(sha.output_size == sizeof(digest));
            std::memcpy(digest.bytes, sha.obuf, sizeof(digest));
            std::free(sha.obuf);
            return digest;
        }

        bool signature_matches(
            Address const &expected, bytes32_t const &digest,
            QcSignature const &signature)
        {
            if (!expected) {
                return false;
            }
            uint256_t const r = load_be<uint256_t>(signature.r);
            uint256_t const s = load_be<uint256_t>(signature.s);
            Secp256k1Signature const checked{r, s};
            if (!checked.is_valid()) {
                return false;
            }
            // TODO(dkg): preserve the recovery ID produced during Rust signing
            // (for example, compactly in `s` per EIP-2098) so this needs only
            // one recovery instead of trying both Ethereum recovery values.
            for (uint8_t const parity : {uint8_t{0}, uint8_t{1}}) {
                auto const recovered = recover_address_from_digest(
                    Secp256k1Signature{r, s, parity}, digest);
                if (recovered && *recovered == expected) {
                    return true;
                }
            }
            return false;
        }

        Result<void> verify_result(
            DkgState const &state, uint64_t const epoch,
            DkgResult const &result, std::vector<Party> const &parties)
        {
            if (!signatures_are_canonical(result.signatures, parties.size())) {
                return DkgError::InvalidDkgResult;
            }
            bytes32_t const digest = done_digest(epoch, result);
            // Quorum is deliberately over registered target-epoch parties;
            // unregistered staking weight is absent from this filtered vector.
            uint256_t total_weight = 0;
            for (auto const &party : parties) {
                total_weight += party.voting_weight;
            }
            uint256_t const quorum = total_weight - (total_weight - 1) / 3;
            uint256_t signed_weight = 0;
            uint64_t const state_epoch = state.meta().epoch.native();
            for (auto const &signature : result.signatures) {
                size_t const signer = signature.signer.native();
                RegisteredParty const registration =
                    state.registered_party(parties[signer].validator_id);
                if (registration.epoch.native() != state_epoch ||
                    registration.address != parties[signer].address ||
                    !signature_matches(
                        registration.registration.qc_verifier,
                        digest,
                        signature)) {
                    return DkgError::InvalidDkgResult;
                }
                signed_weight += parties[signer].voting_weight;
            }
            if (signed_weight < quorum) {
                return DkgError::InvalidDkgResult;
            }
            return outcome::success();
        }

        void
        emit_log(State &state, CallTracerBase &call_tracer, Receipt::Log &&log)
        {
            call_tracer.on_log(log);
            state.store_log(std::move(log));
        }

        Receipt::Log pc_event(
            uint64_t const epoch, uint64_t const index,
            PcQcRecord const &record,
            std::vector<QcSignature> const &signatures)
        {
            constexpr bytes32_t signature = abi_encode_event_signature(
                "PcQcPosted(uint64,uint64,uint32,bytes32,(uint32,bytes32,"
                "bytes32)[])");
            static_assert(
                signature ==
                0xa27c3d889c25a8dcf17eee1d986b8374bc2f1cd2aa270f3e59179cb5b432cba2_bytes32);
            byte_string const data = encode_tuple({
                static_item(static_bytes32(record.digest)),
                dynamic_item(encode_signatures(signatures)),
            });
            return EventBuilder(DKG_CA, signature)
                .add_topic(abi_encode_uint(u64_be{epoch}))
                .add_topic(abi_encode_uint(u64_be{index}))
                .add_topic(abi_encode_uint(record.dealer))
                .add_data(data)
                .build();
        }

        Receipt::Log bve_event(
            uint64_t const epoch, uint64_t const index,
            BveQcRecord const &record,
            std::vector<QcSignature> const &signatures)
        {
            constexpr bytes32_t signature = abi_encode_event_signature(
                "BveQcPosted(uint64,uint64,uint32,bytes32,bytes32,(uint32,"
                "bytes32,bytes32)[])");
            static_assert(
                signature ==
                0xeaa5480ca8f33abc55c5d3bfb939da02ab15b57f517c4130bcd112a66e345ed8_bytes32);
            byte_string const data = encode_tuple({
                static_item(static_bytes32(record.digest)),
                static_item(static_bytes32(record.commitment_digest)),
                dynamic_item(encode_signatures(signatures)),
            });
            return EventBuilder(DKG_CA, signature)
                .add_topic(abi_encode_uint(u64_be{epoch}))
                .add_topic(abi_encode_uint(u64_be{index}))
                .add_topic(abi_encode_uint(record.dealer))
                .add_data(data)
                .build();
        }

        Receipt::Log result_event(
            uint64_t const epoch, ResultRecord const &record,
            std::vector<QcSignature> const &signatures)
        {
            constexpr bytes32_t signature = abi_encode_event_signature(
                "DkgResultPosted(uint64,bytes32,bytes32[18],("
                "uint32,bytes32,bytes32)[])");
            static_assert(
                signature ==
                0x54947dc9933a573707e5fbe7d2cf9cb77f9c5078020722c0d905c73662bfb85c_bytes32);
            byte_string bte;
            for (auto const &word : record.bte_key) {
                append_word(bte, word);
            }
            byte_string const data = encode_tuple({
                static_item(static_bytes32(record.session_id)),
                static_item(std::move(bte)),
                dynamic_item(encode_signatures(signatures)),
            });
            return EventBuilder(DKG_CA, signature)
                .add_topic(abi_encode_uint(u64_be{epoch}))
                .add_data(data)
                .build();
        }

        Result<void> not_payable(uint256_be_t const &value)
        {
            return load_be<uint256_t>(value) == 0
                       ? outcome::success()
                       : Result<void>{DkgError::ValueNonZero};
        }

    } // namespace

    bool initialize_states(State &state)
    {
        if (!state.account_exists(DKG_CA) ||
            !state.account_exists(staking::STAKING_CA)) {
            return false;
        }
        staking::StakingContract::Variables staking_vars{state};
        Store store{state};
        return transition_states(store, staking_vars.epoch.load().native())
            .has_value();
    }

    bool on_staking_snapshot(State &state, uint64_t const next_epoch)
    {
        // Staking can be active before the revision that introduces DKG.
        if (!state.account_exists(DKG_CA)) {
            return true;
        }
        staking::StakingContract::Variables staking_vars{state};
        Store store{state};
        if (transition_states(store, staking_vars.epoch.load().native())
                .has_error()) {
            return false;
        }
        auto const synchronized = synchronized_states(store, state);
        if (synchronized.has_error()) {
            return false;
        }
        auto const [current_epoch, in_delay] = synchronized.value();
        if (!in_delay ||
            current_epoch == std::numeric_limits<uint64_t>::max() ||
            next_epoch != current_epoch + 1) {
            return false;
        }
        return retained_state(store, next_epoch).has_value();
    }

    bool on_staking_epoch_change(State &state, uint64_t const current_epoch)
    {
        if (!state.account_exists(DKG_CA)) {
            return true;
        }
        Store store{state};
        if (transition_states(store, current_epoch).has_error()) {
            return false;
        }
        auto const synchronized = synchronized_states(store, state);
        return synchronized.has_value() &&
               synchronized.value().first == current_epoch;
    }

    DkgContract::DkgContract(
        State &state, CallTracerBase &call_tracer,
        uint64_t const block_number)
        : state_{state}
        , call_tracer_{call_tracer}
        , block_number_{block_number}
    {
    }

    template <Traits traits>
    DkgContract::Dispatch
    DkgContract::precompile_dispatch(byte_string_view &input)
    {
        if (input.size() < 4) {
            return {&DkgContract::precompile_fallback, FALLBACK_GAS, false};
        }
        uint32_t const selector = load_be_unsafe<uint32_t>(input.data());
        input.remove_prefix(4);
        uint64_t const calldata_cost =
            ((input.size() + 31) / 32) * GAS_PER_INPUT_WORD;
        switch (selector) {
        case REGISTER_SELECTOR:
            return {
                &DkgContract::precompile_register,
                REGISTER_GAS + calldata_cost,
                false};
        case POST_PC_QC_SELECTOR:
            return {
                &DkgContract::precompile_post_pc_qc,
                POST_QC_BASE_GAS + calldata_cost,
                false};
        case POST_BVE_QC_SELECTOR:
            return {
                &DkgContract::precompile_post_bve_qc,
                POST_QC_BASE_GAS + calldata_cost,
                false};
        case SUBMIT_RESULT_SELECTOR:
            return {
                &DkgContract::precompile_submit_result,
                SUBMIT_RESULT_GAS + calldata_cost,
                false};
        case REGISTRATION_OF_SELECTOR:
            return {
                &DkgContract::precompile_registration_of,
                READ_REGISTRATION_GAS,
                true};
        case PC_QCS_SELECTOR:
            return {&DkgContract::precompile_pc_qcs, READ_PAGE_GAS, true};
        case BVE_QCS_SELECTOR:
            return {&DkgContract::precompile_bve_qcs, READ_PAGE_GAS, true};
        case DKG_RESULT_SELECTOR:
            return {&DkgContract::precompile_dkg_result, READ_RESULT_GAS, true};
        default:
            return {&DkgContract::precompile_fallback, FALLBACK_GAS, false};
        }
    }

    EXPLICIT_MONAD_TRAITS_MEMBER(DkgContract::precompile_dispatch);

    Result<byte_string> DkgContract::precompile_register(
        byte_string_view const input, Address const &sender,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        Registration registration{};
        if (!decode_registration(input, epoch, registration)) {
            return DkgError::InvalidInput;
        }
        Store store{state_};
        BOOST_OUTCOME_TRY(
            auto const synchronized, synchronized_states(store, state_));
        auto const [current_epoch, in_delay] = synchronized;
        if (in_delay || current_epoch == std::numeric_limits<uint64_t>::max() ||
            epoch != current_epoch + 1) {
            return DkgError::RegistrationClosed;
        }
        uint8_t const index = store.global().active_index.native() ^ 1;
        DkgState const dkg_state = store.dkg_state(index);
        StateMeta const meta = dkg_state.meta();
        if (meta.epoch.native() != epoch) {
            return DkgError::EpochStateUnavailable;
        }
        staking::StakingContract::Variables staking_vars{state_};
        uint64_t const validator_id =
            staking_vars.val_id(sender).load().native();
        if (validator_id == 0) {
            return DkgError::NotValidator;
        }
        uint64_t const state_epoch = meta.epoch.native();
        if (dkg_state.registered_party(validator_id).epoch.native() ==
            state_epoch) {
            return DkgError::AlreadyRegistered;
        }
        dkg_state.registered_party(
            validator_id,
            RegisteredParty{u64_be{state_epoch}, sender, registration});
        return byte_string{};
    }

    Result<byte_string> DkgContract::precompile_post_pc_qc(
        byte_string_view const input, Address const &sender,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        PcQc qc{};
        if (!decode_pc_qc(input, epoch, qc)) {
            return DkgError::InvalidInput;
        }
        Store store{state_};
        BOOST_OUTCOME_TRY(
            auto const protocol, protocol_state(store, state_, epoch));
        StateMeta meta = protocol.state.meta();
        BOOST_OUTCOME_TRY(
            auto const parties,
            party_set(protocol.state, state_, protocol.kind));
        auto const submitter_party_id = party_id(parties, sender);
        if (!submitter_party_id.has_value()) {
            return DkgError::NotEpochParty;
        }
        if (meta.result_recorded.native() != 0) {
            return DkgError::DkgAlreadyFinished;
        }
        if (qc.dealer >= parties.size() ||
            !signatures_are_canonical(qc.signatures, parties.size())) {
            return DkgError::MalformedQc;
        }
        uint64_t const state_epoch = meta.epoch.native();
        // PC acknowledgements are delivered directly to the dealer, so only
        // the dealer can form and post its QC. This keeps PC marker and record
        // growth to maxPartyCount per physical state slot.
        if (*submitter_party_id != qc.dealer) {
            return DkgError::NotPcQcDealer;
        }
        if (protocol.state.pc_dedup(qc.dealer) == state_epoch) {
            return byte_string{};
        }
        if (meta.pc_qc_count.native() == std::numeric_limits<uint64_t>::max()) {
            return DkgError::StateLimitExceeded;
        }
        protocol.state.pc_dedup(qc.dealer, state_epoch);
        uint64_t const record_index = meta.pc_qc_count.native();
        PcQcRecord const record{
            u32_be{qc.dealer},
            qc.digest,
            u32_be{static_cast<uint32_t>(qc.signatures.size())}};
        protocol.state.pc(record_index, record);
        for (uint32_t i = 0; i < qc.signatures.size(); ++i) {
            protocol.state.pc_signature(record_index, i, qc.signatures[i]);
        }
        meta.pc_qc_count = record_index + 1;
        protocol.state.meta(meta);
        emit_log(
            state_,
            call_tracer_,
            pc_event(epoch, record_index, record, qc.signatures));
        return byte_string{};
    }

    Result<byte_string> DkgContract::precompile_post_bve_qc(
        byte_string_view const input, Address const &sender,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        BveQc qc{};
        if (!decode_bve_qc(input, epoch, qc)) {
            return DkgError::InvalidInput;
        }
        Store store{state_};
        BOOST_OUTCOME_TRY(
            auto const protocol, protocol_state(store, state_, epoch));
        StateMeta meta = protocol.state.meta();
        BOOST_OUTCOME_TRY(
            auto const parties,
            party_set(protocol.state, state_, protocol.kind));
        auto const submitter_party_id = party_id(parties, sender);
        if (!submitter_party_id.has_value()) {
            return DkgError::NotEpochParty;
        }
        if (meta.result_recorded.native() != 0) {
            return DkgError::DkgAlreadyFinished;
        }
        if (qc.dealer >= parties.size() ||
            !signatures_are_canonical(qc.signatures, parties.size())) {
            return DkgError::MalformedQc;
        }
        uint64_t const state_epoch = meta.epoch.native();
        // Only the dealer that established this protocol stream with a PC-QC
        // may post its BVE-QC. This bounds BVE markers and records to one per
        // dealer instead of PartyId x dealer.
        if (*submitter_party_id != qc.dealer) {
            return DkgError::NotBveQcDealer;
        }
        if (protocol.state.pc_dedup(qc.dealer) != state_epoch) {
            return DkgError::PcQcRequired;
        }
        if (protocol.state.bve_dedup(qc.dealer) == state_epoch) {
            return byte_string{};
        }
        if (meta.bve_qc_count.native() ==
            std::numeric_limits<uint64_t>::max()) {
            return DkgError::StateLimitExceeded;
        }
        protocol.state.bve_dedup(qc.dealer, state_epoch);
        uint64_t const record_index = meta.bve_qc_count.native();
        BveQcRecord const record{
            u32_be{qc.dealer},
            qc.digest,
            qc.commitment_digest,
            u32_be{static_cast<uint32_t>(qc.signatures.size())}};
        protocol.state.bve(record_index, record);
        for (uint32_t i = 0; i < qc.signatures.size(); ++i) {
            protocol.state.bve_signature(record_index, i, qc.signatures[i]);
        }
        meta.bve_qc_count = record_index + 1;
        protocol.state.meta(meta);
        emit_log(
            state_,
            call_tracer_,
            bve_event(epoch, record_index, record, qc.signatures));
        return byte_string{};
    }

    Result<byte_string> DkgContract::precompile_submit_result(
        byte_string_view const input, Address const &sender,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        DkgResult result{};
        if (!decode_result(input, epoch, result)) {
            return DkgError::InvalidInput;
        }
        Store store{state_};
        BOOST_OUTCOME_TRY(
            auto const protocol, protocol_state(store, state_, epoch));
        StateMeta meta = protocol.state.meta();
        BOOST_OUTCOME_TRY(
            auto const parties,
            party_set(protocol.state, state_, protocol.kind));
        if (!party_id(parties, sender).has_value()) {
            return DkgError::NotEpochParty;
        }
        if (meta.result_recorded.native() != 0) {
            return DkgError::ResultAlreadyRecorded;
        }
        BOOST_OUTCOME_TRY(
            verify_result(protocol.state, epoch, result, parties));
        ResultRecord record{};
        record.recorded_block = block_number_;
        record.session_id = result.session_id;
        std::copy(result.bte_key.begin(), result.bte_key.end(), record.bte_key);
        record.signature_count =
            static_cast<uint32_t>(result.signatures.size());
        protocol.state.result(record);
        for (uint32_t i = 0; i < result.signatures.size(); ++i) {
            protocol.state.result_signature(i, result.signatures[i]);
        }
        meta.result_recorded = 1;
        protocol.state.meta(meta);
        emit_log(
            state_,
            call_tracer_,
            result_event(epoch, record, result.signatures));
        return byte_string{};
    }

    Result<byte_string> DkgContract::precompile_registration_of(
        byte_string_view const input, Address const &,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        uint64_t validator_id;
        if (input.size() != 64 || !uint_at(input, 0, epoch) ||
            !uint_at(input, 32, validator_id)) {
            return DkgError::InvalidInput;
        }
        Store store{state_};
        bool exists = false;
        Registration registration{};
        if (auto const state = retained_state(store, epoch)) {
            RegisteredParty const record =
                state->registered_party(validator_id);
            exists = validator_id != 0 && record.epoch.native() ==
                                              state->meta().epoch.native();
            if (exists) {
                registration = record.registration;
            }
        }
        byte_string output = static_bool(exists);
        output += static_address(registration.qc_verifier);
        output += static_uint(registration.receiver_prefix);
        output += static_bytes32(registration.receiver_x);
        output += static_uint(registration.receiver_proof_nonce);
        output += static_bytes32(registration.receiver_proof_r);
        output += static_bytes32(registration.receiver_proof_s);
        return output;
    }

    Result<byte_string> DkgContract::precompile_pc_qcs(
        byte_string_view const input, Address const &,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        uint64_t start;
        uint32_t limit;
        if (input.size() != 96 || !uint_at(input, 0, epoch) ||
            !uint_at(input, 32, start) || !uint_at(input, 64, limit) ||
            limit == 0) {
            return DkgError::InvalidPage;
        }
        Store store{state_};
        auto const state = retained_state(store, epoch);
        uint64_t const total = state ? state->meta().pc_qc_count.native() : 0;
        if (start > total) {
            return DkgError::InvalidPage;
        }
        uint64_t const effective_limit =
            std::min<uint64_t>(limit, MAX_PAGE_RECORDS);
        uint64_t end = start + std::min(effective_limit, total - start);
        std::vector<byte_string> records;
        uint32_t signature_budget = 0;
        if (state) {
            for (uint64_t i = start; i < end; ++i) {
                PcQcRecord const record = state->pc(i);
                uint32_t const count = record.signature_count.native();
                if (count == 0 || count > MAX_PARTIES ||
                    (i != start &&
                     signature_budget + count > MAX_PAGE_SIGNATURES)) {
                    end = i;
                    break;
                }
                signature_budget += count;
                byte_string const qc =
                    encode_pc_qc(record, load_pc_signatures(*state, i, count));
                records.push_back(qc);
            }
        }
        byte_string const page = encode_tuple({
            static_item(static_uint(u64_be{total})),
            static_item(static_uint(u64_be{end})),
            dynamic_item(encode_dynamic_array(records)),
        });
        return encode_tuple({dynamic_item(page)});
    }

    Result<byte_string> DkgContract::precompile_bve_qcs(
        byte_string_view const input, Address const &,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        uint64_t start;
        uint32_t limit;
        if (input.size() != 96 || !uint_at(input, 0, epoch) ||
            !uint_at(input, 32, start) || !uint_at(input, 64, limit) ||
            limit == 0) {
            return DkgError::InvalidPage;
        }
        Store store{state_};
        auto const state = retained_state(store, epoch);
        uint64_t const total = state ? state->meta().bve_qc_count.native() : 0;
        if (start > total) {
            return DkgError::InvalidPage;
        }
        uint64_t const effective_limit =
            std::min<uint64_t>(limit, MAX_PAGE_RECORDS);
        uint64_t end = start + std::min(effective_limit, total - start);
        std::vector<byte_string> records;
        uint32_t signature_budget = 0;
        if (state) {
            for (uint64_t i = start; i < end; ++i) {
                BveQcRecord const record = state->bve(i);
                uint32_t const count = record.signature_count.native();
                if (count == 0 || count > MAX_PARTIES ||
                    (i != start &&
                     signature_budget + count > MAX_PAGE_SIGNATURES)) {
                    end = i;
                    break;
                }
                signature_budget += count;
                byte_string const qc = encode_bve_qc(
                    record, load_bve_signatures(*state, i, count));
                records.push_back(qc);
            }
        }
        byte_string const page = encode_tuple({
            static_item(static_uint(u64_be{total})),
            static_item(static_uint(u64_be{end})),
            dynamic_item(encode_dynamic_array(records)),
        });
        return encode_tuple({dynamic_item(page)});
    }

    Result<byte_string> DkgContract::precompile_dkg_result(
        byte_string_view const input, Address const &,
        uint256_be_t const &value)
    {
        BOOST_OUTCOME_TRY(not_payable(value));
        uint64_t epoch;
        if (input.size() != 32 || !uint_at(input, 0, epoch)) {
            return DkgError::InvalidInput;
        }
        Store store{state_};
        bool exists = false;
        ResultRecord record{};
        std::vector<QcSignature> signatures;
        if (auto const state = retained_state(store, epoch);
            state && state->meta().result_recorded.native() != 0) {
            exists = true;
            record = state->result();
            uint32_t const count = record.signature_count.native();
            if (count == 0 || count > MAX_PARTIES) {
                return DkgError::StateLimitExceeded;
            }
            signatures = load_result_signatures(*state, count);
        }
        byte_string bte;
        for (auto const &word : record.bte_key) {
            append_word(bte, word);
        }
        byte_string const result = encode_tuple({
            static_item(static_bytes32(record.session_id)),
            static_item(std::move(bte)),
            dynamic_item(encode_signatures(signatures)),
        });
        return encode_tuple({
            static_item(static_bool(exists)),
            static_item(static_uint(record.recorded_block)),
            dynamic_item(result),
        });
    }

    Result<byte_string> DkgContract::precompile_fallback(
        byte_string_view const, Address const &, uint256_be_t const &)
    {
        return DkgError::MethodNotSupported;
    }

} // namespace dkg

MONAD_NAMESPACE_END
