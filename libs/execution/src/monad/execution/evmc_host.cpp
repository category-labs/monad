#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/event/event_recorder.h>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <sys/uio.h>

#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>

MONAD_NAMESPACE_BEGIN

static size_t init_txn_log_iovec(
    Receipt::Log const &log, monad_event_txn_log &event,
    std::span<iovec> out_iov)
{
    size_t iovlen = 0;
    event.address = log.address;
    event.topic_count = static_cast<uint8_t>(size(log.topics));
    event.data_length = static_cast<uint32_t>(size(log.data));
    out_iov[iovlen++] = {.iov_base = &event, .iov_len = sizeof event};

    for (bytes32_t const &topic : log.topics) {
        out_iov[iovlen++] =
            iovec{.iov_base = (void *)topic.bytes, .iov_len = sizeof topic};
    }
    out_iov[iovlen++] = {
        .iov_base = (void *)log.data.data(), .iov_len = event.data_length};
    return iovlen;
}

EvmcHostBase::EvmcHostBase(
    CallTracerBase &call_tracer, evmc_tx_context const &tx_context,
    BlockHashBuffer const &block_hash_buffer, State &state) noexcept
    : tx_context_{tx_context}
    , block_hash_buffer_{block_hash_buffer}
    , state_{state}
    , call_tracer_{call_tracer}
{
}

bytes32_t EvmcHostBase::get_storage(
    Address const &address, bytes32_t const &key) const noexcept
{
    return state_.get_storage(address, key);
}

evmc_storage_status EvmcHostBase::set_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    return state_.set_storage(address, key, value);
}

evmc::uint256be EvmcHostBase::get_balance(Address const &address) const noexcept
{
    return state_.get_balance(address);
}

size_t EvmcHostBase::get_code_size(Address const &address) const noexcept
{
    return state_.get_code_size(address);
}

bytes32_t EvmcHostBase::get_code_hash(Address const &address) const noexcept
{
    if (state_.account_is_dead(address)) {
        return bytes32_t{};
    }
    return state_.get_code_hash(address);
}

size_t EvmcHostBase::copy_code(
    Address const &address, size_t offset, uint8_t *data,
    size_t size) const noexcept
{
    return state_.copy_code(address, offset, data, size);
}

evmc_tx_context EvmcHostBase::get_tx_context() const noexcept
{
    return tx_context_;
}

bytes32_t
EvmcHostBase::get_block_hash(int64_t const block_number) const noexcept
{
    MONAD_ASSERT(block_number >= 0);
    return block_hash_buffer_.get(static_cast<uint64_t>(block_number));
};

void EvmcHostBase::emit_log(
    Address const &address, uint8_t const *data, size_t data_size,
    bytes32_t const topics[], size_t num_topics) noexcept
{
    // MAX_IOVEC_LEN of 7 is:
    //  1 for the `struct monad_event_txn_log` object
    //  5 for the (up to) 5 log topics
    //  1 for the data payload
    constexpr size_t MAX_IOVEC_LEN = 7;
    iovec iov[MAX_IOVEC_LEN];
    monad_event_txn_log txn_log_event{};

    Receipt::Log log{.data = {data, data_size}, .address = address};
    for (auto i = 0u; i < num_topics; ++i) {
        log.topics.push_back({topics[i]});
    }
    size_t const iovlen =
        init_txn_log_iovec(log, txn_log_event, std::span{iov});
    MONAD_EVENT_IOV(MONAD_EVENT_TXN_LOG, 0, iov, iovlen);
    state_.store_log(std::move(log));
}

evmc_access_status EvmcHostBase::access_storage(
    Address const &address, bytes32_t const &key) noexcept
{
    return state_.access_storage(address, key);
}

bytes32_t EvmcHostBase::get_transient_storage(
    Address const &address, bytes32_t const &key) const noexcept
{
    return state_.get_transient_storage(address, key);
}

void EvmcHostBase::set_transient_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    return state_.set_transient_storage(address, key, value);
}

MONAD_NAMESPACE_END
