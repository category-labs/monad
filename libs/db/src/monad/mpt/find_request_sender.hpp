#pragma once

#include <monad/mpt/db_error.hpp>
#include <monad/mpt/trie.hpp>

MONAD_MPT_NAMESPACE_BEGIN

using find_bytes_result_type = std::pair<byte_string, DbError>;

using inflight_node_t = unordered_dense_map<
    chunk_offset_t,
    std::vector<std::function<MONAD_ASYNC_NAMESPACE::result<void>(
        NodeCursor, std::shared_ptr<Node>)>>,
    chunk_offset_t_hasher>;

/*! \brief Sender to perform the asynchronous finding of a node.
 */
class find_request_sender
{
    struct find_receiver;
    friend struct find_receiver;

    UpdateAuxImpl &aux_;
    NodeCursor root_;
    NibblesView key_;
    inflight_node_t &inflights_;
    std::optional<find_bytes_result_type> res_;
    bool tid_checked_{false};
    bool return_value_{true};
    uint8_t const cached_levels_{5};
    uint8_t curr_level_{0};
    std::shared_ptr<Node> subtrie_with_sender_lifetime_{nullptr};

    MONAD_ASYNC_NAMESPACE::result<void> resume_(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
        NodeCursor root)
    {
        root_ = root;
        MONAD_ASSERT(root_.is_valid());
        return (*this)(io_state);
    }

public:
    using result_type = MONAD_ASYNC_NAMESPACE::result<find_bytes_result_type>;

    constexpr find_request_sender(
        UpdateAuxImpl &aux, inflight_node_t &inflights, NodeCursor const root,
        NibblesView const key, bool const return_value,
        uint8_t const cached_levels)
        : aux_(aux)
        , root_(root)
        , key_(key)
        , inflights_(inflights)
        , return_value_(return_value)
        , cached_levels_(cached_levels)
    {
        MONAD_ASSERT(root_.is_valid());
    }

    void reset(NodeCursor root, NibblesView key)
    {
        root_ = root;
        key_ = key;
        curr_level_ = 0;
        subtrie_with_sender_lifetime_ = nullptr;
        MONAD_ASSERT(root_.is_valid());
        tid_checked_ = false;
    }

    MONAD_ASYNC_NAMESPACE::result<void>
    operator()(MONAD_ASYNC_NAMESPACE::erased_connected_operation *) noexcept;

    result_type completed(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
        MONAD_ASYNC_NAMESPACE::result<void> res) const noexcept
    {
        BOOST_OUTCOME_TRY(std::move(res));
        MONAD_ASSERT(res_.has_value());
        return *res_;
    }
};

static_assert(sizeof(find_request_sender) == 120);
static_assert(alignof(find_request_sender) == 8);
static_assert(MONAD_ASYNC_NAMESPACE::sender<find_request_sender>);

MONAD_MPT_NAMESPACE_END
