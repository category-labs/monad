#include <monad/mpt/trie.hpp>

MONAD_MPT_NAMESPACE_BEGIN

/*! \brief Sender to perform the asynchronous finding of a node.
 */
class find_request_sender
{
    struct find_receiver;
    friend struct find_receiver;

    UpdateAuxImpl &aux_;
    NodeCursor root_;
    NibblesView key_;
    inflight_map_t *const inflights_{nullptr};
    std::optional<find_result_type> res_;
    bool tid_checked_{false};

    MONAD_ASYNC_NAMESPACE::result<void> resume_(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *io_state,
        NodeCursor root)
    {
        root_ = root;
        MONAD_ASSERT(root_.is_valid());
        return (*this)(io_state);
    }

public:
    using result_type = MONAD_ASYNC_NAMESPACE::result<find_result_type>;

    constexpr find_request_sender(
        UpdateAuxImpl &aux, NodeCursor root, NibblesView key)
        : aux_(aux)
        , root_(root)
        , key_(key)
    {
        MONAD_ASSERT(root_.is_valid());
    }

    constexpr find_request_sender(
        UpdateAuxImpl &aux, inflight_map_t &inflights, NodeCursor root,
        NibblesView key)
        : aux_(aux)
        , root_(root)
        , key_(key)
        , inflights_(&inflights)
    {
        MONAD_ASSERT(root_.is_valid());
    }

    void reset(NodeCursor root, NibblesView key)
    {
        root_ = root;
        key_ = key;
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

static_assert(sizeof(find_request_sender) == 88);
static_assert(alignof(find_request_sender) == 8);
static_assert(MONAD_ASYNC_NAMESPACE::sender<find_request_sender>);

MONAD_MPT_NAMESPACE_END
