#include <monad/config.hpp>
#include <monad/mpt/node.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
class TreeStoreInterface
{
public:
    virtual void insert(Node const&) = 0;
};
} // namespace mpt

MONAD_NAMESPACE_END
