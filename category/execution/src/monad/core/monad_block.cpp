#include <category/core/blake3.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>

MONAD_NAMESPACE_BEGIN

std::pair<MonadConsensusBlockHeader, bytes32_t>
consensus_header_and_id_from_eth_header(
    BlockHeader const &eth_header, std::optional<uint64_t> const round_number)
{
    auto const header =
        MonadConsensusBlockHeader::from_eth_header(eth_header, round_number);
    return std::make_pair(
        header, to_bytes(blake3(rlp::encode_consensus_block_header(header))));
}

MONAD_NAMESPACE_END
