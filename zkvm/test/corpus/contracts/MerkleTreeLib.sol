// Vendored from https://github.com/eerkaijun/monad-namespaces
// at e6012d8cebf4, path src/libraries/MerkleTreeLib.sol -- unmodified apart from this header.
// The corpus generator deploys this so the guest's anchor harvest and
// pending-array clear run against the real contract, not a stand-in.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @notice Canonical merkle tree construction for message anchors: sorted-pair keccak256
/// over the raw message hashes as leaves, with an odd node promoted unchanged to the next
/// level. Proofs verify with OpenZeppelin `MerkleProof`.
library MerkleTreeLib {
    /// @notice Computes the root over `leaves`. A single leaf is its own root.
    function root(bytes32[] memory leaves) internal pure returns (bytes32) {
        require(leaves.length > 0, "MerkleTreeLib: empty leaves");
        bytes32[] memory layer = leaves;
        while (layer.length > 1) {
            layer = _nextLayer(layer);
        }
        return layer[0];
    }

    /// @notice Generates the merkle path for `leaves[index]`, verifiable against
    /// `root(leaves)` with OpenZeppelin `MerkleProof.verify`.
    function getProof(bytes32[] memory leaves, uint256 index) internal pure returns (bytes32[] memory proof) {
        require(index < leaves.length, "MerkleTreeLib: index out of bounds");
        // A tree over n leaves has depth <= 64 for any practical n (n <= 2^64 leaves).
        bytes32[] memory scratch = new bytes32[](64);
        uint256 length = 0;
        bytes32[] memory layer = leaves;
        while (layer.length > 1) {
            uint256 sibling = index ^ 1;
            if (sibling < layer.length) {
                scratch[length++] = layer[sibling];
            }
            // A promoted odd node keeps its position: it is always the last, even index,
            // and moves to index/2 in the next layer, same as a hashed pair.
            index /= 2;
            layer = _nextLayer(layer);
        }
        proof = new bytes32[](length);
        for (uint256 i = 0; i < length; i++) {
            proof[i] = scratch[i];
        }
    }

    function _nextLayer(bytes32[] memory layer) private pure returns (bytes32[] memory next) {
        uint256 n = layer.length;
        next = new bytes32[]((n + 1) / 2);
        for (uint256 i = 0; i < n / 2; i++) {
            next[i] = _hashPair(layer[2 * i], layer[2 * i + 1]);
        }
        if (n % 2 == 1) {
            next[next.length - 1] = layer[n - 1];
        }
    }

    function _hashPair(bytes32 a, bytes32 b) private pure returns (bytes32) {
        return a < b ? keccak256(abi.encodePacked(a, b)) : keccak256(abi.encodePacked(b, a));
    }
}
