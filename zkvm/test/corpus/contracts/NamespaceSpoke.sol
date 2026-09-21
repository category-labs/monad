// Vendored from https://github.com/eerkaijun/monad-namespaces
// at e6012d8cebf4, path src/NamespaceSpoke.sol -- unmodified apart from this header.
// The corpus generator deploys this so the guest's anchor harvest and
// pending-array clear run against the real contract, not a stand-in.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {INamespaceSpoke} from "./INamespace.sol";
import {MerkleTreeLib} from "./MerkleTreeLib.sol";

/// @notice Namespace-side spoke of the messaging layer, deployed on an L2 namespace. Mirror
/// image of the hub: it records outbound namespace -> L1 messages, and stores the merkle
/// anchors of L1 -> namespace messages that the namespace operator relays from the hub.
/// Application contracts (e.g. the token bridge) consume a message by checking the anchor is
/// recorded here and verifying the merkle proof themselves.
///
/// Not enshrined: the operator (fixed at construction) is the only account that can post L1
/// anchors and finalize namespace message batches — this replaces a protocol's automatic
/// anchor posting.
contract NamespaceSpoke is INamespaceSpoke {
    /// @notice Chain id of the namespace this spoke serves.
    uint64 public immutable NAMESPACE_CHAIN_ID;

    /// @notice Account authorized to post L1 anchors and finalize namespace message batches.
    address public immutable OPERATOR;

    uint256 internal _nonce;
    bytes32[] internal _pendingNamespaceMessages;
    mapping(bytes32 => bool) public l1Anchors;

    modifier onlyOperator() {
        require(msg.sender == OPERATOR, "NamespaceSpoke: not operator");
        _;
    }

    constructor(uint64 namespaceChainId, address operator) {
        require(operator != address(0), "NamespaceSpoke: zero operator");
        NAMESPACE_CHAIN_ID = namespaceChainId;
        OPERATOR = operator;
    }

    // ---------------------------------------------------------------------
    // Anchors from L1 messages
    // ---------------------------------------------------------------------

    /// @notice Operator records a merkle root of L1 -> namespace messages relayed from the hub.
    function postL1Anchor(bytes32 anchor) external onlyOperator {
        l1Anchors[anchor] = true;
    }

    // ---------------------------------------------------------------------
    // Messaging: namespace -> L1
    // ---------------------------------------------------------------------

    function sendNamespaceMessage(address to, bytes calldata data) external {
        uint256 nonce = _nonce++;
        bytes32 messageHash = keccak256(abi.encodePacked(msg.sender, to, keccak256(data), nonce));
        _pendingNamespaceMessages.push(messageHash);
        emit NamespaceMessageRecorded(msg.sender, to, data, nonce, messageHash);
    }

    function pendingNamespaceMessages(uint256 index) external view returns (bytes32) {
        return _pendingNamespaceMessages[index];
    }

    function getPendingNamespaceMessages() external view returns (bytes32[] memory) {
        return _pendingNamespaceMessages;
    }

    /// @notice Operator merkleizes the pending namespace -> L1 messages into an anchor and
    /// clears them. The operator relays the returned anchor onto the hub via
    /// `submitStateSignature`. Returns zero if nothing was pending.
    function finalizeNamespaceMessages() external onlyOperator returns (bytes32 anchor) {
        if (_pendingNamespaceMessages.length == 0) return bytes32(0);
        anchor = MerkleTreeLib.root(_pendingNamespaceMessages);
        delete _pendingNamespaceMessages;
    }
}
