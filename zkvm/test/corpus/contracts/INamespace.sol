// Vendored from https://github.com/eerkaijun/monad-namespaces
// at e6012d8cebf4, path src/interfaces/INamespace.sol -- unmodified apart from this header.
// The corpus generator deploys this so the guest's anchor harvest and
// pending-array clear run against the real contract, not a stand-in.
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @notice L1-side hub interface of the namespace messaging layer. The hub is the single L1
/// contract every namespace (spoke) connects through. It records outbound L1 -> namespace
/// messages and stores merkle anchors of namespace -> L1 messages, which each namespace's
/// operator posts alongside a new state commitment. Application contracts consume a message by
/// checking the anchor is recorded here and verifying the merkle proof themselves (e.g. with
/// OpenZeppelin `MerkleProof`).
interface INamespaceHub {
    /// @notice Emitted for every recorded L1 -> namespace message. Carries the full preimage
    /// so provers can reconstruct the merkle leaf without extra state reads.
    event L1MessageRecorded(
        uint64 indexed namespaceChainId,
        address indexed from,
        address indexed to,
        bytes data,
        uint256 nonce,
        bytes32 messageHash
    );

    // --- Registration ---

    /// @notice Registers `namespaceChainId` with the selected sequencing and state
    /// verification modes, its validator set and the quorum of validator signatures required to
    /// advance the state, recording the caller as the namespace operator. MUST reject the L1
    /// chain id, an already registered chain id, an unknown `stateVerificationMode`, a zero
    /// quorum, a quorum exceeding the validator count, and zero or duplicate validators.
    function registerNamespace(
        uint64 namespaceChainId,
        bool isCentralizedSequencer,
        uint8 stateVerificationMode,
        address[] calldata validators,
        uint256 quorum
    ) external;

    // --- State commitments & namespace -> L1 anchors ---

    /// @notice Returns the state commitment of the namespace as of its latest posted update.
    function readCommitment(uint64 namespaceChainId) external view returns (bytes32 stateCommitment);

    /// @notice The digest a namespace validator signs to approve a state transition, bound to
    /// this hub, the L1 chain, the namespace, and the current `stateNonce`. Signing it attests
    /// that `newStateRoot` is the namespace's state root at block `namespaceBlockNumber`.
    function stateTransitionDigest(
        uint64 namespaceChainId,
        uint64 namespaceBlockNumber,
        bytes32 newStateRoot,
        bytes32 namespaceAnchor
    ) external view returns (bytes32);

    /// @notice A validator submits its signature over a proposed state transition. Votes
    /// accumulate on-chain; the state advances (new commitment written, `namespaceAnchor`
    /// recorded) only once a distinct quorum of the namespace's registered validators has signed
    /// the same transition. Submission is permissionless — the recovered signer is the authority.
    function submitStateSignature(
        uint64 namespaceChainId,
        uint64 namespaceBlockNumber,
        bytes32 newStateRoot,
        bytes32 namespaceAnchor,
        bytes calldata signature
    ) external;

    /// @notice The namespace block number of the latest committed state root.
    function namespaceBlockNumbers(uint64 namespaceChainId) external view returns (uint64);

    /// @notice True if `anchor` is a recorded merkle root of messages sent from
    /// `namespaceChainId` to the L1.
    function namespaceAnchors(uint64 namespaceChainId, bytes32 anchor) external view returns (bool);

    // --- Messaging: L1 -> namespace ---

    /// @notice Records a message to the target namespace. The message hash
    /// `keccak256(abi.encodePacked(msg.sender, to, keccak256(data), nonce))` is appended to the
    /// pending message array for `namespaceChainId`.
    function sendL1Message(uint64 namespaceChainId, address to, bytes calldata data) external;

    /// @notice Operator-only. Merkleizes the pending L1 -> namespace messages into an anchor and
    /// clears them. The operator relays the returned anchor onto the spoke via `postL1Anchor`.
    function finalizeL1Messages(uint64 namespaceChainId) external returns (bytes32 anchor);

    /// @notice Pending L1 -> namespace message hash at `index` for `namespaceChainId`.
    function pendingL1Messages(uint64 namespaceChainId, uint256 index) external view returns (bytes32);
}

/// @notice Namespace-side spoke interface, deployed on an L2 namespace. Mirror image of the
/// hub: records outbound namespace -> L1 messages and stores merkle anchors of L1 -> namespace
/// messages that the namespace operator relays from the hub.
interface INamespaceSpoke {
    /// @notice Emitted for every recorded namespace -> L1 message. Carries the full preimage so
    /// provers can reconstruct the merkle leaf without extra state reads.
    event NamespaceMessageRecorded(
        address indexed from, address indexed to, bytes data, uint256 nonce, bytes32 messageHash
    );

    // --- Anchors from L1 messages ---

    /// @notice Operator-only. Records a merkle root of L1 -> namespace messages relayed from the
    /// hub.
    function postL1Anchor(bytes32 anchor) external;

    /// @notice True if `anchor` is a recorded merkle root of messages sent from the L1 to this
    /// namespace.
    function l1Anchors(bytes32 anchor) external view returns (bool);

    // --- Messaging: namespace -> L1 ---

    /// @notice Records a message to the L1. The message hash
    /// `keccak256(abi.encodePacked(msg.sender, to, keccak256(data), nonce))` is appended to the
    /// pending message array.
    function sendNamespaceMessage(address to, bytes calldata data) external;

    /// @notice Operator-only. Merkleizes the pending namespace -> L1 messages into an anchor and
    /// clears them. The operator relays the returned anchor onto the hub via
    /// `submitStateSignature`.
    function finalizeNamespaceMessages() external returns (bytes32 anchor);

    /// @notice Pending namespace -> L1 message hash at `index`.
    function pendingNamespaceMessages(uint256 index) external view returns (bytes32);
}
