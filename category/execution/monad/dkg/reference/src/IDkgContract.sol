// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @dev Staking ABI calls used by the DKG client when reconstructing parties.
interface IMonadStaking {
    function getValidator(uint64 validatorId) external;
    function getValidatorId(address validator) external returns (uint64 validatorId);
    function getEpoch() external returns (uint64 epoch, bool inEpochDelayPeriod);
    function getConsensusValidatorSet(uint32 startIndex)
        external
        returns (bool done, uint32 nextIndex, uint64[] memory validatorIds);
    function getSnapshotValidatorSet(uint32 startIndex)
        external
        returns (bool done, uint32 nextIndex, uint64[] memory validatorIds);
}

/// @notice Reference ABI for comparing the native DKG contract behavior.
/// monad-bft owns its wire ABI and does not import this file.
interface IDkgContract {
    struct SecpPoint {
        uint8 prefix;
        bytes32 x;
    }

    struct Registration {
        address qcVerifier;
        SecpPoint receiverPublicKey;
        uint32 receiverProofNonce;
        bytes32 receiverProofR;
        bytes32 receiverProofS;
    }

    struct QcSignature {
        uint32 signer;
        bytes32 r;
        bytes32 s;
    }

    struct PcQc {
        uint32 dealer;
        bytes32 digest;
        QcSignature[] signatures;
    }

    struct BveQc {
        uint32 dealer;
        bytes32 digest;
        bytes32 commitmentDigest;
        QcSignature[] signatures;
    }

    struct DkgResult {
        bytes32 sessionId;
        bytes32[18] bteKey;
        QcSignature[] signatures;
    }

    struct PcQcPage {
        uint64 total;
        uint64 next;
        PcQc[] qcs;
    }

    struct BveQcPage {
        uint64 total;
        uint64 next;
        BveQc[] qcs;
    }

    event PcQcPosted(
        uint64 indexed epoch, uint64 indexed index, uint32 indexed dealer, bytes32 digest, QcSignature[] signatures
    );
    event BveQcPosted(
        uint64 indexed epoch,
        uint64 indexed index,
        uint32 indexed dealer,
        bytes32 digest,
        bytes32 commitmentDigest,
        QcSignature[] signatures
    );
    event DkgResultPosted(uint64 indexed epoch, bytes32 sessionId, bytes32[18] bteKey, QcSignature[] signatures);

    error AlreadyRegistered(uint64 epoch, address party);
    error DkgAlreadyFinished(uint64 epoch);
    error InvalidDkgResult();
    error MalformedQc();
    error InvalidPage(uint64 start, uint32 limit);
    error EpochStateUnavailable(uint64 epoch);
    error NotEpochParty(uint64 epoch, address caller);
    error NotPcQcDealer(uint32 dealer, uint32 submitter);
    error NotBveQcDealer(uint32 dealer, uint32 submitter);
    error NotValidator(address caller);
    error PcQcRequired(uint32 dealer);
    error PartySetUnavailable(uint64 epoch);
    error RegistrationClosed(uint64 epoch);
    error ResultAlreadyRecorded(uint64 resultEpoch);
    error StakingLookupFailed();

    function register(uint64 epoch, Registration calldata registration) external;
    function postPcQc(uint64 epoch, PcQc calldata qc) external;
    function postBveQc(uint64 epoch, BveQc calldata qc) external;
    function submitResult(uint64 epoch, DkgResult calldata result) external;
    function registrationOf(uint64 epoch, uint64 validatorId)
        external
        view
        returns (bool exists, Registration memory registration);
    function pcQcs(uint64 epoch, uint64 start, uint32 limit) external view returns (PcQcPage memory page);
    function bveQcs(uint64 epoch, uint64 start, uint32 limit) external view returns (BveQcPage memory page);
    function dkgResult(uint64 epoch)
        external
        view
        returns (bool exists, uint64 recordedBlock, DkgResult memory result);
}
