// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

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

/// @notice Reference model for the native DKG contract. It is not deployed or
/// called by monad-bft and will be removed after native parity review.
///
/// Typed on-chain ordering and final-result verification for DKG.
///
/// Party identity is derived from staking, not supplied by the result submitter.
/// The contract intersects the target epoch's validator set with registrations
/// while preserving validator-set order. The runner uses the same stable filter,
/// so PartyId is the address's compact array index.
///
/// A DKG-DONE QC is accepted only if distinct PartyIds with strictly more than
/// two thirds of the registered parties' exact target-epoch staking weight
/// carry valid secp256k1 signatures over the engine's exact SHA-256 transcript
/// `(epoch, session_id, bte_key)`. Once accepted, the epoch is terminal and no
/// further PC or BVE QC can be appended.
///
/// Access authentication relies on EVM `msg.sender`. Execution authenticates
/// an external transaction's sender, and registration binds that address to a
/// nonzero staking validator ID; no party address is accepted from calldata.
/// PC and BVE writes additionally require that authenticated caller to belong
/// to the epoch's canonical `staking set ∩ registrations` party set. Their
/// embedded QC signatures are only checked structurally here and must be
/// cryptographically verified by protocol consumers against registered
/// `qcVerifier` keys. The Done QC is cryptographically verified on-chain.
contract DkgContract {
    enum ValidatorSetKind {
        Consensus,
        Snapshot
    }

    /// @dev SEC1-compressed secp256k1 point: prefix (2 or 3) plus x-coordinate.
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

    /// @dev Compact secp256k1 signature split into its fixed-width limbs.
    ///
    /// Gas/scaling estimate for the current representation under Monad native
    /// pricing, with 200 parties and 200 individual signatures: `register` is
    /// about 0.15M gas, PC-QC and BVE-QC are about 14M gas each, and
    /// `submitResult` is about 36M gas. The two full 200-party scans in
    /// `_partySet` cost at least 6.516M gas: four 100-validator native pages
    /// cost 3.256M and the corresponding DKG registration reads cost about
    /// 3.260M. `submitResult` additionally performs 200 native `getValidator`
    /// calls at 97.2k gas each (19.440M) before signature verification. Every
    /// individual signature also occupies three new storage words. These are
    /// estimates from the current native getter and storage prices; benchmark
    /// the production execution revision before selecting transaction limits.
    ///
    /// TODO(dkg): consider BLS aggregate QCs: one 256-bit signer bitmap and one
    /// 96-byte aggregate signature replace O(N) `QcSignature` storage. PC/BVE
    /// remain opaque and are verified by consumers. With the current data-read
    /// path, this is estimated to reduce PC-QC/BVE-QC from about 14M to about 7M
    /// gas (about 50%), and `submitResult` from about 36M to 28-30M gas (about
    /// 17-22%). The smaller Done-QC reduction is because its 25.956M party/stake
    /// read floor remains. Aggregation does not remove those per-validator
    /// weight/key reads unless staking pagination returns the fields in batches.
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

    struct RegisteredParty {
        uint64 epoch;
        address party;
        Registration registration;
    }

    struct Party {
        uint64 validatorId;
        address party;
    }

    /// @dev One of two reusable epoch slots. Mapping entries are live only when
    /// their epoch matches this slot's epoch, which makes rollover constant-cost
    /// without copying or iterating historical state.
    struct DkgState {
        uint64 epoch;
        uint64 pcQcCount;
        uint64 bveQcCount;
        bool resultRecorded;
        uint64 resultRecordedBlock;
        DkgResult result;
        mapping(uint64 index => PcQc record) pcQcs;
        mapping(uint64 index => BveQc record) bveQcs;
        mapping(uint64 validatorId => RegisteredParty registration) registrations;
        // PC acknowledgements are delivered directly to the dealer, so only
        // that dealer can form and post its PC-QC. One epoch marker per
        // dealer bounds this collection and its marker keyspace to
        // maxPartyCount entries per state slot.
        mapping(uint32 dealer => uint64 epoch) submittedPcQc;
        // A BVE-QC is admitted only from its dealer after that dealer posted a
        // PC-QC. One epoch marker per dealer therefore bounds this collection
        // and its marker keyspace to maxPartyCount entries per state slot.
        mapping(uint32 dealer => uint64 epoch) submittedBveQc;
    }

    bytes private constant STATEMENT_DOMAIN = "BTX-DKG/protocol/qc-signature/v1";
    bytes private constant DKG_DONE_QC_DOMAIN = "BTX-DKG/protocol/dkg-done-qc/v1";
    uint256 private constant SECP256K1_HALF_N = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0;
    IMonadStaking private immutable STAKING;

    DkgState[2] private states;
    uint8 private activeStateIndex;
    bool private statesInitialized;

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

    constructor(address staking_) {
        STAKING = IMonadStaking(staking_);
    }

    function _requireEpochParty(DkgState storage state, ValidatorSetKind kind)
        private
        returns (Party[] memory parties, uint32 submitterPartyId)
    {
        parties = _partySet(state, kind);
        for (uint256 i = 0; i < parties.length; i++) {
            if (parties[i].party == msg.sender) {
                if (i > type(uint32).max) {
                    revert PartySetUnavailable(state.epoch);
                }
                return (parties, uint32(i));
            }
        }
        revert NotEpochParty(state.epoch, msg.sender);
    }

    /// @notice Register the authenticated caller's DKG keys for `epoch`.
    /// @dev `msg.sender`, rather than a calldata address, is resolved through
    /// staking. A forwarding contract is therefore identified as itself.
    function register(uint64 epoch, Registration calldata registration) external {
        (uint64 currentEpoch, bool inDelay) = _syncStates();
        if (inDelay || currentEpoch == type(uint64).max || epoch != currentEpoch + 1) {
            revert RegistrationClosed(epoch);
        }
        uint8 stateIndex = _nextStateIndex();
        DkgState storage state = states[stateIndex];
        if (state.epoch != epoch) {
            revert EpochStateUnavailable(epoch);
        }
        uint64 validatorId = _validatorId(msg.sender);
        if (validatorId == 0) {
            revert NotValidator(msg.sender);
        }
        uint64 stateEpoch = state.epoch;
        if (state.registrations[validatorId].epoch == stateEpoch) {
            revert AlreadyRegistered(epoch, msg.sender);
        }
        // Public-key validity and proof-of-possession are deliberately evaluated
        // by DKG participants. An invalid registration retains this validator's
        // canonical party slot and voting weight as Byzantine weight.
        state.registrations[validatorId] = RegisteredParty(stateEpoch, msg.sender, registration);
    }

    /// @notice Post one PC-QC from its authenticated dealer.
    /// @dev Embedded signatures are structurally bounded here; consumers
    /// perform their cryptographic verification.
    function postPcQc(uint64 epoch, PcQc calldata qc) external {
        (uint8 stateIndex, ValidatorSetKind kind) = _protocolState(epoch);
        DkgState storage state = states[stateIndex];
        (Party[] memory parties, uint32 submitterPartyId) = _requireEpochParty(state, kind);
        if (state.resultRecorded) {
            revert DkgAlreadyFinished(epoch);
        }
        _validateQc(qc.dealer, qc.signatures, parties.length);
        if (submitterPartyId != qc.dealer) {
            revert NotPcQcDealer(qc.dealer, submitterPartyId);
        }
        uint64 stateEpoch = state.epoch;
        if (state.submittedPcQc[qc.dealer] == stateEpoch) {
            return;
        }
        state.submittedPcQc[qc.dealer] = stateEpoch;

        uint64 index = state.pcQcCount;
        if (index == type(uint64).max) {
            revert MalformedQc();
        }
        state.pcQcCount = index + 1;
        PcQc storage record = state.pcQcs[index];
        delete record.signatures;
        record.dealer = qc.dealer;
        record.digest = qc.digest;
        _copySignatures(record.signatures, qc.signatures);
        emit PcQcPosted(epoch, index, qc.dealer, qc.digest, qc.signatures);
    }

    /// @notice Post one BVE-QC from its authenticated dealer.
    /// @dev Embedded signatures are structurally bounded here; consumers
    /// perform their cryptographic verification.
    function postBveQc(uint64 epoch, BveQc calldata qc) external {
        (uint8 stateIndex, ValidatorSetKind kind) = _protocolState(epoch);
        DkgState storage state = states[stateIndex];
        (Party[] memory parties, uint32 submitterPartyId) = _requireEpochParty(state, kind);
        if (state.resultRecorded) {
            revert DkgAlreadyFinished(epoch);
        }
        _validateQc(qc.dealer, qc.signatures, parties.length);
        uint64 stateEpoch = state.epoch;
        if (submitterPartyId != qc.dealer) {
            revert NotBveQcDealer(qc.dealer, submitterPartyId);
        }
        if (state.submittedPcQc[qc.dealer] != stateEpoch) {
            revert PcQcRequired(qc.dealer);
        }
        if (state.submittedBveQc[qc.dealer] == stateEpoch) {
            return;
        }
        state.submittedBveQc[qc.dealer] = stateEpoch;

        uint64 index = state.bveQcCount;
        if (index == type(uint64).max) {
            revert MalformedQc();
        }
        state.bveQcCount = index + 1;
        BveQc storage record = state.bveQcs[index];
        delete record.signatures;
        record.dealer = qc.dealer;
        record.digest = qc.digest;
        record.commitmentDigest = qc.commitmentDigest;
        _copySignatures(record.signatures, qc.signatures);
        emit BveQcPosted(epoch, index, qc.dealer, qc.digest, qc.commitmentDigest, qc.signatures);
    }

    function submitResult(uint64 epoch, DkgResult calldata result) external {
        (uint8 stateIndex, ValidatorSetKind kind) = _protocolState(epoch);
        DkgState storage state = states[stateIndex];
        (Party[] memory parties,) = _requireEpochParty(state, kind);
        if (state.resultRecorded) {
            revert ResultAlreadyRecorded(epoch);
        }
        _validateDkgResult(state, kind, result, parties);
        state.resultRecorded = true;
        state.resultRecordedBlock = uint64(block.number);
        DkgResult storage record = state.result;
        delete record.signatures;
        record.sessionId = result.sessionId;
        record.bteKey = result.bteKey;
        _copySignatures(record.signatures, result.signatures);
        emit DkgResultPosted(epoch, result.sessionId, result.bteKey, result.signatures);
    }

    /// @notice Returns the registration stored under a staking validator ID.
    /// @dev The client resolves an address through staking before this call.
    /// Keeping this getter local avoids a nested read-only call into the native
    /// staking contract, whose generic ABI entry point is not STATICCALL-safe.
    function registrationOf(uint64 epoch, uint64 validatorId)
        external
        view
        returns (bool exists, Registration memory registration)
    {
        (bool retained, uint8 index) = _stateIndex(epoch);
        if (!retained) {
            return (false, registration);
        }
        DkgState storage state = states[index];
        RegisteredParty storage registered = state.registrations[validatorId];
        exists = validatorId != 0 && registered.epoch == state.epoch;
        if (exists) {
            registration = registered.registration;
        }
    }

    function pcQcs(uint64 epoch, uint64 start, uint32 limit) external view returns (PcQcPage memory page) {
        // Deliberately caller-sized: EVM gas bounds work, while recovery chooses
        // a practical page size for its execution/RPC budget.
        (bool retained, uint8 index) = _stateIndex(epoch);
        uint256 total = retained ? states[index].pcQcCount : 0;
        if (start > total || limit == 0) {
            revert InvalidPage(start, limit);
        }
        uint256 requestedEnd = uint256(start) + limit;
        uint256 end = requestedEnd < total ? requestedEnd : total;
        page.total = _recordIndex(total);
        page.next = _recordIndex(end);
        page.qcs = new PcQc[](end - start);
        if (retained) {
            DkgState storage state = states[index];
            for (uint256 i = start; i < end; i++) {
                page.qcs[i - start] = state.pcQcs[_recordIndex(i)];
            }
        }
    }

    function bveQcs(uint64 epoch, uint64 start, uint32 limit) external view returns (BveQcPage memory page) {
        // Deliberately caller-sized: EVM gas bounds work, while recovery chooses
        // a practical page size for its execution/RPC budget.
        (bool retained, uint8 index) = _stateIndex(epoch);
        uint256 total = retained ? states[index].bveQcCount : 0;
        if (start > total || limit == 0) {
            revert InvalidPage(start, limit);
        }
        uint256 requestedEnd = uint256(start) + limit;
        uint256 end = requestedEnd < total ? requestedEnd : total;
        page.total = _recordIndex(total);
        page.next = _recordIndex(end);
        page.qcs = new BveQc[](end - start);
        if (retained) {
            DkgState storage state = states[index];
            for (uint256 i = start; i < end; i++) {
                page.qcs[i - start] = state.bveQcs[_recordIndex(i)];
            }
        }
    }

    function dkgResult(uint64 epoch)
        external
        view
        returns (bool exists, uint64 recordedBlock, DkgResult memory result)
    {
        (bool retained, uint8 index) = _stateIndex(epoch);
        exists = retained && states[index].resultRecorded;
        if (exists) {
            recordedBlock = states[index].resultRecordedBlock;
            result = states[index].result;
        }
    }

    /// @dev Native execution rotates these slots from authenticated staking
    /// snapshot and epoch-change hooks. This executable Solidity reference has
    /// no native system-hook entrypoint, so it performs the equivalent update
    /// lazily before mutations.
    function _syncStates() private returns (uint64 currentEpoch, bool inDelay) {
        (currentEpoch, inDelay) = _stakingEpoch();
        if (currentEpoch == type(uint64).max) {
            revert StakingLookupFailed();
        }
        uint64 followingEpoch = currentEpoch + 1;
        if (!statesInitialized) {
            activeStateIndex = 0;
            _resetState(states[0], currentEpoch);
            _resetState(states[1], followingEpoch);
            statesInitialized = true;
            return (currentEpoch, inDelay);
        }

        uint8 nextIndex = _nextStateIndex();
        DkgState storage active = states[activeStateIndex];
        DkgState storage next = states[nextIndex];
        if (currentEpoch == active.epoch) {
            if (next.epoch != followingEpoch) {
                _resetState(next, followingEpoch);
            }
            return (currentEpoch, inDelay);
        }
        if (currentEpoch == next.epoch) {
            uint8 retiredIndex = activeStateIndex;
            activeStateIndex = nextIndex;
            _resetState(states[retiredIndex], followingEpoch);
            return (currentEpoch, inDelay);
        }
        if (currentEpoch > next.epoch) {
            activeStateIndex = 0;
            _resetState(states[0], currentEpoch);
            _resetState(states[1], followingEpoch);
            return (currentEpoch, inDelay);
        }
        revert StakingLookupFailed();
    }

    function _resetState(DkgState storage state, uint64 epoch) private {
        state.epoch = epoch;
        state.pcQcCount = 0;
        state.bveQcCount = 0;
        state.resultRecorded = false;
        state.resultRecordedBlock = 0;
    }

    function _nextStateIndex() private view returns (uint8) {
        return activeStateIndex ^ 1;
    }

    function _stateIndex(uint64 epoch) private view returns (bool retained, uint8 index) {
        if (!statesInitialized) {
            return (false, 0);
        }
        if (states[0].epoch == epoch) {
            return (true, 0);
        }
        if (states[1].epoch == epoch) {
            return (true, 1);
        }
        return (false, 0);
    }

    function _protocolState(uint64 epoch) private returns (uint8 stateIndex, ValidatorSetKind kind) {
        (uint64 currentEpoch, bool inDelay) = _syncStates();
        if (epoch == currentEpoch) {
            stateIndex = activeStateIndex;
            kind = inDelay ? ValidatorSetKind.Snapshot : ValidatorSetKind.Consensus;
            return (stateIndex, kind);
        }
        if (inDelay && epoch == currentEpoch + 1) {
            stateIndex = _nextStateIndex();
            kind = ValidatorSetKind.Consensus;
            return (stateIndex, kind);
        }
        revert PartySetUnavailable(epoch);
    }

    /// @dev Derive `PartyId -> address` by stable-filtering registrations through
    /// the target epoch's canonical staking order. The staking window is checked
    /// on every use, so no historical party-set cache is required.
    /// The implementation deliberately relies on staking to enforce its active
    /// validator-set bound (currently 200); this contract does not duplicate it.
    function _partySet(DkgState storage state, ValidatorSetKind kind) private returns (Party[] memory parties) {
        // TODO: expose the active validator-set bound or total length from the
        // staking precompile so this exact-size allocation does not require a
        // second paginated scan.
        parties = new Party[](_registeredPartyCount(state, kind));
        if (parties.length == 0) {
            revert PartySetUnavailable(state.epoch);
        }
        uint256 count;
        uint32 startIndex;
        uint64 stateEpoch = state.epoch;
        while (true) {
            (bool done, uint32 nextIndex, uint64[] memory validatorIds) = _readValidatorPage(kind, startIndex);
            if (!done && nextIndex <= startIndex) {
                revert StakingLookupFailed();
            }
            for (uint256 i = 0; i < validatorIds.length; i++) {
                uint64 validatorId = validatorIds[i];
                if (validatorId == 0) {
                    revert StakingLookupFailed();
                }
                RegisteredParty storage registered = state.registrations[validatorId];
                if (registered.epoch != stateEpoch) {
                    continue;
                }
                if (count == parties.length) {
                    revert StakingLookupFailed();
                }
                parties[count++] = Party(validatorId, registered.party);
            }
            if (done) {
                break;
            }
            startIndex = nextIndex;
        }
        if (count != parties.length) {
            revert StakingLookupFailed();
        }
    }

    function _registeredPartyCount(DkgState storage state, ValidatorSetKind kind) private returns (uint256 count) {
        uint32 startIndex;
        uint64 stateEpoch = state.epoch;
        while (true) {
            (bool done, uint32 nextIndex, uint64[] memory validatorIds) = _readValidatorPage(kind, startIndex);
            if (!done && nextIndex <= startIndex) {
                revert StakingLookupFailed();
            }
            for (uint256 i = 0; i < validatorIds.length; i++) {
                uint64 validatorId = validatorIds[i];
                if (validatorId == 0) {
                    revert StakingLookupFailed();
                }
                if (state.registrations[validatorId].epoch == stateEpoch) {
                    count++;
                }
            }
            if (done) {
                return count;
            }
            startIndex = nextIndex;
        }
    }

    function _stakingEpoch() private returns (uint64 epoch, bool inDelay) {
        try STAKING.getEpoch() returns (uint64 currentEpoch, bool inEpochDelayPeriod) {
            return (currentEpoch, inEpochDelayPeriod);
        } catch {
            revert StakingLookupFailed();
        }
    }

    function _readValidatorPage(ValidatorSetKind kind, uint32 startIndex)
        private
        returns (bool done, uint32 nextIndex, uint64[] memory validatorIds)
    {
        if (kind == ValidatorSetKind.Consensus) {
            try STAKING.getConsensusValidatorSet(startIndex) returns (
                bool pageDone, uint32 followingIndex, uint64[] memory page
            ) {
                return (pageDone, followingIndex, page);
            } catch {
                revert StakingLookupFailed();
            }
        }
        try STAKING.getSnapshotValidatorSet(startIndex) returns (
            bool pageDone, uint32 followingIndex, uint64[] memory page
        ) {
            return (pageDone, followingIndex, page);
        } catch {
            revert StakingLookupFailed();
        }
    }

    function _validatorId(address validator) private returns (uint64) {
        try STAKING.getValidatorId(validator) returns (uint64 validatorId) {
            return validatorId;
        } catch {
            revert StakingLookupFailed();
        }
    }

    function _validateDkgResult(
        DkgState storage state,
        ValidatorSetKind kind,
        DkgResult calldata result,
        Party[] memory parties
    ) private {
        if (!_signaturesAreCanonical(result.signatures, parties.length)) {
            revert InvalidDkgResult();
        }

        uint256[] memory votingWeights = _votingWeights(parties, kind);

        // Quorum is deliberately computed over registered target-epoch parties,
        // not the full staking set. Unregistered staking weight cannot sign and
        // is excluded from both the numerator and denominator.
        bytes32 digest = _doneQcDigest(state.epoch, result.sessionId, result.bteKey);
        if (
            _signedResultVotingWeight(state, result.signatures, parties, votingWeights, digest)
                < _votingWeightQuorum(votingWeights)
        ) {
            revert InvalidDkgResult();
        }
    }

    function _signedResultVotingWeight(
        DkgState storage state,
        QcSignature[] calldata signatures,
        Party[] memory parties,
        uint256[] memory votingWeights,
        bytes32 digest
    ) private view returns (uint256 signedVotingWeight) {
        for (uint256 i = 0; i < signatures.length; i++) {
            QcSignature calldata signature = signatures[i];
            RegisteredParty storage registered = state.registrations[parties[signature.signer].validatorId];
            if (!_signatureMatches(registered.registration.qcVerifier, digest, signature.r, signature.s)) {
                revert InvalidDkgResult();
            }
            signedVotingWeight += votingWeights[signature.signer];
        }
    }

    function _votingWeightQuorum(uint256[] memory votingWeights) private pure returns (uint256) {
        uint256 totalVotingWeight;
        for (uint256 i = 0; i < votingWeights.length; i++) {
            totalVotingWeight += votingWeights[i];
        }
        return totalVotingWeight - (totalVotingWeight - 1) / 3;
    }

    function _validatorStake(uint64 validatorId, ValidatorSetKind kind) private returns (uint256) {
        (bool success, bytes memory output) =
            address(STAKING).call(abi.encodeWithSelector(IMonadStaking.getValidator.selector, validatorId));
        // The staking precompile returns ten fixed words followed by two dynamic
        // key fields. Consensus and snapshot stake are fixed words 6 and 8.
        if (!success || output.length < 320) {
            revert StakingLookupFailed();
        }
        uint256 consensusStake;
        uint256 snapshotStake;
        assembly ("memory-safe") {
            consensusStake := mload(add(output, 0xe0))
            snapshotStake := mload(add(output, 0x120))
        }
        return kind == ValidatorSetKind.Consensus ? consensusStake : snapshotStake;
    }

    function _votingWeights(Party[] memory parties, ValidatorSetKind kind) private returns (uint256[] memory weights) {
        weights = new uint256[](parties.length);
        for (uint256 i = 0; i < parties.length; i++) {
            if (parties[i].validatorId == 0) {
                revert StakingLookupFailed();
            }
            uint256 stake = _validatorStake(parties[i].validatorId, kind);
            if (stake == 0) {
                // Rejecting zero also prevents quorum arithmetic from accepting
                // a party omitted by the Rust engine.
                revert StakingLookupFailed();
            }
            weights[i] = stake;
        }
    }

    /// @dev Reproduce the DKG engine's `dkg_done_qc_statement`. Its framed
    /// uint64 fields are big-endian so packed ABI encoding is canonical.
    function _doneQcDigest(uint64 epoch, bytes32 sessionId, bytes32[18] calldata bteEncryptionKey)
        private
        pure
        returns (bytes32)
    {
        return sha256(
            abi.encodePacked(
                STATEMENT_DOMAIN,
                uint64(DKG_DONE_QC_DOMAIN.length),
                DKG_DONE_QC_DOMAIN,
                epoch,
                uint64(32),
                sessionId,
                bteEncryptionKey
            )
        );
    }

    function _signatureMatches(address expected, bytes32 digest, bytes32 r, bytes32 s) private pure returns (bool) {
        if (expected == address(0) || uint256(s) > SECP256K1_HALF_N) {
            return false;
        }
        // TODO(dkg): preserve the recovery ID produced during Rust signing
        // (for example, compactly in `s` per EIP-2098) so this needs only one
        // `ecrecover` call instead of trying both Ethereum recovery values.
        return ecrecover(digest, 27, r, s) == expected || ecrecover(digest, 28, r, s) == expected;
    }

    function _recordIndex(uint256 index) private pure returns (uint64) {
        if (index > type(uint64).max) {
            revert MalformedQc();
        }
        return uint64(index);
    }

    function _validateQc(uint32 dealer, QcSignature[] calldata signatures, uint256 partyCount) private pure {
        if (dealer >= partyCount || !_signaturesAreCanonical(signatures, partyCount)) {
            revert MalformedQc();
        }
    }

    function _signaturesAreCanonical(QcSignature[] calldata signatures, uint256 partyCount)
        private
        pure
        returns (bool)
    {
        uint256 count = signatures.length;
        if (count == 0 || count > partyCount) {
            return false;
        }
        uint32 previous;
        for (uint256 i = 0; i < count; i++) {
            uint32 signer = signatures[i].signer;
            if (signer >= partyCount || (i != 0 && signer <= previous)) {
                return false;
            }
            previous = signer;
        }
        return true;
    }

    function _copySignatures(QcSignature[] storage target, QcSignature[] calldata source) private {
        for (uint256 i = 0; i < source.length; i++) {
            target.push(source[i]);
        }
    }
}
