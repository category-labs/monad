// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {DkgContract} from "../src/DkgContract.sol";

interface Vm {
    function addr(uint256 privateKey) external pure returns (address);
    function expectEmit(bool checkTopic1, bool checkTopic2, bool checkTopic3, bool checkData, address emitter) external;
    function expectRevert() external;
    function prank(address msgSender) external;
    function sign(uint256 privateKey, bytes32 digest) external pure returns (uint8 v, bytes32 r, bytes32 s);
}

contract TestValidatorLookup {
    uint256 private constant TEST_STAKE = 1 ether;

    mapping(address validator => uint64 id) private validatorIds;
    mapping(uint64 validatorId => uint256 stake) private consensusStakes;
    mapping(uint64 validatorId => uint256 stake) private snapshotStakes;
    uint64[] private consensus;
    uint64[] private snapshot;
    uint64 private epoch = 6;
    uint64 private nextValidatorId = 1;
    bool private inDelay;

    function addTarget(address validator) external {
        uint64 id = nextValidatorId++;
        validatorIds[validator] = id;
        consensusStakes[id] = TEST_STAKE;
        snapshotStakes[id] = TEST_STAKE;
        consensus.push(id);
        snapshot.push(id);
    }

    function addValidator(address validator) external {
        uint64 id = nextValidatorId++;
        validatorIds[validator] = id;
    }

    function setValidatorId(address validator, uint64 validatorId) external {
        validatorIds[validator] = validatorId;
    }

    function setEpoch(uint64 epoch_, bool inDelay_) external {
        epoch = epoch_;
        inDelay = inDelay_;
    }

    function setStake(address validator, uint256 stake) external {
        uint64 validatorId = validatorIds[validator];
        consensusStakes[validatorId] = stake;
        snapshotStakes[validatorId] = stake;
    }

    function setConsensusStake(address validator, uint256 stake) external {
        consensusStakes[validatorIds[validator]] = stake;
    }

    function setSnapshotStake(address validator, uint256 stake) external {
        snapshotStakes[validatorIds[validator]] = stake;
    }

    function getValidatorId(address validator) external view returns (uint64) {
        return validatorIds[validator];
    }

    function getValidator(uint64 validatorId) external view {
        uint256 consensusStake = consensusStakes[validatorId];
        uint256 snapshotStake = snapshotStakes[validatorId];
        assembly ("memory-safe") {
            let output := mload(0x40)
            mstore(add(output, 0x40), consensusStake)
            mstore(add(output, 0xc0), consensusStake)
            mstore(add(output, 0x100), snapshotStake)
            return(output, 0x140)
        }
    }

    function getEpoch() external view returns (uint64, bool) {
        return (epoch, inDelay);
    }

    function getConsensusValidatorSet(uint32 startIndex)
        external
        view
        returns (bool done, uint32 nextIndex, uint64[] memory validatorIds_)
    {
        return page(consensus, startIndex);
    }

    function getSnapshotValidatorSet(uint32 startIndex)
        external
        view
        returns (bool done, uint32 nextIndex, uint64[] memory validatorIds_)
    {
        return page(snapshot, startIndex);
    }

    function page(uint64[] storage source, uint32 startIndex)
        private
        view
        returns (bool done, uint32 nextIndex, uint64[] memory values)
    {
        if (startIndex >= source.length) {
            return (true, startIndex, new uint64[](0));
        }
        uint256 end = source.length < uint256(startIndex) + 100 ? source.length : uint256(startIndex) + 100;
        values = new uint64[](end - startIndex);
        for (uint256 i = startIndex; i < end; i++) {
            values[i - startIndex] = source[i];
        }
        return (end == source.length, uint32(end), values);
    }
}

contract DkgContractTest {
    Vm private constant VM = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint64 private constant EPOCH = 7;

    struct Fixture {
        DkgContract dkg;
        TestValidatorLookup staking;
        address[4] validators;
        uint256[4] qcKeys;
    }

    event PcQcPosted(
        uint64 indexed epoch,
        uint64 indexed index,
        uint32 indexed dealer,
        bytes32 digest,
        DkgContract.QcSignature[] signatures
    );
    event BveQcPosted(
        uint64 indexed epoch,
        uint64 indexed index,
        uint32 indexed dealer,
        bytes32 digest,
        bytes32 commitmentDigest,
        DkgContract.QcSignature[] signatures
    );
    event DkgResultPosted(
        uint64 indexed epoch, bytes32 sessionId, bytes32[18] bteKey, DkgContract.QcSignature[] signatures
    );

    function testRegisterStoresTypedPartyRegistration() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory expected = registration(validator, 1);
        VM.prank(validator);
        dkg.register(EPOCH, expected);

        (bool exists, DkgContract.Registration memory stored) = dkg.registrationOf(EPOCH, 1);
        require(exists, "registration missing");
        require(keccak256(abi.encode(stored)) == keccak256(abi.encode(expected)), "wrong registration");

        (bool unknownExists,) = dkg.registrationOf(EPOCH, 2);
        require(!unknownExists, "unknown validator registration exists");
    }

    function testRegistrationIsValidatorIdKeyedAndBoundToParty() external {
        (DkgContract dkg, TestValidatorLookup staking, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory validatorRegistration = registration(validator, 1);
        VM.prank(validator);
        dkg.register(EPOCH, validatorRegistration);

        address aliasParty = address(0xA11A5);
        staking.setValidatorId(aliasParty, 1);
        (bool exists, DkgContract.Registration memory stored) = dkg.registrationOf(EPOCH, 1);
        require(exists, "validator-ID registration missing");
        require(
            keccak256(abi.encode(stored)) == keccak256(abi.encode(validatorRegistration)),
            "wrong validator-ID registration"
        );

        DkgContract.Registration memory aliasRegistration = registration(aliasParty, 2);
        VM.expectRevert();
        VM.prank(aliasParty);
        dkg.register(EPOCH, aliasRegistration);
    }

    function testReceiverProofMatchesRustVector() external pure {
        address validator = VM.addr(100);
        DkgContract.Registration memory record = registration(validator, 1);
        require(
            receiverKeyProofDigest(validator, record.qcVerifier, record.receiverPublicKey, record.receiverProofNonce)
                == 0x336475c01467c96c760ff8210e598f3e07d0004a6e4bd19c2dcede6e5bad65f1,
            "receiver proof transcript differs from Rust"
        );
        require(
            record.receiverProofR == 0xc76aa5c99ef3e13e46cb5fe8a8cbed3c6dbe0d2bae141f8e430ea0c14dd57198
                && record.receiverProofS == 0x624d2e80fe71603bb686e783debbae1b4b59d339f2b526a0d3b47b527abf08c1,
            "receiver proof signature differs from Rust"
        );
    }

    function testDuplicateRegistrationReverts() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory first = registration(validator, 1);
        VM.prank(validator);
        dkg.register(EPOCH, first);
        DkgContract.Registration memory second = registration(validator, 2);
        VM.expectRevert();
        VM.prank(validator);
        dkg.register(EPOCH, second);
    }

    function testZeroQcVerifierOccupiesByzantinePartySlot() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory malformed = registration(validator, 1);
        malformed.qcVerifier = address(0);

        VM.prank(validator);
        dkg.register(EPOCH, malformed);
        (bool exists, DkgContract.Registration memory stored) = dkg.registrationOf(EPOCH, 1);
        require(exists && stored.qcVerifier == address(0), "Byzantine registration missing");
    }

    function testInvalidReceiverProofOccupiesByzantinePartySlot() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory malformed = registration(validator, 1);
        malformed.receiverProofR = bytes32(uint256(malformed.receiverProofR) ^ 1);

        VM.prank(validator);
        dkg.register(EPOCH, malformed);
        (bool exists,) = dkg.registrationOf(EPOCH, 1);
        require(exists, "Byzantine registration missing");
    }

    function testUnboundQcVerifierOccupiesByzantinePartySlot() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory malformed = registration(validator, 1);
        malformed.qcVerifier = VM.addr(2);

        VM.prank(validator);
        dkg.register(EPOCH, malformed);
        (bool exists,) = dkg.registrationOf(EPOCH, 1);
        require(exists, "Byzantine registration missing");
    }

    function testCopiedReceiverProofOccupiesByzantinePartySlot() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory copied = registration(VM.addr(101), 1);

        VM.prank(validator);
        dkg.register(EPOCH, copied);
        (bool exists,) = dkg.registrationOf(EPOCH, 1);
        require(exists, "Byzantine registration missing");
    }

    function testInvalidPointOccupiesByzantinePartySlot() external {
        (DkgContract dkg,, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory malformed = registration(validator, 1);
        malformed.receiverPublicKey.x = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F;

        VM.prank(validator);
        dkg.register(EPOCH, malformed);
        (bool exists,) = dkg.registrationOf(EPOCH, 1);
        require(exists, "Byzantine registration missing");
    }

    function testRegistrationClosesAtStakingBoundary() external {
        (DkgContract dkg, TestValidatorLookup staking, address validator) = deploySingleRegistrationTarget();
        staking.setEpoch(6, true);
        DkgContract.Registration memory record = registration(validator, 1);
        VM.expectRevert();
        VM.prank(validator);
        dkg.register(EPOCH, record);
    }

    function testUnregisteredStakingCallerCannotWriteDkgState() external {
        TestValidatorLookup staking = new TestValidatorLookup();
        DkgContract dkg = new DkgContract(address(staking));
        address outsider = address(0xBAD);

        DkgContract.Registration memory record = registration(outsider, 1);
        VM.expectRevert();
        VM.prank(outsider);
        dkg.register(EPOCH, record);
    }

    function testMissingStakingTargetCannotWriteDkgState() external {
        DkgContract dkg = new DkgContract(address(0x1000));

        DkgContract.Registration memory record = registration(address(this), 1);
        VM.expectRevert();
        dkg.register(EPOCH, record);
    }

    function testPartyCountCompactsMissingRegistrations() external {
        TestValidatorLookup staking = new TestValidatorLookup();
        DkgContract dkg = new DkgContract(address(staking));
        address[5] memory validators;
        for (uint256 i = 0; i < validators.length; i++) {
            validators[i] = VM.addr(200 + i);
            staking.addTarget(validators[i]);
            if (i != 1) {
                DkgContract.Registration memory record = registration(validators[i], 10);
                VM.prank(validators[i]);
                dkg.register(EPOCH, record);
            }
        }
        staking.setEpoch(6, true);

        VM.prank(validators[2]);
        dkg.postPcQc(EPOCH, pcQc(1, 0x11, 1));

        VM.prank(validators[4]);
        dkg.postPcQc(EPOCH, pcQc(3, 0x12, 1));
        VM.expectRevert();
        VM.prank(validators[0]);
        dkg.postPcQc(EPOCH, pcQc(4, 0x13, 1));
        require(dkg.pcQcs(EPOCH, 0, 10).total == 2, "wrong compact party count");
    }

    function testNonTargetRegistrationsDoNotExpandPartySet() external {
        TestValidatorLookup staking = new TestValidatorLookup();
        DkgContract dkg = new DkgContract(address(staking));
        address[4] memory targets;

        for (uint256 i = 0; i < targets.length; i++) {
            targets[i] = VM.addr(300 + i);
            staking.addTarget(targets[i]);
            DkgContract.Registration memory record = registration(targets[i], i + 1);
            VM.prank(targets[i]);
            dkg.register(EPOCH, record);
        }
        for (uint256 i = 0; i < 257; i++) {
            address nonTarget = VM.addr(1_000 + i);
            staking.addValidator(nonTarget);
            DkgContract.Registration memory record = registration(nonTarget, 500 + i);
            VM.prank(nonTarget);
            dkg.register(EPOCH, record);
        }
        staking.setEpoch(6, true);

        VM.prank(targets[3]);
        dkg.postPcQc(EPOCH, pcQc(3, 0x11, 1));
        VM.expectRevert();
        VM.prank(targets[0]);
        dkg.postPcQc(EPOCH, pcQc(4, 0x12, 1));
        require(dkg.pcQcs(EPOCH, 0, 10).total == 1, "non-target registrations changed party count");
    }

    function testNonTargetValidatorCannotPostProtocolRecord() external {
        Fixture memory fixture = deploySession();
        address outsider = VM.addr(999);
        fixture.staking.addValidator(outsider);
        VM.expectRevert();
        VM.prank(outsider);
        fixture.dkg.postPcQc(EPOCH, pcQc(2, 0x11, 1));
    }

    function testPartySetSupportsStakingBound() external {
        TestValidatorLookup staking = new TestValidatorLookup();
        DkgContract dkg = new DkgContract(address(staking));
        address last;
        for (uint256 i = 0; i < 200; i++) {
            address validator = address(uint160(1000 - i));
            if (i == 199) {
                last = validator;
            }
            staking.addTarget(validator);
            DkgContract.Registration memory record = registration(validator, 10);
            VM.prank(validator);
            dkg.register(EPOCH, record);
        }
        staking.setEpoch(6, true);

        VM.prank(last);
        dkg.postPcQc(EPOCH, pcQc(199, 0x11, 1));
        require(dkg.pcQcs(EPOCH, 0, 1).total == 1, "large party set was rejected");
    }

    function testPcAndBveQcsUseSeparateTypedCollections() external {
        Fixture memory fixture = deploySession();
        DkgContract.PcQc memory pc = pcQc(2, 0x11, 1);
        DkgContract.BveQc memory bve = bveQc(2, 0x22, 1);

        postPc(fixture, pc);
        postBve(fixture, 2, bve);

        DkgContract.PcQcPage memory pcPage = fixture.dkg.pcQcs(EPOCH, 0, 1);
        require(pcPage.total == 1 && pcPage.next == 1, "wrong PC page boundary");
        require(pcPage.qcs.length == 1, "wrong PC page");
        DkgContract.PcQc memory storedPc = pcPage.qcs[0];
        require(storedPc.dealer == pc.dealer && storedPc.digest == pc.digest, "wrong PC");
        require(storedPc.signatures.length == 1, "wrong PC witness");

        DkgContract.BveQcPage memory bvePage = fixture.dkg.bveQcs(EPOCH, 0, 1);
        require(bvePage.total == 1 && bvePage.next == 1, "wrong BVE page boundary");
        require(bvePage.qcs.length == 1, "wrong BVE page");
        DkgContract.BveQc memory storedBve = bvePage.qcs[0];
        require(
            storedBve.dealer == bve.dealer && storedBve.digest == bve.digest
                && storedBve.commitmentDigest == bve.commitmentDigest,
            "wrong BVE"
        );
    }

    function testEmptyQcPagesAndResultAreExplicit() external {
        (DkgContract dkg,,) = deploySingleRegistrationTarget();
        DkgContract.PcQcPage memory pcPage = dkg.pcQcs(EPOCH, 0, 1);
        DkgContract.BveQcPage memory bvePage = dkg.bveQcs(EPOCH, 0, 1);
        (bool resultExists,,) = dkg.dkgResult(EPOCH);
        require(pcPage.total == 0 && pcPage.next == 0 && pcPage.qcs.length == 0, "nonempty PC page");
        require(bvePage.total == 0 && bvePage.next == 0 && bvePage.qcs.length == 0, "nonempty BVE page");
        require(!resultExists, "unexpected result");
    }

    function testProtocolQcsEmitTypedEvents() external {
        Fixture memory fixture = deploySession();
        DkgContract.PcQc memory pc = pcQc(2, 0x11, 1);
        DkgContract.BveQc memory bve = bveQc(2, 0x22, 1);

        VM.expectEmit(true, true, true, true, address(fixture.dkg));
        emit PcQcPosted(EPOCH, 0, pc.dealer, pc.digest, pc.signatures);
        postPc(fixture, pc);

        VM.expectEmit(true, true, true, true, address(fixture.dkg));
        emit BveQcPosted(EPOCH, 0, bve.dealer, bve.digest, bve.commitmentDigest, bve.signatures);
        postBve(fixture, 2, bve);

        DkgContract.DkgResult memory result = signedResult(fixture, 0x33);
        VM.expectEmit(true, false, false, true, address(fixture.dkg));
        emit DkgResultPosted(EPOCH, result.sessionId, result.bteKey, result.signatures);
        submitResult(fixture, result);
    }

    function testResultIsReadableAsSingleDoneQc() external {
        Fixture memory fixture = deploySession();
        DkgContract.DkgResult memory result = signedResult(fixture, 0x33);
        submitResult(fixture, result);

        (bool exists, uint64 recordedBlock, DkgContract.DkgResult memory recorded) =
            fixture.dkg.dkgResult(EPOCH);
        require(exists, "result missing");
        require(recordedBlock == block.number, "wrong result block");
        require(keccak256(abi.encode(recorded.bteKey)) == keccak256(abi.encode(result.bteKey)), "wrong recovery key");
    }

    function testOnlyActiveAndNextStatesSurviveRollover() external {
        Fixture memory fixture = deploySession();
        postPc(fixture, pcQc(0, 0x11, 1));
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        submitResult(fixture, result);

        require(fixture.dkg.pcQcs(EPOCH, 0, 10).total == 1, "next-epoch PC QC missing");
        (bool nextResultExists,,) = fixture.dkg.dkgResult(EPOCH);
        require(nextResultExists, "next-epoch result missing");

        fixture.staking.setEpoch(EPOCH, false);
        for (uint256 i = 0; i < fixture.validators.length; i++) {
            DkgContract.Registration memory record =
                registrationForEpoch(fixture.validators[i], fixture.qcKeys[i], EPOCH + 1);
            VM.prank(fixture.validators[i]);
            fixture.dkg.register(EPOCH + 1, record);
        }
        require(fixture.dkg.pcQcs(EPOCH, 0, 10).total == 1, "promoted PC QC was lost");
        (bool promotedExists,, DkgContract.DkgResult memory promoted) = fixture.dkg.dkgResult(EPOCH);
        require(promotedExists, "promoted result was lost");
        require(keccak256(abi.encode(promoted.bteKey)) == keccak256(abi.encode(result.bteKey)), "wrong promoted key");

        fixture.staking.setEpoch(EPOCH, true);
        VM.prank(fixture.validators[0]);
        fixture.dkg.postPcQc(EPOCH + 1, pcQc(0, 0x22, 1));

        fixture.staking.setEpoch(EPOCH + 1, false);
        for (uint256 i = 0; i < fixture.validators.length; i++) {
            DkgContract.Registration memory record =
                registrationForEpoch(fixture.validators[i], fixture.qcKeys[i], EPOCH + 2);
            VM.prank(fixture.validators[i]);
            fixture.dkg.register(EPOCH + 2, record);
        }
        require(fixture.dkg.pcQcs(EPOCH + 1, 0, 10).total == 1, "active state was not retained");
        require(fixture.dkg.pcQcs(EPOCH, 0, 10).total == 0, "retired PC QCs remain reachable");
        (bool retiredResultExists,,) = fixture.dkg.dkgResult(EPOCH);
        require(!retiredResultExists, "retired result remains reachable");
        (bool oldRegistration,) = fixture.dkg.registrationOf(EPOCH, 1);
        require(!oldRegistration, "retired registration remains reachable");

        fixture.staking.setEpoch(EPOCH + 1, true);
        VM.prank(fixture.validators[0]);
        fixture.dkg.postPcQc(EPOCH + 2, pcQc(0, 0x33, 1));
        DkgContract.PcQcPage memory reused = fixture.dkg.pcQcs(EPOCH + 2, 0, 10);
        require(reused.total == 1, "recycled collection count leaked");
        require(reused.qcs[0].digest == bytes32(uint256(0x33)), "recycled record was not overwritten");

        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.postPcQc(EPOCH, pcQc(0, 0x44, 1));
    }

    function testEpochJumpResetsBothSlots() external {
        (DkgContract dkg, TestValidatorLookup staking, address validator) = deploySingleRegistrationTarget();
        DkgContract.Registration memory initial = registration(validator, 1);
        VM.prank(validator);
        dkg.register(EPOCH, initial);

        staking.setEpoch(EPOCH + 3, false);
        DkgContract.Registration memory jumped = registrationForEpoch(validator, 1, EPOCH + 4);
        VM.prank(validator);
        dkg.register(EPOCH + 4, jumped);

        (bool oldRegistration,) = dkg.registrationOf(EPOCH, 1);
        require(!oldRegistration, "jump retained stale registration");
        require(dkg.pcQcs(EPOCH, 0, 1).total == 0, "jump retained stale PC QCs");
        require(dkg.bveQcs(EPOCH, 0, 1).total == 0, "jump retained stale BVE QCs");
        (bool staleResultExists,,) = dkg.dkgResult(EPOCH);
        require(!staleResultExists, "jump retained stale result");
        (bool newRegistration,) = dkg.registrationOf(EPOCH + 4, 1);
        require(newRegistration, "jumped next state was not initialized");
    }

    function testPcQcIsBoundedPerDealer() external {
        Fixture memory fixture = deploySession();
        DkgContract.PcQc memory original = pcQc(3, 0x11, 1);

        postPc(fixture, original);
        postPc(fixture, original);
        require(recordTotal(fixture.dkg) == 1, "identical QC was recorded twice");

        DkgContract.PcQc memory alternateWitness = pcQc(3, 0x11, 2);
        postPc(fixture, alternateWitness);
        require(recordTotal(fixture.dkg) == 1, "submitter posted two witnesses for one dealer");

        VM.expectRevert();
        postPcAs(fixture, 1, alternateWitness);
        require(recordTotal(fixture.dkg) == 1, "non-dealer posted a PC QC");
    }

    function testBveQcRequiresPcQcFromItsDealer() external {
        Fixture memory fixture = deploySession();
        DkgContract.BveQc memory bve = bveQc(3, 0x11, 1);

        VM.expectRevert();
        postBve(fixture, 3, bve);

        postPc(fixture, pcQc(3, 0x10, 1));

        VM.expectRevert();
        postBve(fixture, 0, bve);

        postBve(fixture, 3, bve);
        postBve(fixture, 3, bveQc(3, 0x11, 2));
        require(fixture.dkg.bveQcs(EPOCH, 0, 10).total == 1, "dealer posted two BVE QCs");
    }

    function testMalformedQcCannotOccupyQcSlot() external {
        Fixture memory fixture = deploySession();
        DkgContract.PcQc memory malformed = pcQc(1, 0x11, 1);
        malformed.signatures[0].signer = 4;

        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.postPcQc(EPOCH, malformed);

        malformed = pcQc(4, 0x11, 1);
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.postPcQc(EPOCH, malformed);
    }

    function testSubmitResultVerifiesQuorumSignatures() external {
        Fixture memory fixture = deploySession();
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        submitResult(fixture, result);

        (bool exists,, DkgContract.DkgResult memory recorded) = fixture.dkg.dkgResult(EPOCH);
        require(exists, "result missing");
        require(recorded.sessionId == result.sessionId, "wrong session id");
        require(recorded.bteKey[0] == result.bteKey[0], "wrong result key");

        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);
    }

    function testSubmitResultUsesConsensusStakeDuringTargetEpoch() external {
        Fixture memory fixture = deploySession();
        // The party set was already persisted, so this proves DONE reads stake
        // at verification instead of persisting it with the party IDs.
        postPc(fixture, pcQc(0, 0x11, 1));
        fixture.staking.setConsensusStake(fixture.validators[0], 7 ether);
        fixture.staking.setEpoch(EPOCH, false);
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        DkgContract.QcSignature[] memory highStakeQuorum = new DkgContract.QcSignature[](1);
        highStakeQuorum[0] = result.signatures[0];
        result.signatures = highStakeQuorum;
        submitResult(fixture, result);
    }

    function testSubmitResultUsesSnapshotStakeAfterTargetBoundary() external {
        Fixture memory fixture = deploySession();
        postPc(fixture, pcQc(0, 0x11, 1));
        fixture.staking.setSnapshotStake(fixture.validators[0], 7 ether);
        fixture.staking.setEpoch(EPOCH, true);

        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        DkgContract.QcSignature[] memory highStakeQuorum = new DkgContract.QcSignature[](1);
        highStakeQuorum[0] = result.signatures[0];
        result.signatures = highStakeQuorum;
        submitResult(fixture, result);
    }

    function testSubmitResultRejectsAfterStakeWindowExpires() external {
        Fixture memory fixture = deploySession();
        postPc(fixture, pcQc(0, 0x11, 1));
        fixture.staking.setEpoch(EPOCH + 1, false);
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);

        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);
    }

    function testSubmitResultUsesExactStakeWithoutUnitRounding() external {
        Fixture memory fixture = deploySession();
        fixture.staking.setStake(fixture.validators[0], 6 ether + 0.5 ether);
        for (uint256 i = 1; i < fixture.validators.length; i++) {
            fixture.staking.setStake(fixture.validators[i], 1 ether + 0.49 ether);
        }
        DkgContract.DkgResult memory fullResult = signedResult(fixture, 0x44);
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        DkgContract.QcSignature[] memory subQuorum = new DkgContract.QcSignature[](1);
        subQuorum[0] = result.signatures[0];
        result.signatures = subQuorum;
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);

        DkgContract.QcSignature[] memory exactQuorum = new DkgContract.QcSignature[](2);
        exactQuorum[0] = fullResult.signatures[0];
        exactQuorum[1] = fullResult.signatures[1];
        result.signatures = exactQuorum;
        submitResult(fixture, result);
    }

    function testSinglePartySetCanPost() external {
        (DkgContract dkg, TestValidatorLookup staking, address validator) = deploySingleRegistrationTarget();
        uint256 qcKey = 1;
        DkgContract.Registration memory record = registration(validator, qcKey);
        VM.prank(validator);
        dkg.register(EPOCH, record);
        staking.setEpoch(6, true);
        VM.prank(validator);
        dkg.postPcQc(EPOCH, pcQc(0, 0x11, 1));
        require(dkg.pcQcs(EPOCH, 0, 1).total == 1, "singleton party set was rejected");
    }

    function testSubmitResultRejectsTamperedKeyAndSignature() external {
        Fixture memory fixture = deploySession();
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        result.sessionId = bytes32(uint256(result.sessionId) ^ 1);
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);

        result = signedResult(fixture, 0x44);
        result.bteKey[5] = bytes32(uint256(result.bteKey[5]) + 1);
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);

        result = signedResult(fixture, 0x44);
        result.signatures[1].s = bytes32(uint256(result.signatures[1].s) ^ 1);
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);
    }

    function testDoneQcRequiresCanonicalSignerOrder() external {
        Fixture memory fixture = deploySession();
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        (result.signatures[0], result.signatures[2]) = (result.signatures[2], result.signatures[0]);
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);

        result = signedResult(fixture, 0x44);
        result.signatures[2] = result.signatures[1];
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);
    }

    function testSubmitResultRejectsSubQuorumAndWrongPartyId() external {
        Fixture memory fixture = deploySession();
        DkgContract.DkgResult memory result = signedResult(fixture, 0x44);
        DkgContract.QcSignature[] memory subQuorum = new DkgContract.QcSignature[](2);
        for (uint256 i = 0; i < 2; i++) {
            subQuorum[i] = result.signatures[i];
        }
        result.signatures = subQuorum;
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);

        result = signedResult(fixture, 0x44);
        result.signatures[2].signer = 3;
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);
    }

    function testDoneQcMakesEpochTerminal() external {
        Fixture memory fixture = deploySession();
        submitResult(fixture, signedResult(fixture, 0x44));

        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.postPcQc(EPOCH, pcQc(1, 0x11, 1));
        VM.expectRevert();
        VM.prank(fixture.validators[0]);
        fixture.dkg.postBveQc(EPOCH, bveQc(1, 0x11, 1));
    }

    function deploySession() private returns (Fixture memory fixture) {
        fixture.staking = new TestValidatorLookup();
        fixture.dkg = new DkgContract(address(fixture.staking));
        for (uint256 i = 0; i < 4; i++) {
            fixture.validators[i] = VM.addr(100 + i);
            fixture.qcKeys[i] = i == 3 ? 6 : i + 1;
            fixture.staking.addTarget(fixture.validators[i]);
            DkgContract.Registration memory record = registration(fixture.validators[i], fixture.qcKeys[i]);
            VM.prank(fixture.validators[i]);
            fixture.dkg.register(EPOCH, record);
        }
        fixture.staking.setEpoch(6, true);
    }

    function deploySingleRegistrationTarget()
        private
        returns (DkgContract dkg, TestValidatorLookup staking, address validator)
    {
        staking = new TestValidatorLookup();
        validator = VM.addr(100);
        staking.addTarget(validator);
        dkg = new DkgContract(address(staking));
    }

    function postPc(Fixture memory fixture, DkgContract.PcQc memory qc) private {
        postPcAs(fixture, qc.dealer, qc);
    }

    function postPcAs(Fixture memory fixture, uint256 validatorIndex, DkgContract.PcQc memory qc) private {
        VM.prank(fixture.validators[validatorIndex]);
        fixture.dkg.postPcQc(EPOCH, qc);
    }

    function postBve(Fixture memory fixture, uint256 validatorIndex, DkgContract.BveQc memory qc) private {
        VM.prank(fixture.validators[validatorIndex]);
        fixture.dkg.postBveQc(EPOCH, qc);
    }

    function submitResult(Fixture memory fixture, DkgContract.DkgResult memory result) private {
        VM.prank(fixture.validators[0]);
        fixture.dkg.submitResult(EPOCH, result);
    }

    function recordTotal(DkgContract dkg) private view returns (uint64) {
        uint64 total = dkg.pcQcs(EPOCH, 0, 1).total + dkg.bveQcs(EPOCH, 0, 1).total;
        (bool resultExists,,) = dkg.dkgResult(EPOCH);
        return total + (resultExists ? 1 : 0);
    }

    function registration(address party, uint256 qcKey) private pure returns (DkgContract.Registration memory result) {
        return registrationForEpoch(party, qcKey, EPOCH);
    }

    function registrationForEpoch(address party, uint256 qcKey, uint64 epoch)
        private
        pure
        returns (DkgContract.Registration memory result)
    {
        result.qcVerifier = VM.addr(qcKey);
        uint256 receiverKey = 1001;
        result.receiverPublicKey =
            DkgContract.SecpPoint({prefix: 3, x: 0x9d1abaec9f5715a15c7628244170951e0f85e87f68ca5393d3f9fc3fa23a69c8});
        bytes32 digest = receiverKeyProofDigestForEpoch(
            epoch, party, result.qcVerifier, result.receiverPublicKey, result.receiverProofNonce
        );
        (, result.receiverProofR, result.receiverProofS) = VM.sign(receiverKey, digest);
    }

    function receiverKeyProofDigest(
        address party,
        address qcVerifier,
        DkgContract.SecpPoint memory receiverKey,
        uint32 proofNonce
    ) private pure returns (bytes32) {
        return receiverKeyProofDigestForEpoch(EPOCH, party, qcVerifier, receiverKey, proofNonce);
    }

    function receiverKeyProofDigestForEpoch(
        uint64 epoch,
        address party,
        address qcVerifier,
        DkgContract.SecpPoint memory receiverKey,
        uint32 proofNonce
    ) private pure returns (bytes32) {
        return sha256(
            abi.encodePacked(
                "BTX-DKG/protocol/receiver-key-pop/v1",
                party,
                _le64(epoch),
                qcVerifier,
                receiverKey.prefix,
                receiverKey.x,
                _le32(proofNonce)
            )
        );
    }

    function pcQc(uint32 dealer, uint8 digest, uint8 witness) private pure returns (DkgContract.PcQc memory) {
        return DkgContract.PcQc({dealer: dealer, digest: bytes32(uint256(digest)), signatures: signatures(witness)});
    }

    function bveQc(uint32 dealer, uint8 digest, uint8 witness) private pure returns (DkgContract.BveQc memory) {
        return DkgContract.BveQc({
            dealer: dealer,
            digest: bytes32(uint256(digest)),
            commitmentDigest: bytes32(uint256(digest + 1)),
            signatures: signatures(witness)
        });
    }

    function signatures(uint8 witness) private pure returns (DkgContract.QcSignature[] memory result) {
        result = new DkgContract.QcSignature[](1);
        result[0] = DkgContract.QcSignature({signer: 0, r: bytes32(uint256(witness)), s: bytes32(uint256(witness + 1))});
    }

    function signedResult(Fixture memory fixture, uint8 pointByte)
        private
        pure
        returns (DkgContract.DkgResult memory result)
    {
        for (uint256 i = 0; i < 18; i++) {
            result.bteKey[i] = bytes32(uint256(pointByte) + i);
        }
        result.sessionId = deriveSessionId(EPOCH, fixture.validators, fixture.qcKeys);
        bytes32 digest = doneQcDigest(EPOCH, result.sessionId, result.bteKey);
        result.signatures = new DkgContract.QcSignature[](3);
        for (uint32 i = 0; i < 3; i++) {
            (, bytes32 r, bytes32 s) = VM.sign(fixture.qcKeys[i], digest);
            result.signatures[i] = DkgContract.QcSignature({signer: i, r: r, s: s});
        }
    }

    function deriveSessionId(uint64 epoch, address[4] memory parties, uint256[4] memory keys)
        private
        pure
        returns (bytes32)
    {
        bytes memory session = abi.encodePacked(
            "BTX-DKG/protocol/session-id/v1", _le64(epoch), _le64(4), _le32(0), _le32(1), _le32(2), _le32(3), _le64(4)
        );
        for (uint256 i = 0; i < 4; i++) {
            session = bytes.concat(session, _le64(1));
        }
        session = bytes.concat(session, _le64(1), _le64(3), _le64(3), _le64(4));
        for (uint256 i = 0; i < 4; i++) {
            session = bytes.concat(session, bytes20(VM.addr(keys[i])));
        }
        session = bytes.concat(session, _le64(4));
        for (uint256 i = 0; i < 4; i++) {
            session = bytes.concat(session, bytes20(parties[i]));
        }
        return sha256(session);
    }

    function doneQcDigest(uint64 epoch, bytes32 sessionId, bytes32[18] memory bteKey) private pure returns (bytes32) {
        return sha256(
            abi.encodePacked(
                "BTX-DKG/protocol/qc-signature/v1",
                uint64(31),
                "BTX-DKG/protocol/dkg-done-qc/v1",
                epoch,
                uint64(32),
                sessionId,
                bteKey
            )
        );
    }

    function _le32(uint32 value) private pure returns (bytes4 result) {
        uint32 reversed;
        for (uint256 i = 0; i < 4; i++) {
            reversed |= uint32(uint8(value >> (i * 8))) << uint32((3 - i) * 8);
        }
        return bytes4(reversed);
    }

    function _le64(uint64 value) private pure returns (bytes8 result) {
        uint64 reversed;
        for (uint256 i = 0; i < 8; i++) {
            reversed |= uint64(uint8(value >> (i * 8))) << uint64((7 - i) * 8);
        }
        return bytes8(reversed);
    }
}
