// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <string>

static std::string const base_gtest_filter =
    ":-"
    // Slow
    "GeneralStateTests/VMTests/vmPerformance.loopExp:"
    "GeneralStateTests/VMTests/vmPerformance.loopMul:"
    "GeneralStateTests/stTimeConsuming.CALLBlake2f_MaxRounds:"
    "GeneralStateTests/stTimeConsuming.static_Call50000_sha256:"
    // Failing on the evmone base branch/tag
    "ValidBlocks/bcValidBlockTest.SimpleTx3LowS:"
    "TransitionTests/bcArrowGlacierToParis.difficultyFormula:"
    "TransitionTests/bcArrowGlacierToParis.powToPosBlockRejection:"
    "TransitionTests/bcArrowGlacierToParis.powToPosTest:"
    "TransitionTests/bcBerlinToLondon.BerlinToLondonTransition:"
    "TransitionTests/bcBerlinToLondon.initialVal:"
    "TransitionTests/bcBerlinToLondon.londonUncles:"
    "TransitionTests/"
    "bcByzantiumToConstantinopleFix.ConstantinopleFixTransition:"
    "TransitionTests/bcEIP158ToByzantium.ByzantiumTransition:"
    "TransitionTests/"
    "bcFrontierToHomestead."
    "CallContractThatCreateContractBeforeAndAfterSwitchover:"
    "TransitionTests/bcFrontierToHomestead.ContractCreationFailsOnHomestead:"
    "TransitionTests/bcFrontierToHomestead.HomesteadOverrideFrontier:"
    "TransitionTests/bcFrontierToHomestead.UncleFromFrontierInHomestead:"
    "TransitionTests/bcFrontierToHomestead.UnclePopulation:"
    "TransitionTests/"
    "bcFrontierToHomestead.blockChainFrontierWithLargerTDvsHomesteadBlockchain:"
    "TransitionTests/"
    "bcFrontierToHomestead."
    "blockChainFrontierWithLargerTDvsHomesteadBlockchain2:"
    "TransitionTests/bcHomesteadToDao.DaoTransactions:"
    "TransitionTests/"
    "bcHomesteadToDao.DaoTransactions_EmptyTransactionAndForkBlocksAhead:"
    "TransitionTests/bcHomesteadToDao.DaoTransactions_UncleExtradata:"
    "TransitionTests/bcHomesteadToDao.DaoTransactions_XBlockm1:"
    "TransitionTests/bcHomesteadToEIP150.EIP150Transition:"
    "TransitionTests/bcMergeToShanghai.shanghaiBeforeTransition:";
