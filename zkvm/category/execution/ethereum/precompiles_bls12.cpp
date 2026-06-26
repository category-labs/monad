// Copyright (C) 2025-26 Category Labs, Inc.
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

// zkVM shadow of precompiles_bls12.cpp. The host TU is dropped from the guest
// build because its precompile execute paths call into blst, which is not
// ported to the bare-metal RISC-V guest. The MSM gas-cost path, however, is
// pure table lookup and is reached from precompiles_gas_cost_impl.cpp (which
// the guest keeps) for Prague+ revisions. Provide just the two msm_discount
// specializations; the blst-backed execute functions stay out of the guest.

#include <category/execution/ethereum/precompiles_bls12.hpp>

#include <algorithm>
#include <array>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

namespace bls12
{
    template <>
    uint16_t msm_discount<G1>(uint64_t const k)
    {
        MONAD_ASSERT(k > 0);

        static constexpr auto table = std::array<uint16_t, 128>{
            1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692,
            687,  682, 677, 673, 669, 665, 661, 658, 654, 651, 648, 645, 642,
            640,  637, 635, 632, 630, 627, 625, 623, 621, 619, 617, 615, 613,
            611,  609, 608, 606, 604, 603, 601, 599, 598, 596, 595, 593, 592,
            591,  589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576, 575,
            574,  573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561,
            560,  559, 558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548,
            547,  547, 546, 545, 544, 543, 542, 541, 540, 540, 539, 538, 537,
            536,  536, 535, 534, 533, 532, 532, 531, 530, 529, 528, 528, 527,
            526,  525, 525, 524, 523, 522, 522, 521, 520, 520, 519};

        return table[std::min(k, 128ul) - 1];
    }

    template <>
    uint16_t msm_discount<G2>(uint64_t const k)
    {
        MONAD_ASSERT(k > 0);

        static constexpr auto table = std::array<uint16_t, 128>{
            1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740,
            732,  724,  717, 711, 704, 699, 693, 688, 683, 679, 674, 670, 666,
            663,  659,  655, 652, 649, 646, 643, 640, 637, 634, 632, 629, 627,
            624,  622,  620, 618, 615, 613, 611, 609, 607, 606, 604, 602, 600,
            598,  597,  595, 593, 592, 590, 589, 587, 586, 584, 583, 582, 580,
            579,  578,  576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565,
            563,  562,  561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552,
            551,  550,  549, 548, 547, 546, 545, 545, 544, 543, 542, 541, 541,
            540,  539,  538, 537, 537, 536, 535, 535, 534, 533, 532, 532, 531,
            530,  530,  529, 528, 528, 527, 526, 526, 525, 524, 524};

        return table[std::min(k, 128ul) - 1];
    }
}

MONAD_NAMESPACE_END
