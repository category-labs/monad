/*
   Copyright 2022 The Silkpre Authors

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

#ifndef SILKPRE_SECP256K1N_HPP_
#define SILKPRE_SECP256K1N_HPP_

// See Yellow Paper, Appendix F "Signing Transactions"
// and EIP-2: Homestead Hard-fork Changes.

#include <optional>

#include <intx/intx.hpp>

namespace silkpre {

// See Appendix F "Signing Transactions" of the Yellow Paper.
inline constexpr auto kSecp256k1n{
    intx::from_string<intx::uint256>("0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141")};

inline constexpr auto kSecp256k1Halfn{kSecp256k1n >> 1};

// Verifies whether the signature values are valid with
// the given chain rules.
//! Verifies whether the signature values are valid with the provided chain rules
//! \param [in] r : signature's r
//! \param [in] s : signature's s
//! \param [in] homestead : whether the chain has homestead rules
//! \return True or false
bool is_valid_signature(const intx::uint256& r, const intx::uint256& s, bool homestead) noexcept;

}  // namespace silkpre

#endif  // SILKPRE_SECP256K1N_HPP_
