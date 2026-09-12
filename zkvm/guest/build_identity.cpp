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

// Keep the commit stamp separate so a rebase rebuilds only this small object.
#ifdef MONAD_ZKVM_OFFICIAL_PROFILE
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] =
    "monad-zkvm-official;commit=" MONAD_ZKVM_BUILD_COMMIT;
#elif defined(MONAD_ZKVM_DEV_PROFILE)
extern "C" [[gnu::used, gnu::section(".monad_zkvm_profile")]]
unsigned char const monad_zkvm_official_profile[] = "monad-zkvm-dev";
#endif
