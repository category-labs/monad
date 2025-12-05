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

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_revision
{
    MONAD_ZERO = 0,
    MONAD_ONE = 1,
    MONAD_TWO = 2,
    MONAD_THREE = 3,
    MONAD_FOUR = 4,
    MONAD_FIVE = 5,
    MONAD_SIX = 6,
    MONAD_SEVEN = 7,
    MONAD_EIGHT = 8,
    MONAD_NEXT = 9
};

inline char const *monad_revision_to_string(enum monad_revision const rev)
{
    switch (rev) {
    case MONAD_ZERO:
        return "MONAD_ZERO";
    case MONAD_ONE:
        return "MONAD_ONE";
    case MONAD_TWO:
        return "MONAD_TWO";
    case MONAD_THREE:
        return "MONAD_THREE";
    case MONAD_FOUR:
        return "MONAD_FOUR";
    case MONAD_FIVE:
        return "MONAD_FIVE";
    case MONAD_SIX:
        return "MONAD_SIX";
    case MONAD_SEVEN:
        return "MONAD_SEVEN";
    case MONAD_EIGHT:
        return "MONAD_EIGHT";
    case MONAD_NEXT:
        return "MONAD_NEXT";
    }
    return ""; // unreachable
}

#ifdef __cplusplus
}
#endif
