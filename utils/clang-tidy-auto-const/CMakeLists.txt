# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

find_package(LLVM 19.1.7 REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)

add_library(ConstCorrectnessChecks SHARED "")
target_compile_options(ConstCorrectnessChecks PRIVATE -fno-rtti)
target_include_directories(
  ConstCorrectnessChecks
  PRIVATE ${CLANG_INCLUDE_DIRS}
          ${LLVM_INCLUDE_DIRS}
)
target_sources(
  ConstCorrectnessChecks
  PRIVATE "ExprAutoMutationAnalyzer.hpp"
          "ExprAutoMutationAnalyzer.cpp"
          "AutoConstCorrectnessCheck.hpp"
          "AutoConstCorrectnessCheck.cpp"
          "MiscUpdateModule.cpp"
)
