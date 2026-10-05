// Copyright (C) 2026 Category Labs, Inc.
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

// int8 x int8 -> int32. linalg.matmul sign-extends the inputs to i32 before
// multiplying. With uint16 dimensions |sum| <= 65535 * 128 * 128 < 2^31, so the
// result is always exact.
//
// %out is caller-provided storage for the result (iree.abi.output), so the
// result is written into it instead of a buffer IREE allocates.
func.func @matmul_i8(%lhs: tensor<?x?xi8>, %rhs: tensor<?x?xi8>,
                  %out: tensor<?x?xi32> {iree.abi.output = 0 : index})
    -> tensor<?x?xi32> {
  %c0 = arith.constant 0 : index
  %c1 = arith.constant 1 : index
  %zero = arith.constant 0 : i32
  %m = tensor.dim %lhs, %c0 : tensor<?x?xi8>
  %n = tensor.dim %rhs, %c1 : tensor<?x?xi8>
  %empty = tensor.empty(%m, %n) : tensor<?x?xi32>
  %init = linalg.fill ins(%zero : i32)
      outs(%empty : tensor<?x?xi32>) -> tensor<?x?xi32>
  %result = linalg.matmul ins(%lhs, %rhs : tensor<?x?xi8>, tensor<?x?xi8>)
      outs(%init : tensor<?x?xi32>) -> tensor<?x?xi32>
  return %result : tensor<?x?xi32>
}

func.func @add_i8(%lhs: tensor<?xi8>, %rhs: tensor<?xi8>,
               %out: tensor<?xi16> {iree.abi.output = 0 : index})
    -> tensor<?xi16> {
  %c0 = arith.constant 0 : index
  %length = tensor.dim %lhs, %c0 : tensor<?xi8>
  %empty = tensor.empty(%length) : tensor<?xi16>

  %result = linalg.generic {
    indexing_maps = [affine_map<(i) -> (i)>,affine_map<(i) -> (i)>,affine_map<(i) -> (i)>],
    iterator_types = ["parallel"]
  } ins(%lhs, %rhs : tensor<?xi8>, tensor<?xi8>)
    outs(%empty : tensor<?xi16>) {
    ^bb0(%lhs_element: i8, %rhs_element: i8, %unused: i16):
      %lhs_wide = arith.extsi %lhs_element : i8 to i16
      %rhs_wide = arith.extsi %rhs_element : i8 to i16
      %sum = arith.addi %lhs_wide, %rhs_wide : i16
      linalg.yield %sum : i16
  } -> tensor<?xi16>

  return %result : tensor<?xi16>
}

func.func @add_i16(%lhs: tensor<?xi16>, %rhs: tensor<?xi16>,
               %out: tensor<?xi32> {iree.abi.output = 0 : index})
    -> tensor<?xi32> {
  %c0 = arith.constant 0 : index
  %length = tensor.dim %lhs, %c0 : tensor<?xi16>
  %empty = tensor.empty(%length) : tensor<?xi32>

  %result = linalg.generic {
    indexing_maps = [affine_map<(i) -> (i)>,affine_map<(i) -> (i)>,affine_map<(i) -> (i)>],
    iterator_types = ["parallel"]
  } ins(%lhs, %rhs : tensor<?xi16>, tensor<?xi16>)
    outs(%empty : tensor<?xi32>) {
    ^bb0(%lhs_element: i16, %rhs_element: i16, %unused: i32):
      %lhs_wide = arith.extsi %lhs_element : i16 to i32
      %rhs_wide = arith.extsi %rhs_element : i16 to i32
      %sum = arith.addi %lhs_wide, %rhs_wide : i32
      linalg.yield %sum : i32
  } -> tensor<?xi32>

  return %result : tensor<?xi32>
}

func.func @add_i32(%lhs: tensor<?xi32>, %rhs: tensor<?xi32>,
               %out: tensor<?xi64> {iree.abi.output = 0 : index})
    -> tensor<?xi64> {
  %c0 = arith.constant 0 : index
  %length = tensor.dim %lhs, %c0 : tensor<?xi32>
  %empty = tensor.empty(%length) : tensor<?xi64>

  %result = linalg.generic {
    indexing_maps = [affine_map<(i) -> (i)>,affine_map<(i) -> (i)>,affine_map<(i) -> (i)>],
    iterator_types = ["parallel"]
  } ins(%lhs, %rhs : tensor<?xi32>, tensor<?xi32>)
    outs(%empty : tensor<?xi64>) {
    ^bb0(%lhs_element: i32, %rhs_element: i32, %unused: i64):
      %lhs_wide = arith.extsi %lhs_element : i32 to i64
      %rhs_wide = arith.extsi %rhs_element : i32 to i64
      %sum = arith.addi %lhs_wide, %rhs_wide : i64
      linalg.yield %sum : i64
  } -> tensor<?xi64>

  return %result : tensor<?xi64>
}
