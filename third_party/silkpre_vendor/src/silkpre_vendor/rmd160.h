/********************************************************************\
 *
 *      FILE:     rmd160.h
 *
 *      CONTENTS: Header file for a sample C-implementation of the
 *                RIPEMD-160 hash-function.
 *      TARGET:   any computer with an ANSI C compiler
 *
 *      AUTHOR:   Antoon Bosselaers, ESAT-COSIC
 *      DATE:     1 March 1996
 *      MODIFIED: 2020-2022 by Andrew Ashikhmin
 *
 *      Copyright (c) 1996 Katholieke Universiteit Leuven
 *
 *      Permission is hereby granted, free of charge, to any person
 *      obtaining a copy of this software and associated documentation
 *      files (the "Software"), to deal in the Software without restriction,
 *      including without limitation the rights to use, copy, modify, merge,
 *      publish, distribute, sublicense, and/or sell copies of the Software,
 *      and to permit persons to whom the Software is furnished to do so,
 *      subject to the following conditions:
 *
 *      The above copyright notice and this permission notice shall be
 *      included in all copies or substantial portions of the Software.
 *
 *      THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *      EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *      MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 *      IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 *      CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 *      TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 *      SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *      Modified 2022 for Silkpre by Andrew Ashikhmin.
 *
\********************************************************************/

#ifndef SILKPRE_RMD160_H_
#define SILKPRE_RMD160_H_

#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

void silkpre_rmd160(uint8_t out[20], const uint8_t* input, size_t len);

#if defined(__cplusplus)
}
#endif

#endif  // SILKPRE_RMD160_H_
