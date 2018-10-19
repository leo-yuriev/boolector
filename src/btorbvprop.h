/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBVPROP_H_INCLUDED
#define BTORBVPROP_H_INCLUDED

#include "btorbv.h"

struct BtorBvDomain
{
  BtorBitVector *lo;
  BtorBitVector *hi;
};

typedef struct BtorBvDomain BtorBvDomain;

/* Create new bit-vector domain of width 'width' with low 0 and high ~0. */
BtorBvDomain *btor_bvprop_new_init (BtorMemMgr *mm, uint32_t width);

/* Create new bit-vector domain with low 'lo' and high 'hi'. Makes copies of
 * lo/hi. */
BtorBvDomain *btor_bvprop_new (BtorMemMgr *mm,
                               const BtorBitVector *lo,
                               const BtorBitVector *hi);

/* Delete bit-vector domain. */
void btor_bvprop_free (BtorMemMgr *mm, BtorBvDomain *d);

/* Check whether bit-vector domain is valid, i.e., ~lo | hi == ones. */
bool btor_bvprop_is_valid (BtorMemMgr *mm, const BtorBvDomain *d);

/* Check whether bit-vector domain is fixed, i.e., lo == hi */
bool btor_bvprop_is_fixed (BtorMemMgr *mm, const BtorBvDomain *d);

/* Propagate domains 'd_x' and 'd_y' of z = (x = y). The domains for 'x' and
 * 'y' are either the same or the resulting domain 'res_xy' is invalid.
 * Domain 'res_d_z' is either fixed (if res_d_xy is fixed or invalid) or valid
 * (all values possible).
 */
void btor_bvprop_eq (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain **res_d_xy,
                     BtorBvDomain **res_d_z);

// TODO:
// propagators:
//
// y = x
// y = ~x
// z = x & y
// y = x << n
// y = x >> n
// z = x o y
// y = x[n:m]
// x < y
//
//
// decomposed propagators:
// z = ite(b,x,y)
// z = x + y
// z = x * y
// z = x udiv y
// z = x urem y
#endif
