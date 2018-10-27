/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
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

/* Create new bit-vector domain with low 'lo' and high 'hi'.
 * Creates copies of lo and hi. */
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
 * (all values possible). Note: 'res_d_z' is optional and can be NULL.
 */
bool btor_bvprop_eq (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain **res_d_xy,
                     BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = ~x. */
bool btor_bvprop_not (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x << n where n is const. */
bool btor_bvprop_sll_const (BtorMemMgr *mm,
                            BtorBvDomain *d_x,
                            BtorBvDomain *d_z,
                            BtorBitVector *n,
                            BtorBvDomain **res_d_x,
                            BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x >> n where n is const. */
bool btor_bvprop_srl_const (BtorMemMgr *mm,
                            BtorBvDomain *d_x,
                            BtorBvDomain *d_z,
                            BtorBitVector *n,
                            BtorBvDomain **res_d_x,
                            BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x & y. */
bool btor_bvprop_and (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x | y. */
bool btor_bvprop_or (BtorMemMgr *mm,
                     BtorBvDomain *d_x,
                     BtorBvDomain *d_y,
                     BtorBvDomain *d_z,
                     BtorBvDomain **res_d_x,
                     BtorBvDomain **res_d_y,
                     BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x | y. */
bool btor_bvprop_xor (BtorMemMgr *mm,
                      BtorBvDomain *d_x,
                      BtorBvDomain *d_y,
                      BtorBvDomain *d_z,
                      BtorBvDomain **res_d_x,
                      BtorBvDomain **res_d_y,
                      BtorBvDomain **res_d_z);

/* Propagate domains 'd_x' and 'd_z' of z = x[upper:lower]. */
bool btor_bvprop_slice (BtorMemMgr *mm,
                        BtorBvDomain *d_x,
                        BtorBvDomain *d_z,
                        uint32_t upper,
                        uint32_t lower,
                        BtorBvDomain **res_d_x,
                        BtorBvDomain **res_d_z);

/* Propagate domains 'd_x', 'd_y' and 'd_z' of z = x o y. */
bool btor_bvprop_concat (BtorMemMgr *mm,
                         BtorBvDomain *d_x,
                         BtorBvDomain *d_y,
                         BtorBvDomain *d_z,
                         BtorBvDomain **res_d_y,
                         BtorBvDomain **res_d_x,
                         BtorBvDomain **res_d_z);

// TODO:
// propagators:
//
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
