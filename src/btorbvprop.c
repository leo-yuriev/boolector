/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 *
 *  Bit-vector operator propagators based on [1] and [2].
 *
 *  [1] Wenxi Wang, Harald SøndergaardPeter J. Stuckey:
 *      A Bit-Vector Solver with Word-Level Propagation
 *  [2] L. Michel, P. Van Hentenryck:
 *      Constraint Satisfaction over Bit-Vectors
 */

#include "btorbvprop.h"

static BtorBvDomain *
new_domain (BtorMemMgr *mm)
{
  BtorBvDomain *res;
  BTOR_CNEW (mm, res);
  return res;
}

BtorBvDomain *
btor_bvprop_new_init (BtorMemMgr *mm, uint32_t width)
{
  assert (mm);
  BtorBvDomain *res = new_domain (mm);
  res->lo = btor_bv_zero (mm, width);
  res->hi = btor_bv_ones (mm, width);
  return res;
}

BtorBvDomain *
btor_bvprop_new (BtorMemMgr *mm,
                 const BtorBitVector *lo,
                 const BtorBitVector *hi)
{
  assert (mm);
  assert (lo);
  assert (hi);
  assert (lo->width == hi->width);

  BtorBvDomain *res = new_domain (mm);
  res->lo = btor_bv_copy (mm, lo);
  res->hi = btor_bv_copy (mm, hi);
  return res;
}

void
btor_bvprop_free (BtorMemMgr *mm, BtorBvDomain *d)
{
  assert (mm);
  assert (d);

  btor_bv_free (mm, d->lo);
  btor_bv_free (mm, d->hi);
  BTOR_DELETE (mm, d);
}

bool
btor_bvprop_is_valid (BtorMemMgr *mm, const BtorBvDomain *d)
{
  BtorBitVector *not_lo       = btor_bv_not (mm, d->lo);
  BtorBitVector *not_lo_or_hi = btor_bv_or (mm, not_lo, d->hi);
  bool res                    = btor_bv_is_ones (not_lo_or_hi);
  btor_bv_free (mm, not_lo);
  btor_bv_free (mm, not_lo_or_hi);
  return res;
}

bool
btor_bvprop_is_fixed (BtorMemMgr *mm, const BtorBvDomain *d)
{
  BtorBitVector *equal = btor_bv_eq (mm, d->lo, d->hi);
  bool res             = btor_bv_is_true (equal);
  btor_bv_free (mm, equal);
  return res;
}

void
btor_bvprop_eq (BtorMemMgr *mm,
                BtorBvDomain *d_x,
                BtorBvDomain *d_y,
                BtorBvDomain **res_d_xy,
                BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (d_y);

  *res_d_xy       = new_domain (mm);
  (*res_d_xy)->lo = btor_bv_or (mm, d_x->lo, d_y->lo);
  (*res_d_xy)->hi = btor_bv_and (mm, d_x->hi, d_y->hi);

  if (btor_bvprop_is_valid (mm, *res_d_xy))
  {
    /* Domain is valid and fixed: equality is true. */
    if (btor_bvprop_is_fixed (mm, *res_d_xy))
    {
      *res_d_z       = new_domain (mm);
      (*res_d_z)->lo = btor_bv_one (mm, 1);
      (*res_d_z)->hi = btor_bv_one (mm, 1);
    }
    /* Domain is valid and not fixed: equality can be true/false. */
    else
    {
      *res_d_z = btor_bvprop_new_init (mm, 1);
    }
  }
  else /* Domain is invalid: equality is false. */
  {
    *res_d_z       = new_domain (mm);
    (*res_d_z)->lo = btor_bv_zero (mm, 1);
    (*res_d_z)->hi = btor_bv_zero (mm, 1);
  }
  assert (btor_bvprop_is_valid (mm, *res_d_z));
}

void
btor_bvprop_not (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (d_z);

  BtorBitVector *not_hi = btor_bv_not (mm, d_z->hi);
  BtorBitVector *not_lo = btor_bv_not (mm, d_z->lo);
  *res_d_x              = new_domain (mm);
  (*res_d_x)->lo        = btor_bv_or (mm, d_x->lo, not_hi);
  (*res_d_x)->hi        = btor_bv_and (mm, d_x->hi, not_lo);
  btor_bv_free (mm, not_hi);
  btor_bv_free (mm, not_lo);

  not_hi         = btor_bv_not (mm, d_x->hi);
  not_lo         = btor_bv_not (mm, d_x->lo);
  *res_d_z       = new_domain (mm);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, not_hi);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, not_lo);
  btor_bv_free (mm, not_hi);
  btor_bv_free (mm, not_lo);
}

void btor_bvprop_sll_const (BtorMemMgr *mm,
                            BtorBvDomain *d_x,
                            BtorBvDomain *d_z,
                            BtorBitVector *n,
                            BtorBvDomain **res_d_x,
                            BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (d_z);

  uint32_t w, wn;
  BtorBitVector *mask1, *mask2, *ones1, *zero1, *ones2, *zero2;
  BtorBitVector *tmp, *tmp1;

  w = d_z->hi->width;
  assert (w == d_z->lo->width);
  assert (w == d_x->hi->width);
  assert (w == d_x->lo->width);
#ifndef NDEBUG
  BtorBitVector *uint32maxbv = btor_bv_ones (mm, 32);
  assert (btor_bv_compare (n, uint32maxbv) <= 0);
  btor_bv_free (mm, uint32maxbv);
#endif
  wn = (uint32_t) btor_bv_to_uint64 (n);

  if (wn == 0)
  {
    mask1 = btor_bv_zero (mm, w);
    mask2 = btor_bv_ones (mm, w);
  }
  else if (w == wn)
  {
    mask1 = btor_bv_ones (mm, w);
    mask2 = btor_bv_zero (mm, w);
  }
  else
  {
    ones1 = btor_bv_ones (mm, wn);
    zero1 = btor_bv_zero (mm, w - wn);
    ones2 = btor_bv_ones (mm, w - wn);
    zero2 = btor_bv_zero (mm, wn);
    mask1 = btor_bv_concat (mm, ones1, zero1);
    mask2 = btor_bv_concat (mm, ones2, zero2);
    btor_bv_free (mm, zero2);
    btor_bv_free (mm, ones2);
    btor_bv_free (mm, zero1);
    btor_bv_free (mm, ones1);
  }

  *res_d_x = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_x' = lo_x | (lo_z >> n) */
  tmp            = btor_bv_srl (mm, d_z->lo, n);
  (*res_d_x)->lo = btor_bv_or (mm, d_x->lo, tmp);
  btor_bv_free (mm, tmp);

  /* hi_x' = ((hi_z >> n) | mask1) & hi_x */
  tmp            = btor_bv_srl (mm, d_z->hi, n);
  tmp1           = btor_bv_or (mm, tmp, mask1);
  (*res_d_x)->hi = btor_bv_and (mm, tmp1, d_x->hi);
  btor_bv_free (mm, tmp);
  btor_bv_free (mm, tmp1);

  /* lo_z' = ((low_x << n) | lo_z) & mask2 */
  tmp            = btor_bv_sll (mm, d_x->lo, n);
  tmp1           = btor_bv_or (mm, tmp, d_z->lo);
  (*res_d_z)->lo = btor_bv_and (mm, tmp1, mask2);
  btor_bv_free (mm, tmp);
  btor_bv_free (mm, tmp1);

  /* hi_z' = (hi_x << n) & hi_z */
  tmp            = btor_bv_sll (mm, d_x->hi, n);
  (*res_d_z)->hi = btor_bv_and (mm, tmp, d_z->hi);
  btor_bv_free (mm, tmp);

  btor_bv_free (mm, mask2);
  btor_bv_free (mm, mask1);
}
