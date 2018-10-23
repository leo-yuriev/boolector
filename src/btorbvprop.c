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

  /**
   * lo_xy = lo_x | lo_y
   * hi_xy = hi_x & hi_y
   */
  *res_d_xy       = new_domain (mm);
  (*res_d_xy)->lo = btor_bv_or (mm, d_x->lo, d_y->lo);
  (*res_d_xy)->hi = btor_bv_and (mm, d_x->hi, d_y->hi);

  if (res_d_z)
  {
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
    /* Domain is invalid: equality is false. */
    else
    {
      *res_d_z       = new_domain (mm);
      (*res_d_z)->lo = btor_bv_zero (mm, 1);
      (*res_d_z)->hi = btor_bv_zero (mm, 1);
    }
    assert (btor_bvprop_is_valid (mm, *res_d_z));
  }
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

  /**
   * lo_x' = lo_x | ~hi_z
   * hi_x' = hi_x & ~hi_z
   */
  BtorBitVector *not_hi = btor_bv_not (mm, d_z->hi);
  BtorBitVector *not_lo = btor_bv_not (mm, d_z->lo);
  *res_d_x              = new_domain (mm);
  (*res_d_x)->lo        = btor_bv_or (mm, d_x->lo, not_hi);
  (*res_d_x)->hi        = btor_bv_and (mm, d_x->hi, not_lo);
  btor_bv_free (mm, not_hi);
  btor_bv_free (mm, not_lo);

  /**
   * lo_z' = lo_z | ~hi_x
   * hi_z' = hi_z & ~hi_x
   */
  not_hi         = btor_bv_not (mm, d_x->hi);
  not_lo         = btor_bv_not (mm, d_x->lo);
  *res_d_z       = new_domain (mm);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, not_hi);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, not_lo);
  btor_bv_free (mm, not_hi);
  btor_bv_free (mm, not_lo);
}

static void
bvprop_shift_const_aux (BtorMemMgr *mm,
                        BtorBvDomain *d_x,
                        BtorBvDomain *d_z,
                        BtorBitVector *n,
                        BtorBvDomain **res_d_x,
                        BtorBvDomain **res_d_z,
                        bool is_srl)
{
  assert (mm);
  assert (d_x);
  assert (d_z);
  assert (n);
  assert (res_d_x);
  assert (res_d_z);

  uint32_t w, wn;
  BtorBitVector *mask1, *mask2, *ones_wn, *zero_wn, *ones_w_wn, *zero_w_wn;
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

  /**
   * SLL: mask1 = 1_[wn]   :: 0_[w-wn]
   *      mask2 = 1_[w-wn] :: 0_[wn]
   * SRL: mask1 = 0_[w-wn] :: 1_[wn]
   *      mask2 = 0_[wn]   :: 1_[w-wn]
   */
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
    zero_wn   = btor_bv_zero (mm, wn);
    zero_w_wn = btor_bv_zero (mm, w - wn);
    ones_wn   = btor_bv_ones (mm, wn);
    ones_w_wn = btor_bv_ones (mm, w - wn);

    if (is_srl)
    {
      mask1 = btor_bv_concat (mm, zero_w_wn, ones_wn);
      mask2 = btor_bv_concat (mm, zero_wn, ones_w_wn);
    }
    else
    {
      mask1 = btor_bv_concat (mm, ones_wn, zero_w_wn);
      mask2 = btor_bv_concat (mm, ones_w_wn, zero_wn);
    }
    btor_bv_free (mm, zero_wn);
    btor_bv_free (mm, zero_w_wn);
    btor_bv_free (mm, ones_wn);
    btor_bv_free (mm, ones_w_wn);
  }

  *res_d_x = new_domain (mm);
  *res_d_z = new_domain (mm);

  /**
   * SLL: lo_x' = lo_x | (lo_z >> n)
   * SRL: lo_x' = lo_x | (lo_z << n)
   */
  tmp = is_srl ? btor_bv_sll (mm, d_z->lo, n) : btor_bv_srl (mm, d_z->lo, n);
  (*res_d_x)->lo = btor_bv_or (mm, d_x->lo, tmp);
  btor_bv_free (mm, tmp);

  /**
   * SLL: hi_x' = ((hi_z >> n) | mask1) & hi_x
   * SRL: hi_x' = ((hi_z << n) | mask1) & hi_x
   */
  tmp  = is_srl ? btor_bv_sll (mm, d_z->hi, n) : btor_bv_srl (mm, d_z->hi, n);
  tmp1 = btor_bv_or (mm, tmp, mask1);
  (*res_d_x)->hi = btor_bv_and (mm, tmp1, d_x->hi);
  btor_bv_free (mm, tmp);
  btor_bv_free (mm, tmp1);

  /**
   * SLL: lo_z' = ((low_x << n) | lo_z) & mask2
   * SRL: lo_z' = ((low_x >> n) | lo_z) & mask2
   */
  tmp  = is_srl ? btor_bv_srl (mm, d_x->lo, n) : btor_bv_sll (mm, d_x->lo, n);
  tmp1 = btor_bv_or (mm, tmp, d_z->lo);
  (*res_d_z)->lo = btor_bv_and (mm, tmp1, mask2);
  btor_bv_free (mm, tmp);
  btor_bv_free (mm, tmp1);

  /**
   * SLL: hi_z' = (hi_x << n) & hi_z
   * SRL: hi_z' = (hi_x >> n) & hi_z
   */
  tmp = is_srl ? btor_bv_srl (mm, d_x->hi, n) : btor_bv_sll (mm, d_x->hi, n);
  (*res_d_z)->hi = btor_bv_and (mm, tmp, d_z->hi);
  btor_bv_free (mm, tmp);

  btor_bv_free (mm, mask2);
  btor_bv_free (mm, mask1);
}

void
btor_bvprop_sll_const (BtorMemMgr *mm,
                       BtorBvDomain *d_x,
                       BtorBvDomain *d_z,
                       BtorBitVector *n,
                       BtorBvDomain **res_d_x,
                       BtorBvDomain **res_d_z)
{
  bvprop_shift_const_aux (mm, d_x, d_z, n, res_d_x, res_d_z, false);
}

void
btor_bvprop_srl_const (BtorMemMgr *mm,
                       BtorBvDomain *d_x,
                       BtorBvDomain *d_z,
                       BtorBitVector *n,
                       BtorBvDomain **res_d_x,
                       BtorBvDomain **res_d_z)
{
  bvprop_shift_const_aux (mm, d_x, d_z, n, res_d_x, res_d_z, true);
}

void
btor_bvprop_and (BtorMemMgr *mm,
                 BtorBvDomain *d_x,
                 BtorBvDomain *d_y,
                 BtorBvDomain *d_z,
                 BtorBvDomain **res_d_x,
                 BtorBvDomain **res_d_y,
                 BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (d_y);
  assert (d_z);
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  BtorBitVector *tmp0, *tmp1;

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_x' = lo_x | lo_z */
  (*res_d_x)->lo = btor_bv_or (mm, d_x->lo, d_z->lo);

  /* hi_x' = hi_x & ~(~hi_z & lo_y) */
  tmp0 = btor_bv_not (mm, d_z->hi);
  tmp1 = btor_bv_and (mm, tmp0, d_y->lo);
  btor_bv_free (mm, tmp0);
  tmp0 = btor_bv_not (mm, tmp1);
  btor_bv_free (mm, tmp1);
  (*res_d_x)->hi = btor_bv_and (mm, d_x->hi, tmp0);
  btor_bv_free (mm, tmp0);

  /* lo_y' = lo_y | lo_z */
  (*res_d_y)->lo = btor_bv_or (mm, d_y->lo, d_z->lo);

  /* hi_y' = hi_y | ~(~hi_z & lo_x) */
  tmp0 = btor_bv_not (mm, d_z->hi);
  tmp1 = btor_bv_and (mm, tmp0, d_x->lo);
  btor_bv_free (mm, tmp0);
  tmp0 = btor_bv_not (mm, tmp1);
  btor_bv_free (mm, tmp1);
  (*res_d_y)->hi = btor_bv_and (mm, d_y->hi, tmp0);
  btor_bv_free (mm, tmp0);

  /* lo_z' = lo_z | (lo_x & lo_y) */
  tmp0           = btor_bv_and (mm, d_x->lo, d_y->lo);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, tmp0);
  btor_bv_free (mm, tmp0);

  /* hi_z' = hi_z & hi_x & hi_y */
  tmp0           = btor_bv_and (mm, d_x->hi, d_y->hi);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, tmp0);
  btor_bv_free (mm, tmp0);
}

void
btor_bvprop_slice (BtorMemMgr *mm,
                   BtorBvDomain *d_x,
                   BtorBvDomain *d_z,
                   uint32_t upper,
                   uint32_t lower,
                   BtorBvDomain **res_d_x,
                   BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (d_z);
  assert (upper >= lower);
  assert (upper < d_x->lo->width);
  assert (upper - lower + 1 == d_z->lo->width);

  /* Apply equality propagator on sliced 'x' domain.
   *
   * lo_x' = lo_x[wx-1:upper+1] o lo_x[upper:lower] | lo_z o lo_x[lower - 1:0]
   * hi_x' = hi_x[wx-1:upper+1] o hi_x[upper:lower] & hi_z o hi_x[lower - 1:0]
   *
   * Note: We don't use the propagator described in [1] since it changes the
   *       don't care bits of 'd_x'.
   */

  BtorBvDomain *sliced_x = new_domain (mm);
  sliced_x->lo           = btor_bv_slice (mm, d_x->lo, upper, lower);
  sliced_x->hi           = btor_bv_slice (mm, d_x->hi, upper, lower);

  btor_bvprop_eq (mm, sliced_x, d_z, res_d_z, 0);
  btor_bvprop_free (mm, sliced_x);

  uint32_t wx = d_x->lo->width;

  *res_d_x = new_domain (mm);

  BtorBitVector *lo_x = btor_bv_copy (mm, (*res_d_z)->lo);
  BtorBitVector *hi_x = btor_bv_copy (mm, (*res_d_z)->hi);
  BtorBitVector *tmp;
  if (lower > 0)
  {
    BtorBitVector *lower_lo_x = btor_bv_slice (mm, d_x->lo, lower - 1, 0);
    BtorBitVector *lower_hi_x = btor_bv_slice (mm, d_x->hi, lower - 1, 0);
    tmp                       = btor_bv_concat (mm, lo_x, lower_lo_x);
    btor_bv_free (mm, lo_x);
    lo_x = tmp;
    tmp  = btor_bv_concat (mm, hi_x, lower_hi_x);
    btor_bv_free (mm, hi_x);
    hi_x = tmp;
    btor_bv_free (mm, lower_lo_x);
    btor_bv_free (mm, lower_hi_x);
  }

  if (upper < wx - 1)
  {
    BtorBitVector *upper_lo_x = btor_bv_slice (mm, d_x->lo, wx - 1, upper + 1);
    BtorBitVector *upper_hi_x = btor_bv_slice (mm, d_x->hi, wx - 1, upper + 1);
    tmp                       = btor_bv_concat (mm, upper_lo_x, lo_x);
    btor_bv_free (mm, lo_x);
    lo_x = tmp;
    tmp  = btor_bv_concat (mm, upper_hi_x, hi_x);
    btor_bv_free (mm, hi_x);
    hi_x = tmp;
    btor_bv_free (mm, upper_lo_x);
    btor_bv_free (mm, upper_hi_x);
  }

  assert (lo_x->width == wx);
  assert (hi_x->width == wx);
  (*res_d_x)->lo = lo_x;
  (*res_d_x)->hi = hi_x;
}

void
btor_bvprop_concat (BtorMemMgr *mm,
                    BtorBvDomain *d_x,
                    BtorBvDomain *d_y,
                    BtorBvDomain *d_z,
                    BtorBvDomain **res_d_x,
                    BtorBvDomain **res_d_y,
                    BtorBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (d_y);
  assert (d_z);
  assert (res_d_x);
  assert (res_d_y);
  assert (res_d_z);

  uint32_t wx, wy, wz;

  wx = d_x->hi->width;
  assert (wx == d_x->lo->width);
  wy = d_y->hi->width;
  assert (wy == d_y->lo->width);
  wz = d_z->hi->width;
  assert (wz == d_z->lo->width);

#if 0
  /* These are the propagators as proposed in [1]. */

  BtorBitVector *mask, *zero, *ones, *tmp0, *tmp1;
  BtorBitVector *lo_x, *hi_x, *lo_y, *hi_y;

  lo_x = btor_bv_uext (mm, d_x->lo, wz - wx);
  hi_x = btor_bv_uext (mm, d_x->hi, wz - wx);
  lo_y = btor_bv_uext (mm, d_y->lo, wz - wy);
  hi_y = btor_bv_uext (mm, d_y->hi, wz - wy);

  zero = btor_bv_zero (mm, wz - wy);
  ones = btor_bv_ones (mm, wy);
  mask = btor_bv_concat (mm, zero, ones);

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_z' = lo_z | ((lo_x << wy) | lo_y) */
  tmp0           = btor_bv_sll_uint32 (mm, lo_x, wy);
  tmp1           = btor_bv_or (mm, tmp0, lo_y);
  (*res_d_z)->lo = btor_bv_or (mm, d_z->lo, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_z' = hi_z & ((hi_x << wy) | hi_y) */
  tmp0           = btor_bv_sll_uint32 (mm, hi_x, wy);
  tmp1           = btor_bv_or (mm, tmp0, hi_y);
  (*res_d_z)->hi = btor_bv_and (mm, d_z->hi, tmp1);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* lo_x' = lo_x | (lo_z >> wy) */
  tmp0           = btor_bv_srl_uint32 (mm, d_z->lo, wy);
  tmp1           = btor_bv_or (mm, lo_x, tmp0);
  (*res_d_x)->lo = btor_bv_slice (mm, tmp1, wx - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_x' = hi_x & (hi_z >> wy) */
  tmp0           = btor_bv_srl_uint32 (mm, d_z->hi, wy);
  tmp1           = btor_bv_and (mm, hi_x, tmp0);
  (*res_d_x)->hi = btor_bv_slice (mm, tmp1, wx - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* lo_y' = lo_y | (lo_z & mask */
  tmp0           = btor_bv_and (mm, d_z->lo, mask);
  tmp1           = btor_bv_or (mm, lo_y, tmp0);
  (*res_d_y)->lo = btor_bv_slice (mm, tmp1, wy - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  /* hi_y' = hi_y & (hi_z & mask) */
  tmp0           = btor_bv_and (mm, d_z->hi, mask);
  tmp1           = btor_bv_and (mm, hi_y, tmp0);
  (*res_d_y)->hi = btor_bv_slice (mm, tmp1, wy - 1, 0);
  btor_bv_free (mm, tmp0);
  btor_bv_free (mm, tmp1);

  btor_bv_free (mm, lo_x);
  btor_bv_free (mm, hi_x);
  btor_bv_free (mm, lo_y);
  btor_bv_free (mm, hi_y);

  btor_bv_free (mm, zero);
  btor_bv_free (mm, ones);
  btor_bv_free (mm, mask);
#else
  /* These propagators are compositional (simpler). */

  BtorBitVector *lo_zx, *lo_zy, *hi_zx, *hi_zy;
  BtorBvDomain *d_zx, *d_zy;

  /* z = zx o zy */
  lo_zx = btor_bv_slice (mm, d_z->lo, wz - 1, wy);
  hi_zx = btor_bv_slice (mm, d_z->hi, wz - 1, wy);
  lo_zy = btor_bv_slice (mm, d_z->lo, wy - 1, 0);
  hi_zy = btor_bv_slice (mm, d_z->hi, wy - 1, 0);
  d_zx  = btor_bvprop_new (mm, lo_zx, hi_zx);
  d_zy  = btor_bvprop_new (mm, lo_zy, hi_zy);

  *res_d_z = new_domain (mm);

  /* res_z = prop(d_zx = d_x) o prop(d_zy o d_y) */
  btor_bvprop_eq (mm, d_zx, d_x, res_d_x, 0);
  btor_bvprop_eq (mm, d_zy, d_y, res_d_y, 0);
  (*res_d_z)->lo = btor_bv_concat (mm, (*res_d_x)->lo, (*res_d_y)->lo);
  (*res_d_z)->hi = btor_bv_concat (mm, (*res_d_x)->hi, (*res_d_y)->hi);

  btor_bv_free (mm, lo_zx);
  btor_bv_free (mm, lo_zy);
  btor_bv_free (mm, hi_zx);
  btor_bv_free (mm, hi_zy);
  btor_bvprop_free (mm, d_zx);
  btor_bvprop_free (mm, d_zy);
#endif
}
