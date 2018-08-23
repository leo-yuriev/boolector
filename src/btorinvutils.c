/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 *
 *  Bit-vector operator invertibility checks based on [1].
 *
 *  [1] Aina Niemetz, Mathias Preiner, Andrew Reynolds, Clark Barrett, Cesare
 *      Tinelli: Solving Quantified Bit-Vectors Using Invertibility Conditions.
 *      CAV (2) 2018: 236-255
 *
 */

#include "btorinvutils.h"

#include <assert.h>

/* Check invertibility condition for x & s = t.
 *
 * IC: t & s = t
 */
bool
btor_is_inv_and (BtorMemMgr *mm, const BtorBitVector *s, const BtorBitVector *t)
{
  BtorBitVector *t_and_s = btor_bv_and (mm, t, s);
  BtorBitVector *eq_t    = btor_bv_eq (mm, t_and_s, t);
  bool res               = btor_bv_is_true (eq_t);
  btor_bv_free (mm, t_and_s);
  btor_bv_free (mm, eq_t);
  return res;
}

/* Check invertibility condition for x o s = t or s o x = t.
 *
 * IC (pos_x = 0): s = t[bw(s) - 1 : 0]
 * IC (pos_x = 1): s = t[bw(t) - 1 : bw(t) - bw(s)]
 */
bool
btor_is_inv_concat (BtorMemMgr *mm,
                    const BtorBitVector *s,
                    const BtorBitVector *t,
                    uint32_t pos_x)
{
  BtorBitVector *slice;
  bool res;
  if (pos_x == 0)
  {
    slice = btor_bv_slice (mm, t, s->width, 0);
  }
  else
  {
    assert (pos_x == 1);
    slice = btor_bv_slice (mm, t, t->width - 1, t->width - s->width);
  }
  BtorBitVector *s_eq_slice = btor_bv_eq (mm, s, slice);
  res                       = btor_bv_is_true (s_eq_slice);
  btor_bv_free (mm, slice);
  btor_bv_free (mm, s_eq_slice);
  return res;
}

/* Check invertibility condition for x * s = t.
 *
 * IC: (-s | s ) & t = t
 */
bool
btor_is_inv_mul (BtorMemMgr *mm, const BtorBitVector *s, const BtorBitVector *t)
{
  BtorBitVector *neg_s      = btor_bv_neg (mm, s);
  BtorBitVector *neg_s_or_s = btor_bv_or (mm, neg_s, s);
  BtorBitVector *and_t      = btor_bv_and (mm, neg_s_or_s, t);
  BtorBitVector *eq_t       = btor_bv_eq (mm, and_t, t);
  bool res                  = btor_bv_is_true (eq_t);
  btor_bv_free (mm, neg_s);
  btor_bv_free (mm, neg_s_or_s);
  btor_bv_free (mm, and_t);
  btor_bv_free (mm, eq_t);
  return res;
}

/* Check invertibility condition for x | s = t.
 *
 * IC: t | s = t
 */
bool
btor_is_inv_or (BtorMemMgr *mm, const BtorBitVector *s, const BtorBitVector *t)
{
  BtorBitVector *t_or_s = btor_bv_or (mm, t, s);
  BtorBitVector *eq_t   = btor_bv_eq (mm, t_or_s, t);
  bool res              = btor_bv_is_true (eq_t);
  btor_bv_free (mm, t_or_s);
  btor_bv_free (mm, eq_t);
  return res;
}

/* Check invertibility condition for x << s = t or s << x = t.
 *
 * IC (pos_x = 0): (t >> s) << s = t
 * IC (pos_x = 1): (\/ s << i = t)  i = 0..bw(s)-1
 */
bool
btor_is_inv_sll (BtorMemMgr *mm,
                 const BtorBitVector *s,
                 const BtorBitVector *t,
                 uint32_t pos_x)
{
  bool res;
  if (pos_x == 0)
  {
    BtorBitVector *t_srl_s = btor_bv_srl (mm, t, s);
    BtorBitVector *sll_s   = btor_bv_sll (mm, t_srl_s, s);
    BtorBitVector *eq_t    = btor_bv_eq (mm, sll_s, t);
    res                    = btor_bv_is_true (eq_t);
    btor_bv_free (mm, t_srl_s);
    btor_bv_free (mm, sll_s);
    btor_bv_free (mm, eq_t);
  }
  else
  {
    assert (pos_x == 1);
    res = false;
    for (uint32_t i = 0; i < s->width && !res; i++)
    {
      BtorBitVector *bv_i    = btor_bv_uint64_to_bv (mm, i, s->width);
      BtorBitVector *s_sll_i = btor_bv_srl (mm, s, bv_i);
      BtorBitVector *eq_t    = btor_bv_eq (mm, s_sll_i, t);
      res                    = btor_bv_is_true (eq_t);
      btor_bv_free (mm, bv_i);
      btor_bv_free (mm, s_sll_i);
      btor_bv_free (mm, eq_t);
    }
  }
  return res;
}

/* Check invertibility condition for x >>a s = t or s >>a x = t.
 *
 * IC (pos_x = 0): (s < bw(s) -> (t << s) >>a s = t)
 *                 /\ (s >= bw(s) -> (t = ~0 \/ t = 0))
 * IC (pos_x = 1): (\/ s >>a i = t)  i = 0..bw(s)-1
 */
bool
btor_is_inv_sra (BtorMemMgr *mm,
                 const BtorBitVector *s,
                 const BtorBitVector *t,
                 uint32_t pos_x)
{
  bool res;
  if (pos_x == 0)
  {
    BtorBitVector *bw_s       = btor_bv_uint64_to_bv (mm, s->width, s->width);
    BtorBitVector *s_ult_bw_s = btor_bv_ult (mm, s, bw_s);

    res = true;
    if (btor_bv_is_true (s_ult_bw_s))
    {
      BtorBitVector *t_sll_s = btor_bv_sll (mm, t, s);
      BtorBitVector *sra_s   = btor_bv_sra (mm, t_sll_s, s);
      BtorBitVector *eq_t    = btor_bv_eq (mm, sra_s, t);
      res                    = btor_bv_is_true (eq_t);
      btor_bv_free (mm, t_sll_s);
      btor_bv_free (mm, sra_s);
      btor_bv_free (mm, eq_t);
    }
    btor_bv_free (mm, s_ult_bw_s);
    if (res)
    {
      BtorBitVector *s_uge_bw_s = btor_bv_ulte (mm, bw_s, s);
      res = (!btor_bv_is_true (s_uge_bw_s) || btor_bv_is_ones (t)
             || btor_bv_is_zero (t));
      btor_bv_free (mm, s_uge_bw_s);
    }
    btor_bv_free (mm, bw_s);
  }
  else
  {
    assert (pos_x == 1);
    res = false;
    for (uint32_t i = 0; i < s->width && !res; i++)
    {
      BtorBitVector *bv_i    = btor_bv_uint64_to_bv (mm, i, s->width);
      BtorBitVector *s_sra_i = btor_bv_sra (mm, s, bv_i);
      BtorBitVector *eq_t    = btor_bv_eq (mm, s_sra_i, t);
      res                    = btor_bv_is_true (eq_t);
      btor_bv_free (mm, bv_i);
      btor_bv_free (mm, s_sra_i);
      btor_bv_free (mm, eq_t);
    }
  }
  return res;
}

/* Check invertibility condition for x >> s = t or s >> x = t.
 *
 * IC (pos_x = 0): (t << s) >> s = t
 * IC (pos_x = 1): (\/ s >> i = t)  i = 0..bw(s)-1
 */
bool
btor_is_inv_srl (BtorMemMgr *mm,
                 const BtorBitVector *s,
                 const BtorBitVector *t,
                 uint32_t pos_x)
{
  bool res;
  if (pos_x == 0)
  {
    BtorBitVector *t_sll_s = btor_bv_sll (mm, t, s);
    BtorBitVector *srl_s   = btor_bv_srl (mm, t_sll_s, s);
    BtorBitVector *eq_t    = btor_bv_eq (mm, srl_s, t);
    res                    = btor_bv_is_true (eq_t);
    btor_bv_free (mm, t_sll_s);
    btor_bv_free (mm, srl_s);
    btor_bv_free (mm, eq_t);
  }
  else
  {
    assert (pos_x == 1);
    res = false;
    for (uint32_t i = 0; i < s->width && !res; i++)
    {
      BtorBitVector *bv_i    = btor_bv_uint64_to_bv (mm, i, s->width);
      BtorBitVector *s_srl_i = btor_bv_srl (mm, s, bv_i);
      BtorBitVector *eq_t    = btor_bv_eq (mm, s_srl_i, t);
      res                    = btor_bv_is_true (eq_t);
      btor_bv_free (mm, bv_i);
      btor_bv_free (mm, s_srl_i);
      btor_bv_free (mm, eq_t);
    }
  }
  return res;
}

/* Check invertibility condition for x < t or t < x.
 *
 * IC (pos_x = 0): t != 0
 * IC (pos_x = 1): t != ~0
 */
bool
btor_is_inv_ult (BtorMemMgr *mm, const BtorBitVector *t, uint32_t pos_x)
{
  (void) mm;
  bool res;
  if (pos_x == 0)
  {
    res = !btor_bv_is_zero (t);
  }
  else
  {
    assert (pos_x == 1);
    res = !btor_bv_is_ones (t);
  }
  return res;
}

/* Check invertibility condition for x / s = t or s / x = t.
 *
 * IC (pos_x = 0): (s * t) / s = t
 * IC (pos_x = 1): s / (s / t) = t
 */
bool
btor_is_inv_udiv (BtorMemMgr *mm,
                  const BtorBitVector *s,
                  const BtorBitVector *t,
                  uint32_t pos_x)
{
  BtorBitVector *udiv;
  bool res;
  if (pos_x == 0)
  {
    BtorBitVector *s_mul_t = btor_bv_mul (mm, s, t);
    udiv                   = btor_bv_udiv (mm, s_mul_t, s);
    btor_bv_free (mm, s_mul_t);
  }
  else
  {
    assert (pos_x == 1);
    BtorBitVector *s_udiv_t = btor_bv_udiv (mm, s, t);
    udiv                    = btor_bv_udiv (mm, s, s_udiv_t);
    btor_bv_free (mm, s_udiv_t);
  }
  BtorBitVector *eq_t = btor_bv_eq (mm, udiv, t);
  res                 = btor_bv_is_true (eq_t);
  btor_bv_free (mm, udiv);
  btor_bv_free (mm, eq_t);
  return res;
}

/* Check invertibility condition for x mod s = t or s mod x = t.
 *
 * IC (pos_x = 0): ~(-s) >= t
 * IC (pos_x = 1): (t + t - s) & s >= t
 */
bool
btor_is_inv_urem (BtorMemMgr *mm,
                  const BtorBitVector *s,
                  const BtorBitVector *t,
                  uint32_t pos_x)
{
  bool res;
  BtorBitVector *neg_s = btor_bv_neg (mm, s);
  if (pos_x == 0)
  {
    BtorBitVector *not_neg_s = btor_bv_not (mm, neg_s);
    BtorBitVector *uge_t     = btor_bv_ulte (mm, t, not_neg_s);
    res                      = btor_bv_is_true (uge_t);
    btor_bv_free (mm, not_neg_s);
    btor_bv_free (mm, uge_t);
  }
  else
  {
    assert (pos_x == 1);
    BtorBitVector *t_add_t = btor_bv_add (mm, t, t);
    BtorBitVector *sub_s   = btor_bv_add (mm, t_add_t, neg_s);
    BtorBitVector *and_s   = btor_bv_and (mm, sub_s, s);
    BtorBitVector *uge_t   = btor_bv_ulte (mm, t, and_s);
    res                    = btor_bv_is_true (uge_t);
    btor_bv_free (mm, t_add_t);
    btor_bv_free (mm, sub_s);
    btor_bv_free (mm, and_s);
    btor_bv_free (mm, uge_t);
  }
  btor_bv_free (mm, neg_s);
  return res;
}
