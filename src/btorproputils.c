/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorproputils.h"

#include "btorinvutils.h"
#include "btorprintmodel.h"
#include "btorslsutils.h"
#include "btorslvprop.h"
#include "btorslvsls.h"
#include "utils/btornodeiter.h"
#include "utils/btorutil.h"

/* ========================================================================== */
/* Path selection (for down-propagation)                                      */
/* ========================================================================== */

static int32_t
select_path_non_const (BtorNode *exp)
{
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (exp->arity <= 2);
  assert (!btor_node_is_bv_const (exp->e[0])
          || (exp->arity > 1 && !btor_node_is_bv_const (exp->e[1])));

  uint32_t i;
  int32_t eidx;

  for (i = 0, eidx = -1; i < exp->arity; i++)
    if (btor_node_is_bv_const (exp->e[i]))
    {
      eidx = i ? 0 : 1;
      break;
    }
  assert (exp->arity == 1 || !btor_node_is_bv_const (exp->e[i ? 0 : 1]));
  return eidx;
}

static int32_t
select_path_random (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  return (int32_t) btor_rng_pick_rand (&btor->rng, 0, exp->arity - 1);
}

static int32_t
select_path_add (Btor *btor, BtorNode *add, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (add);
  assert (btor_node_is_regular (add));
  assert (t);
  assert (s);

  (void) t;
  (void) s;

  int32_t eidx;

  eidx = select_path_non_const (add);
  if (eidx == -1) eidx = select_path_random (btor, add);
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (add));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (add->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (add->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_and (Btor *btor, BtorNode *and, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (and);
  assert (btor_node_is_regular (and));
  assert (t);
  assert (s);

  uint32_t opt;
  int32_t i, eidx;
  BtorBitVector *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (and);

  if (eidx == -1)
  {
    opt = btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL);

    if (opt == BTOR_PROP_PATH_SEL_RANDOM)
    {
      eidx = select_path_random (btor, and);
    }
    else if (btor_node_bv_get_width (btor, and) == 1)
    {
      /* choose 0-branch if exactly one branch is 0, else choose randomly */
      for (i = 0; i < and->arity; i++)
        if (btor_bv_is_zero (s[i])) eidx = eidx == -1 ? i : -1;
      if (eidx == -1) eidx = select_path_random (btor, and);
    }
    else if (opt == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      /* 1) all bits set in t must be set in both inputs, but
       * 2) all bits NOT set in t can be cancelled out by either or both
       * -> choose single input that violates 1)
       * -> else choose randomly */
      for (i = 0; i < and->arity; i++)
      {
        tmp = btor_bv_and (mm, t, s[i]);
        if (btor_bv_compare (tmp, t)) eidx = eidx == -1 ? i : -1;
        btor_bv_free (mm, tmp);
      }
    }
    if (eidx == -1) eidx = select_path_random (btor, and);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (and));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (and->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (and->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_eq (Btor *btor, BtorNode *eq, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (eq);
  assert (btor_node_is_regular (eq));
  assert (t);
  assert (s);

  (void) t;
  (void) s;

  int32_t eidx;
  eidx = select_path_non_const (eq);
  if (eidx == -1) eidx = select_path_random (btor, eq);
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (eq));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (eq->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (eq->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_ult (Btor *btor, BtorNode *ult, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (ult);
  assert (btor_node_is_regular (ult));
  assert (t);
  assert (s);

  int32_t eidx;
  BtorBitVector *bvmax;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (ult);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax = btor_bv_ones (mm, s[0]->width);
      if (btor_bv_is_one (t))
      {
        /* 1...1 < s[1] */
        if (!btor_bv_compare (s[0], bvmax)) eidx = 0;
        /* s[0] < 0 */
        if (btor_bv_is_zero (s[1])) eidx = eidx == -1 ? 1 : -1;
      }
      btor_bv_free (mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random (btor, ult);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (ult));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (ult->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (ult->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_sll (Btor *btor, BtorNode *sll, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (sll);
  assert (btor_node_is_regular (sll));
  assert (t);
  assert (s);

  int32_t eidx;
  uint64_t i, j, shift;

  eidx = select_path_non_const (sll);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      shift = btor_bv_to_uint64 (s[1]);
      /* s[1] and number of LSB 0-bits in t must match */
      for (i = 0; i < shift; i++)
        if (btor_bv_get_bit (t, i))
        {
          eidx = 1;
          goto DONE;
        }
      /* s[0] and t (except for the bits shifted out) must match */
      for (i = 0, j = shift; i < t->width - j; i++)
        if (btor_bv_get_bit (s[0], i) != btor_bv_get_bit (t, j + i))
        {
          eidx = eidx == -1 ? 0 : -1;
          break;
        }
    }
    if (eidx == -1) eidx = select_path_random (btor, sll);
  }
DONE:
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (sll));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (sll->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (sll->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_srl (Btor *btor, BtorNode *srl, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (srl);
  assert (btor_node_is_regular (srl));
  assert (t);
  assert (s);

  int32_t eidx;
  uint64_t i, j, shift;

  eidx = select_path_non_const (srl);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      shift = btor_bv_to_uint64 (s[1]);
      /* s[1] and number of MSB 0-bits in t must match */
      for (i = 0; i < shift; i++)
        if (btor_bv_get_bit (t, t->width - 1 - i))
        {
          eidx = 1;
          goto DONE;
        }
      /* s[0] and t (except for the bits shifted out) must match */
      for (i = 0, j = shift; i < t->width - j; i++)
        if (btor_bv_get_bit (s[0], s[0]->width - 1 - i)
            != btor_bv_get_bit (t, t->width - 1 - (j + i)))
        {
          eidx = eidx == -1 ? 0 : -1;
          break;
        }
    }
    if (eidx == -1) eidx = select_path_random (btor, srl);
  }
DONE:
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (srl));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (srl->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (srl->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_mul (Btor *btor, BtorNode *mul, BtorBitVector *t, BtorBitVector **s)
{
  assert (btor);
  assert (mul);
  assert (btor_node_is_regular (mul));
  assert (t);
  assert (s);

  uint32_t ctz_bvmul;
  int32_t eidx, lsb_s0, lsb_s1;
  bool iszero_s0, iszero_s1;

  eidx = select_path_non_const (mul);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      iszero_s0 = btor_bv_is_zero (s[0]);
      iszero_s1 = btor_bv_is_zero (s[1]);

      lsb_s0 = btor_bv_get_bit (s[0], 0);
      lsb_s1 = btor_bv_get_bit (s[1], 0);

      /* either s[0] or s[1] are 0 but t > 0 */
      if ((iszero_s0 || iszero_s1) && !btor_bv_is_zero (t))
      {
        if (iszero_s0) eidx = 0;
        if (iszero_s1) eidx = eidx == -1 ? 1 : -1;
      }
      /* t is odd but either s[0] or s[1] are even */
      else if (btor_bv_get_bit (t, 0) && (!lsb_s0 || !lsb_s1))
      {
        if (!lsb_s0) eidx = 0;
        if (!lsb_s1) eidx = eidx == -1 ? 1 : -1;
      }
      /* number of 0-LSBs in t < number of 0-LSBs in s[0|1] */
      else
      {
        ctz_bvmul = btor_bv_get_num_trailing_zeros (t);
        if (ctz_bvmul < btor_bv_get_num_trailing_zeros (s[0])) eidx = 0;
        if (ctz_bvmul < btor_bv_get_num_trailing_zeros (s[1]))
          eidx = eidx == -1 ? 1 : -1;
      }
    }
    if (eidx == -1) eidx = select_path_random (btor, mul);
  }
  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (mul));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (mul->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (mul->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_udiv (Btor *btor,
                  BtorNode *udiv,
                  BtorBitVector *t,
                  BtorBitVector **s)
{
  assert (btor);
  assert (udiv);
  assert (btor_node_is_regular (udiv));
  assert (t);
  assert (s);

  int32_t eidx, cmp_udiv_max;
  BtorBitVector *bvmax, *up, *lo, *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (udiv);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax        = btor_bv_ones (mm, s[0]->width);
      cmp_udiv_max = btor_bv_compare (t, bvmax);

      /* s[0] / s[1] = 1...1 -> choose e[1]
       *   + 1...1 / 0 = 1...1
       *   + 1...1 / 1 = 1...1
       *   + x...x / 0 = 1...1 */
      if (!cmp_udiv_max)
        eidx = 1;
      else
      {
        /* 1...1 / e[0] = 0 -> choose e[0] */
        if (btor_bv_is_zero (t) && !btor_bv_compare (s[0], bvmax)) eidx = 0;
        /* s[0] < t -> choose e[0] */
        else if (btor_bv_compare (s[0], t) < 0)
          eidx = 0;
        else
        {
          up  = btor_bv_udiv (mm, s[0], t);
          lo  = btor_bv_inc (mm, t);
          tmp = btor_bv_udiv (mm, s[0], lo);
          btor_bv_free (mm, lo);
          lo = btor_bv_inc (mm, tmp);

          if (btor_bv_compare (lo, up) > 0) eidx = 0;
          btor_bv_free (mm, up);
          btor_bv_free (mm, lo);
          btor_bv_free (mm, tmp);
        }

        /* e[0] / 0 != 1...1 -> choose e[1] */
        if (btor_bv_is_zero (s[1]) || btor_bv_is_umulo (mm, s[1], t))
          eidx = eidx == -1 ? 1 : -1;
      }
      btor_bv_free (mm, bvmax);
    }
    if (eidx == -1) eidx = select_path_random (btor, udiv);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (udiv));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (udiv->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (udiv->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_urem (Btor *btor,
                  BtorNode *urem,
                  BtorBitVector *t,
                  BtorBitVector **s)
{
  assert (btor);
  assert (urem);
  assert (btor_node_is_regular (urem));
  assert (t);
  assert (s);

  int32_t eidx;
  BtorBitVector *bvmax, *sub, *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (urem);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      bvmax = btor_bv_ones (mm, s[0]->width);
      sub   = btor_bv_sub (mm, s[0], t);
      tmp   = btor_bv_dec (mm, s[0]);

      /* t = 1...1 -> s[0] = 1...1 and s[1] = 0...0 */
      if (!btor_bv_compare (t, bvmax))
      {
        if (!btor_bv_is_zero (s[1])) eidx = 1;
        if (btor_bv_compare (s[0], bvmax)) eidx = eidx == -1 ? 0 : -1;
      }
      /* t > 0 and s[1] = 1 */
      else if (!btor_bv_is_zero (t) && btor_bv_is_one (s[1]))
      {
        eidx = 1;
      }
      /* 0 < s[1] <= t */
      else if (!btor_bv_is_zero (s[1]) && btor_bv_compare (s[1], t) <= 0)
      {
        eidx = eidx == -1 ? 1 : -1;
      }
      /* s[0] < t or
       * s[0] > t and s[0] - t <= t or
       *                 and s[0] - 1 = t */
      else if (btor_bv_compare (s[0], t) < 0
               || (btor_bv_compare (s[0], t) > 0
                   && (btor_bv_compare (sub, t) <= 0
                       || !btor_bv_compare (tmp, t))))
      {
        eidx = 0;
      }

      btor_bv_free (mm, tmp);
      btor_bv_free (mm, bvmax);
      btor_bv_free (mm, sub);
    }

    if (eidx == -1) eidx = select_path_random (btor, urem);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (urem));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (urem->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (urem->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_concat (Btor *btor,
                    BtorNode *concat,
                    BtorBitVector *t,
                    BtorBitVector **s)
{
  assert (btor);
  assert (concat);
  assert (btor_node_is_regular (concat));
  assert (t);
  assert (s);

  int32_t eidx;
  BtorBitVector *tmp;
  BtorMemMgr *mm;

  mm   = btor->mm;
  eidx = select_path_non_const (concat);

  if (eidx == -1)
  {
    if (btor_opt_get (btor, BTOR_OPT_PROP_PATH_SEL)
        == BTOR_PROP_PATH_SEL_ESSENTIAL)
    {
      /* s[0] o s[1] = t
       * -> s[0] resp. s[1] must match with t */
      tmp = btor_bv_slice (mm, t, t->width - 1, t->width - s[0]->width);
      if (btor_bv_compare (tmp, s[0])) eidx = 0;
      btor_bv_free (mm, tmp);
      tmp = btor_bv_slice (mm, t, s[1]->width - 1, 0);
      if (btor_bv_compare (tmp, s[1])) eidx = eidx == -1 ? 1 : -1;
      btor_bv_free (mm, tmp);
    }

    if (eidx == -1) eidx = select_path_random (btor, concat);
  }

  assert (eidx >= 0);
#ifndef NBTORLOG
  char *a;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (concat));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (concat->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, s[1]);
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (concat->e[1]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

static int32_t
select_path_slice (Btor *btor,
                   BtorNode *slice,
                   BtorBitVector *t,
                   BtorBitVector **s)
{
  assert (btor);
  assert (slice);
  assert (btor_node_is_regular (slice));
  assert (t);
  assert (s);

  assert (!btor_node_is_bv_const (slice->e[0]));

  (void) btor;
  (void) slice;
  (void) t;
  (void) s;
#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;
  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (slice));
  a = btor_bv_to_char (mm, s[0]);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (slice->e[0]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: 0");
#endif

  return 0;
}

static int32_t
select_path_cond (Btor *btor,
                  BtorNode *cond,
                  BtorBitVector *bvcond,
                  BtorBitVector **s)
{
  assert (btor);
  assert (btor->slv->kind == BTOR_PROP_SOLVER_KIND
          || btor->slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (cond);
  assert (btor_node_is_regular (cond));
  assert (bvcond);
  assert (s);

  bool e1const, e2const;
  int32_t eidx;
  uint32_t prob;
  BtorBitVector *s0;

  (void) bvcond;

  s0 = *s;
  assert (s0);

  if (btor_node_is_bv_const (cond->e[0]))
    eidx = cond->e[0] == btor->true_exp ? 1 : 2;
  else
  {
    e1const = btor_node_is_bv_const (cond->e[1]);
    e2const = btor_node_is_bv_const (cond->e[2]);

    /* flip condition
     *
     * if either the 'then' or 'else' branch is const
     * with probability BTOR_OPT_PROP_FLIP_COND_CONST_PROB,
     * which is dynamically updated (depending on the number
     * times this case has already bin encountered)
     *
     * else with probability BTOR_OPT_PROP_FLIP_COND_PROB,
     * which is constant and will not be updated */
    if (((e1const && btor_bv_is_true (s0))
         || (e2const && btor_bv_is_false (s0)))
        && btor_rng_pick_with_prob (
               &btor->rng,
               (prob =
                    btor_opt_get (btor, BTOR_OPT_PROP_PROB_FLIP_COND_CONST))))
    {
      eidx = 0;

      if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
      {
        BtorPropSolver *slv;
        slv = BTOR_PROP_SOLVER (btor);
        if (++slv->nflip_cond_const
            == btor_opt_get (btor, BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          slv->nflip_cond_const = 0;
          slv->flip_cond_const_prob_delta =
              prob == 0
                  ? 100
                  : (prob == 1000 ? -100 : slv->flip_cond_const_prob_delta);
          btor_opt_set (btor,
                        BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
                        prob + slv->flip_cond_const_prob_delta);
        }
      }
      else
      {
        BtorSLSSolver *slv;
        slv = BTOR_SLS_SOLVER (btor);
        if (++slv->prop_nflip_cond_const
            == btor_opt_get (btor, BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL))
        {
          slv->prop_nflip_cond_const = 0;
          slv->prop_flip_cond_const_prob_delta =
              prob == 0 ? 100
                        : (prob == 1000 ? -100
                                        : slv->prop_flip_cond_const_prob_delta);
          btor_opt_set (btor,
                        BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
                        prob + slv->prop_flip_cond_const_prob_delta);
        }
      }
    }
    else if (btor_rng_pick_with_prob (
                 &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_FLIP_COND)))
    {
      eidx = 0;
    }
    /* assume cond to be fixed and select enabled branch */
    else
    {
      eidx = btor_bv_is_true (s0) ? 1 : 2;
    }
  }

#ifndef NBTORLOG
  char *a;
  BtorMemMgr *mm = btor->mm;

  BTORLOG (2, "");
  BTORLOG (2, "select path: %s", btor_util_node2string (cond));
  a = btor_bv_to_char (mm, s0);
  BTORLOG (2, "       e[0]: %s (%s)", btor_util_node2string (cond->e[0]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, btor_model_get_bv (btor, cond->e[1]));
  BTORLOG (2, "       e[1]: %s (%s)", btor_util_node2string (cond->e[1]), a);
  btor_mem_freestr (mm, a);
  a = btor_bv_to_char (mm, btor_model_get_bv (btor, cond->e[2]));
  BTORLOG (2, "       e[2]: %s (%s)", btor_util_node2string (cond->e[2]), a);
  btor_mem_freestr (mm, a);
  BTORLOG (2, "    * chose: %d", eidx);
#endif
  return eidx;
}

/* ========================================================================== */
/* Consistent value computation                                               */
/* ========================================================================== */

#ifdef NDEBUG
static BtorBitVector *inv_slice_bv (
    Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int32_t);
static BtorBitVector *inv_cond_bv (
    Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int32_t);
#endif

static BtorBitVector *
cons_add_bv (
    Btor *btor, BtorNode *add, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (add);
  assert (btor_node_is_regular (add));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (add->e[eidx]));

  (void) add;
  (void) s;
  (void) eidx;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_add++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }
  return btor_bv_new_random (btor->mm, &btor->rng, t->width);
}

static BtorBitVector *
cons_and_bv (
    Btor *btor, BtorNode *and, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (and);
  assert (btor_node_is_regular (and));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (and->e[eidx]));

  uint32_t i;
  BtorBitVector *res;
  BtorUIntStack dcbits;
  bool b;

  (void) s;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_and++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  b = btor_rng_pick_with_prob (
      &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_AND_FLIP));
  BTOR_INIT_STACK (btor->mm, dcbits);

  res = btor_bv_copy (btor->mm, btor_model_get_bv (btor, and->e[eidx]));

  /* s & res = t
   * -> all bits set in t must be set in res
   * -> all bits not set in t are chosen to be set randomly */
  for (i = 0; i < t->width; i++)
  {
    if (btor_bv_get_bit (t, i))
      btor_bv_set_bit (res, i, 1);
    else if (b)
      BTOR_PUSH_STACK (dcbits, i);
    else
      btor_bv_set_bit (res, i, btor_rng_pick_rand (&btor->rng, 0, 1));
  }

  if (b && BTOR_COUNT_STACK (dcbits))
    btor_bv_flip_bit (
        res,
        BTOR_PEEK_STACK (
            dcbits,
            btor_rng_pick_rand (&btor->rng, 0, BTOR_COUNT_STACK (dcbits) - 1)));

  BTOR_RELEASE_STACK (dcbits);
  return res;
}

static BtorBitVector *
cons_eq_bv (
    Btor *btor, BtorNode *eq, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (eq);
  assert (btor_node_is_regular (eq));
  assert (t);
  assert (t->width == 1);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (eq->e[eidx]));

  (void) t;

  BtorBitVector *res;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_eq++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  if (btor_rng_pick_with_prob (&btor->rng,
                               btor_opt_get (btor, BTOR_OPT_PROP_PROB_EQ_FLIP)))
  {
    res = btor_bv_copy (btor->mm, btor_model_get_bv (btor, eq->e[eidx]));
    btor_bv_flip_bit (res, btor_rng_pick_rand (&btor->rng, 0, res->width - 1));
  }
  else
  {
    res = btor_bv_new_random (btor->mm, &btor->rng, s->width);
  }
  return res;
}

static BtorBitVector *
cons_ult_bv (
    Btor *btor, BtorNode *ult, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (ult);
  assert (btor_node_is_regular (ult));
  assert (t);
  assert (t->width == 1);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BtorBitVector *bvmax, *zero, *tmp, *res;
  BtorMemMgr *mm;

  (void) ult;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_ult++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  mm    = btor->mm;
  bw    = s->width;
  isult = !btor_bv_is_zero (t);
  zero  = btor_bv_new (mm, bw);
  bvmax = btor_bv_ones (mm, bw);

  if (eidx && isult)
  {
    /* s < res = 1  ->  res > 0 */
    tmp = btor_bv_one (mm, bw);
    res = btor_bv_new_random_range (mm, &btor->rng, bw, tmp, bvmax);
    btor_bv_free (mm, tmp);
  }
  else if (!eidx && isult)
  {
    /* res < s = 1  ->  0 <= res < 1...1 */
    tmp = btor_bv_dec (mm, bvmax);
    res = btor_bv_new_random_range (mm, &btor->rng, bw, zero, tmp);
    btor_bv_free (mm, tmp);
  }
  else
  {
    res = btor_bv_new_random (mm, &btor->rng, bw);
  }

  btor_bv_free (mm, bvmax);
  btor_bv_free (mm, zero);

  return res;
}

static BtorBitVector *
cons_sll_bv (
    Btor *btor, BtorNode *sll, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (sll);
  assert (btor_node_is_regular (sll));
  assert (t);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || s->width == t->width);
  assert (eidx || btor_util_log_2 (t->width) == s->width);
  assert (!btor_node_is_bv_const (sll->e[eidx]));

  uint32_t i, ishift, bw, sbw, ctz_bvsll;
  BtorBitVector *res, *from, *to, *shift;
  BtorMemMgr *mm;

  (void) sll;
  (void) s;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_sll++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  mm  = btor->mm;
  bw  = t->width;
  sbw = btor_util_log_2 (bw);

  ctz_bvsll = btor_bv_get_num_trailing_zeros (t);
  from      = btor_bv_new (mm, sbw);
  to        = btor_bv_uint64_to_bv (
      mm, ctz_bvsll == bw ? ctz_bvsll - 1 : ctz_bvsll, sbw);
  shift = btor_bv_new_random_range (mm, &btor->rng, sbw, from, to);
  btor_bv_free (mm, from);
  btor_bv_free (mm, to);

  if (eidx)
  {
    res = shift;
  }
  else
  {
    ishift = btor_bv_to_uint64 (shift);
    res    = btor_bv_srl (mm, t, shift);
    for (i = 0; i < ishift; i++)
      btor_bv_set_bit (res, bw - 1 - i, btor_rng_pick_rand (&btor->rng, 0, 1));
    btor_bv_free (mm, shift);
  }

  return res;
}

static BtorBitVector *
cons_srl_bv (
    Btor *btor, BtorNode *srl, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (srl);
  assert (btor_node_is_regular (srl));
  assert (t);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || s->width == t->width);
  assert (eidx || btor_util_log_2 (t->width) == s->width);
  assert (!btor_node_is_bv_const (srl->e[eidx]));

  uint32_t i, ishift, bw, sbw;
  BtorBitVector *res, *from, *to, *shift;
  BtorMemMgr *mm;

  (void) srl;
  (void) s;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_srl++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  mm  = btor->mm;
  bw  = t->width;
  sbw = btor_util_log_2 (bw);

  for (i = 0; i < bw; i++)
    if (btor_bv_get_bit (t, bw - 1 - i)) break;

  from  = btor_bv_new (mm, sbw);
  to    = btor_bv_uint64_to_bv (mm, i == bw ? i - 1 : i, sbw);
  shift = btor_bv_new_random_range (mm, &btor->rng, sbw, from, to);
  btor_bv_free (mm, from);
  btor_bv_free (mm, to);

  if (eidx)
  {
    res = shift;
  }
  else
  {
    ishift = btor_bv_to_uint64 (shift);
    res    = btor_bv_srl (mm, t, shift);
    for (i = 0; i < ishift; i++)
      btor_bv_set_bit (res, i, btor_rng_pick_rand (&btor->rng, 0, 1));
    btor_bv_free (mm, shift);
  }

  return res;
}

static BtorBitVector *
cons_mul_bv (
    Btor *btor, BtorNode *mul, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (mul);
  assert (btor_node_is_regular (mul));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (mul->e[eidx]));

  uint32_t r, bw, ctz_res, ctz_bvmul;
  BtorBitVector *res, *tmp;
  BtorMemMgr *mm;

  (void) mul;
  (void) s;
  (void) eidx;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_mul++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  mm  = btor->mm;
  bw  = t->width;
  res = btor_bv_new_random (mm, &btor->rng, bw);
  if (!btor_bv_is_zero (t))
  {
    if (btor_bv_is_zero (res))
    {
      btor_bv_free (mm, res);
      res = btor_bv_new_random (mm, &btor->rng, bw);
    }
    /* t odd -> choose odd value > 0 */
    if (btor_bv_get_bit (t, 0))
    {
      if (!btor_bv_get_bit (res, 0)) btor_bv_set_bit (res, 0, 1);
    }
    /* t even -> choose random value > 0
     *               with number of 0-LSBs in res less or equal
     *               than in t */
    else
    {
      ctz_bvmul = btor_bv_get_num_trailing_zeros (t);
      /* choose res as 2^n with ctz(t) >= ctz(res) with prob 0.1 */
      if (btor_rng_pick_with_prob (&btor->rng, 100))
      {
        btor_bv_free (mm, res);
        res = btor_bv_new (mm, bw);
        btor_bv_set_bit (
            res, btor_rng_pick_rand (&btor->rng, 0, ctz_bvmul - 1), 1);
      }
      /* choose res as t / 2^n with prob 0.1
       * (note: bw not necessarily power of 2 -> do not use srl) */
      else if (btor_rng_pick_with_prob (&btor->rng, 100))
      {
        btor_bv_free (mm, res);
        if ((r = btor_rng_pick_rand (&btor->rng, 0, ctz_bvmul)))
        {
          tmp = btor_bv_slice (mm, t, bw - 1, r);
          res = btor_bv_uext (mm, tmp, r);
          btor_bv_free (mm, tmp);
        }
        else
        {
          res = btor_bv_copy (mm, t);
        }
      }
      /* choose random value with ctz(t) >= ctz(res) with prob 0.8 */
      else
      {
        ctz_res = btor_bv_get_num_trailing_zeros (res);
        if (ctz_res > ctz_bvmul)
          btor_bv_set_bit (
              res, btor_rng_pick_rand (&btor->rng, 0, ctz_bvmul - 1), 1);
      }
    }
  }

  return res;
}

static BtorBitVector *
cons_udiv_bv (Btor *btor,
              BtorNode *udiv,
              BtorBitVector *t,
              BtorBitVector *s,
              int32_t eidx)
{
  assert (btor);
  assert (udiv);
  assert (btor_node_is_regular (udiv));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (udiv->e[eidx]));

  uint32_t bw;
  BtorBitVector *res, *tmp, *tmp_s, *zero, *one, *bvmax;
  BtorMemMgr *mm;

  mm    = btor->mm;
  bw    = t->width;
  zero  = btor_bv_new (mm, bw);
  one   = btor_bv_one (mm, bw);
  bvmax = btor_bv_ones (mm, bw);

  (void) udiv;
  (void) s;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_udiv++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  if (eidx)
  {
    /* -> t = 1...1 then res = 0 or res = 1
     * -> else choose res s.t. res * t does not overflow */
    if (!btor_bv_compare (t, bvmax))
      res =
          btor_bv_uint64_to_bv (mm, btor_rng_pick_rand (&btor->rng, 0, 1), bw);
    else
    {
      res = btor_bv_new_random_range (mm, &btor->rng, bw, one, bvmax);
      while (btor_bv_is_umulo (mm, res, t))
      {
        tmp = btor_bv_sub (mm, res, one);
        btor_bv_free (mm, res);
        res = btor_bv_new_random_range (mm, &btor->rng, bw, one, tmp);
        btor_bv_free (mm, tmp);
      }
    }
  }
  else
  {
    /* -> t = 0 then res < 1...1
     * -> t = 1...1 then choose random res
     * -> else choose tmp_s s.t. res = tmp_s * t does not overflow */
    if (btor_bv_is_zero (t))
    {
      tmp = btor_bv_dec (mm, bvmax);
      res = btor_bv_new_random_range (mm, &btor->rng, bw, zero, tmp);
      btor_bv_free (mm, tmp);
    }
    else if (!btor_bv_compare (t, bvmax))
    {
      res = btor_bv_new_random (mm, &btor->rng, bw);
    }
    else
    {
      tmp_s = btor_bv_new_random_range (mm, &btor->rng, bw, one, bvmax);
      while (btor_bv_is_umulo (mm, tmp_s, t))
      {
        tmp = btor_bv_sub (mm, tmp_s, one);
        btor_bv_free (mm, tmp_s);
        tmp_s = btor_bv_new_random_range (mm, &btor->rng, bw, one, tmp);
        btor_bv_free (mm, tmp);
      }
      res = btor_bv_mul (mm, tmp_s, t);
      btor_bv_free (mm, tmp_s);
    }
  }

  btor_bv_free (mm, one);
  btor_bv_free (mm, zero);
  btor_bv_free (mm, bvmax);
  return res;
}

static BtorBitVector *
cons_urem_bv (Btor *btor,
              BtorNode *urem,
              BtorBitVector *t,
              BtorBitVector *s,
              int32_t eidx)
{
  assert (btor);
  assert (urem);
  assert (btor_node_is_regular (urem));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (urem->e[eidx]));

  uint32_t bw;
  BtorBitVector *res, *bvmax, *tmp;
  BtorMemMgr *mm;

  (void) urem;
  (void) s;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_urem++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }
  mm    = btor->mm;
  bw    = t->width;
  bvmax = btor_bv_ones (mm, bw);

  if (eidx)
  {
    /* t = 1...1  ->  res = 0 */
    if (!btor_bv_compare (t, bvmax))
    {
      res = btor_bv_new (mm, bw);
    }
    /* else res > t */
    else
    {
      tmp = btor_bv_inc (mm, t);
      res = btor_bv_new_random_range (mm, &btor->rng, bw, tmp, bvmax);
      btor_bv_free (mm, tmp);
    }
  }
  else
  {
    /* t = 1...1  ->  res = 1...1 */
    if (!btor_bv_compare (t, bvmax))
    {
      res = btor_bv_copy (mm, bvmax);
    }
    /* else res >= t */
    else
    {
      res = btor_bv_new_random_range (mm, &btor->rng, bw, t, bvmax);
    }
  }

  btor_bv_free (mm, bvmax);
  return res;
}

static BtorBitVector *
cons_concat_bv (Btor *btor,
                BtorNode *concat,
                BtorBitVector *t,
                BtorBitVector *s,
                int32_t eidx)
{
  assert (btor);
  assert (concat);
  assert (btor_node_is_regular (concat));
  assert (t);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (concat->e[eidx]));

  int32_t idx;
  uint32_t r;
  BtorBitVector *res;
  const BtorBitVector *bvcur;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.cons_concat++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_cons += 1;
  }

  idx = eidx ? 0 : 1;

  /* If one operand is const, with BTOR_OPT_CONC_FLIP_PROB
   * either slice bits out of current assignment and flip max. one bit
   * randomly, or slice bits out of given assignment 's'.  */

  if (btor_node_is_bv_const (concat->e[idx])
      && btor_rng_pick_with_prob (
             &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_CONC_FLIP)))
  {
    bvcur = btor_model_get_bv (btor, concat);
    res   = eidx ? btor_bv_slice (btor->mm, bvcur, t->width - s->width - 1, 0)
               : btor_bv_slice (btor->mm, bvcur, t->width - 1, s->width);
    r = btor_rng_pick_rand (&btor->rng, 0, res->width);
    if (r) btor_bv_flip_bit (res, r - 1);
  }
  else
  {
    res = eidx ? btor_bv_slice (btor->mm, t, t->width - s->width - 1, 0)
               : btor_bv_slice (btor->mm, t, t->width - 1, s->width);
  }
  return res;
}

static BtorBitVector *
cons_slice_bv (Btor *btor,
               BtorNode *slice,
               BtorBitVector *t,
               BtorBitVector *s,
               int32_t eidx)
{
  return inv_slice_bv (btor, slice, t, s, eidx);
}

static BtorBitVector *
cons_cond_bv (Btor *btor,
              BtorNode *cond,
              BtorBitVector *bvcond,
              BtorBitVector *s,
              int32_t eidx)
{
  return inv_cond_bv (btor, cond, bvcond, s, eidx);
}

/* ========================================================================== */
/* Inverse value computation                                                  */
/* ========================================================================== */

static BtorBitVector *
res_rec_conf (Btor *btor,
              BtorNode *exp,
              BtorNode *e,
              BtorBitVector *t,
              BtorBitVector *s,
              int32_t eidx,
              BtorBitVector *(*fun) (Btor *,
                                     BtorNode *,
                                     BtorBitVector *,
                                     BtorBitVector *,
                                     int32_t),
              char *op)
{
  assert (btor);
  assert (btor->slv->kind == BTOR_PROP_SOLVER_KIND
          || btor->slv->kind == BTOR_SLS_SOLVER_KIND);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (e);
  assert (t);
  assert (s);
  assert (op);
  (void) op;
  (void) e;

  bool is_recoverable;
  uint32_t no_move_on_conflict, prop_entailed;
  BtorBitVector *res;
  BtorMemMgr *mm;

  mm = btor->mm;

  is_recoverable      = btor_node_is_bv_const (e) ? false : true;
  no_move_on_conflict = btor_opt_get (btor, BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT);

  res =
      no_move_on_conflict && !is_recoverable ? 0 : fun (btor, exp, t, s, eidx);
  assert (no_move_on_conflict || res);

#ifndef NDEBUG
  char *str_s = btor_bv_to_char (mm, s);
  char *str_t = btor_bv_to_char (mm, t);
  BTORLOG (2, "");
  if (eidx)
    BTORLOG (2,
             "%s CONFLICT (@%d): %s := %s %s x",
             is_recoverable ? "recoverable" : "non-recoverable",
             btor_node_get_id (exp),
             str_t,
             str_s,
             op);
  else
    BTORLOG (2,
             "%s CONFLICT (@%d): %s := x %s %s",
             is_recoverable ? "recoverable" : "non-recoverable",
             btor_node_get_id (exp),
             str_t,
             op,
             str_s);
  btor_mem_freestr (mm, str_s);
  btor_mem_freestr (mm, str_t);
#endif
  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
    BtorPropSolver *slv = BTOR_PROP_SOLVER (btor);
    if (is_recoverable)
    {
#ifndef NDEBUG
      /* fix counters since we always increase the counter, even in the conflict
       * case  (except for slice and cond where inv = cons) */
      switch (exp->kind)
      {
        case BTOR_BV_ADD_NODE: slv->stats.inv_add -= 1; break;
        case BTOR_BV_AND_NODE: slv->stats.inv_and -= 1; break;
        case BTOR_BV_EQ_NODE: slv->stats.inv_eq -= 1; break;
        case BTOR_BV_ULT_NODE: slv->stats.inv_ult -= 1; break;
        case BTOR_BV_SLL_NODE: slv->stats.inv_sll -= 1; break;
        case BTOR_BV_SRL_NODE: slv->stats.inv_srl -= 1; break;
        case BTOR_BV_MUL_NODE: slv->stats.inv_mul -= 1; break;
        case BTOR_BV_UDIV_NODE: slv->stats.inv_udiv -= 1; break;
        case BTOR_BV_UREM_NODE: slv->stats.inv_urem -= 1; break;
        case BTOR_BV_CONCAT_NODE: slv->stats.inv_concat -= 1; break;
        default:
          assert (btor_node_is_bv_slice (exp) || btor_node_is_bv_cond (exp));
          /* do not decrease, we do not call cons function in conflict case */
      }
#endif
      slv->stats.rec_conf += 1;
      /* recoverable conflict, push entailed propagation */
      assert (exp->arity == 2);
      prop_entailed = btor_opt_get (btor, BTOR_OPT_PROP_ENTAILED);
      if (prop_entailed != BTOR_PROP_ENTAILED_OFF)
      {
        BtorPropInfo prop = {exp, btor_bv_copy (mm, t), eidx ? 0 : 1};
        if (BTOR_EMPTY_STACK (slv->toprop)
            || prop_entailed == BTOR_PROP_ENTAILED_ALL)
        {
          BTOR_PUSH_STACK (slv->toprop, prop);
        }
        else if (prop_entailed == BTOR_PROP_ENTAILED_LAST)
        {
          assert (BTOR_COUNT_STACK (slv->toprop) == 1);
          BTOR_POKE_STACK (slv->toprop, 0, prop);
        }
        assert (prop_entailed == BTOR_PROP_ENTAILED_ALL
                || BTOR_COUNT_STACK (slv->toprop) == 1);
      }
      /* fix counter since we always increase the counter, even in the conflict
       * case (except for slice and cond, where inv = cons)*/
      if (!btor_node_is_bv_slice (exp) && !btor_node_is_bv_cond (exp))
        slv->stats.props_inv -= 1;
    }
    else
    {
      slv->stats.non_rec_conf += 1;
      /* non-recoverable conflict, entailed propagations are thus invalid */
      btor_proputils_reset_prop_info_stack (mm, &slv->toprop);
    }
  }
  else
  {
    if (is_recoverable)
      BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
    else
      BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
  }

  return res;
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static void
check_result_binary_dbg (Btor *btor,
                         BtorBitVector *(*fun) (BtorMemMgr *,
                                                const BtorBitVector *,
                                                const BtorBitVector *),
                         BtorNode *exp,
                         BtorBitVector *s,
                         BtorBitVector *t,
                         BtorBitVector *res,
                         int32_t eidx,
                         char *op)
{
  assert (btor);
  assert (fun);
  assert (exp);
  assert (s);
  assert (t);
  assert (res);
  assert (op);

  (void) exp;
  (void) op;

  BtorBitVector *tmp;
  char *str_s, *str_t, *str_res;

  tmp = eidx ? fun (btor->mm, s, res) : fun (btor->mm, res, s);
  assert (!btor_bv_compare (tmp, t));
  str_t   = btor_bv_to_char (btor->mm, t);
  str_s   = btor_bv_to_char (btor->mm, s);
  str_res = btor_bv_to_char (btor->mm, res);
  BTORLOG (3,
           "prop (e[%d]): %s: %s := %s %s %s",
           eidx,
           btor_util_node2string (exp),
           str_t,
           eidx ? str_s : str_res,
           op,
           eidx ? str_res : str_s);
  btor_bv_free (btor->mm, tmp);
  btor_mem_freestr (btor->mm, str_t);
  btor_mem_freestr (btor->mm, str_s);
  btor_mem_freestr (btor->mm, str_res);
}
#endif

/* -------------------------------------------------------------------------- */
/* INV: and                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_add_bv (
    Btor *btor, BtorNode *add, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (add);
  assert (btor_node_is_regular (add));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (add->e[eidx]));

  BtorBitVector *res;

  (void) add;
  (void) eidx;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_add++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  /**
   * invertibility condition: true
   *
   * res +   s = t   |->   res = t - s
   * s   + res = t   |
   */

  res = btor_bv_sub (btor->mm, t, s);
#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_bv_add, add, s, t, res, eidx, "+");
#endif
  return res;
}

#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_and_bv (
    Btor *btor, BtorNode *and, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (and);
  assert (btor_node_is_regular (and));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (and->e[eidx]));

  uint32_t i;
  int32_t bit_and, bit_e;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
  BtorUIntStack dcbits;
  bool b;

  mm = btor->mm;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_and++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  e  = and->e[eidx ? 0 : 1];
  assert (e);

  /* check invertibility, if not invertible: CONFLICT */
  if (!btor_is_inv_and (mm, s, t))
  {
    return res_rec_conf (btor, and, e, t, s, eidx, cons_and_bv, "AND");
  }

  b = btor_rng_pick_with_prob (
      &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_AND_FLIP));
  BTOR_INIT_STACK (mm, dcbits);

  res = btor_bv_copy (mm, btor_model_get_bv (btor, and->e[eidx]));
  assert (res);

  for (i = 0; i < t->width; i++)
  {
    bit_and = btor_bv_get_bit (t, i);
    bit_e   = btor_bv_get_bit (s, i);

    assert (!bit_and || bit_e);

    /* ----------------------------------------------------------------------
     * res & s = s & res = t
     *
     * -> all bits set in t and s must be set in res
     * -> all bits not set in t but set in s must not be set in res
     * -> all bits not set in s can be chosen to be set randomly
     * ---------------------------------------------------------------------- */
    if (bit_and)
      btor_bv_set_bit (res, i, 1);
    else if (bit_e)
      btor_bv_set_bit (res, i, 0);
    else if (b)
      BTOR_PUSH_STACK (dcbits, i);
    else
      btor_bv_set_bit (res, i, btor_rng_pick_rand (&btor->rng, 0, 1));
  }

  if (b && BTOR_COUNT_STACK (dcbits))
    btor_bv_flip_bit (
        res,
        BTOR_PEEK_STACK (
            dcbits,
            btor_rng_pick_rand (&btor->rng, 0, BTOR_COUNT_STACK (dcbits) - 1)));

#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_bv_and, and, s, t, res, eidx, "AND");
#endif

  BTOR_RELEASE_STACK (dcbits);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: eq                                                                    */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_eq_bv (
    Btor *btor, BtorNode *eq, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (eq);
  assert (btor_node_is_regular (eq));
  assert (t);
  assert (t->width == 1);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (eq->e[eidx]));

  BtorBitVector *res;
  BtorMemMgr *mm;

  mm = btor->mm;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_eq++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  /**
   * invertibility condition: true
   * (res = s) = t   ->   t = 0: choose random res != s
   *                      t = 1: res = s
   */

  if (btor_bv_is_zero (t))
  {
    if (btor_rng_pick_with_prob (
            &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_EQ_FLIP)))
    {
      res = 0;
      do
      {
        if (res) btor_bv_free (btor->mm, res);
        res = btor_bv_copy (btor->mm, btor_model_get_bv (btor, eq->e[eidx]));
        btor_bv_flip_bit (res,
                          btor_rng_pick_rand (&btor->rng, 0, res->width - 1));
      } while (!btor_bv_compare (res, s));
    }
    else
    {
      res = 0;
      do
      {
        if (res) btor_bv_free (mm, res);
        res = btor_bv_new_random (mm, &btor->rng, s->width);
      } while (!btor_bv_compare (res, s));
    }
  }
  else
  {
    res = btor_bv_copy (mm, s);
  }

#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_bv_eq, eq, s, t, res, eidx, "=");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: ult                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_ult_bv (
    Btor *btor, BtorNode *ult, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (ult);
  assert (btor_node_is_regular (ult));
  assert (t);
  assert (t->width == 1);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (ult->e[eidx]));

  bool isult;
  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *zero, *one, *bvmax, *tmp;
  BtorMemMgr *mm;

  mm = btor->mm;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_ult++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  e  = ult->e[eidx ? 0 : 1];
  assert (e);

  /* check invertibility, if not invertible: CONFLICT */
  if (!btor_is_inv_ult (mm, s, t, eidx))
  {
    return res_rec_conf (btor, ult, e, t, s, eidx, cons_ult_bv, "<");
  }

  zero  = btor_bv_new (mm, s->width);
  one   = btor_bv_one (mm, s->width);
  bvmax = btor_bv_ones (mm, s->width);
  isult = !btor_bv_is_zero (t);
  bw    = s->width;

  res = 0;

  if (eidx)
  {
    assert (!isult || btor_bv_compare (s, bvmax)); /* CONFLICT: 1...1 < e[1] */
    if (!isult)
    {
      /* s >= e[1] -------------------------------------------------------- */
      res = btor_bv_new_random_range (mm, &btor->rng, bw, zero, s);
    }
    else
    {
      /* s < e[1] --------------------------------------------------------- */
      tmp = btor_bv_add (mm, s, one);
      res = btor_bv_new_random_range (mm, &btor->rng, bw, tmp, bvmax);
      btor_bv_free (mm, tmp);
    }
  }
  else
  {
    assert (!isult || !btor_bv_is_zero (s)); /* CONFLICT: e[0] < 0  */
    if (!isult)
    {
      /* e[0] >= s -------------------------------------------------------- */
      res = btor_bv_new_random_range (mm, &btor->rng, bw, s, bvmax);
    }
    else
    {
      /* e[0] < s --------------------------------------------------------- */
      tmp = btor_bv_sub (mm, s, one);
      res = btor_bv_new_random_range (mm, &btor->rng, bw, zero, tmp);
      btor_bv_free (mm, tmp);
    }
  }

#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_bv_ult, ult, s, t, res, eidx, "<");
#endif
  btor_bv_free (mm, zero);
  btor_bv_free (mm, one);
  btor_bv_free (mm, bvmax);
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: sll                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_sll_bv (
    Btor *btor, BtorNode *sll, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (sll);
  assert (btor_node_is_regular (sll));
  assert (t);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || s->width == t->width);
  assert (eidx || btor_util_log_2 (t->width) == s->width);
  assert (!btor_node_is_bv_const (sll->e[eidx]));

  uint32_t i, ctz_s, ctz_t, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *tmp, *bvmax;
  BtorMemMgr *mm;

  mm = btor->mm;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_sll++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  e  = sll->e[eidx ? 0 : 1];
  assert (e);

  /* check invertibility, if not invertible: CONFLICT */
  if (!btor_is_inv_sll (mm, s, t, eidx))
  {
    return res_rec_conf (btor, sll, e, t, s, eidx, cons_sll_bv, "<<");
  }

  res = 0;

  /* ------------------------------------------------------------------------
   * s << e[1] = t
   *
   * -> identify possible shift value via zero LSB in t
   *    (considering zero LSB in s)
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    sbw = btor_util_log_2 (t->width);

    if (btor_bv_is_zero (s) && btor_bv_is_zero (t))
    {
      /* 0...0 << e[1] = 0...0 -> choose res randomly ----------------------- */
      res = btor_bv_new_random (mm, &btor->rng, sbw);
    }
    else
    {
      /* -> ctz(s) > ctz (t) -> conflict
       * -> shift = ctz(t) - ctz(s)
       *      -> if t = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       *           + and if res < bw
       * -> else conflict
       * -------------------------------------------------------------------- */
      ctz_s = btor_bv_get_num_trailing_zeros (s);
      ctz_t = btor_bv_get_num_trailing_zeros (t);
      assert (ctz_s <= ctz_t); /* CONFLICT: ctz_s > ctz_t */
      shift = ctz_t - ctz_s;
      assert (shift <= t->width - 1); /* CONFLICT: do not allow shift by bw */
      if (btor_bv_is_zero (t))
      {
        /* x...x0 << e[1] = 0...0
         * -> choose random shift <= res < bw
         * ---------------------------------------------------------------- */
        bvmax = btor_bv_ones (mm, sbw);
        tmp   = btor_bv_uint64_to_bv (mm, (uint64_t) shift, sbw);
        res   = btor_bv_new_random_range (mm, &btor->rng, sbw, tmp, bvmax);
        btor_bv_free (mm, bvmax);
        btor_bv_free (mm, tmp);
      }
      else
      {
#ifndef NDEBUG
        uint32_t j;
        for (i = 0, j = shift, res = 0; i < s->width - j; i++)
        {
          /* CONFLICT: shifted bits must match */
          assert (btor_bv_get_bit (s, i) == btor_bv_get_bit (t, j + i));
        }
#endif
        res = btor_bv_uint64_to_bv (mm, (uint64_t) shift, sbw);
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] << s = t
   *
   * -> e[0] = t >> s
   *    set irrelevant MSBs (the ones that get shifted out) randomly
   * ------------------------------------------------------------------------ */
  else
  {
    /* using uint64_t here is no problem
     * (max bit width currently handled by Boolector is INT32_MAX) */
    shift = btor_bv_to_uint64 (s);

    /* CONFLICT: the LSBs shifted must be zero */
    assert (btor_bv_get_num_trailing_zeros (t) >= shift);

    res = btor_bv_srl (mm, t, s);
    for (i = 0; i < shift; i++)
    {
      btor_bv_set_bit (
          res, res->width - 1 - i, btor_rng_pick_rand (&btor->rng, 0, 1));
    }
  }
#ifndef NDEBUG
  check_result_binary_dbg (btor, btor_bv_sll, sll, s, t, res, eidx, "<<");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: srl                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_srl_bv (
    Btor *btor, BtorNode *srl, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (srl);
  assert (btor_node_is_regular (srl));
  assert (t);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!eidx || s->width == t->width);
  assert (eidx || btor_util_log_2 (t->width) == s->width);
  assert (!btor_node_is_bv_const (srl->e[eidx]));

  uint32_t i, j, clz_s, clz_t, shift, sbw;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_srl++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  mm = btor->mm;
  e  = srl->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* ------------------------------------------------------------------------
   * s >> e[1] = t
   *
   * -> identify possible shift value via zero MSBs in t
   *    (considering zero MSBs in s)
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    sbw = btor_util_log_2 (t->width);

    if (btor_bv_is_zero (s) && btor_bv_is_zero (t))
    {
      /* 0...0 >> e[1] = 0...0 -> choose random res ------------------------- */
      res = btor_bv_new_random (mm, &btor->rng, sbw);
    }
    else
    {
      /* clz(s) > clz(t) -> conflict
       *
       * -> shift = clz(t) - clz(s)
       *      -> if t = 0 choose shift <= res < bw
       *      -> else res = shift
       *           + if all remaining shifted bits match
       *           + and if res < bw
       * -> else conflict
       * -------------------------------------------------------------------- */
      clz_s = btor_bv_get_num_leading_zeros (s);
      clz_t = btor_bv_get_num_leading_zeros (t);
      if (clz_s <= clz_t)
      {
        shift = clz_t - clz_s;

        if (shift > t->width - 1)
        {
          /* CONFLICT: do not allow shift by bw ----------------------------- */
          assert (btor_bv_is_zero (t));
        BVSRL_CONF:
          res = res_rec_conf (btor, srl, e, t, s, eidx, cons_srl_bv, ">>");
#ifndef NDEBUG
          is_inv = false;
#endif
        }
        else if (btor_bv_is_zero (t))
        {
          /* x...x0 >> e[1] = 0...0
           * -> choose random shift <= res < bw
           * ---------------------------------------------------------------- */
          bvmax = btor_bv_ones (mm, sbw);
          tmp   = btor_bv_uint64_to_bv (mm, (uint64_t) shift, sbw);
          res   = btor_bv_new_random_range (mm, &btor->rng, sbw, tmp, bvmax);
          btor_bv_free (mm, bvmax);
          btor_bv_free (mm, tmp);
        }
        else
        {
          for (i = 0, j = shift, res = 0; i < s->width - j; i++)
          {
            if (btor_bv_get_bit (s, s->width - 1 - i)
                != btor_bv_get_bit (t, t->width - 1 - (j + i)))
            {
              /* CONFLICT: shifted bits must match -------------------------- */
              goto BVSRL_CONF;
            }
          }

          res = btor_bv_uint64_to_bv (mm, (uint64_t) shift, sbw);
        }
      }
      else
      {
        goto BVSRL_CONF;
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] >> s = t
   *
   * -> e[0] = t << s
   *    set irrelevant LSBs (the ones that get shifted out) randomly
   * ------------------------------------------------------------------------ */
  else
  {
    /* cast is no problem (max bit width handled by Boolector is INT32_MAX) */
    shift = (int32_t) btor_bv_to_uint64 (s);

    if (btor_bv_get_num_leading_zeros (t) < shift)
    {
      /* CONFLICT: the MSBs shifted must be zero ---------------------------- */
      goto BVSRL_CONF;
    }

    res = btor_bv_sll (mm, t, s);
    for (i = 0; i < shift; i++)
      btor_bv_set_bit (res, i, btor_rng_pick_rand (&btor->rng, 0, 1));
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (btor, btor_bv_srl, srl, s, t, res, eidx, ">>");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: mul                                                                   */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_mul_bv (
    Btor *btor, BtorNode *mul, BtorBitVector *t, BtorBitVector *s, int32_t eidx)
{
  assert (btor);
  assert (mul);
  assert (btor_node_is_regular (mul));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (mul->e[eidx]));

  int32_t lsb_s, t_lsb, ispow2_s;
  uint32_t i, j, bw;
  BtorBitVector *res, *inv, *tmp, *tmp2;
  BtorMemMgr *mm;
  BtorNode *e;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_mul++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  mm = btor->mm;
  e  = mul->e[eidx ? 0 : 1];
  assert (e);
  bw = t->width;

  res = 0;

  /* ------------------------------------------------------------------------
   * s * res = t
   *
   * -> if s = 0: * t = 0 -> choose random value for res
   *              * t > 0 -> conflict
   *
   * -> if t odd and s even -> conflict
   *
   * -> if s odd -> determine res via modular inverse (extended euklid)
   *                  (unique solution)
   *
   * -> else if s is even (non-unique, multiple solutions possible!)
   *      * s = 2^n: + if number of 0-LSBs in t < n -> conflict
   *                 + else res = t >> n
   *                     (with all bits shifted in randomly set to 0 or 1)
   *      * else: s = 2^n * m, m is odd
   *              + if number of 0-LSBs in t < n -> conflict
   *              + else c' = t >> n
   *                (with all bits shifted in randomly set to 0 or 1)
   *                -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
   * ------------------------------------------------------------------------ */

  lsb_s = btor_bv_get_bit (s, 0);
  t_lsb = btor_bv_get_bit (t, 0);

  if (btor_bv_is_zero (s))
  {
    /* s = 0 -> if t = 0 choose random value, else conflict ----------------- */
    if (btor_bv_is_zero (t))
    {
      res = btor_bv_new_random (mm, &btor->rng, bw);
    }
    else
    {
    BVMUL_CONF:
      /* CONFLICT: s = 0 but t != 0 ----------------------------------------- */
      res = res_rec_conf (btor, mul, e, t, s, eidx, cons_mul_bv, "*");
#ifndef NDEBUG
      is_inv = false;
#endif
    }
  }
  else if (t_lsb && !lsb_s)
  {
    /* CONFLICT: t odd and s is even ---------------------------------------- */
    goto BVMUL_CONF;
  }
  else
  {
    /* ----------------------------------------------------------------------
     * s odd
     *
     * -> determine res via modular inverse (extended euklid)
     *    (unique solution)
     * ---------------------------------------------------------------------- */
    if (lsb_s)
    {
      inv = btor_bv_mod_inverse (mm, s);
      res = btor_bv_mul (mm, inv, t);
      btor_bv_free (mm, inv);
    }
    /* ----------------------------------------------------------------------
     * s even
     * (non-unique, multiple solutions possible!)
     *
     * if s = 2^n: + if number of 0-LSBs in t < n -> conflict
     *             + else res = t >> n
     *                      (with all bits shifted in set randomly)
     * else: s = 2^n * m, m is odd
     *       + if number of 0-LSBs in t < n -> conflict
     *       + else c' = t >> n (with all bits shifted in set randomly)
     *         res = c' * m^-1 (with m^-1 the mod inverse of m)
     * ---------------------------------------------------------------------- */
    else
    {
      if ((ispow2_s = btor_bv_power_of_two (s)) >= 0)
      {
        for (i = 0; i < bw; i++)
          if (btor_bv_get_bit (t, i)) break;
        if (i < (uint32_t) ispow2_s)
        {
          /* CONFLICT: number of 0-LSBs in t < n (for s = 2^n) -------------- */
          goto BVMUL_CONF;
        }
        else
        {
          /* res = t >> n with all bits shifted in set randomly
           * (note: bw is not necessarily power of 2 -> do not use srl)
           * ---------------------------------------------------------------- */
          tmp = btor_bv_slice (mm, t, bw - 1, ispow2_s);
          res = btor_bv_uext (mm, tmp, ispow2_s);
          assert (res->width == bw);
          for (i = 0; i < (uint32_t) ispow2_s; i++)
            btor_bv_set_bit (
                res, bw - 1 - i, btor_rng_pick_rand (&btor->rng, 0, 1));
          btor_bv_free (mm, tmp);
        }
      }
      else
      {
        for (i = 0; i < bw; i++)
          if (btor_bv_get_bit (t, i)) break;
        for (j = 0; j < bw; j++)
          if (btor_bv_get_bit (s, j)) break;
        if (i < j)
        {
          /* CONFLICT: number of 0-LSB in t < number of 0-LSB in s ---------- */
          goto BVMUL_CONF;
        }
        else
        {
          /* c' = t >> n (with all bits shifted in set randomly)
           * (note: bw is not necessarily power of 2 -> do not use srl)
           * -> res = c' * m^-1 (with m^-1 the mod inverse of m, m odd)
           * ---------------------------------------------------------------- */
          tmp = btor_bv_slice (mm, t, bw - 1, j);
          res = btor_bv_uext (mm, tmp, j);
          assert (res->width == bw);
          btor_bv_free (mm, tmp);

          tmp  = btor_bv_slice (mm, s, bw - 1, j);
          tmp2 = btor_bv_uext (mm, tmp, j);
          assert (tmp2->width == bw);
          assert (btor_bv_get_bit (tmp2, 0));
          inv = btor_bv_mod_inverse (mm, tmp2);
          btor_bv_free (mm, tmp);
          btor_bv_free (mm, tmp2);
          tmp = res;
          res = btor_bv_mul (mm, tmp, inv);
          /* choose one of all possible values */
          for (i = 0; i < j; i++)
            btor_bv_set_bit (
                res, bw - 1 - i, btor_rng_pick_rand (&btor->rng, 0, 1));
          btor_bv_free (mm, tmp);
          btor_bv_free (mm, inv);
        }
      }
    }
  }

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (btor, btor_bv_mul, mul, s, t, res, eidx, "*");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: udiv                                                                  */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_udiv_bv (Btor *btor,
             BtorNode *udiv,
             BtorBitVector *t,
             BtorBitVector *s,
             int32_t eidx)
{
  assert (btor);
  assert (udiv);
  assert (btor_node_is_regular (udiv));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (udiv->e[eidx]));

  uint32_t bw;
  BtorNode *e;
  BtorBitVector *res, *lo, *up, *one, *bvmax, *tmp;
  BtorMemMgr *mm;
  BtorRNG *rng;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_udiv++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  mm  = btor->mm;
  rng = &btor->rng;
  e   = udiv->e[eidx ? 0 : 1];
  assert (e);
  bw = s->width;

  one   = btor_bv_one (mm, s->width);
  bvmax = btor_bv_ones (mm, t->width); /* 2^bw - 1 */

  res = 0;

  /* ------------------------------------------------------------------------
   * s / e[1] = t
   *
   * -> if t = 2^bw - 1: + s = t = 2^bw - 1 -> e[1] = 1 or e[1] = 0
   *                     + s != t -> e[1] = 0
   * -> if t = 0 and 0 < s < 2^bw - 1 choose random e[1] > s
   *             and s = 0            choose random e[1] > 0
   *             else conflict
   * -> if s < t -> conflict
   * -> if t is a divisor of s choose with 0.5 prob out of
   *      + e[1] = t / s
   *      + choose s s.t. s / e[1] = t
   * -> else choose s s.t. s / e[1] = t
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (!btor_bv_compare (t, bvmax))
    {
      if (!btor_bv_compare (s, t) && btor_rng_pick_with_prob (&btor->rng, 500))
      {
        /* s = t = 2^bw - 1 -> choose either e[1] = 0 or e[1] = 1
         * with prob 0.5
         * ------------------------------------------------------------------ */
        res = btor_bv_one (mm, bw);
      }
      else
      {
        /* t = 2^bw - 1 and s != t -> e[1] = 0 ------------------------------ */
        res = btor_bv_new (mm, bw);
      }
    }
    else if (btor_bv_is_zero (t))
    {
      if (btor_bv_is_zero (s))
      {
        /* t = 0 and s = 0 -> choose random e[1] > 0 ------------------------ */
        res = btor_bv_new_random_range (mm, rng, bw, one, bvmax);
      }
      else if (btor_bv_compare (s, bvmax))
      {
        /* t = 0 and 0 < s < 2^bw - 1 -> choose random e[1] > s ------------- */
        tmp = btor_bv_inc (mm, s);
        res = btor_bv_new_random_range (mm, rng, bw, tmp, bvmax);
        btor_bv_free (mm, tmp);
      }
      else
      {
      BVUDIV_CONF:
        /* CONFLICT --------------------------------------------------------- */
        res = res_rec_conf (btor, udiv, e, t, s, eidx, cons_udiv_bv, "/");
#ifndef NDEBUG
        is_inv = false;
#endif
      }
    }
    else if (btor_bv_compare (s, t) < 0)
    {
      /* CONFLICT: s < t ---------------------------------------------------- */
      goto BVUDIV_CONF;
    }
    else
    {
      /* if t is a divisor of s, choose e[1] = s / t
       * with prob = 0.5 and a s s.t. s / e[1] = t otherwise
       * -------------------------------------------------------------------- */
      tmp = btor_bv_urem (mm, s, t);
      if (btor_bv_is_zero (tmp) && btor_rng_pick_with_prob (rng, 500))
      {
        btor_bv_free (mm, tmp);
        res = btor_bv_udiv (mm, s, t);
      }
      else
      {
        /* choose e[1] out of all options that yield s / e[1] = t
         * Note: udiv always truncates the results towards 0.
         * ------------------------------------------------------------------ */

        /* determine upper and lower bounds for e[1]:
         * up = s / t
         * lo = s / (t + 1) + 1
         * if lo > up -> conflict */
        btor_bv_free (mm, tmp);
        up  = btor_bv_udiv (mm, s, t); /* upper bound */
        tmp = btor_bv_inc (mm, t);
        lo  = btor_bv_udiv (mm, s, tmp); /* lower bound (excl.) */
        btor_bv_free (mm, tmp);
        tmp = lo;
        lo  = btor_bv_inc (mm, tmp); /* lower bound (incl.) */
        btor_bv_free (mm, tmp);

        if (btor_bv_compare (lo, up) > 0)
        {
          /* CONFLICT: lo > up ---------------------------------------------- */
          btor_bv_free (mm, lo);
          btor_bv_free (mm, up);
          goto BVUDIV_CONF;
        }
        else
        {
          /* choose lo <= e[1] <= up ---------------------------------------- */
          res = btor_bv_new_random_range (mm, rng, bw, lo, up);
          btor_bv_free (mm, lo);
          btor_bv_free (mm, up);
        }
      }
    }
  }

  /* ------------------------------------------------------------------------
   * e[0] / s = t
   *
   * -> if t = 2^bw - 1 and s = 1 e[0] = 2^bw-1
   *                    and s = 0, choose random e[0] > 0
   *                    and s > 0 -> conflict
   * -> if s = 0 and t < 2^bw - 1 -> conflict
   * -> if s * t does not overflow, choose with 0.5 prob out of
   *      + e[0] = s * t
   *      + choose s s.t. e[0] / s = t
   * -> else choose s s.t. e[0] / s = t
   * ------------------------------------------------------------------------ */
  else
  {
    if (!btor_bv_compare (t, bvmax))
    {
      if (!btor_bv_compare (s, one))
      {
        /* t = 2^bw-1 and s = 1 -> e[0] = 2^bw-1 ---------------------------- */
        res = btor_bv_copy (mm, bvmax);
      }
      else if (btor_bv_is_zero (s))
      {
        /* t = 2^bw - 1 and s = 0 -> choose random e[0] --------------------- */
        res = btor_bv_new_random (mm, rng, bw);
      }
      else
      {
        /* CONFLICT --------------------------------------------------------- */
        goto BVUDIV_CONF;
      }
    }
    else if (btor_bv_is_zero (s))
    {
      /* CONFLICT: s = 0 and t < 2^bw - 1 ----------------------------------- */
      goto BVUDIV_CONF;
    }
    else
    {
      /* if s * t does not overflow, choose e[0] = s * t
       * with prob = 0.5 and a s s.t. e[0] / s = t otherwise */

      if (btor_bv_is_umulo (mm, s, t))
      {
        /* CONFLICT: overflow: s * t ---------------------------------------- */
        goto BVUDIV_CONF;
      }
      else
      {
        if (btor_rng_pick_with_prob (rng, 500))
          res = btor_bv_mul (mm, s, t);
        else
        {
          /* choose e[0] out of all options that yield
           * e[0] / s = t
           * Note: udiv always truncates the results towards 0.
           * ---------------------------------------------------------------- */

          /* determine upper and lower bounds for e[0]:
           * up = s * (budiv + 1) - 1
           *      if s * (t + 1) does not overflow
           *      else 2^bw - 1
           * lo = s * t */
          lo  = btor_bv_mul (mm, s, t);
          tmp = btor_bv_inc (mm, t);
          if (btor_bv_is_umulo (mm, s, tmp))
          {
            btor_bv_free (mm, tmp);
            up = btor_bv_copy (mm, bvmax);
          }
          else
          {
            up = btor_bv_mul (mm, s, tmp);
            btor_bv_free (mm, tmp);
            tmp = btor_bv_dec (mm, up);
            btor_bv_free (mm, up);
            up = tmp;
          }

          res = btor_bv_new_random_range (mm, &btor->rng, s->width, lo, up);

          btor_bv_free (mm, up);
          btor_bv_free (mm, lo);
        }
      }
    }
  }

  btor_bv_free (mm, bvmax);
  btor_bv_free (mm, one);
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (btor, btor_bv_udiv, udiv, s, t, res, eidx, "/");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: urem                                                                  */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_urem_bv (Btor *btor,
             BtorNode *urem,
             BtorBitVector *t,
             BtorBitVector *s,
             int32_t eidx)
{
  assert (btor);
  assert (urem);
  assert (btor_node_is_regular (urem));
  assert (t);
  assert (s);
  assert (s->width == t->width);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (urem->e[eidx]));

  uint32_t bw, cnt;
  int32_t cmp;
  BtorNode *e;
  BtorBitVector *res, *bvmax, *tmp, *tmp2, *one, *n, *mul, *up, *sub;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_urem++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  mm = btor->mm;
  e  = urem->e[eidx ? 0 : 1];
  assert (e);

  bw = t->width;

  bvmax = btor_bv_ones (mm, bw); /* 2^bw - 1 */
  one   = btor_bv_one (mm, bw);

  res = 0;

  /* -----------------------------------------------------------------------
   * s % e[1] = t
   *
   * -> if t = 1...1 -> s = 1...1 and e[1] = 0...0, else conflict
   * -> if s = t, choose either e[1] = 0 or some e[1] > t randomly
   * -> if t > 0 and t = s - 1, conflict
   * -> if s > t, e[1] = ((s - t) / n) > t, else conflict
   * -> if s < t, conflict
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    if (!btor_bv_compare (t, bvmax))
    {
      /* CONFLICT: t = 1...1 but s != 1...1 --------------------------------- */
      if (btor_bv_compare (s, bvmax))
      {
      BVUREM_CONF:
        res = res_rec_conf (btor, urem, e, t, s, eidx, cons_urem_bv, "%");
#ifndef NDEBUG
        is_inv = false;
#endif
      }
      else
      {
        /* s % e[1] = 1...1 -> s = 1...1, e[1] = 0 -------------------------- */
        res = btor_bv_new (mm, bw);
      }
    }
    else
    {
      cmp = btor_bv_compare (s, t);

      if (cmp == 0)
      {
        /* s = t, choose either e[1] = 0 or random e[1] > t ----------------- */

        /* choose e[1] = 0 with prob = 0.25*/
        if (btor_rng_pick_with_prob (&btor->rng, 250))
          res = btor_bv_new (mm, bw);
        /* t < res <= 2^bw - 1 */
        else
        {
          tmp = btor_bv_add (mm, t, one);
          res = btor_bv_new_random_range (mm, &btor->rng, bw, tmp, bvmax);
          btor_bv_free (mm, tmp);
        }
      }
      else if (cmp > 0)
      {
        /* s > t, e[1] = (s - t) / n ---------------------------------------- */
        if (!btor_bv_is_zero (t))
        {
          tmp = btor_bv_dec (mm, s);
          if (!btor_bv_compare (t, tmp))
          {
            /* CONFLICT:
             * t = s - 1 -> s % e[1] = s - 1
             * -> not possible if t > 0
             * -------------------------------------------------------------- */
            btor_bv_free (mm, tmp);
            goto BVUREM_CONF;
          }
          btor_bv_free (mm, tmp);
        }

        sub = btor_bv_sub (mm, s, t);

        if (btor_bv_compare (sub, t) <= 0)
        {
          /* CONFLICT: s - t <= t ------------------------------------------- */
          btor_bv_free (mm, sub);
          goto BVUREM_CONF;
        }
        else
        {
          /* choose either n = 1 or 1 <= n < (s - t) / t
           * with prob = 0.5
           * ---------------------------------------------------------------- */

          if (btor_rng_pick_with_prob (&btor->rng, 500))
          {
            res = btor_bv_copy (mm, sub);
          }
          else
          {
            /* 1 <= n < (s - t) / t (non-truncating)
             * (note: div truncates towards 0!)
             * -------------------------------------------------------------- */

            if (btor_bv_is_zero (t))
            {
              /* t = 0 -> 1 <= n <= s --------------------------------------- */
              up = btor_bv_copy (mm, s);
            }
            else
            {
              /* e[1] > t
               * -> (s - t) / n > t
               * -> (s - t) / t > n
               * ------------------------------------------------------------ */
              tmp  = btor_bv_urem (mm, sub, t);
              tmp2 = btor_bv_udiv (mm, sub, t);
              if (btor_bv_is_zero (tmp))
              {
                /* (s - t) / t is not truncated
                 * (remainder is 0), therefore the EXclusive
                 * upper bound
                 * -> up = (s - t) / t - 1
                 * ---------------------------------------------------------- */
                up = btor_bv_sub (mm, tmp2, one);
                btor_bv_free (mm, tmp2);
              }
              else
              {
                /* (s - t) / t is truncated
                 * (remainder is not 0), therefore the INclusive
                 * upper bound
                 * -> up = (s - t) / t
                 * ---------------------------------------------------------- */
                up = tmp2;
              }
              btor_bv_free (mm, tmp);
            }

            if (btor_bv_is_zero (up))
              res = btor_bv_udiv (mm, sub, one);
            else
            {
              /* choose 1 <= n <= up randomly
               * s.t (s - t) % n = 0
               * ------------------------------------------------------------ */
              n   = btor_bv_new_random_range (mm, &btor->rng, bw, one, up);
              tmp = btor_bv_urem (mm, sub, n);
              for (cnt = 0; cnt < bw && !btor_bv_is_zero (tmp); cnt++)
              {
                btor_bv_free (mm, n);
                btor_bv_free (mm, tmp);
                n   = btor_bv_new_random_range (mm, &btor->rng, bw, one, up);
                tmp = btor_bv_urem (mm, sub, n);
              }

              if (btor_bv_is_zero (tmp))
              {
                /* res = (s - t) / n */
                res = btor_bv_udiv (mm, sub, n);
              }
              else
              {
                /* fallback: n = 1 */
                res = btor_bv_copy (mm, sub);
              }

              btor_bv_free (mm, n);
              btor_bv_free (mm, tmp);
            }
            btor_bv_free (mm, up);
          }
        }
        btor_bv_free (mm, sub);
      }
      else
      {
        /* CONFLICT: s < t -------------------------------------------------- */
        goto BVUREM_CONF;
      }
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] % s = t
   *
   * -> if s = 0, e[0] = t
   * -> if t = 1...1 and s != 0, conflict
   * -> if s <= t, conflict
   * -> if t > 0 and s = 1, conflict
   * -> else choose either
   *      - e[0] = t, or
   *      - e[0] = s * n + b, with n s.t. (s * n + b) does not overflow
   * ------------------------------------------------------------------------ */
  else
  {
    if (btor_bv_is_zero (s))
    {
    BVUREM_ZERO_0:
      /* s = 0 -> e[0] = t -------------------------------------------------- */
      res = btor_bv_copy (mm, t);
    }
    else if (!btor_bv_is_zero (t) && btor_bv_is_one (s))
    {
      /* CONFLICT: t > 0 and s = 1 ------------------------------------------ */
      goto BVUREM_CONF;
    }
    else if (!btor_bv_compare (t, bvmax))
    {
      if (!btor_bv_is_zero (s))
      {
        /* CONFLICT: s != 0 ------------------------------------------------- */
        goto BVUREM_CONF;
      }
      else
      {
        /* t = 1...1 -> s = 0, e[0] = 1...1 --------------------------------- */
        goto BVUREM_ZERO_0;
      }
    }
    else if (btor_bv_compare (s, t) > 0)
    {
      if (btor_rng_pick_with_prob (&btor->rng, 500))
      {
      BVUREM_EQ_0:
        /* choose simplest solution (0 <= res < s -> res = t)
         * with prob 0.5
         * ------------------------------------------------------------------ */
        res = btor_bv_copy (mm, t);
      }
      else
      {
        /* e[0] = s * n + t,
         * with n s.t. (s * n + t) does not overflow
         * ------------------------------------------------------------------ */
        tmp2 = btor_bv_sub (mm, bvmax, s);

        /* overflow for n = 1 -> only simplest solution possible */
        if (btor_bv_compare (tmp2, t) < 0)
        {
          btor_bv_free (mm, tmp2);
          goto BVUREM_EQ_0;
        }
        else
        {
          btor_bv_free (mm, tmp2);

          tmp = btor_bv_copy (mm, bvmax);
          n   = btor_bv_new_random_range (mm, &btor->rng, bw, one, tmp);

          while (btor_bv_is_umulo (mm, s, n))
          {
            btor_bv_free (mm, tmp);
            tmp = btor_bv_sub (mm, n, one);
            btor_bv_free (mm, n);
            n = btor_bv_new_random_range (mm, &btor->rng, bw, one, tmp);
          }

          mul  = btor_bv_mul (mm, s, n);
          tmp2 = btor_bv_sub (mm, bvmax, mul);

          if (btor_bv_compare (tmp2, t) < 0)
          {
            btor_bv_free (mm, tmp);
            tmp = btor_bv_sub (mm, n, one);
            btor_bv_free (mm, n);
            n = btor_bv_new_random_range (mm, &btor->rng, bw, one, tmp);
            btor_bv_free (mm, mul);
            mul = btor_bv_mul (mm, s, n);
          }

          res = btor_bv_add (mm, mul, t);
          assert (btor_bv_compare (res, mul) >= 0);
          assert (btor_bv_compare (res, t) >= 0);

          btor_bv_free (mm, tmp);
          btor_bv_free (mm, tmp2);
          btor_bv_free (mm, mul);
          btor_bv_free (mm, n);
        }
      }
    }
    else
    {
      /* CONFLICT: s <= t -------------------------------------------- */
      goto BVUREM_CONF;
    }
  }

  btor_bv_free (mm, one);
  btor_bv_free (mm, bvmax);

#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (btor, btor_bv_urem, urem, s, t, res, eidx, "%");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: concat                                                                */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_concat_bv (Btor *btor,
               BtorNode *concat,
               BtorBitVector *t,
               BtorBitVector *s,
               int32_t eidx)
{
  assert (btor);
  assert (concat);
  assert (btor_node_is_regular (concat));
  assert (t);
  assert (s);
  assert (eidx >= 0 && eidx <= 1);
  assert (!btor_node_is_bv_const (concat->e[eidx]));

  BtorNode *e;
  BtorBitVector *res, *tmp;
  BtorMemMgr *mm;
#ifndef NDEBUG
  bool is_inv = true;
#endif

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_concat++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  mm = btor->mm;
  e  = concat->e[eidx ? 0 : 1];
  assert (e);

  res = 0;

  /* ------------------------------------------------------------------------
   * s o e[1] = t
   *
   * -> slice e[1] out of the lower bits of t
   * ------------------------------------------------------------------------ */
  if (eidx)
  {
    tmp = btor_bv_slice (mm, t, t->width - 1, t->width - s->width);
    if (btor_bv_compare (tmp, s))
    {
    BVCONCAT_CONF:
      /* CONFLICT: s bits do not match t ------------------------------------ */
      res = res_rec_conf (btor, concat, e, t, s, eidx, cons_concat_bv, "o");
#ifndef NDEBUG
      is_inv = false;
#endif
    }
    else
    {
      res = btor_bv_slice (mm, t, t->width - s->width - 1, 0);
    }
  }
  /* ------------------------------------------------------------------------
   * e[0] o s = t
   *
   * -> slice e[0] out of the upper bits of t
   * ------------------------------------------------------------------------ */
  else
  {
    tmp = btor_bv_slice (mm, t, s->width - 1, 0);
    if (btor_bv_compare (tmp, s))
    {
      /* CONFLICT: s bits do not match t ------------------------------------ */
      goto BVCONCAT_CONF;
    }
    else
    {
      res = btor_bv_slice (mm, t, t->width - 1, s->width);
    }
  }
  btor_bv_free (mm, tmp);
#ifndef NDEBUG
  if (is_inv)
    check_result_binary_dbg (
        btor, btor_bv_concat, concat, s, t, res, eidx, "o");
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: slice                                                                 */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_slice_bv (Btor *btor,
              BtorNode *slice,
              BtorBitVector *t,
              BtorBitVector *s,
              int32_t eidx)
{
  assert (btor);
  assert (slice);
  assert (btor_node_is_regular (slice));
  assert (t);
  assert (!btor_node_is_bv_const (slice->e[0]));
  (void) eidx;

  uint32_t i, upper, lower, rlower, rupper, rboth;
  BtorNode *e;
  BtorBitVector *res;
  BtorMemMgr *mm;
  bool bkeep, bflip;

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_slice++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  mm = btor->mm;
  e  = slice->e[0];
  assert (e);

  bflip = btor_rng_pick_with_prob (
      &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_SLICE_FLIP));

  bkeep = bflip ? true
                : btor_rng_pick_with_prob (
                      &btor->rng,
                      btor_opt_get (btor, BTOR_OPT_PROP_PROB_SLICE_KEEP_DC));

  upper = btor_node_bv_slice_get_upper (slice);
  lower = btor_node_bv_slice_get_lower (slice);

  res = btor_bv_new (mm, btor_node_bv_get_width (btor, e));

  /* keep previous value for don't care bits or set randomly with prob
   * BTOR_OPT_PROP_PROB_SLICE_KEEP_DC */
  for (i = 0; i < lower; i++)
    btor_bv_set_bit (
        res,
        i,
        bkeep ? btor_bv_get_bit (s, i) : btor_rng_pick_rand (&btor->rng, 0, 1));

  /* set sliced bits to propagated value */
  for (i = lower; i <= upper; i++)
    btor_bv_set_bit (res, i, btor_bv_get_bit (t, i - lower));

  /* keep previous value for don't care bits or set randomly with prob
   * BTOR_OPT_PROP_PROB_SLICE_KEEP_DC */
  for (i = upper + 1; i < res->width; i++)
    btor_bv_set_bit (
        res,
        i,
        bkeep ? btor_bv_get_bit (s, i) : btor_rng_pick_rand (&btor->rng, 0, 1));

  if (bflip)
  {
    rboth  = 0;
    rupper = res->width - 1;
    rlower = 0;

    if (lower)
    {
      rboth += 1;
      rlower = btor_rng_pick_rand (&btor->rng, 0, lower - 1);
    }

    if (upper + 1 < res->width)
    {
      rboth += 2;
      rupper = btor_rng_pick_rand (&btor->rng, upper + 1, res->width - 1);
    }

    switch (rboth)
    {
      case 3:
        assert (rupper >= upper + 1 && rupper < res->width);
        assert (rlower < lower);
        btor_bv_flip_bit (
            res, btor_rng_pick_with_prob (&btor->rng, 500) ? rupper : rlower);
        break;
      case 2:
        assert (rupper >= upper + 1 && rupper < res->width);
        btor_bv_flip_bit (res, rupper);
        break;
      case 1:
        assert (rlower < lower);
        btor_bv_flip_bit (res, rlower);
        break;
    }
  }

#ifndef NDEBUG
  BtorBitVector *tmpdbg = btor_bv_slice (mm, res, upper, lower);
  assert (!btor_bv_compare (tmpdbg, t));
  btor_bv_free (mm, tmpdbg);

  char *str_t   = btor_bv_to_char (mm, t);
  char *str_res = btor_bv_to_char (mm, res);
  BTORLOG (3,
           "prop (xxxxx): %s: %s := %s[%d:%d]",
           btor_util_node2string (slice),
           str_t,
           str_res,
           lower,
           upper);
  btor_mem_freestr (mm, str_t);
  btor_mem_freestr (mm, str_res);
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* INV: cond                                                                  */
/* -------------------------------------------------------------------------- */
#ifdef NDEBUG
static BtorBitVector *
#else
BtorBitVector *
#endif
inv_cond_bv (Btor *btor,
             BtorNode *cond,
             BtorBitVector *t,
             BtorBitVector *s,
             int32_t eidx)
{
  assert (btor);
  assert (cond);
  assert (btor_node_is_regular (cond));
  assert (t);
  assert (!btor_bv_compare (s, btor_model_get_bv (btor, cond->e[0])));
  assert (eidx || !btor_node_is_bv_const (cond->e[eidx]));

  BtorBitVector *res, *s1, *s2;
  BtorMemMgr *mm = btor->mm;

  s1 = (BtorBitVector *) btor_model_get_bv (btor, cond->e[1]);
  s2 = (BtorBitVector *) btor_model_get_bv (btor, cond->e[2]);
#ifndef NDEBUG
  char *str_t  = btor_bv_to_char (btor->mm, t);
  char *str_s0 = btor_bv_to_char (mm, s);
  char *str_s1 = btor_bv_to_char (mm, s1);
  char *str_s2 = btor_bv_to_char (mm, s2);
#endif

  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
#ifndef NDEBUG
    BTOR_PROP_SOLVER (btor)->stats.inv_cond++;
#endif
    BTOR_PROP_SOLVER (btor)->stats.props_inv += 1;
  }

  /* either assume that cond is fixed and propagate snew
   * to enabled path, or flip condition */

  if (eidx == 0)
  {
    /* flip condition */
    res = btor_bv_not (mm, s);
  }
  else
  {
    /* else continue propagating current target value down */
    res = btor_bv_copy (mm, t);
    if (btor_node_is_bv_const (cond->e[eidx]))
    {
      bool is_recoverable = !btor_bv_compare (t, eidx == 1 ? s2 : s1);
#ifndef NDEBUG
      if (eidx == 2)
      {
        BTORLOG (2,
                 "%s CONFLICT (@%d): %s := %s ? %s : x",
                 is_recoverable ? "recoverable" : "non-recoverable",
                 btor_node_get_id (cond),
                 str_t,
                 str_s0,
                 str_s1);
      }
      else
      {
        BTORLOG (2,
                 "%s CONFLICT (@%d): %s := %s ? x : %s",
                 is_recoverable ? "recoverable" : "non-recoverable",
                 btor_node_get_id (cond),
                 str_t,
                 str_s0,
                 str_s2);
      }
      BTORLOG (2, "");
#endif
      if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
      {
        if (is_recoverable)
          BTOR_PROP_SOLVER (btor)->stats.rec_conf += 1;
        else
          BTOR_PROP_SOLVER (btor)->stats.non_rec_conf += 1;
      }
      else
      {
        if (is_recoverable)
          BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf += 1;
        else
          BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf += 1;
      }
    }
  }

#ifndef NDEBUG
  char *str_res = btor_bv_to_char (mm, res);
  BTORLOG (3,
           "prop (e[%d]): %s: %s := %s ? %s : %s",
           eidx,
           btor_util_node2string (cond),
           str_t,
           eidx == 0 ? str_res : str_s0,
           eidx == 1 ? str_res : str_s1,
           eidx == 2 ? str_res : str_s2);
  btor_mem_freestr (mm, str_t);
  btor_mem_freestr (mm, str_res);
  btor_mem_freestr (mm, str_s0);
  btor_mem_freestr (mm, str_s1);
  btor_mem_freestr (mm, str_s2);
#endif
  return res;
}

/* ========================================================================== */
/* Propagation move                                                           */
/* ========================================================================== */

static BtorNode *
select_move (Btor *btor,
             BtorNode *exp,
             BtorBitVector *t,
             BtorBitVector *s[3],
             int32_t eidx,
             BtorBitVector *(*compute_value) (
                 Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int32_t),
             BtorBitVector **value)
{
  assert (btor);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (t);
  assert (s);
  assert (eidx >= 0);
  assert (compute_value);
  assert (value);

  int32_t idx;

  /* special case slice: only one child
   * special case cond: we only need assignment of condition to compute value */
  idx = eidx ? 0
             : (btor_node_is_bv_slice (exp) || btor_node_is_cond (exp) ? 0 : 1);
  *value = compute_value (btor, exp, t, s[idx], eidx);
  return exp->e[eidx];
}

uint64_t
btor_proputils_select_move_prop (Btor *btor,
                                 BtorNode *root,
                                 BtorBitVector *bvroot,
                                 int32_t eidx,
                                 BtorNode **input,
                                 BtorBitVector **assignment)
{
  assert (btor);
  assert (root);
  assert (bvroot);

  bool b;
  int32_t i, nconst;
  uint64_t nprops;
  BtorNode *cur, *real_cur;
  BtorBitVector *bve[3], *bvcur, *bvenew, *tmp;
  int32_t (*select_path) (
      Btor *, BtorNode *, BtorBitVector *, BtorBitVector **);
  BtorBitVector *(*compute_value) (
      Btor *, BtorNode *, BtorBitVector *, BtorBitVector *, int32_t);
#ifndef NBTORLOG
  char *a;
  uint32_t nrecconf_prev, nnonrecconf_prev, nrecconf, nnonrecconf;
  uint32_t ncons = 0;
#endif

  *input      = 0;
  *assignment = 0;
  nprops      = 0;

#ifndef NBTORLOG
  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
    nrecconf_prev    = BTOR_PROP_SOLVER (btor)->stats.rec_conf;
    nnonrecconf_prev = BTOR_PROP_SOLVER (btor)->stats.non_rec_conf;
  }
  else
  {
    assert (btor->slv->kind == BTOR_SLS_SOLVER_KIND);
    nrecconf_prev    = BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf;
    nnonrecconf_prev = BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf;
  }
#endif

  tmp = (BtorBitVector *) btor_model_get_bv (btor, root);
  if (!btor_bv_compare (bvroot, tmp))
  {
    if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
      BTOR_PROP_SOLVER (btor)->stats.fixed_conf++;
    goto DONE;
  }

  cur   = root;
  bvcur = btor_bv_copy (btor->mm, bvroot);

  for (;;)
  {
    real_cur = btor_node_real_addr (cur);

    if (btor_node_is_bv_var (cur))
    {
      *input      = real_cur;
      *assignment = btor_node_is_inverted (cur)
                        ? btor_bv_not (btor->mm, bvcur)
                        : btor_bv_copy (btor->mm, bvcur);
      break;
    }
    else if (btor_node_is_bv_const (cur))
    {
      break;
    }
    else
    {
      assert (!btor_node_is_bv_const (cur));

      if (btor_node_is_inverted (cur))
      {
        tmp   = bvcur;
        bvcur = btor_bv_not (btor->mm, tmp);
        btor_bv_free (btor->mm, tmp);
      }

      /* check if all paths are const, if yes -> conflict */
      for (i = 0, nconst = 0; i < real_cur->arity; i++)
      {
        bve[i] = (BtorBitVector *) btor_model_get_bv (btor, real_cur->e[i]);
        if (btor_node_is_bv_const (real_cur->e[i])) nconst += 1;
      }
      if (nconst > real_cur->arity - 1) break;

#ifndef NBTORLOG
      a = btor_bv_to_char (btor->mm, bvcur);
      BTORLOG (2, "");
      BTORLOG (2, "propagate: %s", a);
      btor_mem_freestr (btor->mm, a);
#endif

      /* we either select a consistent or inverse value
       * as path assignment, depending on the given probability p
       * -> if b then inverse else consistent */
      b = btor_rng_pick_with_prob (
          &btor->rng, btor_opt_get (btor, BTOR_OPT_PROP_PROB_USE_INV_VALUE));
#ifndef NBTORLOG
      if (!b) ncons += 1;
#endif

      /* select path and determine path assignment */
      switch (real_cur->kind)
      {
        case BTOR_BV_ADD_NODE:
          select_path   = select_path_add;
          compute_value = b ? inv_add_bv : cons_add_bv;
          break;
        case BTOR_BV_AND_NODE:
          select_path   = select_path_and;
          compute_value = b ? inv_and_bv : cons_and_bv;
          break;
        case BTOR_BV_EQ_NODE:
          select_path   = select_path_eq;
          compute_value = b ? inv_eq_bv : cons_eq_bv;
          break;
        case BTOR_BV_ULT_NODE:
          select_path   = select_path_ult;
          compute_value = b ? inv_ult_bv : cons_ult_bv;
          break;
        case BTOR_BV_SLL_NODE:
          select_path   = select_path_sll;
          compute_value = b ? inv_sll_bv : cons_sll_bv;
          break;
        case BTOR_BV_SRL_NODE:
          select_path   = select_path_srl;
          compute_value = b ? inv_srl_bv : cons_srl_bv;
          break;
        case BTOR_BV_MUL_NODE:
          select_path   = select_path_mul;
          compute_value = b ? inv_mul_bv : cons_mul_bv;
          break;
        case BTOR_BV_UDIV_NODE:
          select_path   = select_path_udiv;
          compute_value = b ? inv_udiv_bv : cons_udiv_bv;
          break;
        case BTOR_BV_UREM_NODE:
          select_path   = select_path_urem;
          compute_value = b ? inv_urem_bv : cons_urem_bv;
          break;
        case BTOR_BV_CONCAT_NODE:
          select_path   = select_path_concat;
          compute_value = b ? inv_concat_bv : cons_concat_bv;
          break;
        case BTOR_BV_SLICE_NODE:
          select_path   = select_path_slice;
          compute_value = b ? inv_slice_bv : cons_slice_bv;
          break;
        default:
          assert (btor_node_is_bv_cond (real_cur));
          select_path   = select_path_cond;
          compute_value = b ? inv_cond_bv : cons_cond_bv;
      }

      if (eidx == -1) eidx = select_path (btor, real_cur, bvcur, bve);

#ifndef NDEBUG
      if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
      {
        BtorPropInfo prop = {real_cur, btor_bv_copy (btor->mm, bvcur), eidx};
        BTOR_PUSH_STACK (BTOR_PROP_SOLVER (btor)->prop_path, prop);
      }
#endif
      cur = select_move (
          btor, real_cur, bvcur, bve, eidx, compute_value, &bvenew);
      nprops += 1;

      if (!bvenew) break; /* non-recoverable conflict */

      btor_bv_free (btor->mm, bvcur);
      bvcur = bvenew;
      eidx  = -1;
    }
  }

  btor_bv_free (btor->mm, bvcur);

DONE:
#ifndef NBTORLOG
  if (btor->slv->kind == BTOR_PROP_SOLVER_KIND)
  {
    nrecconf    = BTOR_PROP_SOLVER (btor)->stats.rec_conf;
    nnonrecconf = BTOR_PROP_SOLVER (btor)->stats.non_rec_conf;
  }
  else
  {
    assert (btor->slv->kind == BTOR_SLS_SOLVER_KIND);
    nrecconf    = BTOR_SLS_SOLVER (btor)->stats.move_prop_rec_conf;
    nnonrecconf = BTOR_SLS_SOLVER (btor)->stats.move_prop_non_rec_conf;
  }
  nrecconf -= nrecconf_prev;
  nnonrecconf -= nnonrecconf_prev;
  ncons += nrecconf;
  BTORLOG (1, "");
  BTORLOG (1, "propagation path:");
  BTORLOG (1, "    length: %u", nprops);
  BTORLOG (1, "        inverse value props: %u", nprops - ncons);
  BTORLOG (1, "        consistent value props: %u", ncons);
  BTORLOG (1, "    conflicts: %u", nrecconf + nnonrecconf);
  BTORLOG (1, "        recoverable conflicts: %u", nrecconf);
  BTORLOG (1, "        non-recoverable conflicts: %u", nnonrecconf);
#endif
  return nprops;
}

/* ========================================================================== */

void
btor_proputils_clone_prop_info_stack (BtorMemMgr *mm,
                                      BtorPropInfoStack *stack,
                                      BtorPropInfoStack *res,
                                      BtorNodeMap *exp_map)
{
  assert (mm);
  assert (stack);
  assert (res);
  assert (exp_map);

  uint32_t i;
  int32_t cloned_eidx;
  BtorNode *cloned_exp;
  BtorBitVector *cloned_bvexp;

  BTOR_INIT_STACK (mm, *res);
  assert (BTOR_SIZE_STACK (*stack) || !BTOR_COUNT_STACK (*stack));
  if (BTOR_SIZE_STACK (*stack))
  {
    BTOR_NEWN (mm, res->start, BTOR_SIZE_STACK (*stack));
    res->top = res->start;
    res->end = res->start + BTOR_SIZE_STACK (*stack);

    for (i = 0; i < BTOR_COUNT_STACK (*stack); i++)
    {
      assert (BTOR_PEEK_STACK (*stack, i).exp);
      cloned_exp =
          btor_nodemap_mapped (exp_map, BTOR_PEEK_STACK (*stack, i).exp);
      assert (cloned_exp);
      assert (BTOR_PEEK_STACK (*stack, i).bvexp);
      cloned_bvexp = btor_bv_copy (mm, BTOR_PEEK_STACK (*stack, i).bvexp);
      cloned_eidx  = BTOR_PEEK_STACK (*stack, i).eidx;
      assert (cloned_eidx == 0 || cloned_eidx == 1);
      BtorPropInfo cloned_prop = {cloned_exp, cloned_bvexp, cloned_eidx};
      BTOR_PUSH_STACK (*res, cloned_prop);
    }
  }
  assert (BTOR_COUNT_STACK (*stack) == BTOR_COUNT_STACK (*res));
  assert (BTOR_SIZE_STACK (*stack) == BTOR_SIZE_STACK (*res));
}

void
btor_proputils_reset_prop_info_stack (BtorMemMgr *mm, BtorPropInfoStack *stack)
{
  assert (mm);
  assert (stack);

  while (!BTOR_EMPTY_STACK (*stack))
  {
    BtorPropInfo prop = BTOR_POP_STACK (*stack);
    btor_bv_free (mm, prop.bvexp);
  }
  BTOR_RESET_STACK (*stack);
}
