/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testbvprop.h"

#include "boolector.h"
#include "btorbv.h"
#include "btorbvprop.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

/*------------------------------------------------------------------------*/

static BtorMemMgr *g_mm;

#define TEST_BW 3
#define TEST_NUM_CONSTS 27
#define TEST_CONST_LEN (TEST_BW + 1)
char g_consts[TEST_NUM_CONSTS][TEST_CONST_LEN] = {0};

/*------------------------------------------------------------------------*/

#define TEST_BVPROP_RELEASE_D_XZ  \
  do                              \
  {                               \
    btor_bvprop_free (g_mm, d_x); \
    btor_bvprop_free (g_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XZ  \
  do                                \
  {                                 \
    btor_bvprop_free (g_mm, res_x); \
    btor_bvprop_free (g_mm, res_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_D_XYZ \
  do                              \
  {                               \
    btor_bvprop_free (g_mm, d_x); \
    btor_bvprop_free (g_mm, d_y); \
    btor_bvprop_free (g_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XYZ \
  do                                \
  {                                 \
    btor_bvprop_free (g_mm, res_x); \
    btor_bvprop_free (g_mm, res_y); \
    btor_bvprop_free (g_mm, res_z); \
  } while (0)

/*------------------------------------------------------------------------*/

void
init_bvprop_tests (void)
{
  g_mm = btor_mem_mgr_new ();

  /* Initialize all possible values for 3-valued constants of bit-width
   * TEST_BW. */
  char bit     = '0';
  size_t psize = TEST_NUM_CONSTS;
  for (size_t i = 0; i < TEST_BW; i++)
  {
    psize = psize / 3;
    for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
    {
      g_consts[j][i] = bit;
      if ((j + 1) % psize == 0)
      {
        bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
      }
    }
  }
}

char *
slice_str_const (char *str_const, uint32_t from, uint32_t to)
{
  char *res;
  uint32_t len = to - from + 1;

  BTOR_CNEWN (g_mm, res, len + 1);
  strncpy (res, str_const + from, len);
  return res;
}

static void
print_domain (BtorBvDomain *d)
{
  char *s;
  s = btor_bv_to_char (g_mm, d->lo);
  printf ("lo: %s, ", s);
  btor_mem_freestr (g_mm, s);
  s = btor_bv_to_char (g_mm, d->hi);
  printf ("hi: %s\n", s);
  btor_mem_freestr (g_mm, s);
}

/* Create 2-valued bit-vector from 3-valued bit-vector 'bv' by initializing
 * 'x' values to 'bit'. */
static BtorBitVector *
to_bv (const char *c, char bit)
{
  size_t len = strlen (c);
  char buf[len + 1];
  buf[len] = '\0';
  for (size_t i = 0; i < len; i++)
  {
    buf[i] = (c[i] == 'x') ? bit : c[i];
  }
  return btor_bv_char_to_bv (g_mm, buf);
}

/* Create hi for domain from 3-valued bit-vector 'bv'. */
static BtorBitVector *
to_hi (const char *bv)
{
  return to_bv (bv, '1');
}

/* Create lo for domain from 3-valued bit-vector 'bv'. */
static BtorBitVector *
to_lo (const char *bv)
{
  return to_bv (bv, '0');
}

/* Create domain from 3-valued bit-vector 'bv'. */
static BtorBvDomain *
create_domain (const char *bv)
{
  BtorBitVector *lo = to_lo (bv);
  BtorBitVector *hi = to_hi (bv);
  BtorBvDomain *res = btor_bvprop_new (g_mm, lo, hi);
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  return res;
}

/* Create 3-valued bit-vector from domain 'd'. */
static char *
from_domain (BtorMemMgr *mm, BtorBvDomain *d)
{
  assert (btor_bvprop_is_valid (mm, d));
  char *lo = btor_bv_to_char (mm, d->lo);
  char *hi = btor_bv_to_char (mm, d->hi);

  size_t len = strlen (lo);
  for (size_t i = 0; i < len; i++)
  {
    if (lo[i] != hi[i])
    {
      /* lo[i] == '1' && hi[i] == '0' would be an invalid domain. */
      assert (lo[i] == '0');
      assert (hi[i] == '1');
      lo[i] = 'x';
    }
  }
  btor_mem_freestr (mm, hi);
  return lo;
}

static bool
is_xxx_domain (BtorMemMgr *mm, BtorBvDomain *d)
{
  assert (mm);
  assert (d);
  char *str_d = from_domain (mm, d);
  bool res    = strchr (str_d, '1') == NULL && strchr (str_d, '0') == NULL;
  btor_mem_freestr (mm, str_d);
  return res;
}

static bool
is_valid (BtorMemMgr *mm,
          BtorBvDomain *d_x,
          BtorBvDomain *d_y,
          BtorBvDomain *d_z)
{
  return (!d_x || btor_bvprop_is_valid (mm, d_x))
         && (!d_y || btor_bvprop_is_valid (mm, d_y))
         && (!d_z || btor_bvprop_is_valid (mm, d_z));
}

static bool
is_false_eq (const char *a, const char *b)
{
  assert (strlen (a) == strlen (b));
  size_t len = strlen (a);
  for (size_t i = 0; i < len; i++)
  {
    if (a[i] == 'x' || b[i] == 'x')
    {
      continue;
    }
    if (a[i] != b[i])
    {
      return true;
    }
  }
  return false;
}

static bool
is_true_eq (const char *a, const char *b)
{
  assert (strlen (a) == strlen (b));
  size_t len = strlen (a);
  for (size_t i = 0; i < len; i++)
  {
    if (a[i] == 'x' && b[i] == 'x')
    {
      return false;
    }
    if (a[i] != 'x' && b[i] != 'x')
    {
      if (a[i] != b[i])
      {
        return false;
      }
    }
  }
  return true;
}

static void
check_not (BtorBvDomain *d_x, BtorBvDomain *d_z)
{
  char *str_x = from_domain (g_mm, d_x);
  char *str_z = from_domain (g_mm, d_z);
  assert (strlen (str_x) == strlen (str_z));

  size_t len = strlen (str_x);
  for (size_t i = 0; i < len; i++)
  {
    assert (str_x[i] != 'x' || str_z[i] == 'x');
    assert (str_x[i] != '0' || str_z[i] == '1');
    assert (str_x[i] != '1' || str_z[i] == '0');
    assert (str_z[i] != '0' || str_x[i] == '1');
    assert (str_z[i] != '1' || str_x[i] == '0');
  }
  btor_mem_freestr (g_mm, str_x);
  btor_mem_freestr (g_mm, str_z);
}

static bool
check_const_bits (BtorBvDomain *d, const char *expected)
{
  assert (btor_bvprop_is_valid (g_mm, d));
  size_t len = strlen (expected);
  uint32_t bit_lo, bit_hi;
  bool res = true;

  for (size_t i = 0; i < len && res; i++)
  {
    bit_lo = btor_bv_get_bit (d->lo, len - 1 - i);
    bit_hi = btor_bv_get_bit (d->hi, len - 1 - i);
    if (expected[i] == 'x')
    {
      res &= bit_lo != bit_hi;
    }
    else
    {
      res &= bit_lo == bit_hi;
    }
  }
  return res;
}

static void
check_sll_const (BtorBvDomain *d_x, BtorBvDomain *d_z, uint32_t n)
{
  if (btor_bvprop_is_valid (g_mm, d_x) && btor_bvprop_is_valid (g_mm, d_z))
  {
    size_t i, len;
    char *str_x = from_domain (g_mm, d_x);
    char *str_z = from_domain (g_mm, d_z);
    assert (strlen (str_x) == strlen (str_z));

    for (i = 0, len = strlen (str_x); i < len; i++)
    {
      assert (i >= n || str_z[len - 1 - i] == '0');
      assert (i < n || str_z[len - 1 - i] == str_x[len - 1 - i + n]);
    }
    btor_mem_freestr (g_mm, str_x);
    btor_mem_freestr (g_mm, str_z);
  }
}

static void
check_srl_const (BtorBvDomain *d_x, BtorBvDomain *d_z, uint32_t n)
{
  if (btor_bvprop_is_valid (g_mm, d_x) && btor_bvprop_is_valid (g_mm, d_z))
  {
    size_t i, len;
    char *str_x = from_domain (g_mm, d_x);
    char *str_z = from_domain (g_mm, d_z);
    assert (strlen (str_x) == strlen (str_z));

    for (i = 0, len = strlen (str_x); i < len; i++)
    {
      assert (i >= n || str_z[i] == '0');
      assert (i < n || str_z[i] == str_x[i - n]);
    }
    btor_mem_freestr (g_mm, str_x);
    btor_mem_freestr (g_mm, str_z);
  }
}

static void
check_concat (BtorBvDomain *d_x, BtorBvDomain *d_y, BtorBvDomain *d_z)
{
  size_t i, len_x, len_y;
  char *str_x = from_domain (g_mm, d_x);
  char *str_y = from_domain (g_mm, d_y);
  char *str_z = from_domain (g_mm, d_z);
  assert (strlen (str_x) + strlen (str_y) == strlen (str_z));

  for (i = 0, len_x = strlen (str_x); i < len_x; i++)
  {
    assert (str_x[i] == str_z[i]);
  }
  for (i = 0, len_y = strlen (str_y); i < len_y; i++)
  {
    assert (str_y[i] == str_z[i + len_x]);
  }
  btor_mem_freestr (g_mm, str_x);
  btor_mem_freestr (g_mm, str_y);
  btor_mem_freestr (g_mm, str_z);
}

static void
check_sat (BtorBvDomain *d_x,
           BtorBvDomain *d_y,
           BtorBvDomain *d_z,
           BtorBvDomain *res_x,
           BtorBvDomain *res_y,
           BtorBvDomain *res_z,
           BoolectorNode *(*unfun) (Btor *, BoolectorNode *),
           BoolectorNode *(*binfun) (Btor *, BoolectorNode *, BoolectorNode *) )
{
  assert (d_x);
  assert (d_z);
  assert (res_x);
  assert (res_z);
  assert (unfun || binfun);

  size_t i;
  int32_t sat_res;
  uint32_t bw, idx;
  char *str_x, *str_y, *str_z;
  Btor *btor;
  BoolectorNode *x, *y, *z, *fun, *eq, *slice, *one, *zero;
  BoolectorSort sw, s1;

  str_x = from_domain (g_mm, d_x);
  str_y = 0;
  str_z = from_domain (g_mm, d_z);

  btor = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_MODEL_GEN, 1);
  bw   = d_x->lo->width;
  sw   = boolector_bitvec_sort (btor, bw);
  s1   = boolector_bitvec_sort (btor, 1);
  one  = boolector_one (btor, s1);
  zero = boolector_zero (btor, s1);
  x    = boolector_var (btor, sw, "x");
  y    = 0;
  z    = boolector_var (btor, sw, "z");
  if (unfun)
  {
    fun = unfun (btor, x);
  }
  else
  {
    str_y = from_domain (g_mm, d_y);
    y     = boolector_var (btor, sw, "y");
    fun   = binfun (btor, x, y);
  }
  eq = boolector_eq (btor, fun, z);
  boolector_assert (btor, eq);
  boolector_release (btor, fun);
  boolector_release (btor, eq);

  for (i = 0; i < bw; i++)
  {
    idx = bw - i - 1;
    if (str_x[i] != 'x')
    {
      slice = boolector_slice (btor, x, idx, idx);
      eq    = boolector_eq (btor, slice, str_x[i] == '1' ? one : zero);
      boolector_assert (btor, eq);
      boolector_release (btor, eq);
      boolector_release (btor, slice);
    }
    if (str_y && str_y[i] != 'x')
    {
      slice = boolector_slice (btor, y, idx, idx);
      eq    = boolector_eq (btor, slice, str_y[i] == '1' ? one : zero);
      boolector_assert (btor, eq);
      boolector_release (btor, eq);
      boolector_release (btor, slice);
    }
    if (str_z[i] != 'x')
    {
      slice = boolector_slice (btor, z, idx, idx);
      eq    = boolector_eq (btor, slice, str_z[i] == '1' ? one : zero);
      boolector_assert (btor, eq);
      boolector_release (btor, eq);
      boolector_release (btor, slice);
    }
  }

  // boolector_dump_smt2 (btor, stdout);
  sat_res = boolector_sat (btor);
  assert (sat_res != BTOR_RESULT_SAT || is_valid (g_mm, res_x, res_y, res_z));
  assert (sat_res != BTOR_RESULT_UNSAT
          || !is_valid (g_mm, res_x, res_y, res_z));
  // printf ("sat_res %d\n", sat_res);
  // if (sat_res == BOOLECTOR_SAT)
  //{
  //  boolector_print_model (btor, "btor", stdout);
  //}

  boolector_release (btor, x);
  if (y) boolector_release (btor, y);
  boolector_release (btor, z);
  boolector_release (btor, one);
  boolector_release (btor, zero);
  boolector_release_sort (btor, sw);
  boolector_release_sort (btor, s1);
  boolector_delete (btor);
  btor_mem_freestr (g_mm, str_x);
  if (str_y) btor_mem_freestr (g_mm, str_y);
  btor_mem_freestr (g_mm, str_z);
}

/*------------------------------------------------------------------------*/

void
test_valid_domain_bvprop ()
{
  BtorBitVector *lo, *hi;
  BtorBvDomain *d;

  /* check valid */
  lo = btor_bv_char_to_bv (g_mm, "0101011");
  hi = btor_bv_char_to_bv (g_mm, "1101011");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (btor_bvprop_is_valid (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);

  /* check invalid */
  lo = btor_bv_char_to_bv (g_mm, "1101011");
  hi = btor_bv_char_to_bv (g_mm, "0101011");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (!btor_bvprop_is_valid (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);
}

void
test_fixed_domain_bvprop ()
{
  BtorBitVector *lo, *hi;
  BtorBvDomain *d;

  /* check fixed */
  lo = btor_bv_char_to_bv (g_mm, "0001111");
  hi = btor_bv_char_to_bv (g_mm, "0001111");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (btor_bvprop_is_fixed (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);

  /* check not fixed */
  lo = btor_bv_char_to_bv (g_mm, "0001111");
  hi = btor_bv_char_to_bv (g_mm, "0001011");
  d  = btor_bvprop_new (g_mm, lo, hi);

  assert (!btor_bvprop_is_fixed (g_mm, d));
  btor_bv_free (g_mm, lo);
  btor_bv_free (g_mm, hi);
  btor_bvprop_free (g_mm, d);
}

void
test_new_init_domain_bvprop ()
{
  BtorBvDomain *d = btor_bvprop_new_init (g_mm, 32);
  assert (btor_bvprop_is_valid (g_mm, d));
  assert (!btor_bvprop_is_fixed (g_mm, d));
  btor_bvprop_free (g_mm, d);
}

void
test_eq_bvprop ()
{
  char *str_z;
  BtorBvDomain *d_x, *d_y, *res_xy, *res_z;

  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain (g_consts[i]);
    for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
    {
      d_y = create_domain (g_consts[j]);
      (void) btor_bvprop_eq (g_mm, d_x, d_y, &res_xy, &res_z);
      if (btor_bvprop_is_fixed (g_mm, res_z))
      {
        str_z = from_domain (g_mm, res_z);
        assert (strlen (str_z) == 1);
        assert (str_z[0] == '0' || str_z[0] == '1');
        if (str_z[0] == '0')
        {
          assert (!btor_bvprop_is_valid (g_mm, res_xy));
          assert (is_false_eq (g_consts[i], g_consts[j]));
        }
        else
        {
          assert (str_z[0] == '1');
          assert (btor_bvprop_is_valid (g_mm, res_xy));
          assert (btor_bvprop_is_fixed (g_mm, res_xy));
          assert (is_true_eq (g_consts[i], g_consts[j]));
        }
        btor_mem_freestr (g_mm, str_z);
      }
      else
      {
        assert (btor_bvprop_is_valid (g_mm, res_xy));
        assert (!is_false_eq (g_consts[i], g_consts[j]));
        assert (!is_true_eq (g_consts[i], g_consts[j]));
      }
      btor_bvprop_free (g_mm, d_y);
      btor_bvprop_free (g_mm, res_xy);
      btor_bvprop_free (g_mm, res_z);
    }
    btor_bvprop_free (g_mm, d_x);
  }
}

void
test_not_bvprop ()
{
  bool res;
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain (g_consts[i]);

    for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
    {
      d_z = create_domain (g_consts[j]);
      res = btor_bvprop_not (g_mm, d_x, d_z, &res_x, &res_z);
      check_sat (d_x, 0, d_z, res_x, 0, res_z, boolector_not, 0);

      if (btor_bvprop_is_valid (g_mm, res_z))
      {
        assert (res);
        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));
        assert (btor_bvprop_is_valid (g_mm, res_x));
        assert (!btor_bvprop_is_fixed (g_mm, d_z)
                || (btor_bvprop_is_fixed (g_mm, res_x)
                    && btor_bvprop_is_fixed (g_mm, res_z)));
        check_not (res_x, res_z);
      }
      else
      {
        assert (!res);
        bool valid = true;
        for (size_t k = 0; k < TEST_BW && valid; k++)
        {
          if (g_consts[i][k] != 'x' && g_consts[i][k] == g_consts[j][k])
          {
            valid = false;
          }
        }
        assert (!valid);
      }
      btor_bvprop_free (g_mm, d_z);
      TEST_BVPROP_RELEASE_RES_XZ;
    }
    btor_bvprop_free (g_mm, d_x);
  }
}

static void
test_shift_const_bvprop_aux (bool is_srl)
{
  bool res;
  size_t i, j;
  uint32_t n;
  BtorBitVector *bv_n;
  BtorBvDomain *d_x, *d_y, *d_z, *res_x, *res_z;

  for (j = 0; j < 2; j++)
  {
    if (j)
      d_z = btor_bvprop_new_init (g_mm, TEST_BW);
    else
      d_x = btor_bvprop_new_init (g_mm, TEST_BW);

    for (i = 0; i < TEST_NUM_CONSTS; i++)
    {
      if (j)
        d_x = create_domain (g_consts[i]);
      else
        d_z = create_domain (g_consts[i]);

      for (n = 0; n < TEST_BW + 1; n++)
      {
        bv_n = btor_bv_uint64_to_bv (g_mm, n, TEST_BW);
        d_y  = btor_bvprop_new (g_mm, bv_n, bv_n);
        if (is_srl)
        {
          res = btor_bvprop_srl_const (g_mm, d_x, d_z, bv_n, &res_x, &res_z);
          check_sat (d_x, d_y, d_z, res_x, 0, res_z, 0, boolector_srl);
        }
        else
        {
          btor_bvprop_sll_const (g_mm, d_x, d_z, bv_n, &res_x, &res_z);
          check_sat (d_x, d_y, d_z, res_x, 0, res_z, 0, boolector_sll);
        }
        assert (res || !is_valid (g_mm, res_x, 0, res_z));

        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bvprop_is_valid (g_mm, res_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!res || !btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bvprop_is_valid (g_mm, res_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));

        assert (j == 0
                || btor_bvprop_is_fixed (g_mm, d_x)
                       == btor_bvprop_is_fixed (g_mm, res_x));
        if (is_srl)
          check_srl_const (res_x, res_z, n);
        else
          check_sll_const (res_x, res_z, n);

        TEST_BVPROP_RELEASE_RES_XZ;
        btor_bv_free (g_mm, bv_n);
        btor_bvprop_free (g_mm, d_y);
      }
      if (j)
        btor_bvprop_free (g_mm, d_x);
      else
        btor_bvprop_free (g_mm, d_z);
    }

    if (j)
      btor_bvprop_free (g_mm, d_z);
    else
      btor_bvprop_free (g_mm, d_x);
  }
}

void
test_sll_const_bvprop ()
{
  test_shift_const_bvprop_aux (false);
}

void
test_srl_const_bvprop ()
{
  test_shift_const_bvprop_aux (true);
}

#define TEST_BVPROP_AND 0
#define TEST_BVPROP_OR 1
#define TEST_BVPROP_XOR 2

void
test_and_or_xor_bvprop_aux (int32_t op)
{
  BtorBvDomain *d_x, *d_y, *d_z;
  BtorBvDomain *res_x, *res_y, *res_z;

  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_z = create_domain (g_consts[i]);
    for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
    {
      d_x = create_domain (g_consts[j]);
      for (size_t k = 0; k < TEST_NUM_CONSTS; k++)
      {
        d_y = create_domain (g_consts[k]);

        if (op == TEST_BVPROP_AND)
        {
          btor_bvprop_and (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
        }
        else if (op == TEST_BVPROP_OR)
        {
          btor_bvprop_or (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
        }
        else
        {
          assert (op == TEST_BVPROP_XOR);
          btor_bvprop_xor (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
        }

        assert (!btor_bvprop_is_fixed (g_mm, d_x)
                || !btor_bvprop_is_valid (g_mm, res_x)
                || !btor_bv_compare (d_x->lo, res_x->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_y)
                || !btor_bvprop_is_valid (g_mm, res_y)
                || !btor_bv_compare (d_y->lo, res_y->lo));
        assert (!btor_bvprop_is_fixed (g_mm, d_z)
                || !btor_bvprop_is_valid (g_mm, res_z)
                || !btor_bv_compare (d_z->lo, res_z->lo));

        if (btor_bvprop_is_valid (g_mm, res_z))
        {
          assert (btor_bvprop_is_valid (g_mm, res_x));
          assert (btor_bvprop_is_valid (g_mm, res_y));

          for (size_t l = 0; l < TEST_BW; l++)
          {
            if (op == TEST_BVPROP_AND)
            {
              assert (g_consts[i][l] != '1'
                      || (g_consts[j][l] != '0' && g_consts[k][l] != '0'));
              assert (g_consts[i][l] != '0'
                      || (g_consts[j][l] != '1' || g_consts[k][l] != '1'));
            }
            else if (op == TEST_BVPROP_OR)
            {
              assert (g_consts[i][l] != '1' || g_consts[j][l] != '0'
                      || g_consts[k][l] != '0');
              assert (g_consts[i][l] != '0'
                      || (g_consts[j][l] != '1' && g_consts[k][l] != '1'));
            }
            else
            {
              assert (op == TEST_BVPROP_XOR);
              assert (g_consts[i][l] != '1'
                      || (g_consts[j][l] != '0' || g_consts[k][l] != '0')
                      || (g_consts[j][l] != '1' || g_consts[k][l] != '1'));
              assert (g_consts[i][l] != '0'
                      || ((g_consts[j][l] != '0' || g_consts[k][l] != '1')
                          && (g_consts[j][l] != '1' || g_consts[k][l] != '0')));
            }
          }
        }
        else
        {
          bool valid = true;
          for (size_t l = 0; l < TEST_BW && valid; l++)
          {
            if ((op == TEST_BVPROP_AND
                 && ((g_consts[i][l] == '0' && g_consts[j][l] != '0'
                      && g_consts[k][l] != '0')
                     || (g_consts[i][l] == '1'
                         && (g_consts[j][l] == '0' || g_consts[k][l] == '0'))))
                || (op == TEST_BVPROP_OR
                    && ((g_consts[i][l] == '1' && g_consts[j][l] != '1'
                         && g_consts[k][l] != '1')
                        || (g_consts[i][l] == '0'
                            && (g_consts[j][l] == '1'
                                || g_consts[k][l] == '1'))))
                || (op == TEST_BVPROP_XOR
                    && ((g_consts[i][l] == '1'
                         && ((g_consts[j][l] != '0' && g_consts[k][l] != '0')
                             || (g_consts[j][l] != '1'
                                 && g_consts[k][l] != '1')))
                        || (g_consts[i][l] == '0'
                            && ((g_consts[j][l] != '1' && g_consts[k][l] != '0')
                                || (g_consts[j][l] != '0'
                                    && g_consts[k][l] != '1'))))))
            {
              valid = false;
            }
          }
          assert (!valid);
        }
        btor_bvprop_free (g_mm, d_y);
        TEST_BVPROP_RELEASE_RES_XYZ;
      }
      btor_bvprop_free (g_mm, d_x);
    }
    btor_bvprop_free (g_mm, d_z);
  }
}

void
test_and_bvprop ()
{
  test_and_or_xor_bvprop_aux (TEST_BVPROP_AND);
}

void
test_or_bvprop ()
{
  test_and_or_xor_bvprop_aux (TEST_BVPROP_OR);
}

void
test_xor_bvprop ()
{
  test_and_or_xor_bvprop_aux (TEST_BVPROP_XOR);
}

void
test_slice_bvprop ()
{
  char buf[TEST_BW + 1];
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain (g_consts[i]);
    for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
    {
      for (uint32_t lower = 0; lower < TEST_BW; lower++)
      {
        for (uint32_t upper = lower; upper < TEST_BW; upper++)
        {
          memset (buf, 0, sizeof (buf));
          memcpy (buf, &g_consts[j][TEST_BW - 1 - upper], upper - lower + 1);
          assert (strlen (buf) > 0);
          assert (strlen (buf) == upper - lower + 1);

          d_z = create_domain (buf);
          btor_bvprop_slice (g_mm, d_x, d_z, upper, lower, &res_x, &res_z);

          assert (!btor_bvprop_is_fixed (g_mm, d_x)
                  || !btor_bvprop_is_valid (g_mm, res_x)
                  || !btor_bv_compare (d_x->lo, res_x->lo));
          assert (!btor_bvprop_is_fixed (g_mm, d_z)
                  || !btor_bvprop_is_valid (g_mm, res_z)
                  || !btor_bv_compare (d_z->lo, res_z->lo));

          if (btor_bvprop_is_valid (g_mm, res_z))
          {
            assert (btor_bvprop_is_valid (g_mm, res_x));
            char *str_res_x = from_domain (g_mm, res_x);
            char *str_res_z = from_domain (g_mm, res_z);
            for (size_t k = 0; k < upper - lower + 1; k++)
            {
              assert (str_res_z[k] == str_res_x[TEST_BW - 1 - upper + k]);
            }
            btor_mem_freestr (g_mm, str_res_x);
            btor_mem_freestr (g_mm, str_res_z);
          }
          else
          {
            assert (!btor_bvprop_is_valid (g_mm, res_x));
            bool valid = true;
            for (size_t k = 0; k < TEST_BW; k++)
            {
              if (buf[k] != g_consts[i][TEST_BW - 1 - upper + k])
              {
                valid = false;
                break;
              }
            }
            assert (!valid);
          }
          btor_bvprop_free (g_mm, d_z);
          TEST_BVPROP_RELEASE_RES_XZ;
        }
      }
    }
    btor_bvprop_free (g_mm, d_x);
  }
}

#define TEST_PROPBV_CONCAT                                            \
  do                                                                  \
  {                                                                   \
    btor_bvprop_concat (g_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z); \
    assert (!btor_bvprop_is_fixed (g_mm, d_x)                         \
            || !btor_bv_compare (d_x->lo, res_x->lo));                \
    assert (!btor_bvprop_is_fixed (g_mm, d_y)                         \
            || !btor_bv_compare (d_y->lo, res_y->lo));                \
    assert (!btor_bvprop_is_fixed (g_mm, d_z)                         \
            || !btor_bv_compare (d_z->lo, res_z->lo));                \
    check_concat (res_x, res_y, res_z);                               \
    assert (btor_bvprop_is_valid (g_mm, res_x));                      \
    assert (btor_bvprop_is_valid (g_mm, res_y));                      \
    assert (btor_bvprop_is_valid (g_mm, res_z));                      \
    assert (!btor_bvprop_is_fixed (g_mm, d_x)                         \
            || btor_bvprop_is_fixed (g_mm, res_x));                   \
    assert (!btor_bvprop_is_fixed (g_mm, d_y)                         \
            || btor_bvprop_is_fixed (g_mm, res_y));                   \
    assert (!btor_bvprop_is_fixed (g_mm, d_z)                         \
            || (btor_bvprop_is_fixed (g_mm, res_x)                    \
                && btor_bvprop_is_fixed (g_mm, res_y)                 \
                && btor_bvprop_is_fixed (g_mm, res_z)));              \
    TEST_BVPROP_RELEASE_D_XYZ;                                        \
    TEST_BVPROP_RELEASE_RES_XYZ;                                      \
  } while (0)

void
test_concat_bvprop ()
{
  size_t i, j, k;
  char *s_const;
  BtorBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

  for (i = 1; i < TEST_BW; i++)
  {
    j = TEST_BW - i;
    for (k = 0; k < TEST_NUM_CONSTS; k++)
    {
      d_x = btor_bvprop_new_init (g_mm, i);
      d_y = btor_bvprop_new_init (g_mm, j);
      assert (i + j == TEST_BW);
      d_z = btor_bvprop_new_init (g_mm, TEST_BW);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (g_consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_y = btor_bvprop_new_init (g_mm, j);
      d_z = btor_bvprop_new_init (g_mm, TEST_BW);
      TEST_PROPBV_CONCAT;

      d_x     = btor_bvprop_new_init (g_mm, i);
      s_const = slice_str_const (g_consts[k], i, TEST_BW - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = btor_bvprop_new_init (g_mm, TEST_BW);
      TEST_PROPBV_CONCAT;

      d_x = btor_bvprop_new_init (g_mm, i);
      d_y = btor_bvprop_new_init (g_mm, j);
      d_z = create_domain (g_consts[k]);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (g_consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      s_const = slice_str_const (g_consts[k], i, TEST_BW - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = btor_bvprop_new_init (g_mm, TEST_BW);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (g_consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_y = btor_bvprop_new_init (g_mm, j);
      d_z = create_domain (g_consts[k]);
      TEST_PROPBV_CONCAT;

      d_x     = btor_bvprop_new_init (g_mm, i);
      s_const = slice_str_const (g_consts[k], i, TEST_BW - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = create_domain (g_consts[k]);
      TEST_PROPBV_CONCAT;

      s_const = slice_str_const (g_consts[k], 0, i - 1);
      d_x     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      s_const = slice_str_const (g_consts[k], i, TEST_BW - 1);
      d_y     = create_domain (s_const);
      btor_mem_freestr (g_mm, s_const);
      d_z = create_domain (g_consts[k]);
      TEST_PROPBV_CONCAT;
    }
  }
}

/*------------------------------------------------------------------------*/

void
run_bvprop_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (valid_domain_bvprop);
  BTOR_RUN_TEST (fixed_domain_bvprop);
  BTOR_RUN_TEST (new_init_domain_bvprop);
  BTOR_RUN_TEST (eq_bvprop);
  BTOR_RUN_TEST (not_bvprop);
  BTOR_RUN_TEST (sll_const_bvprop);
  BTOR_RUN_TEST (srl_const_bvprop);
  BTOR_RUN_TEST (and_bvprop);
  BTOR_RUN_TEST (or_bvprop);
  BTOR_RUN_TEST (xor_bvprop);
  BTOR_RUN_TEST (slice_bvprop);
  BTOR_RUN_TEST (concat_bvprop);
}

void
finish_bvprop_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}
