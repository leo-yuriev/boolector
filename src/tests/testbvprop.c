/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testbvprop.h"
#include "btorbvprop.h"
#include "btorcore.h"
#include "testrunner.h"

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

static bool
check_not (BtorBvDomain *d_x, BtorBvDomain *d_z)
{
  bool res    = true;
  char *str_x = from_domain (g_mm, d_x);
  char *str_z = from_domain (g_mm, d_z);
  assert (strlen (str_x) == strlen (str_z));

  size_t len = strlen (str_x);
  for (size_t i = 0; i < len; i++)
  {
    if (((str_x[i] == 'x') != (str_z[i] == 'x'))
        || (str_x[i] == '0' && str_z[i] != '1')
        || (str_x[i] == '1' && str_z[i] != '0')
        || (str_z[i] == '0' && str_x[i] != '1')
        || (str_z[i] == '1' && str_x[i] != '0'))
    {
      res = false;
      break;
    }
  }
  btor_mem_freestr (g_mm, str_x);
  btor_mem_freestr (g_mm, str_z);
  return res;
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
  char *str_x = from_domain (g_mm, d_x);
  char *str_z = from_domain (g_mm, d_z);
  assert (strlen (str_x) == strlen (str_z));

  size_t len = strlen (str_x);
  for (size_t i = 0; i < len; i++)
  {
    assert (i >= n || str_z[len - 1 - i] == '0');
    assert (i < n || str_z[len - 1 - i] == str_x[len - 1 - i + n]);
  }
  btor_mem_freestr (g_mm, str_x);
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
      btor_bvprop_eq (g_mm, d_x, d_y, &res_xy, &res_z);
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
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  d_z = btor_bvprop_new_init (g_mm, TEST_BW);
  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain (g_consts[i]);
    btor_bvprop_not (g_mm, d_x, d_z, &res_x, &res_z);

    assert (btor_bvprop_is_valid (g_mm, res_x));
    assert (btor_bvprop_is_valid (g_mm, res_z));
    assert (btor_bvprop_is_fixed (g_mm, d_x)
            == btor_bvprop_is_fixed (g_mm, res_x));
    assert (btor_bvprop_is_fixed (g_mm, d_x)
            == btor_bvprop_is_fixed (g_mm, res_z));
    assert (check_not (res_x, res_z));

    btor_bvprop_free (g_mm, d_x);
    btor_bvprop_free (g_mm, res_x);
    btor_bvprop_free (g_mm, res_z);
  }
  btor_bvprop_free (g_mm, d_z);

  d_x = btor_bvprop_new_init (g_mm, TEST_BW);
  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_z = create_domain (g_consts[i]);
    btor_bvprop_not (g_mm, d_x, d_z, &res_x, &res_z);

    assert (btor_bvprop_is_valid (g_mm, res_x));
    assert (btor_bvprop_is_valid (g_mm, res_z));
    assert (btor_bvprop_is_fixed (g_mm, d_z)
            == btor_bvprop_is_fixed (g_mm, res_x));
    assert (btor_bvprop_is_fixed (g_mm, d_z)
            == btor_bvprop_is_fixed (g_mm, res_z));
    assert (check_not (res_x, res_z));

    btor_bvprop_free (g_mm, d_z);
    btor_bvprop_free (g_mm, res_x);
    btor_bvprop_free (g_mm, res_z);
  }
  btor_bvprop_free (g_mm, d_x);
}

void
test_sll_const_bvprop ()
{
  size_t i;
  uint32_t n;
  BtorBitVector *bv_n;
  BtorBvDomain *d_x, *d_z, *res_x, *res_z;

  d_z = btor_bvprop_new_init (g_mm, TEST_BW);
  for (i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain (g_consts[i]);
    for (n = 0; n < TEST_BW + 1; n++)
    {
      bv_n = btor_bv_uint64_to_bv(g_mm, n, TEST_BW);
      btor_bvprop_sll_const (g_mm, d_x, d_z, bv_n, &res_x, &res_z);
      assert (btor_bvprop_is_valid (g_mm, res_x));
      assert (btor_bvprop_is_valid (g_mm, res_z));
      assert (btor_bvprop_is_fixed (g_mm, d_x)
              == btor_bvprop_is_fixed (g_mm, res_x));
      check_sll_const (res_x, res_z, n);

      btor_bvprop_free (g_mm, res_x);
      btor_bvprop_free (g_mm, res_z);
      btor_bv_free (g_mm, bv_n);
    }
    btor_bvprop_free (g_mm, d_x);
  }
  btor_bvprop_free (g_mm, d_z);

  d_z = btor_bvprop_new_init (g_mm, TEST_BW);
  for (i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain (g_consts[i]);
    for (n = 0; n < TEST_BW + 1; n++)
    {
      bv_n = btor_bv_uint64_to_bv(g_mm, n, TEST_BW);
      btor_bvprop_sll_const (g_mm, d_x, d_z, bv_n, &res_x, &res_z);
      assert (btor_bvprop_is_valid (g_mm, res_x));
      assert (btor_bvprop_is_valid (g_mm, res_z));
      assert (btor_bvprop_is_fixed (g_mm, d_x)
              == btor_bvprop_is_fixed (g_mm, res_x));
      check_sll_const (res_x, res_z, n);

      btor_bvprop_free (g_mm, res_x);
      btor_bvprop_free (g_mm, res_z);
      btor_bv_free (g_mm, bv_n);
    }
    btor_bvprop_free (g_mm, d_x);
  }
  btor_bvprop_free (g_mm, d_z);
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
}

void
finish_bvprop_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}
