/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
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

/*------------------------------------------------------------------------*/

void
init_bvprop_tests (void)
{
  g_mm = btor_mem_mgr_new ();
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

/*------------------------------------------------------------------------*/

void
run_bvprop_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (valid_domain_bvprop);
  BTOR_RUN_TEST (fixed_domain_bvprop);
  BTOR_RUN_TEST (new_init_domain_bvprop);
}

void
finish_bvprop_tests (void)
{
  btor_mem_mgr_delete (g_mm);
}
