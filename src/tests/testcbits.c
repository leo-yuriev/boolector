/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorcore.h"
#include "btorexp.h"
#include "btornode.h"
#include "dumper/btordumpbtor.h"
#include "testexp.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static Btor *g_btor = NULL;

void
init_cbits_tests (void)
{
}

void
init_cbits_test (void)
{
  g_btor = btor_new ();
  btor_opt_set (g_btor, BTOR_OPT_REWRITE_LEVEL, 0);
}

void
finish_cbits_test (void)
{
  btor_delete (g_btor);
}

static void
test_const_cbits (void)
{
  BtorNode *n, *real_n;
  BtorBitVector *bv;
  uint32_t i;

  init_cbits_test ();

  bv = btor_bv_char_to_bv (g_btor->mm, "00010011");
  n  = btor_exp_bv_const (g_btor, bv);
  /* constants are normalized such that LSB = 0 */
  assert (btor_node_is_inverted (n));
  real_n = btor_node_real_addr (n);
  btor_synthesize_exp (g_btor, n, 0);
  assert (real_n->av);
  assert (real_n->av->width == 8);
  for (i = 0; i < real_n->av->width; i++)
    assert (btor_aig_is_const (real_n->av->aigs[i]));
  /* Note: n is inverted due to normalization */
  assert (btor_aig_is_true (real_n->av->aigs[0]));
  assert (btor_aig_is_true (real_n->av->aigs[1]));
  assert (btor_aig_is_true (real_n->av->aigs[2]));
  assert (btor_aig_is_false (real_n->av->aigs[3]));
  assert (btor_aig_is_true (real_n->av->aigs[4]));
  assert (btor_aig_is_true (real_n->av->aigs[5]));
  assert (btor_aig_is_false (real_n->av->aigs[6]));
  assert (btor_aig_is_false (real_n->av->aigs[7]));
  btor_node_release (g_btor, n);
  btor_bv_free (g_btor->mm, bv);
  finish_cbits_test ();
}

#define TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE(node) \
  do                                                 \
  {                                                  \
    btor_node_release (g_btor, node);                \
    btor_node_release (g_btor, n0);                  \
    btor_node_release (g_btor, n1);                  \
  } while (0)

#define TEST_CBITS_CLEAN_UP_NODES     \
  do                                  \
  {                                   \
    btor_node_release (g_btor, n0);   \
    btor_node_release (g_btor, n1);   \
    btor_node_release (g_btor, v0);   \
    btor_node_release (g_btor, v1);   \
    btor_node_release (g_btor, zero); \
    btor_node_release (g_btor, ones); \
  } while (0)

#define TEST_CBITS_CLEAN_UP_NODES_ALL(node) \
  do                                        \
  {                                         \
    btor_node_release (g_btor, node);       \
    TEST_CBITS_CLEAN_UP_NODES;              \
  } while (0)

static void
test_concat_cbits (void)
{
  BtorNode *n0, *n1, *v0, *v1, *zero, *ones;
  BtorSortId s;
  uint32_t i;

  init_cbits_test ();

  s    = btor_sort_bv (g_btor, 4);
  zero = btor_exp_bv_zero (g_btor, s);
  ones = btor_exp_bv_ones (g_btor, s);
  v0   = btor_exp_var (g_btor, s, "v0");
  v1   = btor_exp_var (g_btor, s, "v1");
  /* n0 = 0000 :: v0 = 0000xxxx */
  n0 = btor_exp_bv_concat (g_btor, zero, v0);
  assert (!btor_node_is_inverted (n0));
  btor_synthesize_exp (g_btor, n0, 0);
  /* n1 = 1111 :: v1 = 1111xxxx */
  n1 = btor_exp_bv_concat (g_btor, ones, v1);
  assert (!btor_node_is_inverted (n1));
  btor_synthesize_exp (g_btor, n1, 0);
  for (i = 0; i < 4; i++)
  {
    assert (btor_aig_is_false (n0->av->aigs[i]));
    assert (btor_aig_is_true (n1->av->aigs[i]));
  }
  for (i = 4; i < 8; i++)
  {
    assert (!btor_aig_is_const (n0->av->aigs[i]));
    assert (!btor_aig_is_const (n1->av->aigs[i]));
  }
  TEST_CBITS_CLEAN_UP_NODES;
  btor_sort_release (g_btor, s);
  finish_cbits_test ();
}

/* add ------------------------------------------------------------ */

/**
 * xxxC + xxxC = xxxC
 */
static void
test_add_cbits_xxxC (void)
{
  BtorNode *n0, *n1, *v0, *v1, *zero, *ones, *add;
  BtorSortId s1, s3;
  uint32_t i;

  init_cbits_test ();

  s1 = btor_sort_bv (g_btor, 1);
  s3 = btor_sort_bv (g_btor, 3);

  zero = btor_exp_bv_zero (g_btor, s1);
  ones = btor_exp_bv_ones (g_btor, s1);

  v0 = btor_exp_var (g_btor, s3, "v0");
  v1 = btor_exp_var (g_btor, s3, "v1");

  /* xxx0 + xxx0 = xxx0 */
  n0  = btor_exp_bv_concat (g_btor, v0, zero);
  n1  = btor_exp_bv_concat (g_btor, v1, zero);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xxx0 + xxx1 = xxx1 */
  n0  = btor_exp_bv_concat (g_btor, v0, zero);
  n1  = btor_exp_bv_concat (g_btor, v1, ones);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xxx1 + xxx0 = xxx1 */
  n0  = btor_exp_bv_concat (g_btor, v0, ones);
  n1  = btor_exp_bv_concat (g_btor, v1, zero);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xxx1 + xxx1 = xxx0 */
  n0  = btor_exp_bv_concat (g_btor, v0, ones);
  n1  = btor_exp_bv_concat (g_btor, v1, ones);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[3]));

  /* clean up */
  TEST_CBITS_CLEAN_UP_NODES_ALL (add);
  btor_sort_release (g_btor, s1);
  btor_sort_release (g_btor, s3);
  finish_cbits_test ();
}

/**
 * xxCC + xxCC = xxCC
 */
static void
test_add_cbits_xxCC (void)
{
  BtorNode *n0, *n1, *v0, *v1, *zero, *ones, *one, *two, *add;
  BtorSortId s2;
  uint32_t i;

  init_cbits_test ();

  s2 = btor_sort_bv (g_btor, 2);

  zero = btor_exp_bv_zero (g_btor, s2);
  ones = btor_exp_bv_ones (g_btor, s2);
  one  = btor_exp_bv_one (g_btor, s2);
  two  = btor_exp_bv_int (g_btor, 2, s2);

  v0 = btor_exp_var (g_btor, s2, "v0");
  v1 = btor_exp_var (g_btor, s2, "v1");

  /* xx00 + xx00 = xx00 */
  n0  = btor_exp_bv_concat (g_btor, v0, zero);
  n1  = btor_exp_bv_concat (g_btor, v1, zero);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_false (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx01 + xx00 = xx01 */
  n0  = btor_exp_bv_concat (g_btor, v0, one);
  n1  = btor_exp_bv_concat (g_btor, v1, zero);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[2]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx10 + xx00 = xx10 */
  n0  = btor_exp_bv_concat (g_btor, v0, two);
  n1  = btor_exp_bv_concat (g_btor, v1, zero);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[2]));
  assert (btor_aig_is_false (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx11 + xx00 = xx11 */
  n0  = btor_exp_bv_concat (g_btor, v0, ones);
  n1  = btor_exp_bv_concat (g_btor, v1, zero);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_true (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx00 + xx01 = xx01 */
  n0  = btor_exp_bv_concat (g_btor, v0, zero);
  n1  = btor_exp_bv_concat (g_btor, v1, one);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[2]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx00 + xx10 = xx10 */
  n0  = btor_exp_bv_concat (g_btor, v0, zero);
  n1  = btor_exp_bv_concat (g_btor, v1, two);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[2]));
  assert (btor_aig_is_false (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx00 + xx11 = xx11 */
  n0  = btor_exp_bv_concat (g_btor, v0, zero);
  n1  = btor_exp_bv_concat (g_btor, v1, ones);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_true (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx01 + xx01 = xx10 */
  n0  = btor_exp_bv_concat (g_btor, v0, one);
  n1  = btor_exp_bv_concat (g_btor, v1, one);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[2]));
  assert (btor_aig_is_false (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx10 + xx01 = xx11 */
  n0  = btor_exp_bv_concat (g_btor, v0, two);
  n1  = btor_exp_bv_concat (g_btor, v1, one);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_true (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx11 + xx01 = xx00 */
  n0  = btor_exp_bv_concat (g_btor, v0, ones);
  n1  = btor_exp_bv_concat (g_btor, v1, one);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_false (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx01 + xx10 = xx11 */
  n0  = btor_exp_bv_concat (g_btor, v0, one);
  n1  = btor_exp_bv_concat (g_btor, v1, two);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_true (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx10 + xx10 = xx00 */
  n0  = btor_exp_bv_concat (g_btor, v0, two);
  n1  = btor_exp_bv_concat (g_btor, v1, two);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_false (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx11 + xx10 = xx01 */
  n0  = btor_exp_bv_concat (g_btor, v0, ones);
  n1  = btor_exp_bv_concat (g_btor, v1, two);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[2]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx01 + xx11 = xx00 */
  n0  = btor_exp_bv_concat (g_btor, v0, one);
  n1  = btor_exp_bv_concat (g_btor, v1, ones);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  for (i = 2; i < 4; i++) assert (btor_aig_is_false (add->av->aigs[i]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx10 + xx11 = xx01 */
  n0  = btor_exp_bv_concat (g_btor, v0, two);
  n1  = btor_exp_bv_concat (g_btor, v1, ones);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[2]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* xx11 + xx11 = xx10 */
  n0  = btor_exp_bv_concat (g_btor, v0, ones);
  n1  = btor_exp_bv_concat (g_btor, v1, ones);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 2; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[2]));
  assert (btor_aig_is_false (add->av->aigs[3]));

  /* clean up */
  TEST_CBITS_CLEAN_UP_NODES_ALL (add);
  btor_node_release (g_btor, one);
  btor_node_release (g_btor, two);
  btor_sort_release (g_btor, s2);
  finish_cbits_test ();
}

/**
 * CxxC + CxxC = xxxC
 */
static void
test_add_cbits_CxxC (void)
{
  BtorNode *n0, *n1, *v0, *v1, *zero, *ones, *add, *tmp;
  BtorSortId s1, s2;
  uint32_t i;

  init_cbits_test ();

  s1 = btor_sort_bv (g_btor, 1);
  s2 = btor_sort_bv (g_btor, 2);

  zero = btor_exp_bv_zero (g_btor, s1);
  ones = btor_exp_bv_ones (g_btor, s1);

  v0 = btor_exp_var (g_btor, s2, "v0");
  v1 = btor_exp_var (g_btor, s2, "v1");

  /* 0xx0 + 0xx0 = xxx0 */
  tmp  = btor_exp_bv_concat (g_btor, v0, zero);
  n0   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  tmp  = btor_exp_bv_concat (g_btor, v1, zero);
  n1   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* 0xx1 + 0xx0 = xxx1 */
  tmp  = btor_exp_bv_concat (g_btor, v0, ones);
  n0   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  tmp  = btor_exp_bv_concat (g_btor, v1, zero);
  n1   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* 0xx0 + 0xx1 = xxx1 */
  tmp  = btor_exp_bv_concat (g_btor, v0, zero);
  n0   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  tmp  = btor_exp_bv_concat (g_btor, v1, ones);
  n1   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_true (add->av->aigs[3]));
  TEST_CBITS_CLEAN_UP_NODES_INTERMEDIATE (add);

  /* 0xx1 + 0xx1 = xxx0 */
  tmp  = btor_exp_bv_concat (g_btor, v0, ones);
  n0   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  tmp  = btor_exp_bv_concat (g_btor, v1, ones);
  n1   = btor_exp_bv_concat (g_btor, zero, tmp);
  btor_node_release (g_btor, tmp);
  add = btor_exp_bv_add (g_btor, n0, n1);
  btor_synthesize_exp (g_btor, add, 0);
  for (i = 0; i < 3; i++) assert (!btor_aig_is_const (add->av->aigs[i]));
  assert (btor_aig_is_false (add->av->aigs[3]));

  /* clean up */
  TEST_CBITS_CLEAN_UP_NODES_ALL (add);
  btor_sort_release (g_btor, s1);
  btor_sort_release (g_btor, s2);
  finish_cbits_test ();
}

void
run_cbits_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (const_cbits);
  BTOR_RUN_TEST (concat_cbits);
  BTOR_RUN_TEST (add_cbits_xxxC);
  BTOR_RUN_TEST (add_cbits_xxCC);
  BTOR_RUN_TEST (add_cbits_CxxC);
}

void
finish_cbits_tests (void)
{
}
