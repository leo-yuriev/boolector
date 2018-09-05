/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorslvprop.h"

#include "btorabort.h"
#include "btorbv.h"
#include "btorclone.h"
#include "btorcore.h"
#include "btordbg.h"
#include "btorlsutils.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btornode.h"
#include "btoropt.h"
#include "btorproputils.h"
#include "btorprintmodel.h"
#include "btorslsutils.h"

#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"
#include "utils/btorutil.h"

#include <math.h>

/*------------------------------------------------------------------------*/

#define BTOR_PROP_MAXSTEPS_CFACT 100
#define BTOR_PROP_MAXSTEPS(i) \
  (BTOR_PROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BTOR_PROP_SELECT_CFACT 20

/*------------------------------------------------------------------------*/

static BtorNode *
select_constraint (Btor *btor, uint32_t nmoves)
{
  assert (btor);

  BtorNode *res, *cur;
  BtorPropSolver *slv;
  BtorIntHashTableIterator it;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  assert (slv->roots);
  assert (slv->roots->count);

#ifndef NDEBUG
  BtorPtrHashTableIterator pit;
  BtorNode *root;
  btor_iter_hashptr_init (&pit, btor->unsynthesized_constraints);
  btor_iter_hashptr_queue (&pit, btor->assumptions);
  while (btor_iter_hashptr_has_next (&pit))
  {
    root = btor_iter_hashptr_next (&pit);
    if (btor_bv_is_false (btor_model_get_bv (btor, root)))
      assert (btor_hashint_map_contains (slv->roots, btor_node_get_id (root)));
    else
      assert (!btor_hashint_map_contains (slv->roots, btor_node_get_id (root)));
  }
#endif

  res = 0;

  if (btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT))
  {
    assert (slv->score);

    int32_t *selected;
    double value, max_value, score;
    max_value = 0.0;
    btor_iter_hashint_init (&it, slv->roots);
    while (btor_iter_hashint_has_next (&it))
    {
      selected = &slv->roots->data[it.cur_pos].as_int;
      cur      = btor_node_get_by_id (btor, btor_iter_hashint_next (&it));

      assert (btor_hashint_map_contains (slv->score, btor_node_get_id (cur)));
      score = btor_hashint_map_get (slv->score, btor_node_get_id (cur))->as_dbl;
      assert (score < 1.0);
      value = score + BTOR_PROP_SELECT_CFACT * sqrt (log (*selected) / nmoves);

      if (!res || value > max_value)
      {
        res       = cur;
        max_value = value;
        *selected += 1;
      }
    }
  }
  else
  {
    size_t j, r;

    j = 0;
    r = btor_rng_pick_rand (&btor->rng, 0, slv->roots->count - 1);
    btor_iter_hashint_init (&it, slv->roots);
    while (btor_iter_hashint_has_next (&it) && j <= r)
    {
      res = btor_node_get_by_id (btor, btor_iter_hashint_next (&it));
      j += 1;
    }
    assert (res);
    assert (!btor_node_is_bv_const (res));
  }

  assert (res);
  assert (btor_bv_is_zero (btor_model_get_bv (btor, res)));

  BTORLOG (1, "");
  BTORLOG (1, "select constraint: %s", btor_util_node2string (res));

  return res;
}

static bool
move (Btor *btor)
{
  assert (btor);

  BTORLOG (1, "");
  BTORLOG (1, "*** move");

  BtorNode *root, *input;
  BtorBitVector *bvroot, *assignment;
  BtorPropSolver *slv;
  BtorIntHashTable *exps;
  BtorPropInfo prop;
  int32_t eidx;
  uint64_t props, nprops;
#ifndef NBTORLOG
  size_t i;
#endif

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  assert (BTOR_EMPTY_STACK (slv->prop_path));
  nprops = btor_opt_get (btor, BTOR_OPT_PROP_NPROPS);

  bvroot = 0;
  do
  {
    if (nprops && slv->stats.props >= nprops) goto DONE;

#ifndef NDEBUG
    btor_proputils_reset_prop_info_stack (slv->btor->mm, &slv->prop_path);
#endif

    if (bvroot) btor_bv_free (btor->mm, bvroot);

#ifndef NBTORLOG
    BTORLOG (1, "entailed propagations: %u", BTOR_COUNT_STACK (slv->toprop));
    for (i = 0; i < BTOR_COUNT_STACK (slv->toprop); i++)
    {
      BtorPropInfo *p = &slv->toprop.start[i];
      char *bvprop    = btor_bv_to_char (btor->mm, p->bvexp);
      BTORLOG (1, "  %s: %s", btor_util_node2string (p->exp), bvprop);
      btor_mem_freestr (btor->mm, bvprop);
    }
#endif

    if (BTOR_EMPTY_STACK (slv->toprop))
    {
      root   = select_constraint (btor, slv->stats.moves);
      bvroot = btor_bv_one (btor->mm, 1);
      eidx   = -1;
    }
    else
    {
      prop   = BTOR_POP_STACK (slv->toprop);
      root   = prop.exp;
      bvroot = prop.bvexp;
      eidx   = prop.eidx;
    }

    props = btor_proputils_select_move_prop (
        btor, root, bvroot, eidx, &input, &assignment);
    slv->stats.props += props;
    if (eidx != -1) slv->stats.props_entailed += props;
  } while (!input);

  assert (assignment);

  btor_bv_free (btor->mm, bvroot);

#ifndef NBTORLOG
  char *a;
  BtorBitVector *ass;
  ass = (BtorBitVector *) btor_model_get_bv (btor, input);
  a   = btor_bv_to_char (btor->mm, ass);
  BTORLOG (1, "");
  BTORLOG (1, "move");
  BTORLOG (1,
           "  input: %s%s",
           btor_node_is_regular (input) ? "" : "-",
           btor_util_node2string (input));
  BTORLOG (1, "  prev. assignment: %s", a);
  btor_mem_freestr (btor->mm, a);
  a = btor_bv_to_char (btor->mm, assignment);
  BTORLOG (1, "  new   assignment: %s", a);
  btor_mem_freestr (btor->mm, a);
#endif

  exps = btor_hashint_map_new (btor->mm);
  assert (btor_node_is_regular (input));
  btor_hashint_map_add (exps, input->id)->as_ptr = assignment;
  btor_lsutils_update_cone (
      btor,
      btor->bv_model,
      slv->roots,
      btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT) ? slv->score : 0,
      exps,
      true,
      &slv->stats.updates,
      &slv->time.update_cone,
      &slv->time.update_cone_reset,
      &slv->time.update_cone_model_gen,
      &slv->time.update_cone_compute_score);
  btor_hashint_map_delete (exps);

#ifndef NDEBUG
  size_t cnt;
  BtorBitVector *bvass, *bvtarget;
  BtorNode *n;
  cnt = BTOR_COUNT_STACK (slv->prop_path);
  for (i = 0; i < cnt; i++)
  {
    n = BTOR_PEEK_STACK (slv->prop_path, cnt - 1 - i).exp;
    assert (btor_node_is_regular (n));
    bvass    = (BtorBitVector *) btor_model_get_bv (btor, n);
    bvtarget = BTOR_PEEK_STACK (slv->prop_path, cnt - 1 - i).bvexp;
    if (btor_bv_compare (bvass, bvtarget)) break;
  }
  BTORLOG (1, "  matching target values: %u", i);
#endif

  slv->stats.moves += 1;
  if (eidx != -1)
  {
    slv->stats.moves_entailed += 1;
    slv->stats.fixed_conf += 1;
  }
  btor_bv_free (btor->mm, assignment);

DONE:
#ifndef NDEBUG
  btor_proputils_reset_prop_info_stack (slv->btor->mm, &slv->prop_path);
#endif
  return true;
}

/*------------------------------------------------------------------------*/

static BtorPropSolver *
clone_prop_solver (Btor *clone, BtorPropSolver *slv, BtorNodeMap *exp_map)
{
  assert (clone);
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);

  BtorPropSolver *res;

  (void) exp_map;

  BTOR_NEW (clone->mm, res);
  memcpy (res, slv, sizeof (BtorPropSolver));

  res->btor  = clone;
  res->roots = btor_hashint_map_clone (clone->mm, slv->roots, 0, 0);
  res->score =
      btor_hashint_map_clone (clone->mm, slv->score, btor_clone_data_as_dbl, 0);

  btor_proputils_clone_prop_info_stack (
      clone->mm, &slv->toprop, &res->toprop, exp_map);
#ifndef NDEBUG
  btor_proputils_clone_prop_info_stack (
      clone->mm, &slv->prop_path, &res->prop_path, exp_map);
#endif
  return res;
}

static void
delete_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  if (slv->score) btor_hashint_map_delete (slv->score);
  if (slv->roots) btor_hashint_map_delete (slv->roots);

  assert (BTOR_EMPTY_STACK (slv->toprop));
  BTOR_RELEASE_STACK (slv->toprop);
#ifndef NDEBUG
  assert (BTOR_EMPTY_STACK (slv->prop_path));
  BTOR_RELEASE_STACK (slv->prop_path);
#endif
  BTOR_DELETE (slv->btor->mm, slv);
}

/* This is an extra function in order to be able to test completeness
 * via test suite. */
#ifdef NDEBUG
static inline int32_t
#else
int32_t
#endif
sat_prop_solver_aux (Btor *btor)
{
  assert (btor);

  uint32_t j, max_steps;
  int32_t sat_result;
  uint32_t nprops;
  BtorNode *root;
  BtorPtrHashTableIterator it;
  BtorPropSolver *slv;

  slv = BTOR_PROP_SOLVER (btor);
  assert (slv);
  nprops = btor_opt_get (btor, BTOR_OPT_PROP_NPROPS);

  /* check for constraints occurring in both phases */
  btor_iter_hashptr_init (&it, btor->assumptions);
  while (btor_iter_hashptr_has_next (&it))
  {
    root = btor_iter_hashptr_next (&it);
    if (btor_hashptr_table_get (btor->unsynthesized_constraints,
                                btor_node_invert (root)))
      goto UNSAT;
    if (btor_hashptr_table_get (btor->assumptions, btor_node_invert (root)))
      goto UNSAT;
  }

  for (;;)
  {
    assert (BTOR_EMPTY_STACK (slv->toprop));

    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert (!slv->roots);
    slv->roots = btor_hashint_map_new (btor->mm);
    assert (btor->synthesized_constraints->count == 0);
    btor_iter_hashptr_init (&it, btor->unsynthesized_constraints);
    btor_iter_hashptr_queue (&it, btor->assumptions);
    while (btor_iter_hashptr_has_next (&it))
    {
      root = btor_iter_hashptr_next (&it);

      if (!btor_hashint_map_contains (slv->roots, btor_node_get_id (root))
          && btor_bv_is_zero (btor_model_get_bv (btor, root)))
      {
        if (btor_node_is_bv_const (root))
          goto UNSAT; /* contains false constraint -> unsat */
        btor_hashint_map_add (slv->roots, btor_node_get_id (root));
      }
    }

    if (!slv->score && btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT))
      slv->score = btor_hashint_map_new (btor->mm);

    if (btor_terminate (btor))
    {
      sat_result = BTOR_RESULT_UNKNOWN;
      goto DONE;
    }

    /* all constraints sat? */
    if (!slv->roots->count) goto SAT;

    /* compute initial sls score */
    if (btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT))
      btor_slsutils_compute_sls_scores (
          btor, btor->bv_model, btor->fun_model, slv->score);

    /* init */
    slv->flip_cond_const_prob =
        btor_opt_get (btor, BTOR_OPT_PROP_PROB_FLIP_COND_CONST);
    slv->flip_cond_const_prob_delta =
        slv->flip_cond_const_prob > (BTOR_PROB_MAX / 2)
            ? -BTOR_PROPUTILS_PROB_FLIP_COND_CONST_DELTA
            : BTOR_PROPUTILS_PROB_FLIP_COND_CONST_DELTA;

    /* move */
    for (j = 0, max_steps = BTOR_PROP_MAXSTEPS (slv->stats.restarts + 1);
         !btor_opt_get (btor, BTOR_OPT_PROP_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (btor_terminate (btor) || (nprops && slv->stats.props >= nprops))
      {
        sat_result = BTOR_RESULT_UNKNOWN;
        goto DONE;
      }

      if (!(move (btor))) goto UNSAT;

      /* all constraints sat? */
      if (!slv->roots->count) goto SAT;
    }

    /* restart */
    slv->api.generate_model ((BtorSolver *) slv, false, true);
    btor_hashint_map_delete (slv->roots);
    slv->roots = 0;
    if (btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT))
    {
      btor_hashint_map_delete (slv->score);
      slv->score = btor_hashint_map_new (btor->mm);
    }
    slv->stats.restarts += 1;
    btor_proputils_reset_prop_info_stack (slv->btor->mm, &slv->toprop);
  }

SAT:
  sat_result = BTOR_RESULT_SAT;
  goto DONE;

UNSAT:
  sat_result = BTOR_RESULT_UNSAT;

DONE:
  if (slv->roots)
  {
    btor_hashint_map_delete (slv->roots);
    slv->roots = 0;
  }
  if (slv->score)
  {
    btor_hashint_map_delete (slv->score);
    slv->score = 0;
  }
  btor_proputils_reset_prop_info_stack (slv->btor->mm, &slv->toprop);
  assert (BTOR_EMPTY_STACK (slv->prop_path));
  return sat_result;
}

/* Note: failed assumptions handling not necessary, prop only works for SAT */
static int32_t
sat_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  int32_t sat_result;
  Btor *btor;

  btor = slv->btor;
  assert (!btor->inconsistent);

  if (btor_terminate (btor))
  {
    sat_result = BTOR_RESULT_UNKNOWN;
    goto DONE;
  }

  BTOR_ABORT (btor->ufs->count != 0
                  || (!btor_opt_get (btor, BTOR_OPT_BETA_REDUCE_ALL)
                      && btor->lambdas->count != 0),
              "prop engine supports QF_BV only");

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model ((BtorSolver *) slv, false, true);
  sat_result = sat_prop_solver_aux (btor);
DONE:
  assert (BTOR_EMPTY_STACK (slv->toprop));
  return sat_result;
}

static void
generate_model_prop_solver (BtorPropSolver *slv,
                            bool model_for_all_nodes,
                            bool reset)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

  if (!reset && btor->bv_model) return;
  btor_model_init_bv (btor, &btor->bv_model);
  btor_model_init_fun (btor, &btor->fun_model);
  btor_model_generate (
      btor, btor->bv_model, btor->fun_model, model_for_all_nodes);
}

static void
print_stats_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;
  bool enable_entailed = btor_opt_get (slv->btor, BTOR_OPT_PROP_ENTAILED);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "restarts: %u", slv->stats.restarts);
  BTOR_MSG (btor->msg, 1, "moves: %u", slv->stats.moves);
  if (enable_entailed)
    BTOR_MSG (
        btor->msg, 1, "    entailed moves: %u", slv->stats.moves_entailed);

  BTOR_MSG (btor->msg,
            1,
            "moves per second: %.2f",
            (double) slv->stats.moves / (btor->time.sat - btor->time.simplify));
  BTOR_MSG (btor->msg, 1, "propagation (steps): %u", slv->stats.props);
  if (enable_entailed)
    BTOR_MSG (btor->msg,
              1,
              "    entailed propagations: %u",
              slv->stats.props_entailed);
  BTOR_MSG (btor->msg,
            1,
            "    consistent value propagations: %u",
            slv->stats.props_cons);
  BTOR_MSG (
      btor->msg, 1, "    inverse value propagations: %u", slv->stats.props_inv);
  BTOR_MSG (btor->msg,
            1,
            "propagation (steps) per second: %.2f",
            (double) slv->stats.props / (btor->time.sat - btor->time.simplify));
  BTOR_MSG (btor->msg,
            1,
            "propagation conflicts (non-recoverable): %u",
            slv->stats.non_rec_conf);
  BTOR_MSG (btor->msg,
            1,
            "propagation conflicts (recoverable): %u",
            slv->stats.rec_conf);
  if (enable_entailed)
  {
    BTOR_MSG (btor->msg,
              1,
              "   fixed recoverable conflicts: %u",
              slv->stats.fixed_conf);
    BTOR_MSG (btor->msg,
              1,
              "   recoverable conflicts fixed without an entailed move: %u",
              slv->stats.fixed_conf - slv->stats.moves_entailed);
  }
  BTOR_MSG (btor->msg, 1, "updates (cone): %u", slv->stats.updates);
#ifndef NDEBUG
  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "consistent value computations:");
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (add): %u", slv->stats.cons_add);
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (and): %u", slv->stats.cons_and);
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (eq): %u", slv->stats.cons_eq);
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (ult): %u", slv->stats.cons_ult);
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (sll): %u", slv->stats.cons_sll);
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (srl): %u", slv->stats.cons_srl);
  BTOR_MSG (
      btor->msg, 1, "    consistent fun calls (mul): %u", slv->stats.cons_mul);
  BTOR_MSG (btor->msg,
            1,
            "    consistent fun calls (udiv): %u",
            slv->stats.cons_udiv);
  BTOR_MSG (btor->msg,
            1,
            "    consistent fun calls (urem): %u",
            slv->stats.cons_urem);
  BTOR_MSG (btor->msg,
            1,
            "    consistent fun calls (concat): %u",
            slv->stats.cons_concat);
  BTOR_MSG (btor->msg,
            1,
            "    consistent fun calls (slice): %u",
            slv->stats.cons_slice);
  BTOR_MSG (btor->msg,
            1,
            "    consistent fun calls (cond): %u",
            slv->stats.cons_cond);

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg, 1, "inverse value computations:");
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (add): %u", slv->stats.inv_add);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (and): %u", slv->stats.inv_and);
  BTOR_MSG (btor->msg, 1, "    inverse fun calls (eq): %u", slv->stats.inv_eq);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (ult): %u", slv->stats.inv_ult);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (sll): %u", slv->stats.inv_sll);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (srl): %u", slv->stats.inv_srl);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (mul): %u", slv->stats.inv_mul);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (udiv): %u", slv->stats.inv_udiv);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (urem): %u", slv->stats.inv_urem);
  BTOR_MSG (btor->msg,
            1,
            "    inverse fun calls (concat): %u",
            slv->stats.inv_concat);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (slice): %u", slv->stats.inv_slice);
  BTOR_MSG (
      btor->msg, 1, "    inverse fun calls (cond): %u", slv->stats.inv_cond);
#endif
}

static void
print_time_stats_prop_solver (BtorPropSolver *slv)
{
  assert (slv);
  assert (slv->kind == BTOR_PROP_SOLVER_KIND);
  assert (slv->btor);
  assert (slv->btor->slv == (BtorSolver *) slv);

  Btor *btor = slv->btor;

  BTOR_MSG (btor->msg, 1, "");
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (total)",
            slv->time.update_cone);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (reset)",
            slv->time.update_cone_reset);
  BTOR_MSG (btor->msg,
            1,
            "%.2f seconds for updating cone (model gen)",
            slv->time.update_cone_model_gen);
  if (btor_opt_get (btor, BTOR_OPT_PROP_USE_BANDIT))
    BTOR_MSG (btor->msg,
              1,
              "%.2f seconds for updating cone (compute score)",
              slv->time.update_cone_compute_score);
  BTOR_MSG (btor->msg, 1, "");
}

static void
print_model_prop_solver (BtorPropSolver *slv, const char *format, FILE *file)
{
  btor_print_model_aufbv (slv->btor, format, file);
}

BtorSolver *
btor_new_prop_solver (Btor *btor)
{
  assert (btor);

  BtorPropSolver *slv;

  BTOR_CNEW (btor->mm, slv);

  slv->btor = btor;
  slv->kind = BTOR_PROP_SOLVER_KIND;

  slv->api.clone = (BtorSolverClone) clone_prop_solver;
  slv->api.delet = (BtorSolverDelete) delete_prop_solver;
  slv->api.sat   = (BtorSolverSat) sat_prop_solver;
  slv->api.generate_model =
      (BtorSolverGenerateModel) generate_model_prop_solver;
  slv->api.print_stats = (BtorSolverPrintStats) print_stats_prop_solver;
  slv->api.print_time_stats =
      (BtorSolverPrintTimeStats) print_time_stats_prop_solver;
  slv->api.print_model = (BtorSolverPrintModel) print_model_prop_solver;

  BTOR_INIT_STACK (btor->mm, slv->toprop);
#ifndef NDEBUG
  BTOR_INIT_STACK (btor->mm, slv->prop_path);
#endif

  BTOR_MSG (btor->msg, 1, "enabled prop engine");

  return (BtorSolver *) slv;
}
