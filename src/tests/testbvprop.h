/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTBVPROP_H_INCLUDED
#define TESTBVPROP_H_INCLUDED

#include <stdint.h>

void init_bvprop_tests (void);

void run_bvprop_tests (int32_t argc, char **argv);

void finish_bvprop_tests (void);

#endif
