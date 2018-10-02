/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TESTCBITS_H_INCLUDED
#define TESTCBITS_H_INCLUDED

#include <stdint.h>

void init_cbits_tests (void);

void run_cbits_tests (int32_t argc, char **argv);

void finish_cbits_tests (void);

#endif
