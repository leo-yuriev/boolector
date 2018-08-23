/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORINVUTILS_H_INCLUDED
#define BTORINVUTILS_H_INCLUDED

#include "btorbv.h"

/*------------------------------------------------------------------------*/

bool btor_is_inv_and (BtorMemMgr *mm,
                      const BtorBitVector *s,
                      const BtorBitVector *t);

bool btor_is_inv_concat (BtorMemMgr *mm,
                         const BtorBitVector *s,
                         const BtorBitVector *t,
                         uint32_t pos_x);

bool btor_is_inv_mul (BtorMemMgr *mm,
                      const BtorBitVector *s,
                      const BtorBitVector *t);

bool btor_is_inv_or (BtorMemMgr *mm,
                     const BtorBitVector *s,
                     const BtorBitVector *t);

bool btor_is_inv_sll (BtorMemMgr *mm,
                      const BtorBitVector *s,
                      const BtorBitVector *t,
                      uint32_t pos_x);

bool btor_is_inv_sra (BtorMemMgr *mm,
                      const BtorBitVector *s,
                      const BtorBitVector *t,
                      uint32_t pos_x);

bool btor_is_inv_srl (BtorMemMgr *mm,
                      const BtorBitVector *s,
                      const BtorBitVector *t,
                      uint32_t pos_x);

bool btor_is_inv_udiv (BtorMemMgr *mm,
                       const BtorBitVector *s,
                       const BtorBitVector *t,
                       uint32_t pos_x);

bool btor_is_inv_ult (BtorMemMgr *mm, const BtorBitVector *t, uint32_t pos_x);

bool btor_is_inv_urem (BtorMemMgr *mm,
                       const BtorBitVector *s,
                       const BtorBitVector *t,
                       uint32_t pos_x);

#endif
