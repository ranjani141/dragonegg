/* Subroutines used for code generation on IA-32.
   Copyright (C) 1988-2017 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "rtl.h"
#include "tree.h"
#include "memmodel.h"
#include "gimple.h"
#include "cfghooks.h"
#include "cfgloop.h"
#include "df.h"
#include "tm_p.h"
#include "stringpool.h"
#include "expmed.h"
#include "regs.h"
#include "emit-rtl.h"
#include "cgraph.h"
#include "diagnostic.h"
#include "cfgbuild.h"
#include "alias.h"
#include "fold-const.h"
#include "attribs.h"
#include "calls.h"
#include "stor-layout.h"
#include "varasm.h"
#include "output.h"
#include "flags.h"
#include "except.h"
#include "explow.h"
#include "expr.h"
#include "cfgrtl.h"
#include "langhooks.h"
#include "gimplify.h"
#include "params.h"
#include "cselib.h"
#include "sched-int.h"
#include "opts.h"
#include "tree-pass.h"
#include "context.h"
#include "pass_manager.h"
#include "target-globals.h"
#include "gimple-iterator.h"
#include "tree-vectorizer.h"
#include "shrink-wrap.h"
#include "builtins.h"
#include "rtl-iter.h"
#include "tree-iterator.h"
#include "tree-chkp.h"
#include "rtl-chkp.h"
#include "dbgcnt.h"
#include "regrename.h"
#include "dojump.h"
#include "fold-const-call.h"
#include "tree-vrp.h"
#include "tree-ssanames.h"
#include "selftest.h"
#include "selftest-rtl.h"
#include "print-rtl.h"
#include "intl.h"
#include "ifcvt.h"
#include "symbol-summary.h"
#include "ipa-prop.h"
#include "ipa-fnsummary.h"

#ifndef CHECK_STACK_LIMIT
#define CHECK_STACK_LIMIT (-1)
#endif

/* Return index of given mode in mult and division cost tables.  */
#define MODE_INDEX(mode)					\
  ((mode) == QImode ? 0						\
   : (mode) == HImode ? 1					\
   : (mode) == SImode ? 2					\
   : (mode) == DImode ? 3					\
   : 4)

/* Processor costs (relative to an add) */
/* We assume COSTS_N_INSNS is defined as (N)*4 and an addition is 2 bytes.  */
#define COSTS_N_BYTES(N) ((N) * 2)

#define DUMMY_STRINGOP_ALGS {libcall, {{-1, libcall, false}}}

static stringop_algs ix86_size_memcpy[2] = {
  {rep_prefix_1_byte, {{-1, rep_prefix_1_byte, false}}},
  {rep_prefix_1_byte, {{-1, rep_prefix_1_byte, false}}}};
static stringop_algs ix86_size_memset[2] = {
  {rep_prefix_1_byte, {{-1, rep_prefix_1_byte, false}}},
  {rep_prefix_1_byte, {{-1, rep_prefix_1_byte, false}}}};

const
struct processor_costs ix86_size_cost = {/* costs for tuning for size */
  COSTS_N_BYTES (2),			/* cost of an add instruction */
  COSTS_N_BYTES (3),			/* cost of a lea instruction */
  COSTS_N_BYTES (2),			/* variable shift costs */
  COSTS_N_BYTES (3),			/* constant shift costs */
  {COSTS_N_BYTES (3),			/* cost of starting multiply for QI */
   COSTS_N_BYTES (3),			/*				 HI */
   COSTS_N_BYTES (3),			/*				 SI */
   COSTS_N_BYTES (3),			/*				 DI */
   COSTS_N_BYTES (5)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_BYTES (3),			/* cost of a divide/mod for QI */
   COSTS_N_BYTES (3),			/*			    HI */
   COSTS_N_BYTES (3),			/*			    SI */
   COSTS_N_BYTES (3),			/*			    DI */
   COSTS_N_BYTES (5)},			/*			    other */
  COSTS_N_BYTES (3),			/* cost of movsx */
  COSTS_N_BYTES (3),			/* cost of movzx */
  0,					/* "large" insn */
  2,					/* MOVE_RATIO */
  2,				     /* cost for loading QImode using movzbl */
  {2, 2, 2},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 2, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {2, 2, 2},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {2, 2, 2},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  3,					/* cost of moving MMX register */
  {3, 3},				/* cost of loading MMX registers
					   in SImode and DImode */
  {3, 3},				/* cost of storing MMX registers
					   in SImode and DImode */
  3,					/* cost of moving SSE register */
  {3, 3, 3},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {3, 3, 3},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  0,					/* size of l1 cache  */
  0,					/* size of l2 cache  */
  0,					/* size of prefetch block */
  0,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_BYTES (2),			/* cost of FADD and FSUB insns.  */
  COSTS_N_BYTES (2),			/* cost of FMUL instruction.  */
  COSTS_N_BYTES (2),			/* cost of FDIV instruction.  */
  COSTS_N_BYTES (2),			/* cost of FABS instruction.  */
  COSTS_N_BYTES (2),			/* cost of FCHS instruction.  */
  COSTS_N_BYTES (2),			/* cost of FSQRT instruction.  */
  ix86_size_memcpy,
  ix86_size_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  1,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  1,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/* Processor costs (relative to an add) */
static stringop_algs i386_memcpy[2] = {
  {rep_prefix_1_byte, {{-1, rep_prefix_1_byte, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs i386_memset[2] = {
  {rep_prefix_1_byte, {{-1, rep_prefix_1_byte, false}}},
  DUMMY_STRINGOP_ALGS};

static const
struct processor_costs i386_cost = {	/* 386 specific costs */
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (3),			/* variable shift costs */
  COSTS_N_INSNS (2),			/* constant shift costs */
  {COSTS_N_INSNS (6),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (6),			/*				 HI */
   COSTS_N_INSNS (6),			/*				 SI */
   COSTS_N_INSNS (6),			/*				 DI */
   COSTS_N_INSNS (6)},			/*			      other */
  COSTS_N_INSNS (1),			/* cost of multiply per each bit set */
  {COSTS_N_INSNS (23),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (23),			/*			    HI */
   COSTS_N_INSNS (23),			/*			    SI */
   COSTS_N_INSNS (23),			/*			    DI */
   COSTS_N_INSNS (23)},			/*			    other */
  COSTS_N_INSNS (3),			/* cost of movsx */
  COSTS_N_INSNS (2),			/* cost of movzx */
  15,					/* "large" insn */
  3,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {2, 4, 2},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 4, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {8, 8, 8},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {8, 8, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 8, 16},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 8, 16},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  0,					/* size of l1 cache  */
  0,					/* size of l2 cache  */
  0,					/* size of prefetch block */
  0,					/* number of parallel prefetches */
  1,					/* Branch cost */
  COSTS_N_INSNS (23),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (27),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (88),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (22),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (24),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (122),			/* cost of FSQRT instruction.  */
  i386_memcpy,
  i386_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs i486_memcpy[2] = {
  {rep_prefix_4_byte, {{-1, rep_prefix_4_byte, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs i486_memset[2] = {
  {rep_prefix_4_byte, {{-1, rep_prefix_4_byte, false}}},
  DUMMY_STRINGOP_ALGS};

static const
struct processor_costs i486_cost = {	/* 486 specific costs */
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (3),			/* variable shift costs */
  COSTS_N_INSNS (2),			/* constant shift costs */
  {COSTS_N_INSNS (12),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (12),			/*				 HI */
   COSTS_N_INSNS (12),			/*				 SI */
   COSTS_N_INSNS (12),			/*				 DI */
   COSTS_N_INSNS (12)},			/*			      other */
  1,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (40),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (40),			/*			    HI */
   COSTS_N_INSNS (40),			/*			    SI */
   COSTS_N_INSNS (40),			/*			    DI */
   COSTS_N_INSNS (40)},			/*			    other */
  COSTS_N_INSNS (3),			/* cost of movsx */
  COSTS_N_INSNS (2),			/* cost of movzx */
  15,					/* "large" insn */
  3,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {2, 4, 2},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 4, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {8, 8, 8},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {8, 8, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 8, 16},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 8, 16},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  4,					/* size of l1 cache.  486 has 8kB cache
					   shared for code and data, so 4kB is
					   not really precise.  */
  4,					/* size of l2 cache  */
  0,					/* size of prefetch block */
  0,					/* number of parallel prefetches */
  1,					/* Branch cost */
  COSTS_N_INSNS (8),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (16),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (73),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (3),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (3),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (83),			/* cost of FSQRT instruction.  */
  i486_memcpy,
  i486_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs pentium_memcpy[2] = {
  {libcall, {{256, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs pentium_memset[2] = {
  {libcall, {{-1, rep_prefix_4_byte, false}}},
  DUMMY_STRINGOP_ALGS};

static const
struct processor_costs pentium_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (4),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (11),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (11),			/*				 HI */
   COSTS_N_INSNS (11),			/*				 SI */
   COSTS_N_INSNS (11),			/*				 DI */
   COSTS_N_INSNS (11)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (25),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (25),			/*			    HI */
   COSTS_N_INSNS (25),			/*			    SI */
   COSTS_N_INSNS (25),			/*			    DI */
   COSTS_N_INSNS (25)},			/*			    other */
  COSTS_N_INSNS (3),			/* cost of movsx */
  COSTS_N_INSNS (2),			/* cost of movzx */
  8,					/* "large" insn */
  6,					/* MOVE_RATIO */
  6,				     /* cost for loading QImode using movzbl */
  {2, 4, 2},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 4, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {2, 2, 6},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 4, 6},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  8,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 8, 16},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 8, 16},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  8,					/* size of l1 cache.  */
  8,					/* size of l2 cache  */
  0,					/* size of prefetch block */
  0,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (3),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (3),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (39),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (1),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (1),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (70),			/* cost of FSQRT instruction.  */
  pentium_memcpy,
  pentium_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static const
struct processor_costs lakemont_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1) + 1,		/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (11),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (11),			/*				 HI */
   COSTS_N_INSNS (11),			/*				 SI */
   COSTS_N_INSNS (11),			/*				 DI */
   COSTS_N_INSNS (11)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (25),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (25),			/*			    HI */
   COSTS_N_INSNS (25),			/*			    SI */
   COSTS_N_INSNS (25),			/*			    DI */
   COSTS_N_INSNS (25)},			/*			    other */
  COSTS_N_INSNS (3),			/* cost of movsx */
  COSTS_N_INSNS (2),			/* cost of movzx */
  8,					/* "large" insn */
  17,					/* MOVE_RATIO */
  6,				     /* cost for loading QImode using movzbl */
  {2, 4, 2},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 4, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {2, 2, 6},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 4, 6},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  8,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 8, 16},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 8, 16},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  8,					/* size of l1 cache.  */
  8,					/* size of l2 cache  */
  0,					/* size of prefetch block */
  0,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (3),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (3),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (39),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (1),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (1),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (70),			/* cost of FSQRT instruction.  */
  pentium_memcpy,
  pentium_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/* PentiumPro has optimized rep instructions for blocks aligned by 8 bytes
   (we ensure the alignment).  For small blocks inline loop is still a
   noticeable win, for bigger blocks either rep movsl or rep movsb is
   way to go.  Rep movsb has apparently more expensive startup time in CPU,
   but after 4K the difference is down in the noise.  */
static stringop_algs pentiumpro_memcpy[2] = {
  {rep_prefix_4_byte, {{128, loop, false}, {1024, unrolled_loop, false},
                       {8192, rep_prefix_4_byte, false},
                       {-1, rep_prefix_1_byte, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs pentiumpro_memset[2] = {
  {rep_prefix_4_byte, {{1024, unrolled_loop, false},
                       {8192, rep_prefix_4_byte, false},
                       {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static const
struct processor_costs pentiumpro_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (4),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (4),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (4)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (17),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (17),			/*			    HI */
   COSTS_N_INSNS (17),			/*			    SI */
   COSTS_N_INSNS (17),			/*			    DI */
   COSTS_N_INSNS (17)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  6,					/* MOVE_RATIO */
  2,				     /* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 2, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {2, 2, 6},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 4, 6},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {2, 2},				/* cost of loading MMX registers
					   in SImode and DImode */
  {2, 2},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {2, 2, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {2, 2, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  8,					/* size of l1 cache.  */
  256,					/* size of l2 cache  */
  32,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (3),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (5),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (56),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (56),			/* cost of FSQRT instruction.  */
  pentiumpro_memcpy,
  pentiumpro_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs geode_memcpy[2] = {
  {libcall, {{256, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs geode_memset[2] = {
  {libcall, {{256, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static const
struct processor_costs geode_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (2),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (7),			/*				 SI */
   COSTS_N_INSNS (7),			/*				 DI */
   COSTS_N_INSNS (7)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (15),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (23),			/*			    HI */
   COSTS_N_INSNS (39),			/*			    SI */
   COSTS_N_INSNS (39),			/*			    DI */
   COSTS_N_INSNS (39)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  4,					/* MOVE_RATIO */
  1,				     /* cost for loading QImode using movzbl */
  {1, 1, 1},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {1, 1, 1},				/* cost of storing integer registers */
  1,					/* cost of reg,reg fld/fst */
  {1, 1, 1},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 6, 6},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */

  2,					/* cost of moving MMX register */
  {2, 2},				/* cost of loading MMX registers
					   in SImode and DImode */
  {2, 2},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {2, 2, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {2, 2, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  64,					/* size of l1 cache.  */
  128,					/* size of l2 cache.  */
  32,					/* size of prefetch block */
  1,					/* number of parallel prefetches */
  1,					/* Branch cost */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (11),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (47),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (1),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (1),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (54),			/* cost of FSQRT instruction.  */
  geode_memcpy,
  geode_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs k6_memcpy[2] = {
  {libcall, {{256, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs k6_memset[2] = {
  {libcall, {{256, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static const
struct processor_costs k6_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (2),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (3),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (3),			/*				 DI */
   COSTS_N_INSNS (3)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (18),			/*			    HI */
   COSTS_N_INSNS (18),			/*			    SI */
   COSTS_N_INSNS (18),			/*			    DI */
   COSTS_N_INSNS (18)},			/*			    other */
  COSTS_N_INSNS (2),			/* cost of movsx */
  COSTS_N_INSNS (2),			/* cost of movzx */
  8,					/* "large" insn */
  4,					/* MOVE_RATIO */
  3,				     /* cost for loading QImode using movzbl */
  {4, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 3, 2},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {6, 6, 6},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 4, 4},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {2, 2},				/* cost of loading MMX registers
					   in SImode and DImode */
  {2, 2},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {2, 2, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {2, 2, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  6,					/* MMX or SSE register to integer */
  32,					/* size of l1 cache.  */
  32,					/* size of l2 cache.  Some models
					   have integrated l2 cache, but
					   optimizing for k6 is not important
					   enough to worry about that.  */
  32,					/* size of prefetch block */
  1,					/* number of parallel prefetches */
  1,					/* Branch cost */
  COSTS_N_INSNS (2),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (2),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (56),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (56),			/* cost of FSQRT instruction.  */
  k6_memcpy,
  k6_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/* For some reason, Athlon deals better with REP prefix (relative to loops)
   compared to K8. Alignment becomes important after 8 bytes for memcpy and
   128 bytes for memset.  */
static stringop_algs athlon_memcpy[2] = {
  {libcall, {{2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs athlon_memset[2] = {
  {libcall, {{2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};
static const
struct processor_costs athlon_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (2),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (5),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (5),			/*				 HI */
   COSTS_N_INSNS (5),			/*				 SI */
   COSTS_N_INSNS (5),			/*				 DI */
   COSTS_N_INSNS (5)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {3, 4, 3},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {3, 4, 3},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {4, 4, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 4},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 6},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 5},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  64,					/* size of l1 cache.  */
  256,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  5,					/* Branch cost */
  COSTS_N_INSNS (4),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (4),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (24),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (35),			/* cost of FSQRT instruction.  */
  athlon_memcpy,
  athlon_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/* K8 has optimized REP instruction for medium sized blocks, but for very
   small blocks it is better to use loop. For large blocks, libcall can
   do nontemporary accesses and beat inline considerably.  */
static stringop_algs k8_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs k8_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static const
struct processor_costs k8_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (2),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (5)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {3, 4, 3},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {3, 4, 3},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {4, 4, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {3, 3},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 3, 6},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 5},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  64,					/* size of l1 cache.  */
  512,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches */
  3,					/* Branch cost */
  COSTS_N_INSNS (4),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (4),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (19),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (35),			/* cost of FSQRT instruction.  */

  k8_memcpy,
  k8_memset,
  4,					/* scalar_stmt_cost.  */
  2,					/* scalar load_cost.  */
  2,					/* scalar_store_cost.  */
  5,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  2,					/* vec_align_load_cost.  */
  3,					/* vec_unalign_load_cost.  */
  3,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  2,					/* cond_not_taken_branch_cost.  */
};

/* AMDFAM10 has optimized REP instruction for medium sized blocks, but for
   very small blocks it is better to use loop. For large blocks, libcall can
   do nontemporary accesses and beat inline considerably.  */
static stringop_algs amdfam10_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs amdfam10_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
struct processor_costs amdfam10_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (2),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (5)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {3, 4, 3},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {3, 4, 3},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {4, 4, 12},				/* cost of loading fp registers
		   			   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
 		   			   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {3, 3},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 3},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 5},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
  					/* On K8:
  					    MOVD reg64, xmmreg Double FSTORE 4
					    MOVD reg32, xmmreg Double FSTORE 4
					   On AMDFAM10:
					    MOVD reg64, xmmreg Double FADD 3
							       1/1  1/1
					    MOVD reg32, xmmreg Double FADD 3
							       1/1  1/1 */
  64,					/* size of l1 cache.  */
  512,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (4),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (4),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (19),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (35),			/* cost of FSQRT instruction.  */

  amdfam10_memcpy,
  amdfam10_memset,
  4,					/* scalar_stmt_cost.  */
  2,					/* scalar load_cost.  */
  2,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  2,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  2,					/* vec_store_cost.  */
  2,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/*  BDVER1 has optimized REP instruction for medium sized blocks, but for
    very small blocks it is better to use loop. For large blocks, libcall
    can do nontemporary accesses and beat inline considerably.  */
static stringop_algs bdver1_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs bdver1_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};

const struct processor_costs bdver1_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (4),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (4),			/*				 SI */
   COSTS_N_INSNS (6),			/*				 DI */
   COSTS_N_INSNS (6)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {5, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {5, 5, 12},				/* cost of loading fp registers
		   			   in SFmode, DFmode and XFmode */
  {4, 4, 8},				/* cost of storing fp registers
 		   			   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 4},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 4},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 4},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  2,					/* MMX or SSE register to integer */
  					/* On K8:
					    MOVD reg64, xmmreg Double FSTORE 4
					    MOVD reg32, xmmreg Double FSTORE 4
					   On AMDFAM10:
					    MOVD reg64, xmmreg Double FADD 3
							       1/1  1/1
					    MOVD reg32, xmmreg Double FADD 3
							       1/1  1/1 */
  16,					/* size of l1 cache.  */
  2048,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (6),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (42),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (52),			/* cost of FSQRT instruction.  */

  bdver1_memcpy,
  bdver1_memset,
  6,					/* scalar_stmt_cost.  */
  4,					/* scalar load_cost.  */
  4,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  4,					/* vec_align_load_cost.  */
  4,					/* vec_unalign_load_cost.  */
  4,					/* vec_store_cost.  */
  4,					/* cond_taken_branch_cost.  */
  2,					/* cond_not_taken_branch_cost.  */
};

/*  BDVER2 has optimized REP instruction for medium sized blocks, but for
    very small blocks it is better to use loop. For large blocks, libcall
    can do nontemporary accesses and beat inline considerably.  */

static stringop_algs bdver2_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs bdver2_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};

const struct processor_costs bdver2_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (4),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (4),			/*				 SI */
   COSTS_N_INSNS (6),			/*				 DI */
   COSTS_N_INSNS (6)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {5, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {5, 5, 12},				/* cost of loading fp registers
		   			   in SFmode, DFmode and XFmode */
  {4, 4, 8},				/* cost of storing fp registers
 		   			   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 4},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 4},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 4},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  2,					/* MMX or SSE register to integer */
  					/* On K8:
					    MOVD reg64, xmmreg Double FSTORE 4
					    MOVD reg32, xmmreg Double FSTORE 4
					   On AMDFAM10:
					    MOVD reg64, xmmreg Double FADD 3
							       1/1  1/1
					    MOVD reg32, xmmreg Double FADD 3
							       1/1  1/1 */
  16,					/* size of l1 cache.  */
  2048,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (6),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (42),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (52),			/* cost of FSQRT instruction.  */

  bdver2_memcpy,
  bdver2_memset,
  6,					/* scalar_stmt_cost.  */
  4,					/* scalar load_cost.  */
  4,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  4,					/* vec_align_load_cost.  */
  4,					/* vec_unalign_load_cost.  */
  4,					/* vec_store_cost.  */
  4,					/* cond_taken_branch_cost.  */
  2,					/* cond_not_taken_branch_cost.  */
};


  /*  BDVER3 has optimized REP instruction for medium sized blocks, but for
      very small blocks it is better to use loop. For large blocks, libcall
      can do nontemporary accesses and beat inline considerably.  */
static stringop_algs bdver3_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs bdver3_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
struct processor_costs bdver3_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (4),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (4),			/*				 SI */
   COSTS_N_INSNS (6),			/*				 DI */
   COSTS_N_INSNS (6)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {5, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {5, 5, 12},				/* cost of loading fp registers
		   			   in SFmode, DFmode and XFmode */
  {4, 4, 8},				/* cost of storing fp registers
 		   			   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 4},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 4},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 4},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  2,					/* MMX or SSE register to integer */
  16,					/* size of l1 cache.  */
  2048,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (6),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (42),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (52),			/* cost of FSQRT instruction.  */

  bdver3_memcpy,
  bdver3_memset,
  6,					/* scalar_stmt_cost.  */
  4,					/* scalar load_cost.  */
  4,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  4,					/* vec_align_load_cost.  */
  4,					/* vec_unalign_load_cost.  */
  4,					/* vec_store_cost.  */
  4,					/* cond_taken_branch_cost.  */
  2,					/* cond_not_taken_branch_cost.  */
};

/*  BDVER4 has optimized REP instruction for medium sized blocks, but for
    very small blocks it is better to use loop. For large blocks, libcall
    can do nontemporary accesses and beat inline considerably.  */
static stringop_algs bdver4_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs bdver4_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
struct processor_costs bdver4_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (4),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (4),			/*				 SI */
   COSTS_N_INSNS (6),			/*				 DI */
   COSTS_N_INSNS (6)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {5, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {5, 5, 12},				/* cost of loading fp registers
		   			   in SFmode, DFmode and XFmode */
  {4, 4, 8},				/* cost of storing fp registers
 		   			   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {4, 4},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 4},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 4},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  2,					/* MMX or SSE register to integer */
  16,					/* size of l1 cache.  */
  2048,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (6),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (42),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (52),			/* cost of FSQRT instruction.  */

  bdver4_memcpy,
  bdver4_memset,
  6,					/* scalar_stmt_cost.  */
  4,					/* scalar load_cost.  */
  4,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  4,					/* vec_align_load_cost.  */
  4,					/* vec_unalign_load_cost.  */
  4,					/* vec_store_cost.  */
  4,					/* cond_taken_branch_cost.  */
  2,					/* cond_not_taken_branch_cost.  */
};


/*  ZNVER1 has optimized REP instruction for medium sized blocks, but for
    very small blocks it is better to use loop.  For large blocks, libcall
    can do nontemporary accesses and beat inline considerably.  */
static stringop_algs znver1_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
	     {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
	     {-1, libcall, false}}}};
static stringop_algs znver1_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
	     {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
	     {-1, libcall, false}}}};
struct processor_costs znver1_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction.  */
  COSTS_N_INSNS (1),			/* cost of a lea instruction.  */
  COSTS_N_INSNS (1),			/* variable shift costs.  */
  COSTS_N_INSNS (1),			/* constant shift costs.  */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI.  */
   COSTS_N_INSNS (3),			/*				 HI.  */
   COSTS_N_INSNS (3),			/*				 SI.  */
   COSTS_N_INSNS (4),			/*				 DI.  */
   COSTS_N_INSNS (4)},			/*			      other.  */
  0,					/* cost of multiply per each bit
					    set.  */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI.  */
   COSTS_N_INSNS (35),			/*			    HI.  */
   COSTS_N_INSNS (51),			/*			    SI.  */
   COSTS_N_INSNS (83),			/*			    DI.  */
   COSTS_N_INSNS (83)},			/*			    other.  */
  COSTS_N_INSNS (1),			/* cost of movsx.  */
  COSTS_N_INSNS (1),			/* cost of movzx.  */
  8,					/* "large" insn.  */
  9,					/* MOVE_RATIO.  */
  4,					/* cost for loading QImode using
					   movzbl.  */
  {5, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer
					   registers.  */
  2,					/* cost of reg,reg fld/fst.  */
  {5, 5, 12},				/* cost of loading fp registers
		   			   in SFmode, DFmode and XFmode.  */
  {4, 4, 8},				/* cost of storing fp registers
 		   			   in SFmode, DFmode and XFmode.  */
  2,					/* cost of moving MMX register.  */
  {4, 4},				/* cost of loading MMX registers
					   in SImode and DImode.  */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode.  */
  2,					/* cost of moving SSE register.  */
  {4, 4, 4},				/* cost of loading SSE registers
					   in SImode, DImode and TImode.  */
  {4, 4, 4},				/* cost of storing SSE registers
					   in SImode, DImode and TImode.  */
  2,					/* MMX or SSE register to integer.  */
  32,					/* size of l1 cache.  */
  512,					/* size of l2 cache.  */
  64,					/* size of prefetch block.  */
  /* New AMD processors never drop prefetches; if they cannot be performed
     immediately, they are queued.  We set number of simultaneous prefetches
     to a large constant to reflect this (it probably is not a good idea not
     to limit number of prefetches at all, as their execution also takes some
     time).  */
  100,					/* number of parallel prefetches.  */
  2,					/* Branch cost.  */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (6),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (42),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (52),			/* cost of FSQRT instruction.  */

  znver1_memcpy,
  znver1_memset,
  6,					/* scalar_stmt_cost.  */
  4,					/* scalar load_cost.  */
  4,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  4,					/* vec_align_load_cost.  */
  4,					/* vec_unalign_load_cost.  */
  4,					/* vec_store_cost.  */
  4,					/* cond_taken_branch_cost.  */
  2,					/* cond_not_taken_branch_cost.  */
};

  /* BTVER1 has optimized REP instruction for medium sized blocks, but for
     very small blocks it is better to use loop. For large blocks, libcall can
     do nontemporary accesses and beat inline considerably.  */
static stringop_algs btver1_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs btver1_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
const struct processor_costs btver1_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (2),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (5)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {3, 4, 3},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {3, 4, 3},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {4, 4, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {3, 3},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 3},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 5},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
					/* On K8:
					   MOVD reg64, xmmreg Double FSTORE 4
					   MOVD reg32, xmmreg Double FSTORE 4
					   On AMDFAM10:
					   MOVD reg64, xmmreg Double FADD 3
							       1/1  1/1
					    MOVD reg32, xmmreg Double FADD 3
							       1/1  1/1 */
  32,					/* size of l1 cache.  */
  512,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (4),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (4),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (19),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (35),			/* cost of FSQRT instruction.  */

  btver1_memcpy,
  btver1_memset,
  4,					/* scalar_stmt_cost.  */
  2,					/* scalar load_cost.  */
  2,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  2,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  2,					/* vec_store_cost.  */
  2,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs btver2_memcpy[2] = {
  {libcall, {{6, loop, false}, {14, unrolled_loop, false},
             {-1, rep_prefix_4_byte, false}}},
  {libcall, {{16, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs btver2_memset[2] = {
  {libcall, {{8, loop, false}, {24, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{48, unrolled_loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
const struct processor_costs btver2_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (2),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (5)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (19),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (35),			/*			    HI */
   COSTS_N_INSNS (51),			/*			    SI */
   COSTS_N_INSNS (83),			/*			    DI */
   COSTS_N_INSNS (83)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  9,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {3, 4, 3},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {3, 4, 3},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {4, 4, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {3, 3},				/* cost of loading MMX registers
					   in SImode and DImode */
  {4, 4},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {4, 4, 3},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {4, 4, 5},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  3,					/* MMX or SSE register to integer */
					/* On K8:
					   MOVD reg64, xmmreg Double FSTORE 4
					   MOVD reg32, xmmreg Double FSTORE 4
					   On AMDFAM10:
					   MOVD reg64, xmmreg Double FADD 3
							       1/1  1/1
					    MOVD reg32, xmmreg Double FADD 3
							       1/1  1/1 */
  32,					/* size of l1 cache.  */
  2048,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  100,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (4),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (4),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (19),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (35),			/* cost of FSQRT instruction.  */
  btver2_memcpy,
  btver2_memset,
  4,					/* scalar_stmt_cost.  */
  2,					/* scalar load_cost.  */
  2,					/* scalar_store_cost.  */
  6,					/* vec_stmt_cost.  */
  0,					/* vec_to_scalar_cost.  */
  2,					/* scalar_to_vec_cost.  */
  2,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  2,					/* vec_store_cost.  */
  2,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs pentium4_memcpy[2] = {
  {libcall, {{12, loop_1_byte, false}, {-1, rep_prefix_4_byte, false}}},
  DUMMY_STRINGOP_ALGS};
static stringop_algs pentium4_memset[2] = {
  {libcall, {{6, loop_1_byte, false}, {48, loop, false},
             {20480, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  DUMMY_STRINGOP_ALGS};

static const
struct processor_costs pentium4_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (3),			/* cost of a lea instruction */
  COSTS_N_INSNS (4),			/* variable shift costs */
  COSTS_N_INSNS (4),			/* constant shift costs */
  {COSTS_N_INSNS (15),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (15),			/*				 HI */
   COSTS_N_INSNS (15),			/*				 SI */
   COSTS_N_INSNS (15),			/*				 DI */
   COSTS_N_INSNS (15)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (56),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (56),			/*			    HI */
   COSTS_N_INSNS (56),			/*			    SI */
   COSTS_N_INSNS (56),			/*			    DI */
   COSTS_N_INSNS (56)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  16,					/* "large" insn */
  6,					/* MOVE_RATIO */
  2,				     /* cost for loading QImode using movzbl */
  {4, 5, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {2, 3, 2},				/* cost of storing integer registers */
  2,					/* cost of reg,reg fld/fst */
  {2, 2, 6},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 4, 6},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {2, 2},				/* cost of loading MMX registers
					   in SImode and DImode */
  {2, 2},				/* cost of storing MMX registers
					   in SImode and DImode */
  12,					/* cost of moving SSE register */
  {12, 12, 12},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {2, 2, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  10,					/* MMX or SSE register to integer */
  8,					/* size of l1 cache.  */
  256,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  2,					/* Branch cost */
  COSTS_N_INSNS (5),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (7),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (43),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (2),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (2),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (43),			/* cost of FSQRT instruction.  */
  pentium4_memcpy,
  pentium4_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs nocona_memcpy[2] = {
  {libcall, {{12, loop_1_byte, false}, {-1, rep_prefix_4_byte, false}}},
  {libcall, {{32, loop, false}, {20000, rep_prefix_8_byte, false},
             {100000, unrolled_loop, false}, {-1, libcall, false}}}};

static stringop_algs nocona_memset[2] = {
  {libcall, {{6, loop_1_byte, false}, {48, loop, false},
             {20480, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{24, loop, false}, {64, unrolled_loop, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};

static const
struct processor_costs nocona_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1),			/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (10),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (10),			/*				 HI */
   COSTS_N_INSNS (10),			/*				 SI */
   COSTS_N_INSNS (10),			/*				 DI */
   COSTS_N_INSNS (10)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (66),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (66),			/*			    HI */
   COSTS_N_INSNS (66),			/*			    SI */
   COSTS_N_INSNS (66),			/*			    DI */
   COSTS_N_INSNS (66)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  16,					/* "large" insn */
  17,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  3,					/* cost of reg,reg fld/fst */
  {12, 12, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {4, 4, 4},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  6,					/* cost of moving MMX register */
  {12, 12},				/* cost of loading MMX registers
					   in SImode and DImode */
  {12, 12},				/* cost of storing MMX registers
					   in SImode and DImode */
  6,					/* cost of moving SSE register */
  {12, 12, 12},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {12, 12, 12},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  8,					/* MMX or SSE register to integer */
  8,					/* size of l1 cache.  */
  1024,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  8,					/* number of parallel prefetches */
  1,					/* Branch cost */
  COSTS_N_INSNS (6),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (8),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (40),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (3),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (3),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (44),			/* cost of FSQRT instruction.  */
  nocona_memcpy,
  nocona_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs atom_memcpy[2] = {
  {libcall, {{11, loop, false}, {-1, rep_prefix_4_byte, false}}},
  {libcall, {{32, loop, false}, {64, rep_prefix_4_byte, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static stringop_algs atom_memset[2] = {
  {libcall, {{8, loop, false}, {15, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{24, loop, false}, {32, unrolled_loop, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static const
struct processor_costs atom_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1) + 1,		/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (2)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  17,					/* MOVE_RATIO */
  4,					/* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {12, 12, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {8, 8, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {8, 8, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  32,					/* size of l1 cache.  */
  256,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  3,					/* Branch cost */
  COSTS_N_INSNS (8),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (8),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (20),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (8),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (8),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (40),			/* cost of FSQRT instruction.  */
  atom_memcpy,
  atom_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs slm_memcpy[2] = {
  {libcall, {{11, loop, false}, {-1, rep_prefix_4_byte, false}}},
  {libcall, {{32, loop, false}, {64, rep_prefix_4_byte, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static stringop_algs slm_memset[2] = {
  {libcall, {{8, loop, false}, {15, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{24, loop, false}, {32, unrolled_loop, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static const
struct processor_costs slm_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1) + 1,		/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (3),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (2)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  17,					/* MOVE_RATIO */
  4,					/* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {12, 12, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {8, 8, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {8, 8, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  32,					/* size of l1 cache.  */
  256,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  3,					/* Branch cost */
  COSTS_N_INSNS (8),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (8),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (20),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (8),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (8),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (40),			/* cost of FSQRT instruction.  */
  slm_memcpy,
  slm_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  4,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

static stringop_algs intel_memcpy[2] = {
  {libcall, {{11, loop, false}, {-1, rep_prefix_4_byte, false}}},
  {libcall, {{32, loop, false}, {64, rep_prefix_4_byte, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static stringop_algs intel_memset[2] = {
  {libcall, {{8, loop, false}, {15, unrolled_loop, false},
             {2048, rep_prefix_4_byte, false}, {-1, libcall, false}}},
  {libcall, {{24, loop, false}, {32, unrolled_loop, false},
             {8192, rep_prefix_8_byte, false}, {-1, libcall, false}}}};
static const
struct processor_costs intel_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  COSTS_N_INSNS (1) + 1,		/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (3),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (2)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  17,					/* MOVE_RATIO */
  4,					/* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {12, 12, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {8, 8, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {8, 8, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  32,					/* size of l1 cache.  */
  256,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  3,					/* Branch cost */
  COSTS_N_INSNS (8),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (8),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (20),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (8),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (8),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (40),			/* cost of FSQRT instruction.  */
  intel_memcpy,
  intel_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  4,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/* Generic should produce code tuned for Core-i7 (and newer chips)
   and btver1 (and newer chips).  */

static stringop_algs generic_memcpy[2] = {
  {libcall, {{32, loop, false}, {8192, rep_prefix_4_byte, false},
             {-1, libcall, false}}},
  {libcall, {{32, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static stringop_algs generic_memset[2] = {
  {libcall, {{32, loop, false}, {8192, rep_prefix_4_byte, false},
             {-1, libcall, false}}},
  {libcall, {{32, loop, false}, {8192, rep_prefix_8_byte, false},
             {-1, libcall, false}}}};
static const
struct processor_costs generic_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  /* On all chips taken into consideration lea is 2 cycles and more.  With
     this cost however our current implementation of synth_mult results in
     use of unnecessary temporary registers causing regression on several
     SPECfp benchmarks.  */
  COSTS_N_INSNS (1) + 1,		/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (2)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  17,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {12, 12, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {8, 8, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {8, 8, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  32,					/* size of l1 cache.  */
  512,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  /* Benchmarks shows large regressions on K8 sixtrack benchmark when this
     value is increased to perhaps more appropriate value of 5.  */
  3,					/* Branch cost */
  COSTS_N_INSNS (8),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (8),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (20),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (8),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (8),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (40),			/* cost of FSQRT instruction.  */
  generic_memcpy,
  generic_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};

/* core_cost should produce code tuned for Core familly of CPUs.  */
static stringop_algs core_memcpy[2] = {
  {libcall, {{1024, rep_prefix_4_byte, true}, {-1, libcall, false}}},
  {libcall, {{24, loop, true}, {128, rep_prefix_8_byte, true},
             {-1, libcall, false}}}};
static stringop_algs core_memset[2] = {
  {libcall, {{6, loop_1_byte, true},
             {24, loop, true},
             {8192, rep_prefix_4_byte, true},
             {-1, libcall, false}}},
  {libcall, {{24, loop, true}, {512, rep_prefix_8_byte, true},
             {-1, libcall, false}}}};

static const
struct processor_costs core_cost = {
  COSTS_N_INSNS (1),			/* cost of an add instruction */
  /* On all chips taken into consideration lea is 2 cycles and more.  With
     this cost however our current implementation of synth_mult results in
     use of unnecessary temporary registers causing regression on several
     SPECfp benchmarks.  */
  COSTS_N_INSNS (1) + 1,		/* cost of a lea instruction */
  COSTS_N_INSNS (1),			/* variable shift costs */
  COSTS_N_INSNS (1),			/* constant shift costs */
  {COSTS_N_INSNS (3),			/* cost of starting multiply for QI */
   COSTS_N_INSNS (4),			/*				 HI */
   COSTS_N_INSNS (3),			/*				 SI */
   COSTS_N_INSNS (4),			/*				 DI */
   COSTS_N_INSNS (2)},			/*			      other */
  0,					/* cost of multiply per each bit set */
  {COSTS_N_INSNS (18),			/* cost of a divide/mod for QI */
   COSTS_N_INSNS (26),			/*			    HI */
   COSTS_N_INSNS (42),			/*			    SI */
   COSTS_N_INSNS (74),			/*			    DI */
   COSTS_N_INSNS (74)},			/*			    other */
  COSTS_N_INSNS (1),			/* cost of movsx */
  COSTS_N_INSNS (1),			/* cost of movzx */
  8,					/* "large" insn */
  17,					/* MOVE_RATIO */
  4,				     /* cost for loading QImode using movzbl */
  {4, 4, 4},				/* cost of loading integer registers
					   in QImode, HImode and SImode.
					   Relative to reg-reg move (2).  */
  {4, 4, 4},				/* cost of storing integer registers */
  4,					/* cost of reg,reg fld/fst */
  {12, 12, 12},				/* cost of loading fp registers
					   in SFmode, DFmode and XFmode */
  {6, 6, 8},				/* cost of storing fp registers
					   in SFmode, DFmode and XFmode */
  2,					/* cost of moving MMX register */
  {8, 8},				/* cost of loading MMX registers
					   in SImode and DImode */
  {8, 8},				/* cost of storing MMX registers
					   in SImode and DImode */
  2,					/* cost of moving SSE register */
  {8, 8, 8},				/* cost of loading SSE registers
					   in SImode, DImode and TImode */
  {8, 8, 8},				/* cost of storing SSE registers
					   in SImode, DImode and TImode */
  5,					/* MMX or SSE register to integer */
  64,					/* size of l1 cache.  */
  512,					/* size of l2 cache.  */
  64,					/* size of prefetch block */
  6,					/* number of parallel prefetches */
  /* FIXME perhaps more appropriate value is 5.  */
  3,					/* Branch cost */
  COSTS_N_INSNS (8),			/* cost of FADD and FSUB insns.  */
  COSTS_N_INSNS (8),			/* cost of FMUL instruction.  */
  COSTS_N_INSNS (20),			/* cost of FDIV instruction.  */
  COSTS_N_INSNS (8),			/* cost of FABS instruction.  */
  COSTS_N_INSNS (8),			/* cost of FCHS instruction.  */
  COSTS_N_INSNS (40),			/* cost of FSQRT instruction.  */
  core_memcpy,
  core_memset,
  1,					/* scalar_stmt_cost.  */
  1,					/* scalar load_cost.  */
  1,					/* scalar_store_cost.  */
  1,					/* vec_stmt_cost.  */
  1,					/* vec_to_scalar_cost.  */
  1,					/* scalar_to_vec_cost.  */
  1,					/* vec_align_load_cost.  */
  2,					/* vec_unalign_load_cost.  */
  1,					/* vec_store_cost.  */
  3,					/* cond_taken_branch_cost.  */
  1,					/* cond_not_taken_branch_cost.  */
};


/* Set by -mtune.  */
const struct processor_costs *ix86_tune_cost = &pentium_cost;

/* Set by -mtune or -Os.  */
const struct processor_costs *ix86_cost = &pentium_cost;

/* Processor feature/optimization bitmasks.  */
#define m_386 (1U<<PROCESSOR_I386)
#define m_486 (1U<<PROCESSOR_I486)
#define m_PENT (1U<<PROCESSOR_PENTIUM)
#define m_LAKEMONT (1U<<PROCESSOR_LAKEMONT)
#define m_PPRO (1U<<PROCESSOR_PENTIUMPRO)
#define m_PENT4 (1U<<PROCESSOR_PENTIUM4)
#define m_NOCONA (1U<<PROCESSOR_NOCONA)
#define m_P4_NOCONA (m_PENT4 | m_NOCONA)
#define m_CORE2 (1U<<PROCESSOR_CORE2)
#define m_NEHALEM (1U<<PROCESSOR_NEHALEM)
#define m_SANDYBRIDGE (1U<<PROCESSOR_SANDYBRIDGE)
#define m_HASWELL (1U<<PROCESSOR_HASWELL)
#define m_CORE_ALL (m_CORE2 | m_NEHALEM  | m_SANDYBRIDGE | m_HASWELL)
#define m_BONNELL (1U<<PROCESSOR_BONNELL)
#define m_SILVERMONT (1U<<PROCESSOR_SILVERMONT)
#define m_KNL (1U<<PROCESSOR_KNL)
#define m_SKYLAKE_AVX512 (1U<<PROCESSOR_SKYLAKE_AVX512)
#define m_INTEL (1U<<PROCESSOR_INTEL)

#define m_GEODE (1U<<PROCESSOR_GEODE)
#define m_K6 (1U<<PROCESSOR_K6)
#define m_K6_GEODE (m_K6 | m_GEODE)
#define m_K8 (1U<<PROCESSOR_K8)
#define m_ATHLON (1U<<PROCESSOR_ATHLON)
#define m_ATHLON_K8 (m_K8 | m_ATHLON)
#define m_AMDFAM10 (1U<<PROCESSOR_AMDFAM10)
#define m_BDVER1 (1U<<PROCESSOR_BDVER1)
#define m_BDVER2 (1U<<PROCESSOR_BDVER2)
#define m_BDVER3 (1U<<PROCESSOR_BDVER3)
#define m_BDVER4 (1U<<PROCESSOR_BDVER4)
#define m_ZNVER1 (1U<<PROCESSOR_ZNVER1)
#define m_BTVER1 (1U<<PROCESSOR_BTVER1)
#define m_BTVER2 (1U<<PROCESSOR_BTVER2)
#define m_BDVER	(m_BDVER1 | m_BDVER2 | m_BDVER3 | m_BDVER4)
#define m_BTVER (m_BTVER1 | m_BTVER2)
#define m_AMD_MULTIPLE (m_ATHLON_K8 | m_AMDFAM10 | m_BDVER | m_BTVER \
			| m_ZNVER1)

#define m_GENERIC (1U<<PROCESSOR_GENERIC)

/* Feature tests against the various tunings.  */
unsigned char ix86_tune_features[X86_TUNE_LAST];

/* Feature tests against the various architecture variations.  */
unsigned char ix86_arch_features[X86_ARCH_LAST];

/* In case the average insn count for single function invocation is
   lower than this constant, emit fast (but longer) prologue and
   epilogue code.  */
#define FAST_PROLOGUE_INSN_COUNT 20

/* Names for 8 (low), 8 (high), and 16-bit registers, respectively.  */
static const char *const qi_reg_name[] = QI_REGISTER_NAMES;
static const char *const qi_high_reg_name[] = QI_HIGH_REGISTER_NAMES;
static const char *const hi_reg_name[] = HI_REGISTER_NAMES;

/* Array of the smallest class containing reg number REGNO, indexed by
   REGNO.  Used by REGNO_REG_CLASS in i386.h.  */

enum reg_class const regclass_map[FIRST_PSEUDO_REGISTER] =
{
  /* ax, dx, cx, bx */
  AREG, DREG, CREG, BREG,
  /* si, di, bp, sp */
  SIREG, DIREG, NON_Q_REGS, NON_Q_REGS,
  /* FP registers */
  FP_TOP_REG, FP_SECOND_REG, FLOAT_REGS, FLOAT_REGS,
  FLOAT_REGS, FLOAT_REGS, FLOAT_REGS, FLOAT_REGS,
  /* arg pointer */
  NON_Q_REGS,
  /* flags, fpsr, fpcr, frame */
  NO_REGS, NO_REGS, NO_REGS, NON_Q_REGS,
  /* SSE registers */
  SSE_FIRST_REG, SSE_REGS, SSE_REGS, SSE_REGS, SSE_REGS, SSE_REGS,
  SSE_REGS, SSE_REGS,
  /* MMX registers */
  MMX_REGS, MMX_REGS, MMX_REGS, MMX_REGS, MMX_REGS, MMX_REGS,
  MMX_REGS, MMX_REGS,
  /* REX registers */
  NON_Q_REGS, NON_Q_REGS, NON_Q_REGS, NON_Q_REGS,
  NON_Q_REGS, NON_Q_REGS, NON_Q_REGS, NON_Q_REGS,
  /* SSE REX registers */
  SSE_REGS, SSE_REGS, SSE_REGS, SSE_REGS, SSE_REGS, SSE_REGS,
  SSE_REGS, SSE_REGS,
  /* AVX-512 SSE registers */
  EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS,
  EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS,
  EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS,
  EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS, EVEX_SSE_REGS,
  /* Mask registers.  */
  MASK_REGS, MASK_EVEX_REGS, MASK_EVEX_REGS, MASK_EVEX_REGS,
  MASK_EVEX_REGS, MASK_EVEX_REGS, MASK_EVEX_REGS, MASK_EVEX_REGS,
  /* MPX bound registers */
  BND_REGS, BND_REGS, BND_REGS, BND_REGS,
};

/* The "default" register map used in 32bit mode.  */

int const dbx_register_map[FIRST_PSEUDO_REGISTER] =
{
  0, 2, 1, 3, 6, 7, 4, 5,		/* general regs */
  12, 13, 14, 15, 16, 17, 18, 19,	/* fp regs */
  -1, -1, -1, -1, -1,			/* arg, flags, fpsr, fpcr, frame */
  21, 22, 23, 24, 25, 26, 27, 28,	/* SSE */
  29, 30, 31, 32, 33, 34, 35, 36,       /* MMX */
  -1, -1, -1, -1, -1, -1, -1, -1,	/* extended integer registers */
  -1, -1, -1, -1, -1, -1, -1, -1,	/* extended SSE registers */
  -1, -1, -1, -1, -1, -1, -1, -1,       /* AVX-512 registers 16-23*/
  -1, -1, -1, -1, -1, -1, -1, -1,       /* AVX-512 registers 24-31*/
  93, 94, 95, 96, 97, 98, 99, 100,      /* Mask registers */
  101, 102, 103, 104,			/* bound registers */
};

/* The "default" register map used in 64bit mode.  */

int const dbx64_register_map[FIRST_PSEUDO_REGISTER] =
{
  0, 1, 2, 3, 4, 5, 6, 7,		/* general regs */
  33, 34, 35, 36, 37, 38, 39, 40,	/* fp regs */
  -1, -1, -1, -1, -1,			/* arg, flags, fpsr, fpcr, frame */
  17, 18, 19, 20, 21, 22, 23, 24,	/* SSE */
  41, 42, 43, 44, 45, 46, 47, 48,       /* MMX */
  8,9,10,11,12,13,14,15,		/* extended integer registers */
  25, 26, 27, 28, 29, 30, 31, 32,	/* extended SSE registers */
  67, 68, 69, 70, 71, 72, 73, 74,       /* AVX-512 registers 16-23 */
  75, 76, 77, 78, 79, 80, 81, 82,       /* AVX-512 registers 24-31 */
  118, 119, 120, 121, 122, 123, 124, 125, /* Mask registers */
  126, 127, 128, 129,			/* bound registers */
};

/* Define the register numbers to be used in Dwarf debugging information.
   The SVR4 reference port C compiler uses the following register numbers
   in its Dwarf output code:
	0 for %eax (gcc regno = 0)
	1 for %ecx (gcc regno = 2)
	2 for %edx (gcc regno = 1)
	3 for %ebx (gcc regno = 3)
	4 for %esp (gcc regno = 7)
	5 for %ebp (gcc regno = 6)
	6 for %esi (gcc regno = 4)
	7 for %edi (gcc regno = 5)
   The following three DWARF register numbers are never generated by
   the SVR4 C compiler or by the GNU compilers, but SDB on x86/svr4
   believes these numbers have these meanings.
	8  for %eip    (no gcc equivalent)
	9  for %eflags (gcc regno = 17)
	10 for %trapno (no gcc equivalent)
   It is not at all clear how we should number the FP stack registers
   for the x86 architecture.  If the version of SDB on x86/svr4 were
   a bit less brain dead with respect to floating-point then we would
   have a precedent to follow with respect to DWARF register numbers
   for x86 FP registers, but the SDB on x86/svr4 is so completely
   broken with respect to FP registers that it is hardly worth thinking
   of it as something to strive for compatibility with.
   The version of x86/svr4 SDB I have at the moment does (partially)
   seem to believe that DWARF register number 11 is associated with
   the x86 register %st(0), but that's about all.  Higher DWARF
   register numbers don't seem to be associated with anything in
   particular, and even for DWARF regno 11, SDB only seems to under-
   stand that it should say that a variable lives in %st(0) (when
   asked via an `=' command) if we said it was in DWARF regno 11,
   but SDB still prints garbage when asked for the value of the
   variable in question (via a `/' command).
   (Also note that the labels SDB prints for various FP stack regs
   when doing an `x' command are all wrong.)
   Note that these problems generally don't affect the native SVR4
   C compiler because it doesn't allow the use of -O with -g and
   because when it is *not* optimizing, it allocates a memory
   location for each floating-point variable, and the memory
   location is what gets described in the DWARF AT_location
   attribute for the variable in question.
   Regardless of the severe mental illness of the x86/svr4 SDB, we
   do something sensible here and we use the following DWARF
   register numbers.  Note that these are all stack-top-relative
   numbers.
	11 for %st(0) (gcc regno = 8)
	12 for %st(1) (gcc regno = 9)
	13 for %st(2) (gcc regno = 10)
	14 for %st(3) (gcc regno = 11)
	15 for %st(4) (gcc regno = 12)
	16 for %st(5) (gcc regno = 13)
	17 for %st(6) (gcc regno = 14)
	18 for %st(7) (gcc regno = 15)
*/
int const svr4_dbx_register_map[FIRST_PSEUDO_REGISTER] =
{
  0, 2, 1, 3, 6, 7, 5, 4,		/* general regs */
  11, 12, 13, 14, 15, 16, 17, 18,	/* fp regs */
  -1, 9, -1, -1, -1,			/* arg, flags, fpsr, fpcr, frame */
  21, 22, 23, 24, 25, 26, 27, 28,	/* SSE registers */
  29, 30, 31, 32, 33, 34, 35, 36,	/* MMX registers */
  -1, -1, -1, -1, -1, -1, -1, -1,	/* extended integer registers */
  -1, -1, -1, -1, -1, -1, -1, -1,	/* extended SSE registers */
  -1, -1, -1, -1, -1, -1, -1, -1,       /* AVX-512 registers 16-23*/
  -1, -1, -1, -1, -1, -1, -1, -1,       /* AVX-512 registers 24-31*/
  93, 94, 95, 96, 97, 98, 99, 100,      /* Mask registers */
  101, 102, 103, 104,			/* bound registers */
};

/* Define parameter passing and return registers.  */

static int const x86_64_int_parameter_registers[6] =
{
  DI_REG, SI_REG, DX_REG, CX_REG, R8_REG, R9_REG
};

static int const x86_64_ms_abi_int_parameter_registers[4] =
{
  CX_REG, DX_REG, R8_REG, R9_REG
};

static int const x86_64_int_return_registers[4] =
{
  AX_REG, DX_REG, DI_REG, SI_REG
};

/* Additional registers that are clobbered by SYSV calls.  */

#define NUM_X86_64_MS_CLOBBERED_REGS 12
static int const x86_64_ms_sysv_extra_clobbered_registers
		 [NUM_X86_64_MS_CLOBBERED_REGS] =
{
  SI_REG, DI_REG,
  XMM6_REG, XMM7_REG,
  XMM8_REG, XMM9_REG, XMM10_REG, XMM11_REG,
  XMM12_REG, XMM13_REG, XMM14_REG, XMM15_REG
};

enum xlogue_stub {
  XLOGUE_STUB_SAVE,
  XLOGUE_STUB_RESTORE,
  XLOGUE_STUB_RESTORE_TAIL,
  XLOGUE_STUB_SAVE_HFP,
  XLOGUE_STUB_RESTORE_HFP,
  XLOGUE_STUB_RESTORE_HFP_TAIL,

  XLOGUE_STUB_COUNT
};

enum xlogue_stub_sets {
  XLOGUE_SET_ALIGNED,
  XLOGUE_SET_ALIGNED_PLUS_8,
  XLOGUE_SET_HFP_ALIGNED_OR_REALIGN,
  XLOGUE_SET_HFP_ALIGNED_PLUS_8,

  XLOGUE_SET_COUNT
};

/* Define the structure for the machine field in struct function.  */

struct GTY(()) stack_local_entry {
  unsigned short mode;
  unsigned short n;
  rtx rtl;
  struct stack_local_entry *next;
};

#if 0
/* Which cpu are we scheduling for.  */
enum attr_cpu ix86_schedule;

/* Which cpu are we optimizing for.  */
enum processor_type ix86_tune;

/* Which instruction set architecture to use.  */
enum processor_type ix86_arch;

/* True if processor has SSE prefetch instruction.  */
unsigned char x86_prefetch_sse;

/* -mstackrealign option */
static const char ix86_force_align_arg_pointer_string[]
  = "force_align_arg_pointer";

static rtx (*ix86_gen_leave) (void);
static rtx (*ix86_gen_add3) (rtx, rtx, rtx);
static rtx (*ix86_gen_sub3) (rtx, rtx, rtx);
static rtx (*ix86_gen_sub3_carry) (rtx, rtx, rtx, rtx, rtx);
static rtx (*ix86_gen_one_cmpl2) (rtx, rtx);
static rtx (*ix86_gen_monitor) (rtx, rtx, rtx);
static rtx (*ix86_gen_monitorx) (rtx, rtx, rtx);
static rtx (*ix86_gen_clzero) (rtx);
static rtx (*ix86_gen_andsp) (rtx, rtx, rtx);
static rtx (*ix86_gen_allocate_stack_worker) (rtx, rtx);
static rtx (*ix86_gen_adjust_stack_and_probe) (rtx, rtx, rtx);
static rtx (*ix86_gen_probe_stack_range) (rtx, rtx, rtx);
static rtx (*ix86_gen_tls_global_dynamic_64) (rtx, rtx, rtx);
static rtx (*ix86_gen_tls_local_dynamic_base_64) (rtx, rtx);

/* Preferred alignment for stack boundary in bits.  */
unsigned int ix86_preferred_stack_boundary;

/* Alignment for incoming stack boundary in bits specified at
   command line.  */
static unsigned int ix86_user_incoming_stack_boundary;

/* Default alignment for incoming stack boundary in bits.  */
static unsigned int ix86_default_incoming_stack_boundary;

/* Alignment for incoming stack boundary in bits.  */
unsigned int ix86_incoming_stack_boundary;

/* Calling abi specific va_list type nodes.  */
static GTY(()) tree sysv_va_list_type_node;
static GTY(()) tree ms_va_list_type_node;

/* Prefix built by ASM_GENERATE_INTERNAL_LABEL.  */
char internal_label_prefix[16];
int internal_label_prefix_len;

/* Fence to use after loop using movnt.  */
tree x86_mfence;

/* Register class used for passing given 64bit part of the argument.
   These represent classes as documented by the PS ABI, with the exception
   of SSESF, SSEDF classes, that are basically SSE class, just gcc will
   use SF or DFmode move instead of DImode to avoid reformatting penalties.

   Similarly we play games with INTEGERSI_CLASS to use cheaper SImode moves
   whenever possible (upper half does contain padding).  */
enum x86_64_reg_class
  {
    X86_64_NO_CLASS,
    X86_64_INTEGER_CLASS,
    X86_64_INTEGERSI_CLASS,
    X86_64_SSE_CLASS,
    X86_64_SSESF_CLASS,
    X86_64_SSEDF_CLASS,
    X86_64_SSEUP_CLASS,
    X86_64_X87_CLASS,
    X86_64_X87UP_CLASS,
    X86_64_COMPLEX_X87_CLASS,
    X86_64_MEMORY_CLASS
  };

#define MAX_CLASSES 8

/* Table of constants used by fldpi, fldln2, etc....  */
static REAL_VALUE_TYPE ext_80387_constants_table [5];
static bool ext_80387_constants_init;


static struct machine_function * ix86_init_machine_status (void);
static rtx ix86_function_value (const_tree, const_tree, bool);
static bool ix86_function_value_regno_p (const unsigned int);
static unsigned int ix86_function_arg_boundary (machine_mode,
						const_tree);
static rtx ix86_static_chain (const_tree, bool);
static int ix86_function_regparm (const_tree, const_tree);
static void ix86_compute_frame_layout (void);
static bool ix86_expand_vector_init_one_nonzero (bool, machine_mode,
						 rtx, rtx, int);
static void ix86_add_new_builtins (HOST_WIDE_INT, HOST_WIDE_INT);
static tree ix86_canonical_va_list_type (tree);
static void predict_jump (int);
static unsigned int split_stack_prologue_scratch_regno (void);
static bool i386_asm_output_addr_const_extra (FILE *, rtx);

enum ix86_function_specific_strings
{
  IX86_FUNCTION_SPECIFIC_ARCH,
  IX86_FUNCTION_SPECIFIC_TUNE,
  IX86_FUNCTION_SPECIFIC_MAX
};

static char *ix86_target_string (HOST_WIDE_INT, HOST_WIDE_INT, int, int,
				 const char *, const char *, enum fpmath_unit,
				 bool);
static void ix86_function_specific_save (struct cl_target_option *,
					 struct gcc_options *opts);
static void ix86_function_specific_restore (struct gcc_options *opts,
					    struct cl_target_option *);
static void ix86_function_specific_post_stream_in (struct cl_target_option *);
static void ix86_function_specific_print (FILE *, int,
					  struct cl_target_option *);
static bool ix86_valid_target_attribute_p (tree, tree, tree, int);
static bool ix86_valid_target_attribute_inner_p (tree, char *[],
						 struct gcc_options *,
						 struct gcc_options *,
						 struct gcc_options *);
static bool ix86_can_inline_p (tree, tree);
static void ix86_set_current_function (tree);
static unsigned int ix86_minimum_incoming_stack_boundary (bool);

static enum calling_abi ix86_function_abi (const_tree);


#ifndef SUBTARGET32_DEFAULT_CPU
#define SUBTARGET32_DEFAULT_CPU "i386"
#endif

/* Whether -mtune= or -march= were specified */
static int ix86_tune_defaulted;
static int ix86_arch_specified;

/* Vectorization library interface and handlers.  */
static tree (*ix86_veclib_handler) (combined_fn, tree, tree);

static tree ix86_veclibabi_svml (combined_fn, tree, tree);
static tree ix86_veclibabi_acml (combined_fn, tree, tree);

/* Processor target table, indexed by processor number */
struct ptt
{
  const char *const name;			/* processor name  */
  const struct processor_costs *cost;		/* Processor costs */
  const int align_loop;				/* Default alignments.  */
  const int align_loop_max_skip;
  const int align_jump;
  const int align_jump_max_skip;
  const int align_func;
};

/* This table must be in sync with enum processor_type in i386.h.  */ 
static const struct ptt processor_target_table[PROCESSOR_max] =
{
  {"generic", &generic_cost, 16, 10, 16, 10, 16},
  {"i386", &i386_cost, 4, 3, 4, 3, 4},
  {"i486", &i486_cost, 16, 15, 16, 15, 16},
  {"pentium", &pentium_cost, 16, 7, 16, 7, 16},
  {"lakemont", &lakemont_cost, 16, 7, 16, 7, 16},
  {"pentiumpro", &pentiumpro_cost, 16, 15, 16, 10, 16},
  {"pentium4", &pentium4_cost, 0, 0, 0, 0, 0},
  {"nocona", &nocona_cost, 0, 0, 0, 0, 0},
  {"core2", &core_cost, 16, 10, 16, 10, 16},
  {"nehalem", &core_cost, 16, 10, 16, 10, 16},
  {"sandybridge", &core_cost, 16, 10, 16, 10, 16},
  {"haswell", &core_cost, 16, 10, 16, 10, 16},
  {"bonnell", &atom_cost, 16, 15, 16, 7, 16},
  {"silvermont", &slm_cost, 16, 15, 16, 7, 16},
  {"knl", &slm_cost, 16, 15, 16, 7, 16},
  {"skylake-avx512", &core_cost, 16, 10, 16, 10, 16},
  {"intel", &intel_cost, 16, 15, 16, 7, 16},
  {"geode", &geode_cost, 0, 0, 0, 0, 0},
  {"k6", &k6_cost, 32, 7, 32, 7, 32},
  {"athlon", &athlon_cost, 16, 7, 16, 7, 16},
  {"k8", &k8_cost, 16, 7, 16, 7, 16},
  {"amdfam10", &amdfam10_cost, 32, 24, 32, 7, 32},
  {"bdver1", &bdver1_cost, 16, 10, 16, 7, 11},
  {"bdver2", &bdver2_cost, 16, 10, 16, 7, 11},
  {"bdver3", &bdver3_cost, 16, 10, 16, 7, 11},
  {"bdver4", &bdver4_cost, 16, 10, 16, 7, 11},
  {"btver1", &btver1_cost, 16, 10, 16, 7, 11},
  {"btver2", &btver2_cost, 16, 10, 16, 7, 11},
  {"znver1", &znver1_cost, 16, 15, 16, 15, 16}
};

static unsigned int
rest_of_handle_insert_vzeroupper (void)
{
  int i;

  /* vzeroupper instructions are inserted immediately after reload to
     account for possible spills from 256bit registers.  The pass
     reuses mode switching infrastructure by re-running mode insertion
     pass, so disable entities that have already been processed.  */
  for (i = 0; i < MAX_386_ENTITIES; i++)
    ix86_optimize_mode_switching[i] = 0;

  ix86_optimize_mode_switching[AVX_U128] = 1;

  /* Call optimize_mode_switching.  */
  g->get_passes ()->execute_pass_mode_switching ();
  return 0;
}

/* Return 1 if INSN uses or defines a hard register.
   Hard register uses in a memory address are ignored.
   Clobbers and flags definitions are ignored.  */

static bool
has_non_address_hard_reg (rtx_insn *insn)
{
  df_ref ref;
  FOR_EACH_INSN_DEF (ref, insn)
    if (HARD_REGISTER_P (DF_REF_REAL_REG (ref))
	&& !DF_REF_FLAGS_IS_SET (ref, DF_REF_MUST_CLOBBER)
	&& DF_REF_REGNO (ref) != FLAGS_REG)
      return true;

  FOR_EACH_INSN_USE (ref, insn)
    if (!DF_REF_REG_MEM_P (ref) && HARD_REGISTER_P (DF_REF_REAL_REG (ref)))
      return true;

  return false;
}

/* Check if comparison INSN may be transformed
   into vector comparison.  Currently we transform
   zero checks only which look like:

   (set (reg:CCZ 17 flags)
        (compare:CCZ (ior:SI (subreg:SI (reg:DI x) 4)
                             (subreg:SI (reg:DI x) 0))
		     (const_int 0 [0])))  */

static bool
convertible_comparison_p (rtx_insn *insn)
{
  if (!TARGET_SSE4_1)
    return false;

  rtx def_set = single_set (insn);

  gcc_assert (def_set);

  rtx src = SET_SRC (def_set);
  rtx dst = SET_DEST (def_set);

  gcc_assert (GET_CODE (src) == COMPARE);

  if (GET_CODE (dst) != REG
      || REGNO (dst) != FLAGS_REG
      || GET_MODE (dst) != CCZmode)
    return false;

  rtx op1 = XEXP (src, 0);
  rtx op2 = XEXP (src, 1);

  if (op2 != CONST0_RTX (GET_MODE (op2)))
    return false;

  if (GET_CODE (op1) != IOR)
    return false;

  op2 = XEXP (op1, 1);
  op1 = XEXP (op1, 0);

  if (!SUBREG_P (op1)
      || !SUBREG_P (op2)
      || GET_MODE (op1) != SImode
      || GET_MODE (op2) != SImode
      || ((SUBREG_BYTE (op1) != 0
	   || SUBREG_BYTE (op2) != GET_MODE_SIZE (SImode))
	  && (SUBREG_BYTE (op2) != 0
	      || SUBREG_BYTE (op1) != GET_MODE_SIZE (SImode))))
    return false;

  op1 = SUBREG_REG (op1);
  op2 = SUBREG_REG (op2);

  if (op1 != op2
      || !REG_P (op1)
      || GET_MODE (op1) != DImode)
    return false;

  return true;
}

/* The DImode version of scalar_to_vector_candidate_p.  */

static bool
dimode_scalar_to_vector_candidate_p (rtx_insn *insn)
{
  rtx def_set = single_set (insn);

  if (!def_set)
    return false;

  if (has_non_address_hard_reg (insn))
    return false;

  rtx src = SET_SRC (def_set);
  rtx dst = SET_DEST (def_set);

  if (GET_CODE (src) == COMPARE)
    return convertible_comparison_p (insn);

  /* We are interested in DImode promotion only.  */
  if ((GET_MODE (src) != DImode
       && !CONST_INT_P (src))
      || GET_MODE (dst) != DImode)
    return false;

  if (!REG_P (dst) && !MEM_P (dst))
    return false;

  switch (GET_CODE (src))
    {
    case ASHIFTRT:
      if (!TARGET_AVX512VL)
	return false;
      /* FALLTHRU */

    case ASHIFT:
    case LSHIFTRT:
      if (!REG_P (XEXP (src, 1))
	  && (!SUBREG_P (XEXP (src, 1))
	      || SUBREG_BYTE (XEXP (src, 1)) != 0
	      || !REG_P (SUBREG_REG (XEXP (src, 1))))
	  && (!CONST_INT_P (XEXP (src, 1))
	      || !IN_RANGE (INTVAL (XEXP (src, 1)), 0, 63)))
	return false;

      if (GET_MODE (XEXP (src, 1)) != QImode
	  && !CONST_INT_P (XEXP (src, 1)))
	return false;
      break;

    case PLUS:
    case MINUS:
    case IOR:
    case XOR:
    case AND:
      if (!REG_P (XEXP (src, 1))
	  && !MEM_P (XEXP (src, 1))
	  && !CONST_INT_P (XEXP (src, 1)))
	return false;

      if (GET_MODE (XEXP (src, 1)) != DImode
	  && !CONST_INT_P (XEXP (src, 1)))
	return false;
      break;

    case NEG:
    case NOT:
      break;

    case REG:
      return true;

    case MEM:
    case CONST_INT:
      return REG_P (dst);

    default:
      return false;
    }

  if (!REG_P (XEXP (src, 0))
      && !MEM_P (XEXP (src, 0))
      && !CONST_INT_P (XEXP (src, 0))
      /* Check for andnot case.  */
      && (GET_CODE (src) != AND
	  || GET_CODE (XEXP (src, 0)) != NOT
	  || !REG_P (XEXP (XEXP (src, 0), 0))))
      return false;

  if (GET_MODE (XEXP (src, 0)) != DImode
      && !CONST_INT_P (XEXP (src, 0)))
    return false;

  return true;
}

/* The TImode version of scalar_to_vector_candidate_p.  */

static bool
timode_scalar_to_vector_candidate_p (rtx_insn *insn)
{
  rtx def_set = single_set (insn);

  if (!def_set)
    return false;

  if (has_non_address_hard_reg (insn))
    return false;

  rtx src = SET_SRC (def_set);
  rtx dst = SET_DEST (def_set);

  /* Only TImode load and store are allowed.  */
  if (GET_MODE (dst) != TImode)
    return false;

  if (MEM_P (dst))
    {
      /* Check for store.  Memory must be aligned or unaligned store
	 is optimal.  Only support store from register, standard SSE
	 constant or CONST_WIDE_INT generated from piecewise store.

	 ??? Verify performance impact before enabling CONST_INT for
	 __int128 store.  */
      if (misaligned_operand (dst, TImode)
	  && !TARGET_SSE_UNALIGNED_STORE_OPTIMAL)
	return false;

      switch (GET_CODE (src))
	{
	default:
	  return false;

	case REG:
	case CONST_WIDE_INT:
	  return true;

	case CONST_INT:
	  return standard_sse_constant_p (src, TImode);
	}
    }
  else if (MEM_P (src))
    {
      /* Check for load.  Memory must be aligned or unaligned load is
	 optimal.  */
      return (REG_P (dst)
	      && (!misaligned_operand (src, TImode)
		  || TARGET_SSE_UNALIGNED_LOAD_OPTIMAL));
    }

  return false;
}

/* Return 1 if INSN may be converted into vector
   instruction.  */

static bool
scalar_to_vector_candidate_p (rtx_insn *insn)
{
  if (TARGET_64BIT)
    return timode_scalar_to_vector_candidate_p (insn);
  else
    return dimode_scalar_to_vector_candidate_p (insn);
}

/* The DImode version of remove_non_convertible_regs.  */

static void
dimode_remove_non_convertible_regs (bitmap candidates)
{
  bitmap_iterator bi;
  unsigned id;
  bitmap regs = BITMAP_ALLOC (NULL);

  EXECUTE_IF_SET_IN_BITMAP (candidates, 0, id, bi)
    {
      rtx def_set = single_set (DF_INSN_UID_GET (id)->insn);
      rtx reg = SET_DEST (def_set);

      if (!REG_P (reg)
	  || bitmap_bit_p (regs, REGNO (reg))
	  || HARD_REGISTER_P (reg))
	continue;

      for (df_ref def = DF_REG_DEF_CHAIN (REGNO (reg));
	   def;
	   def = DF_REF_NEXT_REG (def))
	{
	  if (!bitmap_bit_p (candidates, DF_REF_INSN_UID (def)))
	    {
	      if (dump_file)
		fprintf (dump_file,
			 "r%d has non convertible definition in insn %d\n",
			 REGNO (reg), DF_REF_INSN_UID (def));

	      bitmap_set_bit (regs, REGNO (reg));
	      break;
	    }
	}
    }

  EXECUTE_IF_SET_IN_BITMAP (regs, 0, id, bi)
    {
      for (df_ref def = DF_REG_DEF_CHAIN (id);
	   def;
	   def = DF_REF_NEXT_REG (def))
	if (bitmap_bit_p (candidates, DF_REF_INSN_UID (def)))
	  {
	    if (dump_file)
	      fprintf (dump_file, "Removing insn %d from candidates list\n",
		       DF_REF_INSN_UID (def));

	    bitmap_clear_bit (candidates, DF_REF_INSN_UID (def));
	  }
    }

  BITMAP_FREE (regs);
}

/* For a register REGNO, scan instructions for its defs and uses.
   Put REGNO in REGS if a def or use isn't in CANDIDATES.  */

static void
timode_check_non_convertible_regs (bitmap candidates, bitmap regs,
				   unsigned int regno)
{
  for (df_ref def = DF_REG_DEF_CHAIN (regno);
       def;
       def = DF_REF_NEXT_REG (def))
    {
      if (!bitmap_bit_p (candidates, DF_REF_INSN_UID (def)))
	{
	  if (dump_file)
	    fprintf (dump_file,
		     "r%d has non convertible def in insn %d\n",
		     regno, DF_REF_INSN_UID (def));

	  bitmap_set_bit (regs, regno);
	  break;
	}
    }

  for (df_ref ref = DF_REG_USE_CHAIN (regno);
       ref;
       ref = DF_REF_NEXT_REG (ref))
    {
      /* Debug instructions are skipped.  */
      if (NONDEBUG_INSN_P (DF_REF_INSN (ref))
	  && !bitmap_bit_p (candidates, DF_REF_INSN_UID (ref)))
	{
	  if (dump_file)
	    fprintf (dump_file,
		     "r%d has non convertible use in insn %d\n",
		     regno, DF_REF_INSN_UID (ref));

	  bitmap_set_bit (regs, regno);
	  break;
	}
    }
}

/* The TImode version of remove_non_convertible_regs.  */

static void
timode_remove_non_convertible_regs (bitmap candidates)
{
  bitmap_iterator bi;
  unsigned id;
  bitmap regs = BITMAP_ALLOC (NULL);

  EXECUTE_IF_SET_IN_BITMAP (candidates, 0, id, bi)
    {
      rtx def_set = single_set (DF_INSN_UID_GET (id)->insn);
      rtx dest = SET_DEST (def_set);
      rtx src = SET_SRC (def_set);

      if ((!REG_P (dest)
	   || bitmap_bit_p (regs, REGNO (dest))
	   || HARD_REGISTER_P (dest))
	  && (!REG_P (src)
	      || bitmap_bit_p (regs, REGNO (src))
	      || HARD_REGISTER_P (src)))
	continue;

      if (REG_P (dest))
	timode_check_non_convertible_regs (candidates, regs,
					   REGNO (dest));

      if (REG_P (src))
	timode_check_non_convertible_regs (candidates, regs,
					   REGNO (src));
    }

  EXECUTE_IF_SET_IN_BITMAP (regs, 0, id, bi)
    {
      for (df_ref def = DF_REG_DEF_CHAIN (id);
	   def;
	   def = DF_REF_NEXT_REG (def))
	if (bitmap_bit_p (candidates, DF_REF_INSN_UID (def)))
	  {
	    if (dump_file)
	      fprintf (dump_file, "Removing insn %d from candidates list\n",
		       DF_REF_INSN_UID (def));

	    bitmap_clear_bit (candidates, DF_REF_INSN_UID (def));
	  }

      for (df_ref ref = DF_REG_USE_CHAIN (id);
	   ref;
	   ref = DF_REF_NEXT_REG (ref))
	if (bitmap_bit_p (candidates, DF_REF_INSN_UID (ref)))
	  {
	    if (dump_file)
	      fprintf (dump_file, "Removing insn %d from candidates list\n",
		       DF_REF_INSN_UID (ref));

	    bitmap_clear_bit (candidates, DF_REF_INSN_UID (ref));
	  }
    }

  BITMAP_FREE (regs);
}

/* For a given bitmap of insn UIDs scans all instruction and
   remove insn from CANDIDATES in case it has both convertible
   and not convertible definitions.

   All insns in a bitmap are conversion candidates according to
   scalar_to_vector_candidate_p.  Currently it implies all insns
   are single_set.  */

static void
remove_non_convertible_regs (bitmap candidates)
{
  if (TARGET_64BIT)
    timode_remove_non_convertible_regs (candidates);
  else
    dimode_remove_non_convertible_regs (candidates);
}

class scalar_chain
{
 public:
  scalar_chain ();
  virtual ~scalar_chain ();

  static unsigned max_id;

  /* ID of a chain.  */
  unsigned int chain_id;
  /* A queue of instructions to be included into a chain.  */
  bitmap queue;
  /* Instructions included into a chain.  */
  bitmap insns;
  /* All registers defined by a chain.  */
  bitmap defs;
  /* Registers used in both vector and sclar modes.  */
  bitmap defs_conv;

  void build (bitmap candidates, unsigned insn_uid);
  virtual int compute_convert_gain () = 0;
  int convert ();

 protected:
  void add_to_queue (unsigned insn_uid);
  void emit_conversion_insns (rtx insns, rtx_insn *pos);

 private:
  void add_insn (bitmap candidates, unsigned insn_uid);
  void analyze_register_chain (bitmap candidates, df_ref ref);
  virtual void mark_dual_mode_def (df_ref def) = 0;
  virtual void convert_insn (rtx_insn *insn) = 0;
  virtual void convert_registers () = 0;
};

class dimode_scalar_chain : public scalar_chain
{
 public:
  int compute_convert_gain ();
 private:
  void mark_dual_mode_def (df_ref def);
  rtx replace_with_subreg (rtx x, rtx reg, rtx subreg);
  void replace_with_subreg_in_insn (rtx_insn *insn, rtx reg, rtx subreg);
  void convert_insn (rtx_insn *insn);
  void convert_op (rtx *op, rtx_insn *insn);
  void convert_reg (unsigned regno);
  void make_vector_copies (unsigned regno);
  void convert_registers ();
  int vector_const_cost (rtx exp);
};

class timode_scalar_chain : public scalar_chain
{
 public:
  /* Convert from TImode to V1TImode is always faster.  */
  int compute_convert_gain () { return 1; }

 private:
  void mark_dual_mode_def (df_ref def);
  void fix_debug_reg_uses (rtx reg);
  void convert_insn (rtx_insn *insn);
  /* We don't convert registers to difference size.  */
  void convert_registers () {}
};

unsigned scalar_chain::max_id = 0;

/* Initialize new chain.  */

scalar_chain::scalar_chain ()
{
  chain_id = ++max_id;

   if (dump_file)
    fprintf (dump_file, "Created a new instruction chain #%d\n", chain_id);

  bitmap_obstack_initialize (NULL);
  insns = BITMAP_ALLOC (NULL);
  defs = BITMAP_ALLOC (NULL);
  defs_conv = BITMAP_ALLOC (NULL);
  queue = NULL;
}

/* Free chain's data.  */

scalar_chain::~scalar_chain ()
{
  BITMAP_FREE (insns);
  BITMAP_FREE (defs);
  BITMAP_FREE (defs_conv);
  bitmap_obstack_release (NULL);
}

/* Add instruction into chains' queue.  */

void
scalar_chain::add_to_queue (unsigned insn_uid)
{
  if (bitmap_bit_p (insns, insn_uid)
      || bitmap_bit_p (queue, insn_uid))
    return;

  if (dump_file)
    fprintf (dump_file, "  Adding insn %d into chain's #%d queue\n",
	     insn_uid, chain_id);
  bitmap_set_bit (queue, insn_uid);
}

/* For DImode conversion, mark register defined by DEF as requiring
   conversion.  */

void
dimode_scalar_chain::mark_dual_mode_def (df_ref def)
{
  gcc_assert (DF_REF_REG_DEF_P (def));

  if (bitmap_bit_p (defs_conv, DF_REF_REGNO (def)))
    return;

  if (dump_file)
    fprintf (dump_file,
	     "  Mark r%d def in insn %d as requiring both modes in chain #%d\n",
	     DF_REF_REGNO (def), DF_REF_INSN_UID (def), chain_id);

  bitmap_set_bit (defs_conv, DF_REF_REGNO (def));
}

/* For TImode conversion, it is unused.  */

void
timode_scalar_chain::mark_dual_mode_def (df_ref)
{
  gcc_unreachable ();
}

/* Check REF's chain to add new insns into a queue
   and find registers requiring conversion.  */

void
scalar_chain::analyze_register_chain (bitmap candidates, df_ref ref)
{
  df_link *chain;

  gcc_assert (bitmap_bit_p (insns, DF_REF_INSN_UID (ref))
	      || bitmap_bit_p (candidates, DF_REF_INSN_UID (ref)));
  add_to_queue (DF_REF_INSN_UID (ref));

  for (chain = DF_REF_CHAIN (ref); chain; chain = chain->next)
    {
      unsigned uid = DF_REF_INSN_UID (chain->ref);

      if (!NONDEBUG_INSN_P (DF_REF_INSN (chain->ref)))
	continue;

      if (!DF_REF_REG_MEM_P (chain->ref))
	{
	  if (bitmap_bit_p (insns, uid))
	    continue;

	  if (bitmap_bit_p (candidates, uid))
	    {
	      add_to_queue (uid);
	      continue;
	    }
	}

      if (DF_REF_REG_DEF_P (chain->ref))
	{
	  if (dump_file)
	    fprintf (dump_file, "  r%d def in insn %d isn't convertible\n",
		     DF_REF_REGNO (chain->ref), uid);
	  mark_dual_mode_def (chain->ref);
	}
      else
	{
	  if (dump_file)
	    fprintf (dump_file, "  r%d use in insn %d isn't convertible\n",
		     DF_REF_REGNO (chain->ref), uid);
	  mark_dual_mode_def (ref);
	}
    }
}

/* Add instruction into a chain.  */

void
scalar_chain::add_insn (bitmap candidates, unsigned int insn_uid)
{
  if (bitmap_bit_p (insns, insn_uid))
    return;

  if (dump_file)
    fprintf (dump_file, "  Adding insn %d to chain #%d\n", insn_uid, chain_id);

  bitmap_set_bit (insns, insn_uid);

  rtx_insn *insn = DF_INSN_UID_GET (insn_uid)->insn;
  rtx def_set = single_set (insn);
  if (def_set && REG_P (SET_DEST (def_set))
      && !HARD_REGISTER_P (SET_DEST (def_set)))
    bitmap_set_bit (defs, REGNO (SET_DEST (def_set)));

  df_ref ref;
  df_ref def;
  for (ref = DF_INSN_UID_DEFS (insn_uid); ref; ref = DF_REF_NEXT_LOC (ref))
    if (!HARD_REGISTER_P (DF_REF_REG (ref)))
      for (def = DF_REG_DEF_CHAIN (DF_REF_REGNO (ref));
	   def;
	   def = DF_REF_NEXT_REG (def))
	analyze_register_chain (candidates, def);
  for (ref = DF_INSN_UID_USES (insn_uid); ref; ref = DF_REF_NEXT_LOC (ref))
    if (!DF_REF_REG_MEM_P (ref))
      analyze_register_chain (candidates, ref);
}

/* Build new chain starting from insn INSN_UID recursively
   adding all dependent uses and definitions.  */

void
scalar_chain::build (bitmap candidates, unsigned insn_uid)
{
  queue = BITMAP_ALLOC (NULL);
  bitmap_set_bit (queue, insn_uid);

  if (dump_file)
    fprintf (dump_file, "Building chain #%d...\n", chain_id);

  while (!bitmap_empty_p (queue))
    {
      insn_uid = bitmap_first_set_bit (queue);
      bitmap_clear_bit (queue, insn_uid);
      bitmap_clear_bit (candidates, insn_uid);
      add_insn (candidates, insn_uid);
    }

  if (dump_file)
    {
      fprintf (dump_file, "Collected chain #%d...\n", chain_id);
      fprintf (dump_file, "  insns: ");
      dump_bitmap (dump_file, insns);
      if (!bitmap_empty_p (defs_conv))
	{
	  bitmap_iterator bi;
	  unsigned id;
	  const char *comma = "";
	  fprintf (dump_file, "  defs to convert: ");
	  EXECUTE_IF_SET_IN_BITMAP (defs_conv, 0, id, bi)
	    {
	      fprintf (dump_file, "%sr%d", comma, id);
	      comma = ", ";
	    }
	  fprintf (dump_file, "\n");
	}
    }

  BITMAP_FREE (queue);
}

/* Return a cost of building a vector costant
   instead of using a scalar one.  */

int
dimode_scalar_chain::vector_const_cost (rtx exp)
{
  gcc_assert (CONST_INT_P (exp));

  if (standard_sse_constant_p (exp, V2DImode))
    return COSTS_N_INSNS (1);
  return ix86_cost->sse_load[1];
}

/* Compute a gain for chain conversion.  */

int
dimode_scalar_chain::compute_convert_gain ()
{
  bitmap_iterator bi;
  unsigned insn_uid;
  int gain = 0;
  int cost = 0;

  if (dump_file)
    fprintf (dump_file, "Computing gain for chain #%d...\n", chain_id);

  EXECUTE_IF_SET_IN_BITMAP (insns, 0, insn_uid, bi)
    {
      rtx_insn *insn = DF_INSN_UID_GET (insn_uid)->insn;
      rtx def_set = single_set (insn);
      rtx src = SET_SRC (def_set);
      rtx dst = SET_DEST (def_set);

      if (REG_P (src) && REG_P (dst))
	gain += COSTS_N_INSNS (2) - ix86_cost->sse_move;
      else if (REG_P (src) && MEM_P (dst))
	gain += 2 * ix86_cost->int_store[2] - ix86_cost->sse_store[1];
      else if (MEM_P (src) && REG_P (dst))
	gain += 2 * ix86_cost->int_load[2] - ix86_cost->sse_load[1];
      else if (GET_CODE (src) == ASHIFT
	       || GET_CODE (src) == ASHIFTRT
	       || GET_CODE (src) == LSHIFTRT)
	{
    	  if (CONST_INT_P (XEXP (src, 0)))
	    gain -= vector_const_cost (XEXP (src, 0));
	  if (CONST_INT_P (XEXP (src, 1)))
	    {
	      gain += ix86_cost->shift_const;
	      if (INTVAL (XEXP (src, 1)) >= 32)
		gain -= COSTS_N_INSNS (1);
	    }
	  else
	    /* Additional gain for omitting two CMOVs.  */
	    gain += ix86_cost->shift_var + COSTS_N_INSNS (2);
	}
      else if (GET_CODE (src) == PLUS
	       || GET_CODE (src) == MINUS
	       || GET_CODE (src) == IOR
	       || GET_CODE (src) == XOR
	       || GET_CODE (src) == AND)
	{
	  gain += ix86_cost->add;
	  /* Additional gain for andnot for targets without BMI.  */
	  if (GET_CODE (XEXP (src, 0)) == NOT
	      && !TARGET_BMI)
	    gain += 2 * ix86_cost->add;

	  if (CONST_INT_P (XEXP (src, 0)))
	    gain -= vector_const_cost (XEXP (src, 0));
	  if (CONST_INT_P (XEXP (src, 1)))
	    gain -= vector_const_cost (XEXP (src, 1));
	}
      else if (GET_CODE (src) == NEG
	       || GET_CODE (src) == NOT)
	gain += ix86_cost->add - COSTS_N_INSNS (1);
      else if (GET_CODE (src) == COMPARE)
	{
	  /* Assume comparison cost is the same.  */
	}
      else if (CONST_INT_P (src))
	{
	  if (REG_P (dst))
	    gain += COSTS_N_INSNS (2);
	  else if (MEM_P (dst))
	    gain += 2 * ix86_cost->int_store[2] - ix86_cost->sse_store[1];
	  gain -= vector_const_cost (src);
	}
      else
	gcc_unreachable ();
    }

  if (dump_file)
    fprintf (dump_file, "  Instruction conversion gain: %d\n", gain);

  EXECUTE_IF_SET_IN_BITMAP (defs_conv, 0, insn_uid, bi)
    cost += DF_REG_DEF_COUNT (insn_uid) * ix86_cost->mmxsse_to_integer;

  if (dump_file)
    fprintf (dump_file, "  Registers conversion cost: %d\n", cost);

  gain -= cost;

  if (dump_file)
    fprintf (dump_file, "  Total gain: %d\n", gain);

  return gain;
}

/* Replace REG in X with a V2DI subreg of NEW_REG.  */

rtx
dimode_scalar_chain::replace_with_subreg (rtx x, rtx reg, rtx new_reg)
{
  if (x == reg)
    return gen_rtx_SUBREG (V2DImode, new_reg, 0);

  const char *fmt = GET_RTX_FORMAT (GET_CODE (x));
  int i, j;
  for (i = GET_RTX_LENGTH (GET_CODE (x)) - 1; i >= 0; i--)
    {
      if (fmt[i] == 'e')
	XEXP (x, i) = replace_with_subreg (XEXP (x, i), reg, new_reg);
      else if (fmt[i] == 'E')
	for (j = XVECLEN (x, i) - 1; j >= 0; j--)
	  XVECEXP (x, i, j) = replace_with_subreg (XVECEXP (x, i, j),
						   reg, new_reg);
    }

  return x;
}

/* Replace REG in INSN with a V2DI subreg of NEW_REG.  */

void
dimode_scalar_chain::replace_with_subreg_in_insn (rtx_insn *insn,
						  rtx reg, rtx new_reg)
{
  replace_with_subreg (single_set (insn), reg, new_reg);
}

/* Insert generated conversion instruction sequence INSNS
   after instruction AFTER.  New BB may be required in case
   instruction has EH region attached.  */

void
scalar_chain::emit_conversion_insns (rtx insns, rtx_insn *after)
{
  if (!control_flow_insn_p (after))
    {
      emit_insn_after (insns, after);
      return;
    }

  basic_block bb = BLOCK_FOR_INSN (after);
  edge e = find_fallthru_edge (bb->succs);
  gcc_assert (e);

  basic_block new_bb = split_edge (e);
  emit_insn_after (insns, BB_HEAD (new_bb));
}

/* Make vector copies for all register REGNO definitions
   and replace its uses in a chain.  */

void
dimode_scalar_chain::make_vector_copies (unsigned regno)
{
  rtx reg = regno_reg_rtx[regno];
  rtx vreg = gen_reg_rtx (DImode);
  bool count_reg = false;
  df_ref ref;

  for (ref = DF_REG_DEF_CHAIN (regno); ref; ref = DF_REF_NEXT_REG (ref))
    if (!bitmap_bit_p (insns, DF_REF_INSN_UID (ref)))
      {
	df_ref use;

	/* Detect the count register of a shift instruction.  */
	for (use = DF_REG_USE_CHAIN (regno); use; use = DF_REF_NEXT_REG (use))
	  if (bitmap_bit_p (insns, DF_REF_INSN_UID (use)))
	    {
	      rtx_insn *insn = DF_REF_INSN (use);
	      rtx def_set = single_set (insn);

	      gcc_assert (def_set);

	      rtx src = SET_SRC (def_set);

	      if ((GET_CODE (src) == ASHIFT
		   || GET_CODE (src) == ASHIFTRT
		   || GET_CODE (src) == LSHIFTRT)
		  && !CONST_INT_P (XEXP (src, 1))
		  && reg_or_subregno (XEXP (src, 1)) == regno)
		count_reg = true;
	    }

	start_sequence ();
	if (count_reg)
	  {
	    rtx qreg = gen_lowpart (QImode, reg);
	    rtx tmp = gen_reg_rtx (SImode);

	    if (TARGET_ZERO_EXTEND_WITH_AND
		&& optimize_function_for_speed_p (cfun))
	      {
		emit_move_insn (tmp, const0_rtx);
		emit_insn (gen_movstrictqi
			   (gen_lowpart (QImode, tmp), qreg));
	      }
	    else
	      emit_insn (gen_rtx_SET
			 (tmp, gen_rtx_ZERO_EXTEND (SImode, qreg)));

	    if (!TARGET_INTER_UNIT_MOVES_TO_VEC)
	      {
		rtx slot = assign_386_stack_local (SImode, SLOT_STV_TEMP);
		emit_move_insn (slot, tmp);
		tmp = copy_rtx (slot);
	      }

	    emit_insn (gen_zero_extendsidi2 (vreg, tmp));
	  }
	else if (!TARGET_INTER_UNIT_MOVES_TO_VEC)
	  {
	    rtx tmp = assign_386_stack_local (DImode, SLOT_STV_TEMP);
	    emit_move_insn (adjust_address (tmp, SImode, 0),
			    gen_rtx_SUBREG (SImode, reg, 0));
	    emit_move_insn (adjust_address (tmp, SImode, 4),
			    gen_rtx_SUBREG (SImode, reg, 4));
	    emit_move_insn (vreg, tmp);
	  }
	else if (TARGET_SSE4_1)
	  {
	    emit_insn (gen_sse2_loadld (gen_rtx_SUBREG (V4SImode, vreg, 0),
					CONST0_RTX (V4SImode),
					gen_rtx_SUBREG (SImode, reg, 0)));
	    emit_insn (gen_sse4_1_pinsrd (gen_rtx_SUBREG (V4SImode, vreg, 0),
					  gen_rtx_SUBREG (V4SImode, vreg, 0),
					  gen_rtx_SUBREG (SImode, reg, 4),
					  GEN_INT (2)));
	  }
	else
	  {
	    rtx tmp = gen_reg_rtx (DImode);
	    emit_insn (gen_sse2_loadld (gen_rtx_SUBREG (V4SImode, vreg, 0),
					CONST0_RTX (V4SImode),
					gen_rtx_SUBREG (SImode, reg, 0)));
	    emit_insn (gen_sse2_loadld (gen_rtx_SUBREG (V4SImode, tmp, 0),
					CONST0_RTX (V4SImode),
					gen_rtx_SUBREG (SImode, reg, 4)));
	    emit_insn (gen_vec_interleave_lowv4si
		       (gen_rtx_SUBREG (V4SImode, vreg, 0),
			gen_rtx_SUBREG (V4SImode, vreg, 0),
			gen_rtx_SUBREG (V4SImode, tmp, 0)));
	  }
	rtx_insn *seq = get_insns ();
	end_sequence ();
	rtx_insn *insn = DF_REF_INSN (ref);
	emit_conversion_insns (seq, insn);

	if (dump_file)
	  fprintf (dump_file,
		   "  Copied r%d to a vector register r%d for insn %d\n",
		   regno, REGNO (vreg), INSN_UID (insn));
      }

  for (ref = DF_REG_USE_CHAIN (regno); ref; ref = DF_REF_NEXT_REG (ref))
    if (bitmap_bit_p (insns, DF_REF_INSN_UID (ref)))
      {
	rtx_insn *insn = DF_REF_INSN (ref);
	if (count_reg)
	  {
	    rtx def_set = single_set (insn);
	    gcc_assert (def_set);

	    rtx src = SET_SRC (def_set);

	    if ((GET_CODE (src) == ASHIFT
		 || GET_CODE (src) == ASHIFTRT
		 || GET_CODE (src) == LSHIFTRT)
		&& !CONST_INT_P (XEXP (src, 1))
		&& reg_or_subregno (XEXP (src, 1)) == regno)
	      XEXP (src, 1) = vreg;
	  }
	else
	  replace_with_subreg_in_insn (insn, reg, vreg);

	if (dump_file)
	  fprintf (dump_file, "  Replaced r%d with r%d in insn %d\n",
		   regno, REGNO (vreg), INSN_UID (insn));
      }
}

/* Convert all definitions of register REGNO
   and fix its uses.  Scalar copies may be created
   in case register is used in not convertible insn.  */

void
dimode_scalar_chain::convert_reg (unsigned regno)
{
  bool scalar_copy = bitmap_bit_p (defs_conv, regno);
  rtx reg = regno_reg_rtx[regno];
  rtx scopy = NULL_RTX;
  df_ref ref;
  bitmap conv;

  conv = BITMAP_ALLOC (NULL);
  bitmap_copy (conv, insns);

  if (scalar_copy)
    scopy = gen_reg_rtx (DImode);

  for (ref = DF_REG_DEF_CHAIN (regno); ref; ref = DF_REF_NEXT_REG (ref))
    {
      rtx_insn *insn = DF_REF_INSN (ref);
      rtx def_set = single_set (insn);
      rtx src = SET_SRC (def_set);
      rtx reg = DF_REF_REG (ref);

      if (!MEM_P (src))
	{
	  replace_with_subreg_in_insn (insn, reg, reg);
	  bitmap_clear_bit (conv, INSN_UID (insn));
	}

      if (scalar_copy)
	{
	  start_sequence ();
	  if (!TARGET_INTER_UNIT_MOVES_FROM_VEC)
	    {
	      rtx tmp = assign_386_stack_local (DImode, SLOT_STV_TEMP);
	      emit_move_insn (tmp, reg);
	      emit_move_insn (gen_rtx_SUBREG (SImode, scopy, 0),
			      adjust_address (tmp, SImode, 0));
	      emit_move_insn (gen_rtx_SUBREG (SImode, scopy, 4),
			      adjust_address (tmp, SImode, 4));
	    }
	  else if (TARGET_SSE4_1)
	    {
	      rtx tmp = gen_rtx_PARALLEL (VOIDmode, gen_rtvec (1, const0_rtx));
	      emit_insn
		(gen_rtx_SET
		 (gen_rtx_SUBREG (SImode, scopy, 0),
		  gen_rtx_VEC_SELECT (SImode,
				      gen_rtx_SUBREG (V4SImode, reg, 0), tmp)));

	      tmp = gen_rtx_PARALLEL (VOIDmode, gen_rtvec (1, const1_rtx));
	      emit_insn
		(gen_rtx_SET
		 (gen_rtx_SUBREG (SImode, scopy, 4),
		  gen_rtx_VEC_SELECT (SImode,
				      gen_rtx_SUBREG (V4SImode, reg, 0), tmp)));
	    }
	  else
	    {
	      rtx vcopy = gen_reg_rtx (V2DImode);
	      emit_move_insn (vcopy, gen_rtx_SUBREG (V2DImode, reg, 0));
	      emit_move_insn (gen_rtx_SUBREG (SImode, scopy, 0),
			      gen_rtx_SUBREG (SImode, vcopy, 0));
	      emit_move_insn (vcopy,
			      gen_rtx_LSHIFTRT (V2DImode, vcopy, GEN_INT (32)));
	      emit_move_insn (gen_rtx_SUBREG (SImode, scopy, 4),
			      gen_rtx_SUBREG (SImode, vcopy, 0));
	    }
	  rtx_insn *seq = get_insns ();
	  end_sequence ();
	  emit_conversion_insns (seq, insn);

	  if (dump_file)
	    fprintf (dump_file,
		     "  Copied r%d to a scalar register r%d for insn %d\n",
		     regno, REGNO (scopy), INSN_UID (insn));
	}
    }

  for (ref = DF_REG_USE_CHAIN (regno); ref; ref = DF_REF_NEXT_REG (ref))
    if (bitmap_bit_p (insns, DF_REF_INSN_UID (ref)))
      {
	if (bitmap_bit_p (conv, DF_REF_INSN_UID (ref)))
	  {
	    rtx_insn *insn = DF_REF_INSN (ref);

	    rtx def_set = single_set (insn);
	    gcc_assert (def_set);

	    rtx src = SET_SRC (def_set);
	    rtx dst = SET_DEST (def_set);

	    if ((GET_CODE (src) == ASHIFT
		 || GET_CODE (src) == ASHIFTRT
		 || GET_CODE (src) == LSHIFTRT)
		&& !CONST_INT_P (XEXP (src, 1))
		&& reg_or_subregno (XEXP (src, 1)) == regno)
	      {
		rtx tmp2 = gen_reg_rtx (V2DImode);

		start_sequence ();

		if (TARGET_SSE4_1)
		  emit_insn (gen_sse4_1_zero_extendv2qiv2di2
			     (tmp2, gen_rtx_SUBREG (V16QImode, reg, 0)));
		else
		  {
		    rtx vec_cst
		      = gen_rtx_CONST_VECTOR (V2DImode,
					      gen_rtvec (2, GEN_INT (0xff),
							 const0_rtx));
		    vec_cst
		      = validize_mem (force_const_mem (V2DImode, vec_cst));

		    emit_insn (gen_rtx_SET
			       (tmp2,
				gen_rtx_AND (V2DImode,
					     gen_rtx_SUBREG (V2DImode, reg, 0),
					     vec_cst)));
		  }
		rtx_insn *seq = get_insns ();
		end_sequence ();

		emit_insn_before (seq, insn);

		XEXP (src, 1) = gen_rtx_SUBREG (DImode, tmp2, 0);
	      }
	    else if (!MEM_P (dst) || !REG_P (src))
	      replace_with_subreg_in_insn (insn, reg, reg);

	    bitmap_clear_bit (conv, INSN_UID (insn));
	  }
      }
    /* Skip debug insns and uninitialized uses.  */
    else if (DF_REF_CHAIN (ref)
	     && NONDEBUG_INSN_P (DF_REF_INSN (ref)))
      {
	gcc_assert (scopy);
	replace_rtx (DF_REF_INSN (ref), reg, scopy);
	df_insn_rescan (DF_REF_INSN (ref));
      }

  BITMAP_FREE (conv);
}

/* Convert operand OP in INSN.  We should handle
   memory operands and uninitialized registers.
   All other register uses are converted during
   registers conversion.  */

void
dimode_scalar_chain::convert_op (rtx *op, rtx_insn *insn)
{
  *op = copy_rtx_if_shared (*op);

  if (GET_CODE (*op) == NOT)
    {
      convert_op (&XEXP (*op, 0), insn);
      PUT_MODE (*op, V2DImode);
    }
  else if (MEM_P (*op))
    {
      rtx tmp = gen_reg_rtx (DImode);

      emit_insn_before (gen_move_insn (tmp, *op), insn);
      *op = gen_rtx_SUBREG (V2DImode, tmp, 0);

      if (dump_file)
	fprintf (dump_file, "  Preloading operand for insn %d into r%d\n",
		 INSN_UID (insn), REGNO (tmp));
    }
  else if (REG_P (*op))
    {
      /* We may have not converted register usage in case
	 this register has no definition.  Otherwise it
	 should be converted in convert_reg.  */
      df_ref ref;
      FOR_EACH_INSN_USE (ref, insn)
	if (DF_REF_REGNO (ref) == REGNO (*op))
	  {
	    gcc_assert (!DF_REF_CHAIN (ref));
	    break;
	  }
      *op = gen_rtx_SUBREG (V2DImode, *op, 0);
    }
  else if (CONST_INT_P (*op))
    {
      rtx vec_cst;
      rtx tmp = gen_rtx_SUBREG (V2DImode, gen_reg_rtx (DImode), 0);

      /* Prefer all ones vector in case of -1.  */
      if (constm1_operand (*op, GET_MODE (*op)))
	vec_cst = CONSTM1_RTX (V2DImode);
      else
	vec_cst = gen_rtx_CONST_VECTOR (V2DImode,
					gen_rtvec (2, *op, const0_rtx));

      if (!standard_sse_constant_p (vec_cst, V2DImode))
	{
	  start_sequence ();
	  vec_cst = validize_mem (force_const_mem (V2DImode, vec_cst));
	  rtx_insn *seq = get_insns ();
	  end_sequence ();
	  emit_insn_before (seq, insn);
	}

      emit_insn_before (gen_move_insn (copy_rtx (tmp), vec_cst), insn);
      *op = tmp;
    }
  else
    {
      gcc_assert (SUBREG_P (*op));
      gcc_assert (GET_MODE (*op) == V2DImode);
    }
}

/* Convert INSN to vector mode.  */

void
dimode_scalar_chain::convert_insn (rtx_insn *insn)
{
  rtx def_set = single_set (insn);
  rtx src = SET_SRC (def_set);
  rtx dst = SET_DEST (def_set);
  rtx subreg;

  if (MEM_P (dst) && !REG_P (src))
    {
      /* There are no scalar integer instructions and therefore
	 temporary register usage is required.  */
      rtx tmp = gen_reg_rtx (DImode);
      emit_conversion_insns (gen_move_insn (dst, tmp), insn);
      dst = gen_rtx_SUBREG (V2DImode, tmp, 0);
    }

  switch (GET_CODE (src))
    {
    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
      convert_op (&XEXP (src, 0), insn);
      PUT_MODE (src, V2DImode);
      break;

    case PLUS:
    case MINUS:
    case IOR:
    case XOR:
    case AND:
      convert_op (&XEXP (src, 0), insn);
      convert_op (&XEXP (src, 1), insn);
      PUT_MODE (src, V2DImode);
      break;

    case NEG:
      src = XEXP (src, 0);
      convert_op (&src, insn);
      subreg = gen_reg_rtx (V2DImode);
      emit_insn_before (gen_move_insn (subreg, CONST0_RTX (V2DImode)), insn);
      src = gen_rtx_MINUS (V2DImode, subreg, src);
      break;

    case NOT:
      src = XEXP (src, 0);
      convert_op (&src, insn);
      subreg = gen_reg_rtx (V2DImode);
      emit_insn_before (gen_move_insn (subreg, CONSTM1_RTX (V2DImode)), insn);
      src = gen_rtx_XOR (V2DImode, src, subreg);
      break;

    case MEM:
      if (!REG_P (dst))
	convert_op (&src, insn);
      break;

    case REG:
      if (!MEM_P (dst))
	convert_op (&src, insn);
      break;

    case SUBREG:
      gcc_assert (GET_MODE (src) == V2DImode);
      break;

    case COMPARE:
      src = SUBREG_REG (XEXP (XEXP (src, 0), 0));

      gcc_assert ((REG_P (src) && GET_MODE (src) == DImode)
		  || (SUBREG_P (src) && GET_MODE (src) == V2DImode));

      if (REG_P (src))
	subreg = gen_rtx_SUBREG (V2DImode, src, 0);
      else
	subreg = copy_rtx_if_shared (src);
      emit_insn_before (gen_vec_interleave_lowv2di (copy_rtx_if_shared (subreg),
						    copy_rtx_if_shared (subreg),
						    copy_rtx_if_shared (subreg)),
			insn);
      dst = gen_rtx_REG (CCmode, FLAGS_REG);
      src = gen_rtx_UNSPEC (CCmode, gen_rtvec (2, copy_rtx_if_shared (src),
					       copy_rtx_if_shared (src)),
			    UNSPEC_PTEST);
      break;

    case CONST_INT:
      convert_op (&src, insn);
      break;

    default:
      gcc_unreachable ();
    }

  SET_SRC (def_set) = src;
  SET_DEST (def_set) = dst;

  /* Drop possible dead definitions.  */
  PATTERN (insn) = def_set;

  INSN_CODE (insn) = -1;
  recog_memoized (insn);
  df_insn_rescan (insn);
}

/* Fix uses of converted REG in debug insns.  */

void
timode_scalar_chain::fix_debug_reg_uses (rtx reg)
{
  if (!flag_var_tracking)
    return;

  df_ref ref, next;
  for (ref = DF_REG_USE_CHAIN (REGNO (reg)); ref; ref = next)
    {
      rtx_insn *insn = DF_REF_INSN (ref);
      /* Make sure the next ref is for a different instruction,
         so that we're not affected by the rescan.  */
      next = DF_REF_NEXT_REG (ref);
      while (next && DF_REF_INSN (next) == insn)
	next = DF_REF_NEXT_REG (next);

      if (DEBUG_INSN_P (insn))
	{
	  /* It may be a debug insn with a TImode variable in
	     register.  */
	  bool changed = false;
	  for (; ref != next; ref = DF_REF_NEXT_REG (ref))
	    {
	      rtx *loc = DF_REF_LOC (ref);
	      if (REG_P (*loc) && GET_MODE (*loc) == V1TImode)
		{
		  *loc = gen_rtx_SUBREG (TImode, *loc, 0);
		  changed = true;
		}
	    }
	  if (changed)
	    df_insn_rescan (insn);
	}
    }
}

/* Convert INSN from TImode to V1T1mode.  */

void
timode_scalar_chain::convert_insn (rtx_insn *insn)
{
  rtx def_set = single_set (insn);
  rtx src = SET_SRC (def_set);
  rtx dst = SET_DEST (def_set);

  switch (GET_CODE (dst))
    {
    case REG:
      {
	rtx tmp = find_reg_equal_equiv_note (insn);
	if (tmp)
	  PUT_MODE (XEXP (tmp, 0), V1TImode);
	PUT_MODE (dst, V1TImode);
	fix_debug_reg_uses (dst);
      }
      break;
    case MEM:
      PUT_MODE (dst, V1TImode);
      break;

    default:
      gcc_unreachable ();
    }

  switch (GET_CODE (src))
    {
    case REG:
      PUT_MODE (src, V1TImode);
      /* Call fix_debug_reg_uses only if SRC is never defined.  */
      if (!DF_REG_DEF_CHAIN (REGNO (src)))
	fix_debug_reg_uses (src);
      break;

    case MEM:
      PUT_MODE (src, V1TImode);
      break;

    case CONST_WIDE_INT:
      if (NONDEBUG_INSN_P (insn))
	{
	  /* Since there are no instructions to store 128-bit constant,
	     temporary register usage is required.  */
	  rtx tmp = gen_reg_rtx (V1TImode);
	  start_sequence ();
	  src = gen_rtx_CONST_VECTOR (V1TImode, gen_rtvec (1, src));
	  src = validize_mem (force_const_mem (V1TImode, src));
	  rtx_insn *seq = get_insns ();
	  end_sequence ();
	  if (seq)
	    emit_insn_before (seq, insn);
	  emit_conversion_insns (gen_rtx_SET (dst, tmp), insn);
	  dst = tmp;
	}
      break;

    case CONST_INT:
      switch (standard_sse_constant_p (src, TImode))
	{
	case 1:
	  src = CONST0_RTX (GET_MODE (dst));
	  break;
	case 2:
	  src = CONSTM1_RTX (GET_MODE (dst));
	  break;
	default:
	  gcc_unreachable ();
	}
      if (NONDEBUG_INSN_P (insn))
	{
	  rtx tmp = gen_reg_rtx (V1TImode);
	  /* Since there are no instructions to store standard SSE
	     constant, temporary register usage is required.  */
	  emit_conversion_insns (gen_rtx_SET (dst, tmp), insn);
	  dst = tmp;
	}
      break;

    default:
      gcc_unreachable ();
    }

  SET_SRC (def_set) = src;
  SET_DEST (def_set) = dst;

  /* Drop possible dead definitions.  */
  PATTERN (insn) = def_set;

  INSN_CODE (insn) = -1;
  recog_memoized (insn);
  df_insn_rescan (insn);
}

void
dimode_scalar_chain::convert_registers ()
{
  bitmap_iterator bi;
  unsigned id;

  EXECUTE_IF_SET_IN_BITMAP (defs, 0, id, bi)
    convert_reg (id);

  EXECUTE_IF_AND_COMPL_IN_BITMAP (defs_conv, defs, 0, id, bi)
    make_vector_copies (id);
}

/* Convert whole chain creating required register
   conversions and copies.  */

int
scalar_chain::convert ()
{
  bitmap_iterator bi;
  unsigned id;
  int converted_insns = 0;

  if (!dbg_cnt (stv_conversion))
    return 0;

  if (dump_file)
    fprintf (dump_file, "Converting chain #%d...\n", chain_id);

  convert_registers ();

  EXECUTE_IF_SET_IN_BITMAP (insns, 0, id, bi)
    {
      convert_insn (DF_INSN_UID_GET (id)->insn);
      converted_insns++;
    }

  return converted_insns;
}

/* Main STV pass function.  Find and convert scalar
   instructions into vector mode when profitable.  */

static unsigned int
convert_scalars_to_vector ()
{
  basic_block bb;
  bitmap candidates;
  int converted_insns = 0;

  bitmap_obstack_initialize (NULL);
  candidates = BITMAP_ALLOC (NULL);

  calculate_dominance_info (CDI_DOMINATORS);
  df_set_flags (DF_DEFER_INSN_RESCAN);
  df_chain_add_problem (DF_DU_CHAIN | DF_UD_CHAIN);
  df_md_add_problem ();
  df_analyze ();

  /* Find all instructions we want to convert into vector mode.  */
  if (dump_file)
    fprintf (dump_file, "Searching for mode conversion candidates...\n");

  FOR_EACH_BB_FN (bb, cfun)
    {
      rtx_insn *insn;
      FOR_BB_INSNS (bb, insn)
	if (scalar_to_vector_candidate_p (insn))
	  {
	    if (dump_file)
	      fprintf (dump_file, "  insn %d is marked as a candidate\n",
		       INSN_UID (insn));

	    bitmap_set_bit (candidates, INSN_UID (insn));
	  }
    }

  remove_non_convertible_regs (candidates);

  if (bitmap_empty_p (candidates))
    if (dump_file)
      fprintf (dump_file, "There are no candidates for optimization.\n");

  while (!bitmap_empty_p (candidates))
    {
      unsigned uid = bitmap_first_set_bit (candidates);
      scalar_chain *chain;

      if (TARGET_64BIT)
	chain = new timode_scalar_chain;
      else
	chain = new dimode_scalar_chain;

      /* Find instructions chain we want to convert to vector mode.
	 Check all uses and definitions to estimate all required
	 conversions.  */
      chain->build (candidates, uid);

      if (chain->compute_convert_gain () > 0)
	converted_insns += chain->convert ();
      else
	if (dump_file)
	  fprintf (dump_file, "Chain #%d conversion is not profitable\n",
		   chain->chain_id);

      delete chain;
    }

  if (dump_file)
    fprintf (dump_file, "Total insns converted: %d\n", converted_insns);

  BITMAP_FREE (candidates);
  bitmap_obstack_release (NULL);
  df_process_deferred_rescans ();

  /* Conversion means we may have 128bit register spills/fills
     which require aligned stack.  */
  if (converted_insns)
    {
      if (crtl->stack_alignment_needed < 128)
	crtl->stack_alignment_needed = 128;
      if (crtl->stack_alignment_estimated < 128)
	crtl->stack_alignment_estimated = 128;
      /* Fix up DECL_RTL/DECL_INCOMING_RTL of arguments.  */
      if (TARGET_64BIT)
	for (tree parm = DECL_ARGUMENTS (current_function_decl);
	     parm; parm = DECL_CHAIN (parm))
	  {
	    if (TYPE_MODE (TREE_TYPE (parm)) != TImode)
	      continue;
	    if (DECL_RTL_SET_P (parm)
		&& GET_MODE (DECL_RTL (parm)) == V1TImode)
	      {
		rtx r = DECL_RTL (parm);
		if (REG_P (r))
		  SET_DECL_RTL (parm, gen_rtx_SUBREG (TImode, r, 0));
	      }
	    if (DECL_INCOMING_RTL (parm)
		&& GET_MODE (DECL_INCOMING_RTL (parm)) == V1TImode)
	      {
		rtx r = DECL_INCOMING_RTL (parm);
		if (REG_P (r))
		  DECL_INCOMING_RTL (parm) = gen_rtx_SUBREG (TImode, r, 0);
	      }
	  }
    }

  return 0;
}

namespace {

const pass_data pass_data_insert_vzeroupper =
{
  RTL_PASS, /* type */
  "vzeroupper", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_MACH_DEP, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  TODO_df_finish, /* todo_flags_finish */
};

class pass_insert_vzeroupper : public rtl_opt_pass
{
public:
  pass_insert_vzeroupper(gcc::context *ctxt)
    : rtl_opt_pass(pass_data_insert_vzeroupper, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      return TARGET_AVX && !TARGET_AVX512F
	     && TARGET_VZEROUPPER && flag_expensive_optimizations
	     && !optimize_size;
    }

  virtual unsigned int execute (function *)
    {
      return rest_of_handle_insert_vzeroupper ();
    }

}; // class pass_insert_vzeroupper

const pass_data pass_data_stv =
{
  RTL_PASS, /* type */
  "stv", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_MACH_DEP, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  TODO_df_finish, /* todo_flags_finish */
};

class pass_stv : public rtl_opt_pass
{
public:
  pass_stv (gcc::context *ctxt)
    : rtl_opt_pass (pass_data_stv, ctxt),
      timode_p (false)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      return (timode_p == !!TARGET_64BIT
	      && TARGET_STV && TARGET_SSE2 && optimize > 1);
    }

  virtual unsigned int execute (function *)
    {
      return convert_scalars_to_vector ();
    }

  opt_pass *clone ()
    {
      return new pass_stv (m_ctxt);
    }

  void set_pass_param (unsigned int n, bool param)
    {
      gcc_assert (n == 0);
      timode_p = param;
    }

private:
  bool timode_p;
}; // class pass_stv

} // anon namespace

rtl_opt_pass *
make_pass_insert_vzeroupper (gcc::context *ctxt)
{
  return new pass_insert_vzeroupper (ctxt);
}

rtl_opt_pass *
make_pass_stv (gcc::context *ctxt)
{
  return new pass_stv (ctxt);
}

/* Return true if a red-zone is in use.  */

bool
ix86_using_red_zone (void)
{
  return TARGET_RED_ZONE && !TARGET_64BIT_MS_ABI;
}

/* Return a string that documents the current -m options.  The caller is
   responsible for freeing the string.  */

static char *
ix86_target_string (HOST_WIDE_INT isa, HOST_WIDE_INT isa2,
		    int flags, int flags2,
		    const char *arch, const char *tune,
		    enum fpmath_unit fpmath, bool add_nl_p)
{
  struct ix86_target_opts
  {
    const char *option;		/* option string */
    HOST_WIDE_INT mask;		/* isa mask options */
  };

  /* This table is ordered so that options like -msse4.2 that imply other
     ISAs come first.  Target string will be displayed in the same order.  */
  static struct ix86_target_opts isa2_opts[] =
  {
    { "-mrdpid",	OPTION_MASK_ISA_RDPID },
    { "-msgx",		OPTION_MASK_ISA_SGX },
    { "-mavx5124vnniw", OPTION_MASK_ISA_AVX5124VNNIW },
    { "-mavx5124fmaps", OPTION_MASK_ISA_AVX5124FMAPS },
    { "-mavx512vpopcntdq", OPTION_MASK_ISA_AVX512VPOPCNTDQ }
  };
  static struct ix86_target_opts isa_opts[] =
  {
    { "-mavx512vbmi",	OPTION_MASK_ISA_AVX512VBMI },
    { "-mavx512ifma",	OPTION_MASK_ISA_AVX512IFMA },
    { "-mavx512vl",	OPTION_MASK_ISA_AVX512VL },
    { "-mavx512bw",	OPTION_MASK_ISA_AVX512BW },
    { "-mavx512dq",	OPTION_MASK_ISA_AVX512DQ },
    { "-mavx512er",	OPTION_MASK_ISA_AVX512ER },
    { "-mavx512pf",	OPTION_MASK_ISA_AVX512PF },
    { "-mavx512cd",	OPTION_MASK_ISA_AVX512CD },
    { "-mavx512f",	OPTION_MASK_ISA_AVX512F },
    { "-mavx2",		OPTION_MASK_ISA_AVX2 },
    { "-mfma",		OPTION_MASK_ISA_FMA },
    { "-mxop",		OPTION_MASK_ISA_XOP },
    { "-mfma4",		OPTION_MASK_ISA_FMA4 },
    { "-mf16c",		OPTION_MASK_ISA_F16C },
    { "-mavx",		OPTION_MASK_ISA_AVX },
/*  { "-msse4"		OPTION_MASK_ISA_SSE4 }, */
    { "-msse4.2",	OPTION_MASK_ISA_SSE4_2 },
    { "-msse4.1",	OPTION_MASK_ISA_SSE4_1 },
    { "-msse4a",	OPTION_MASK_ISA_SSE4A },
    { "-mssse3",	OPTION_MASK_ISA_SSSE3 },
    { "-msse3",		OPTION_MASK_ISA_SSE3 },
    { "-maes",		OPTION_MASK_ISA_AES },
    { "-msha",		OPTION_MASK_ISA_SHA },
    { "-mpclmul",	OPTION_MASK_ISA_PCLMUL },
    { "-msse2",		OPTION_MASK_ISA_SSE2 },
    { "-msse",		OPTION_MASK_ISA_SSE },
    { "-m3dnowa",	OPTION_MASK_ISA_3DNOW_A },
    { "-m3dnow",	OPTION_MASK_ISA_3DNOW },
    { "-mmmx",		OPTION_MASK_ISA_MMX },
    { "-mrtm",		OPTION_MASK_ISA_RTM },
    { "-mprfchw",	OPTION_MASK_ISA_PRFCHW },
    { "-mrdseed",	OPTION_MASK_ISA_RDSEED },
    { "-madx",		OPTION_MASK_ISA_ADX },
    { "-mprefetchwt1",	OPTION_MASK_ISA_PREFETCHWT1 },
    { "-mclflushopt",	OPTION_MASK_ISA_CLFLUSHOPT },
    { "-mxsaves",	OPTION_MASK_ISA_XSAVES },
    { "-mxsavec",	OPTION_MASK_ISA_XSAVEC },
    { "-mxsaveopt",	OPTION_MASK_ISA_XSAVEOPT },
    { "-mxsave",	OPTION_MASK_ISA_XSAVE },
    { "-mabm",		OPTION_MASK_ISA_ABM },
    { "-mbmi",		OPTION_MASK_ISA_BMI },
    { "-mbmi2",		OPTION_MASK_ISA_BMI2 },
    { "-mlzcnt",	OPTION_MASK_ISA_LZCNT },
    { "-mtbm",		OPTION_MASK_ISA_TBM },
    { "-mpopcnt",	OPTION_MASK_ISA_POPCNT },
    { "-mcx16",		OPTION_MASK_ISA_CX16 },
    { "-msahf",		OPTION_MASK_ISA_SAHF },
    { "-mmovbe",	OPTION_MASK_ISA_MOVBE },
    { "-mcrc32",	OPTION_MASK_ISA_CRC32 },
    { "-mfsgsbase",	OPTION_MASK_ISA_FSGSBASE },
    { "-mrdrnd",	OPTION_MASK_ISA_RDRND },
    { "-mmwaitx",	OPTION_MASK_ISA_MWAITX },
    { "-mclzero",	OPTION_MASK_ISA_CLZERO },
    { "-mpku",		OPTION_MASK_ISA_PKU },
    { "-mlwp",		OPTION_MASK_ISA_LWP },
    { "-mhle",		OPTION_MASK_ISA_HLE },
    { "-mfxsr",		OPTION_MASK_ISA_FXSR },
    { "-mmpx",		OPTION_MASK_ISA_MPX },
    { "-mclwb",		OPTION_MASK_ISA_CLWB }
  };

  /* Flag options.  */
  static struct ix86_target_opts flag_opts[] =
  {
    { "-m128bit-long-double",		MASK_128BIT_LONG_DOUBLE },
    { "-mlong-double-128",		MASK_LONG_DOUBLE_128 },
    { "-mlong-double-64",		MASK_LONG_DOUBLE_64 },
    { "-m80387",			MASK_80387 },
    { "-maccumulate-outgoing-args",	MASK_ACCUMULATE_OUTGOING_ARGS },
    { "-malign-double",			MASK_ALIGN_DOUBLE },
    { "-mcld",				MASK_CLD },
    { "-mfp-ret-in-387",		MASK_FLOAT_RETURNS },
    { "-mieee-fp",			MASK_IEEE_FP },
    { "-minline-all-stringops",		MASK_INLINE_ALL_STRINGOPS },
    { "-minline-stringops-dynamically",	MASK_INLINE_STRINGOPS_DYNAMICALLY },
    { "-mms-bitfields",			MASK_MS_BITFIELD_LAYOUT },
    { "-mno-align-stringops",		MASK_NO_ALIGN_STRINGOPS },
    { "-mno-fancy-math-387",		MASK_NO_FANCY_MATH_387 },
    { "-mno-push-args",			MASK_NO_PUSH_ARGS },
    { "-mno-red-zone",			MASK_NO_RED_ZONE },
    { "-momit-leaf-frame-pointer",	MASK_OMIT_LEAF_FRAME_POINTER },
    { "-mrecip",			MASK_RECIP },
    { "-mrtd",				MASK_RTD },
    { "-msseregparm",			MASK_SSEREGPARM },
    { "-mstack-arg-probe",		MASK_STACK_PROBE },
    { "-mtls-direct-seg-refs",		MASK_TLS_DIRECT_SEG_REFS },
    { "-mvect8-ret-in-mem",		MASK_VECT8_RETURNS },
    { "-m8bit-idiv",			MASK_USE_8BIT_IDIV },
    { "-mvzeroupper",			MASK_VZEROUPPER },
    { "-mstv",				MASK_STV },
    { "-mavx256-split-unaligned-load",	MASK_AVX256_SPLIT_UNALIGNED_LOAD },
    { "-mavx256-split-unaligned-store",	MASK_AVX256_SPLIT_UNALIGNED_STORE },
    { "-mprefer-avx128",		MASK_PREFER_AVX128 },
    { "-mcall-ms2sysv-xlogues",		MASK_CALL_MS2SYSV_XLOGUES }
  };

  /* Additional flag options.  */
  static struct ix86_target_opts flag2_opts[] =
  {
    { "-mgeneral-regs-only",		OPTION_MASK_GENERAL_REGS_ONLY },
  };

  const char *opts[ARRAY_SIZE (isa_opts) + ARRAY_SIZE (isa2_opts)
		   + ARRAY_SIZE (flag_opts) + ARRAY_SIZE (flag2_opts) + 6][2];

  char isa_other[40];
  char isa2_other[40];
  char flags_other[40];
  char flags2_other[40];
  unsigned num = 0;
  unsigned i, j;
  char *ret;
  char *ptr;
  size_t len;
  size_t line_len;
  size_t sep_len;
  const char *abi;

  memset (opts, '\0', sizeof (opts));

  /* Add -march= option.  */
  if (arch)
    {
      opts[num][0] = "-march=";
      opts[num++][1] = arch;
    }

  /* Add -mtune= option.  */
  if (tune)
    {
      opts[num][0] = "-mtune=";
      opts[num++][1] = tune;
    }

  /* Add -m32/-m64/-mx32.  */
  if ((isa & OPTION_MASK_ISA_64BIT) != 0)
    {
      if ((isa & OPTION_MASK_ABI_64) != 0)
	abi = "-m64";
      else
	abi = "-mx32";
      isa &= ~ (OPTION_MASK_ISA_64BIT
		| OPTION_MASK_ABI_64
		| OPTION_MASK_ABI_X32);
    }
  else
    abi = "-m32";
  opts[num++][0] = abi;

  /* Pick out the options in isa2 options.  */
  for (i = 0; i < ARRAY_SIZE (isa2_opts); i++)
    {
      if ((isa2 & isa2_opts[i].mask) != 0)
	{
	  opts[num++][0] = isa2_opts[i].option;
	  isa2 &= ~ isa2_opts[i].mask;
	}
    }

  if (isa2 && add_nl_p)
    {
      opts[num++][0] = isa2_other;
      sprintf (isa2_other, "(other isa2: %#" HOST_WIDE_INT_PRINT "x)", isa2);
    }

  /* Pick out the options in isa options.  */
  for (i = 0; i < ARRAY_SIZE (isa_opts); i++)
    {
      if ((isa & isa_opts[i].mask) != 0)
	{
	  opts[num++][0] = isa_opts[i].option;
	  isa &= ~ isa_opts[i].mask;
	}
    }

  if (isa && add_nl_p)
    {
      opts[num++][0] = isa_other;
      sprintf (isa_other, "(other isa: %#" HOST_WIDE_INT_PRINT "x)", isa);
    }

  /* Add flag options.  */
  for (i = 0; i < ARRAY_SIZE (flag_opts); i++)
    {
      if ((flags & flag_opts[i].mask) != 0)
	{
	  opts[num++][0] = flag_opts[i].option;
	  flags &= ~ flag_opts[i].mask;
	}
    }

  if (flags && add_nl_p)
    {
      opts[num++][0] = flags_other;
      sprintf (flags_other, "(other flags: %#x)", flags);
    }

    /* Add additional flag options.  */
  for (i = 0; i < ARRAY_SIZE (flag2_opts); i++)
    {
      if ((flags2 & flag2_opts[i].mask) != 0)
	{
	  opts[num++][0] = flag2_opts[i].option;
	  flags2 &= ~ flag2_opts[i].mask;
	}
    }

  if (flags2 && add_nl_p)
    {
      opts[num++][0] = flags2_other;
      sprintf (flags2_other, "(other flags2: %#x)", flags2);
    }

  /* Add -fpmath= option.  */
  if (fpmath)
    {
      opts[num][0] = "-mfpmath=";
      switch ((int) fpmath)
	{
	case FPMATH_387:
	  opts[num++][1] = "387";
	  break;

	case FPMATH_SSE:
	  opts[num++][1] = "sse";
	  break;

	case FPMATH_387 | FPMATH_SSE:
	  opts[num++][1] = "sse+387";
	  break;

	default:
	  gcc_unreachable ();
	}
    }

  /* Any options?  */
  if (num == 0)
    return NULL;

  gcc_assert (num < ARRAY_SIZE (opts));

  /* Size the string.  */
  len = 0;
  sep_len = (add_nl_p) ? 3 : 1;
  for (i = 0; i < num; i++)
    {
      len += sep_len;
      for (j = 0; j < 2; j++)
	if (opts[i][j])
	  len += strlen (opts[i][j]);
    }

  /* Build the string.  */
  ret = ptr = (char *) xmalloc (len);
  line_len = 0;

  for (i = 0; i < num; i++)
    {
      size_t len2[2];

      for (j = 0; j < 2; j++)
	len2[j] = (opts[i][j]) ? strlen (opts[i][j]) : 0;

      if (i != 0)
	{
	  *ptr++ = ' ';
	  line_len++;

	  if (add_nl_p && line_len + len2[0] + len2[1] > 70)
	    {
	      *ptr++ = '\\';
	      *ptr++ = '\n';
	      line_len = 0;
	    }
	}

      for (j = 0; j < 2; j++)
	if (opts[i][j])
	  {
	    memcpy (ptr, opts[i][j], len2[j]);
	    ptr += len2[j];
	    line_len += len2[j];
	  }
    }

  *ptr = '\0';
  gcc_assert (ret + len >= ptr);

  return ret;
}

/* Return true, if profiling code should be emitted before
   prologue. Otherwise it returns false.
   Note: For x86 with "hotfix" it is sorried.  */
static bool
ix86_profile_before_prologue (void)
{
  return flag_fentry != 0;
}

/* Function that is callable from the debugger to print the current
   options.  */
void ATTRIBUTE_UNUSED
ix86_debug_options (void)
{
  char *opts = ix86_target_string (ix86_isa_flags, ix86_isa_flags2,
				   target_flags, ix86_target_flags,
				   ix86_arch_string,ix86_tune_string,
				   ix86_fpmath, true);

  if (opts)
    {
      fprintf (stderr, "%s\n\n", opts);
      free (opts);
    }
  else
    fputs ("<no options>\n\n", stderr);

  return;
}

/* Return true if T is one of the bytes we should avoid with
   -fmitigate-rop.  */

static bool
ix86_rop_should_change_byte_p (int t)
{
  return t == 0xc2 || t == 0xc3 || t == 0xca || t == 0xcb;
}

static const char *stringop_alg_names[] = {
#define DEF_ENUM
#define DEF_ALG(alg, name) #name,
//#include "stringop.def"
#undef DEF_ENUM
#undef DEF_ALG
};

/* Parse parameter string passed to -mmemcpy-strategy= or -mmemset-strategy=.
   The string is of the following form (or comma separated list of it):

     strategy_alg:max_size:[align|noalign]

   where the full size range for the strategy is either [0, max_size] or
   [min_size, max_size], in which min_size is the max_size + 1 of the
   preceding range.  The last size range must have max_size == -1.

   Examples:

    1.
       -mmemcpy-strategy=libcall:-1:noalign

      this is equivalent to (for known size memcpy) -mstringop-strategy=libcall


   2.
      -mmemset-strategy=rep_8byte:16:noalign,vector_loop:2048:align,libcall:-1:noalign

      This is to tell the compiler to use the following strategy for memset
      1) when the expected size is between [1, 16], use rep_8byte strategy;
      2) when the size is between [17, 2048], use vector_loop;
      3) when the size is > 2048, use libcall.  */

struct stringop_size_range
{
  int max;
  stringop_alg alg;
  bool noalign;
};

static void
ix86_parse_stringop_strategy_string (char *strategy_str, bool is_memset)
{
  const struct stringop_algs *default_algs;
  stringop_size_range input_ranges[MAX_STRINGOP_ALGS];
  char *curr_range_str, *next_range_str;
  const char *opt = is_memset ? "-mmemset_strategy=" : "-mmemcpy_strategy=";
  int i = 0, n = 0;

  if (is_memset)
    default_algs = &ix86_cost->memset[TARGET_64BIT != 0];
  else
    default_algs = &ix86_cost->memcpy[TARGET_64BIT != 0];

  curr_range_str = strategy_str;

  do
    {
      int maxs;
      char alg_name[128];
      char align[16];
      next_range_str = strchr (curr_range_str, ',');
      if (next_range_str)
        *next_range_str++ = '\0';

      if (3 != sscanf (curr_range_str, "%20[^:]:%d:%10s",
                       alg_name, &maxs, align))
        {
	  error ("wrong argument %qs to option %qs", curr_range_str, opt);
          return;
        }

      if (n > 0 && (maxs < (input_ranges[n - 1].max + 1) && maxs != -1))
        {
	  error ("size ranges of option %qs should be increasing", opt);
          return;
        }

      for (i = 0; i < last_alg; i++)
	if (!strcmp (alg_name, stringop_alg_names[i]))
	  break;

      if (i == last_alg)
        {
	  error ("wrong strategy name %qs specified for option %qs",
		 alg_name, opt);

	  auto_vec <const char *> candidates;
	  for (i = 0; i < last_alg; i++)
	    if ((stringop_alg) i != rep_prefix_8_byte || TARGET_64BIT)
	      candidates.safe_push (stringop_alg_names[i]);

	  char *s;
	  const char *hint
	    = candidates_list_and_hint (alg_name, s, candidates);
	  if (hint)
	    inform (input_location,
		    "valid arguments to %qs are: %s; did you mean %qs?",
		    opt, s, hint);
	  else
	    inform (input_location, "valid arguments to %qs are: %s",
		    opt, s);
	  XDELETEVEC (s);
          return;
        }

      if ((stringop_alg) i == rep_prefix_8_byte
	  && !TARGET_64BIT)
	{
	  /* rep; movq isn't available in 32-bit code.  */
	  error ("strategy name %qs specified for option %qs "
		 "not supported for 32-bit code", alg_name, opt);
	  return;
	}

      input_ranges[n].max = maxs;
      input_ranges[n].alg = (stringop_alg) i;
      if (!strcmp (align, "align"))
        input_ranges[n].noalign = false;
      else if (!strcmp (align, "noalign"))
        input_ranges[n].noalign = true;
      else
        {
	  error ("unknown alignment %qs specified for option %qs", align, opt);
          return;
        }
      n++;
      curr_range_str = next_range_str;
    }
  while (curr_range_str);

  if (input_ranges[n - 1].max != -1)
    {
      error ("the max value for the last size range should be -1"
             " for option %qs", opt);
      return;
    }

  if (n > MAX_STRINGOP_ALGS)
    {
      error ("too many size ranges specified in option %qs", opt);
      return;
    }

  /* Now override the default algs array.  */
  for (i = 0; i < n; i++)
    {
      *const_cast<int *>(&default_algs->size[i].max) = input_ranges[i].max;
      *const_cast<stringop_alg *>(&default_algs->size[i].alg)
          = input_ranges[i].alg;
      *const_cast<int *>(&default_algs->size[i].noalign)
          = input_ranges[i].noalign;
    }
}


/* parse -mtune-ctrl= option. When DUMP is true,
   print the features that are explicitly set.  */

static void
parse_mtune_ctrl_str (bool dump)
{
  if (!ix86_tune_ctrl_string)
    return;

  char *next_feature_string = NULL;
  char *curr_feature_string = xstrdup (ix86_tune_ctrl_string);
  char *orig = curr_feature_string;
  int i;
  do
    {
      bool clear = false;

      next_feature_string = strchr (curr_feature_string, ',');
      if (next_feature_string)
        *next_feature_string++ = '\0';
      if (*curr_feature_string == '^')
        {
          curr_feature_string++;
          clear = true;
        }
      for (i = 0; i < X86_TUNE_LAST; i++)
        {
          if (!strcmp (curr_feature_string, ix86_tune_feature_names[i]))
            {
              ix86_tune_features[i] = !clear;
              if (dump)
                fprintf (stderr, "Explicitly %s feature %s\n",
                         clear ? "clear" : "set", ix86_tune_feature_names[i]);
              break;
            }
        }
      if (i == X86_TUNE_LAST)
        error ("Unknown parameter to option -mtune-ctrl: %s",
               clear ? curr_feature_string - 1 : curr_feature_string);
      curr_feature_string = next_feature_string;
    }
  while (curr_feature_string);
  free (orig);
}

/* Helper function to set ix86_tune_features. IX86_TUNE is the
   processor type.  */

static void
set_ix86_tune_features (enum processor_type ix86_tune, bool dump)
{
  unsigned int ix86_tune_mask = 1u << ix86_tune;
  int i;

  for (i = 0; i < X86_TUNE_LAST; ++i)
    {
      if (ix86_tune_no_default)
        ix86_tune_features[i] = 0;
      else
        ix86_tune_features[i] = !!(initial_ix86_tune_features[i] & ix86_tune_mask);
    }

  if (dump)
    {
      fprintf (stderr, "List of x86 specific tuning parameter names:\n");
      for (i = 0; i < X86_TUNE_LAST; i++)
        fprintf (stderr, "%s : %s\n", ix86_tune_feature_names[i],
                 ix86_tune_features[i] ? "on" : "off");
    }

  parse_mtune_ctrl_str (dump);
}


/* Default align_* from the processor table.  */

static void
ix86_default_align (struct gcc_options *opts)
{
  if (opts->x_align_loops == 0)
    {
      opts->x_align_loops = processor_target_table[ix86_tune].align_loop;
      align_loops_max_skip = processor_target_table[ix86_tune].align_loop_max_skip;
    }
  if (opts->x_align_jumps == 0)
    {
      opts->x_align_jumps = processor_target_table[ix86_tune].align_jump;
      align_jumps_max_skip = processor_target_table[ix86_tune].align_jump_max_skip;
    }
  if (opts->x_align_functions == 0)
    {
      opts->x_align_functions = processor_target_table[ix86_tune].align_func;
    }
}

/* Implement TARGET_OVERRIDE_OPTIONS_AFTER_CHANGE hook.  */

static void
ix86_override_options_after_change (void)
{
  ix86_default_align (&global_options);
}

/* Override various settings based on options.  If MAIN_ARGS_P, the
   options are from the command line, otherwise they are from
   attributes.  Return true if there's an error related to march
   option.  */

static bool
ix86_option_override_internal (bool main_args_p,
			       struct gcc_options *opts,
			       struct gcc_options *opts_set)
{
  int i;
  unsigned int ix86_arch_mask;
  const bool ix86_tune_specified = (opts->x_ix86_tune_string != NULL);

#define PTA_3DNOW		(HOST_WIDE_INT_1 << 0)
#define PTA_3DNOW_A		(HOST_WIDE_INT_1 << 1)
#define PTA_64BIT		(HOST_WIDE_INT_1 << 2)
#define PTA_ABM			(HOST_WIDE_INT_1 << 3)
#define PTA_AES			(HOST_WIDE_INT_1 << 4)
#define PTA_AVX			(HOST_WIDE_INT_1 << 5)
#define PTA_BMI			(HOST_WIDE_INT_1 << 6)
#define PTA_CX16		(HOST_WIDE_INT_1 << 7)
#define PTA_F16C		(HOST_WIDE_INT_1 << 8)
#define PTA_FMA			(HOST_WIDE_INT_1 << 9)
#define PTA_FMA4		(HOST_WIDE_INT_1 << 10)
#define PTA_FSGSBASE		(HOST_WIDE_INT_1 << 11)
#define PTA_LWP			(HOST_WIDE_INT_1 << 12)
#define PTA_LZCNT		(HOST_WIDE_INT_1 << 13)
#define PTA_MMX			(HOST_WIDE_INT_1 << 14)
#define PTA_MOVBE		(HOST_WIDE_INT_1 << 15)
#define PTA_NO_SAHF		(HOST_WIDE_INT_1 << 16)
#define PTA_PCLMUL		(HOST_WIDE_INT_1 << 17)
#define PTA_POPCNT		(HOST_WIDE_INT_1 << 18)
#define PTA_PREFETCH_SSE	(HOST_WIDE_INT_1 << 19)
#define PTA_RDRND		(HOST_WIDE_INT_1 << 20)
#define PTA_SSE			(HOST_WIDE_INT_1 << 21)
#define PTA_SSE2		(HOST_WIDE_INT_1 << 22)
#define PTA_SSE3		(HOST_WIDE_INT_1 << 23)
#define PTA_SSE4_1		(HOST_WIDE_INT_1 << 24)
#define PTA_SSE4_2		(HOST_WIDE_INT_1 << 25)
#define PTA_SSE4A		(HOST_WIDE_INT_1 << 26)
#define PTA_SSSE3		(HOST_WIDE_INT_1 << 27)
#define PTA_TBM			(HOST_WIDE_INT_1 << 28)
#define PTA_XOP			(HOST_WIDE_INT_1 << 29)
#define PTA_AVX2		(HOST_WIDE_INT_1 << 30)
#define PTA_BMI2		(HOST_WIDE_INT_1 << 31)
#define PTA_RTM			(HOST_WIDE_INT_1 << 32)
#define PTA_HLE			(HOST_WIDE_INT_1 << 33)
#define PTA_PRFCHW		(HOST_WIDE_INT_1 << 34)
#define PTA_RDSEED		(HOST_WIDE_INT_1 << 35)
#define PTA_ADX			(HOST_WIDE_INT_1 << 36)
#define PTA_FXSR		(HOST_WIDE_INT_1 << 37)
#define PTA_XSAVE		(HOST_WIDE_INT_1 << 38)
#define PTA_XSAVEOPT		(HOST_WIDE_INT_1 << 39)
#define PTA_AVX512F		(HOST_WIDE_INT_1 << 40)
#define PTA_AVX512ER		(HOST_WIDE_INT_1 << 41)
#define PTA_AVX512PF		(HOST_WIDE_INT_1 << 42)
#define PTA_AVX512CD		(HOST_WIDE_INT_1 << 43)
#define PTA_MPX			(HOST_WIDE_INT_1 << 44)
#define PTA_SHA			(HOST_WIDE_INT_1 << 45)
#define PTA_PREFETCHWT1		(HOST_WIDE_INT_1 << 46)
#define PTA_CLFLUSHOPT		(HOST_WIDE_INT_1 << 47)
#define PTA_XSAVEC		(HOST_WIDE_INT_1 << 48)
#define PTA_XSAVES		(HOST_WIDE_INT_1 << 49)
#define PTA_AVX512DQ		(HOST_WIDE_INT_1 << 50)
#define PTA_AVX512BW		(HOST_WIDE_INT_1 << 51)
#define PTA_AVX512VL		(HOST_WIDE_INT_1 << 52)
#define PTA_AVX512IFMA		(HOST_WIDE_INT_1 << 53)
#define PTA_AVX512VBMI		(HOST_WIDE_INT_1 << 54)
#define PTA_CLWB		(HOST_WIDE_INT_1 << 55)
#define PTA_MWAITX		(HOST_WIDE_INT_1 << 56)
#define PTA_CLZERO		(HOST_WIDE_INT_1 << 57)
#define PTA_NO_80387		(HOST_WIDE_INT_1 << 58)
#define PTA_PKU			(HOST_WIDE_INT_1 << 59)
#define PTA_AVX5124VNNIW	(HOST_WIDE_INT_1 << 60)
#define PTA_AVX5124FMAPS	(HOST_WIDE_INT_1 << 61)
#define PTA_AVX512VPOPCNTDQ	(HOST_WIDE_INT_1 << 62)
#define PTA_SGX			(HOST_WIDE_INT_1 << 63)

#define PTA_CORE2 \
  (PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3 | PTA_SSSE3 \
   | PTA_CX16 | PTA_FXSR)
#define PTA_NEHALEM \
  (PTA_CORE2 | PTA_SSE4_1 | PTA_SSE4_2 | PTA_POPCNT)
#define PTA_WESTMERE \
  (PTA_NEHALEM | PTA_AES | PTA_PCLMUL)
#define PTA_SANDYBRIDGE \
  (PTA_WESTMERE | PTA_AVX | PTA_XSAVE | PTA_XSAVEOPT)
#define PTA_IVYBRIDGE \
  (PTA_SANDYBRIDGE | PTA_FSGSBASE | PTA_RDRND | PTA_F16C)
#define PTA_HASWELL \
  (PTA_IVYBRIDGE | PTA_AVX2 | PTA_BMI | PTA_BMI2 | PTA_LZCNT \
   | PTA_FMA | PTA_MOVBE | PTA_HLE)
#define PTA_BROADWELL \
  (PTA_HASWELL | PTA_ADX | PTA_PRFCHW | PTA_RDSEED)
#define PTA_SKYLAKE \
  (PTA_BROADWELL | PTA_CLFLUSHOPT | PTA_XSAVEC | PTA_XSAVES)
#define PTA_SKYLAKE_AVX512 \
  (PTA_SKYLAKE | PTA_AVX512F | PTA_AVX512CD | PTA_AVX512VL \
   | PTA_AVX512BW | PTA_AVX512DQ | PTA_PKU)
#define PTA_KNL \
  (PTA_BROADWELL | PTA_AVX512PF | PTA_AVX512ER | PTA_AVX512F | PTA_AVX512CD)
#define PTA_BONNELL \
  (PTA_CORE2 | PTA_MOVBE)
#define PTA_SILVERMONT \
  (PTA_WESTMERE | PTA_MOVBE)

/* if this reaches 64, need to widen struct pta flags below */

  static struct pta
    {
      const char *const name;		/* processor name or nickname.  */
      const enum processor_type processor;
      const enum attr_cpu schedule;
      const unsigned HOST_WIDE_INT flags;
    }
  const processor_alias_table[] =
    {
      {"i386", PROCESSOR_I386, CPU_NONE, 0},
      {"i486", PROCESSOR_I486, CPU_NONE, 0},
      {"i586", PROCESSOR_PENTIUM, CPU_PENTIUM, 0},
      {"pentium", PROCESSOR_PENTIUM, CPU_PENTIUM, 0},
      {"lakemont", PROCESSOR_LAKEMONT, CPU_PENTIUM, PTA_NO_80387},
      {"pentium-mmx", PROCESSOR_PENTIUM, CPU_PENTIUM, PTA_MMX},
      {"winchip-c6", PROCESSOR_I486, CPU_NONE, PTA_MMX},
      {"winchip2", PROCESSOR_I486, CPU_NONE, PTA_MMX | PTA_3DNOW},
      {"c3", PROCESSOR_I486, CPU_NONE, PTA_MMX | PTA_3DNOW},
      {"samuel-2", PROCESSOR_I486, CPU_NONE, PTA_MMX | PTA_3DNOW},
      {"c3-2", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
	PTA_MMX | PTA_SSE | PTA_FXSR},
      {"nehemiah", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
        PTA_MMX | PTA_SSE | PTA_FXSR},
      {"c7", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
        PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3 | PTA_FXSR},
      {"esther", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
        PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3 | PTA_FXSR},
      {"i686", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO, 0},
      {"pentiumpro", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO, 0},
      {"pentium2", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO, PTA_MMX | PTA_FXSR},
      {"pentium3", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
	PTA_MMX | PTA_SSE | PTA_FXSR},
      {"pentium3m", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
	PTA_MMX | PTA_SSE | PTA_FXSR},
      {"pentium-m", PROCESSOR_PENTIUMPRO, CPU_PENTIUMPRO,
	PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_FXSR},
      {"pentium4", PROCESSOR_PENTIUM4, CPU_NONE,
	PTA_MMX |PTA_SSE | PTA_SSE2 | PTA_FXSR},
      {"pentium4m", PROCESSOR_PENTIUM4, CPU_NONE,
	PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_FXSR},
      {"prescott", PROCESSOR_NOCONA, CPU_NONE,
	PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3 | PTA_FXSR},
      {"nocona", PROCESSOR_NOCONA, CPU_NONE,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
	| PTA_CX16 | PTA_NO_SAHF | PTA_FXSR},
      {"core2", PROCESSOR_CORE2, CPU_CORE2, PTA_CORE2},
      {"nehalem", PROCESSOR_NEHALEM, CPU_NEHALEM, PTA_NEHALEM},
      {"corei7", PROCESSOR_NEHALEM, CPU_NEHALEM, PTA_NEHALEM},
      {"westmere", PROCESSOR_NEHALEM, CPU_NEHALEM, PTA_WESTMERE},
      {"sandybridge", PROCESSOR_SANDYBRIDGE, CPU_NEHALEM,
	PTA_SANDYBRIDGE},
      {"corei7-avx", PROCESSOR_SANDYBRIDGE, CPU_NEHALEM,
	PTA_SANDYBRIDGE},
      {"ivybridge", PROCESSOR_SANDYBRIDGE, CPU_NEHALEM,
	PTA_IVYBRIDGE},
      {"core-avx-i", PROCESSOR_SANDYBRIDGE, CPU_NEHALEM,
	PTA_IVYBRIDGE},
      {"haswell", PROCESSOR_HASWELL, CPU_HASWELL, PTA_HASWELL},
      {"core-avx2", PROCESSOR_HASWELL, CPU_HASWELL, PTA_HASWELL},
      {"broadwell", PROCESSOR_HASWELL, CPU_HASWELL, PTA_BROADWELL},
      {"skylake", PROCESSOR_HASWELL, CPU_HASWELL, PTA_SKYLAKE},
      {"skylake-avx512", PROCESSOR_HASWELL, CPU_HASWELL, PTA_SKYLAKE_AVX512},
      {"bonnell", PROCESSOR_BONNELL, CPU_ATOM, PTA_BONNELL},
      {"atom", PROCESSOR_BONNELL, CPU_ATOM, PTA_BONNELL},
      {"silvermont", PROCESSOR_SILVERMONT, CPU_SLM, PTA_SILVERMONT},
      {"slm", PROCESSOR_SILVERMONT, CPU_SLM, PTA_SILVERMONT},
      {"knl", PROCESSOR_KNL, CPU_SLM, PTA_KNL},
      {"intel", PROCESSOR_INTEL, CPU_SLM, PTA_NEHALEM},
      {"geode", PROCESSOR_GEODE, CPU_GEODE,
	PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_PREFETCH_SSE},
      {"k6", PROCESSOR_K6, CPU_K6, PTA_MMX},
      {"k6-2", PROCESSOR_K6, CPU_K6, PTA_MMX | PTA_3DNOW},
      {"k6-3", PROCESSOR_K6, CPU_K6, PTA_MMX | PTA_3DNOW},
      {"athlon", PROCESSOR_ATHLON, CPU_ATHLON,
	PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_PREFETCH_SSE},
      {"athlon-tbird", PROCESSOR_ATHLON, CPU_ATHLON,
	PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_PREFETCH_SSE},
      {"athlon-4", PROCESSOR_ATHLON, CPU_ATHLON,
	PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE | PTA_FXSR},
      {"athlon-xp", PROCESSOR_ATHLON, CPU_ATHLON,
	PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE | PTA_FXSR},
      {"athlon-mp", PROCESSOR_ATHLON, CPU_ATHLON,
	PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE | PTA_FXSR},
      {"x86-64", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_NO_SAHF | PTA_FXSR},
      {"eden-x2", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3 | PTA_FXSR},
      {"nano", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_FXSR},
      {"nano-1000", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_FXSR},
      {"nano-2000", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_FXSR},
      {"nano-3000", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_SSE4_1 | PTA_FXSR},
      {"nano-x2", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_SSE4_1 | PTA_FXSR},
      {"eden-x4", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_SSE4_1 | PTA_FXSR},
      {"nano-x4", PROCESSOR_K8, CPU_K8,
        PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
        | PTA_SSSE3 | PTA_SSE4_1 | PTA_FXSR},
      {"k8", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_NO_SAHF | PTA_FXSR},
      {"k8-sse3", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_SSE3 | PTA_NO_SAHF | PTA_FXSR},
      {"opteron", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_NO_SAHF | PTA_FXSR},
      {"opteron-sse3", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_SSE3 | PTA_NO_SAHF | PTA_FXSR},
      {"athlon64", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_NO_SAHF | PTA_FXSR},
      {"athlon64-sse3", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_SSE3 | PTA_NO_SAHF | PTA_FXSR},
      {"athlon-fx", PROCESSOR_K8, CPU_K8,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE
	| PTA_SSE2 | PTA_NO_SAHF | PTA_FXSR},
      {"amdfam10", PROCESSOR_AMDFAM10, CPU_AMDFAM10,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE | PTA_SSE2
	| PTA_SSE3 | PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_PRFCHW | PTA_FXSR},
      {"barcelona", PROCESSOR_AMDFAM10, CPU_AMDFAM10,
	PTA_64BIT | PTA_MMX | PTA_3DNOW | PTA_3DNOW_A | PTA_SSE | PTA_SSE2
	| PTA_SSE3 | PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_PRFCHW | PTA_FXSR},
      {"bdver1", PROCESSOR_BDVER1, CPU_BDVER1,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
	| PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_SSSE3 | PTA_SSE4_1
	| PTA_SSE4_2 | PTA_AES | PTA_PCLMUL | PTA_AVX | PTA_FMA4
	| PTA_XOP | PTA_LWP | PTA_PRFCHW | PTA_FXSR | PTA_XSAVE},
      {"bdver2", PROCESSOR_BDVER2, CPU_BDVER2,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
	| PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_SSSE3 | PTA_SSE4_1
	| PTA_SSE4_2 | PTA_AES | PTA_PCLMUL | PTA_AVX | PTA_FMA4
	| PTA_XOP | PTA_LWP | PTA_BMI | PTA_TBM | PTA_F16C
	| PTA_FMA | PTA_PRFCHW | PTA_FXSR | PTA_XSAVE},
      {"bdver3", PROCESSOR_BDVER3, CPU_BDVER3,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
	| PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_SSSE3 | PTA_SSE4_1
	| PTA_SSE4_2 | PTA_AES | PTA_PCLMUL | PTA_AVX | PTA_FMA4
	| PTA_XOP | PTA_LWP | PTA_BMI | PTA_TBM | PTA_F16C
	| PTA_FMA | PTA_PRFCHW | PTA_FXSR | PTA_XSAVE 
	| PTA_XSAVEOPT | PTA_FSGSBASE},
      {"bdver4", PROCESSOR_BDVER4, CPU_BDVER4,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
	| PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_SSSE3 | PTA_SSE4_1
	| PTA_SSE4_2 | PTA_AES | PTA_PCLMUL | PTA_AVX | PTA_AVX2 
	| PTA_FMA4 | PTA_XOP | PTA_LWP | PTA_BMI | PTA_BMI2 
	| PTA_TBM | PTA_F16C | PTA_FMA | PTA_PRFCHW | PTA_FXSR 
	| PTA_XSAVE | PTA_XSAVEOPT | PTA_FSGSBASE | PTA_RDRND
	| PTA_MOVBE | PTA_MWAITX},
      {"znver1", PROCESSOR_ZNVER1, CPU_ZNVER1,
	PTA_64BIT | PTA_MMX | PTA_SSE | PTA_SSE2 | PTA_SSE3
	| PTA_SSE4A | PTA_CX16 | PTA_ABM | PTA_SSSE3 | PTA_SSE4_1
	| PTA_SSE4_2 | PTA_AES | PTA_PCLMUL | PTA_AVX | PTA_AVX2
	| PTA_BMI | PTA_BMI2 | PTA_F16C | PTA_FMA | PTA_PRFCHW
	| PTA_FXSR | PTA_XSAVE | PTA_XSAVEOPT | PTA_FSGSBASE
	| PTA_RDRND | PTA_MOVBE | PTA_MWAITX | PTA_ADX | PTA_RDSEED
	| PTA_CLZERO | PTA_CLFLUSHOPT | PTA_XSAVEC | PTA_XSAVES
	| PTA_SHA | PTA_LZCNT | PTA_POPCNT},
      {"btver1", PROCESSOR_BTVER1, CPU_GENERIC,
	PTA_64BIT | PTA_MMX |  PTA_SSE  | PTA_SSE2 | PTA_SSE3
	| PTA_SSSE3 | PTA_SSE4A |PTA_ABM | PTA_CX16 | PTA_PRFCHW
	| PTA_FXSR | PTA_XSAVE},
      {"btver2", PROCESSOR_BTVER2, CPU_BTVER2,
	PTA_64BIT | PTA_MMX |  PTA_SSE  | PTA_SSE2 | PTA_SSE3
	| PTA_SSSE3 | PTA_SSE4A |PTA_ABM | PTA_CX16 | PTA_SSE4_1
	| PTA_SSE4_2 | PTA_AES | PTA_PCLMUL | PTA_AVX
	| PTA_BMI | PTA_F16C | PTA_MOVBE | PTA_PRFCHW
	| PTA_FXSR | PTA_XSAVE | PTA_XSAVEOPT},

      {"generic", PROCESSOR_GENERIC, CPU_GENERIC,
	PTA_64BIT
	| PTA_HLE /* flags are only used for -march switch.  */ },
    };

  /* -mrecip options.  */
  static struct
    {
      const char *string;           /* option name */
      unsigned int mask;            /* mask bits to set */
    }
  const recip_options[] =
    {
      { "all",       RECIP_MASK_ALL },
      { "none",      RECIP_MASK_NONE },
      { "div",       RECIP_MASK_DIV },
      { "sqrt",      RECIP_MASK_SQRT },
      { "vec-div",   RECIP_MASK_VEC_DIV },
      { "vec-sqrt",  RECIP_MASK_VEC_SQRT },
    };

  int const pta_size = ARRAY_SIZE (processor_alias_table);

  /* Turn off both OPTION_MASK_ABI_64 and OPTION_MASK_ABI_X32 if
     TARGET_64BIT_DEFAULT is true and TARGET_64BIT is false.  */
  if (TARGET_64BIT_DEFAULT && !TARGET_64BIT_P (opts->x_ix86_isa_flags))
    opts->x_ix86_isa_flags &= ~(OPTION_MASK_ABI_64 | OPTION_MASK_ABI_X32);
#ifdef TARGET_BI_ARCH
  else
    {
#if TARGET_BI_ARCH == 1
      /* When TARGET_BI_ARCH == 1, by default, OPTION_MASK_ABI_64
	 is on and OPTION_MASK_ABI_X32 is off.  We turn off
	 OPTION_MASK_ABI_64 if OPTION_MASK_ABI_X32 is turned on by
	 -mx32.  */
      if (TARGET_X32_P (opts->x_ix86_isa_flags))
	opts->x_ix86_isa_flags &= ~OPTION_MASK_ABI_64;
#else
      /* When TARGET_BI_ARCH == 2, by default, OPTION_MASK_ABI_X32 is
	 on and OPTION_MASK_ABI_64 is off.  We turn off
	 OPTION_MASK_ABI_X32 if OPTION_MASK_ABI_64 is turned on by
	 -m64 or OPTION_MASK_CODE16 is turned on by -m16.  */
      if (TARGET_LP64_P (opts->x_ix86_isa_flags)
	  || TARGET_16BIT_P (opts->x_ix86_isa_flags))
	opts->x_ix86_isa_flags &= ~OPTION_MASK_ABI_X32;
#endif
      if (TARGET_64BIT_P (opts->x_ix86_isa_flags)
	  && TARGET_IAMCU_P (opts->x_target_flags))
	sorry ("Intel MCU psABI isn%'t supported in %s mode",
	       TARGET_X32_P (opts->x_ix86_isa_flags) ? "x32" : "64-bit");
    }
#endif

  if (TARGET_X32_P (opts->x_ix86_isa_flags))
    {
      /* Always turn on OPTION_MASK_ISA_64BIT and turn off
	 OPTION_MASK_ABI_64 for TARGET_X32.  */
      opts->x_ix86_isa_flags |= OPTION_MASK_ISA_64BIT;
      opts->x_ix86_isa_flags &= ~OPTION_MASK_ABI_64;
    }
  else if (TARGET_16BIT_P (opts->x_ix86_isa_flags))
    opts->x_ix86_isa_flags &= ~(OPTION_MASK_ISA_64BIT
				| OPTION_MASK_ABI_X32
				| OPTION_MASK_ABI_64);
  else if (TARGET_LP64_P (opts->x_ix86_isa_flags))
    {
      /* Always turn on OPTION_MASK_ISA_64BIT and turn off
	 OPTION_MASK_ABI_X32 for TARGET_LP64.  */
      opts->x_ix86_isa_flags |= OPTION_MASK_ISA_64BIT;
      opts->x_ix86_isa_flags &= ~OPTION_MASK_ABI_X32;
    }

#ifdef SUBTARGET_OVERRIDE_OPTIONS
  SUBTARGET_OVERRIDE_OPTIONS;
#endif

#ifdef SUBSUBTARGET_OVERRIDE_OPTIONS
  SUBSUBTARGET_OVERRIDE_OPTIONS;
#endif

  /* -fPIC is the default for x86_64.  */
  if (TARGET_MACHO && TARGET_64BIT_P (opts->x_ix86_isa_flags))
    opts->x_flag_pic = 2;

  /* Need to check -mtune=generic first.  */
  if (opts->x_ix86_tune_string)
    {
      /* As special support for cross compilers we read -mtune=native
	     as -mtune=generic.  With native compilers we won't see the
	     -mtune=native, as it was changed by the driver.  */
      if (!strcmp (opts->x_ix86_tune_string, "native"))
	{
	  opts->x_ix86_tune_string = "generic";
	}
      else if (!strcmp (opts->x_ix86_tune_string, "x86-64"))
        warning (OPT_Wdeprecated,
		 main_args_p
		 ? G_("%<-mtune=x86-64%> is deprecated; use %<-mtune=k8%> "
		      "or %<-mtune=generic%> instead as appropriate")
		 : G_("%<target(\"tune=x86-64\")%> is deprecated; use "
		      "%<target(\"tune=k8\")%> or %<target(\"tune=generic\")%>"
		      " instead as appropriate"));
    }
  else
    {
      if (opts->x_ix86_arch_string)
	opts->x_ix86_tune_string = opts->x_ix86_arch_string;
      if (!opts->x_ix86_tune_string)
	{
	  opts->x_ix86_tune_string
	    = processor_target_table[TARGET_CPU_DEFAULT].name;
	  ix86_tune_defaulted = 1;
	}

      /* opts->x_ix86_tune_string is set to opts->x_ix86_arch_string
	 or defaulted.  We need to use a sensible tune option.  */
      if (!strcmp (opts->x_ix86_tune_string, "x86-64"))
	{
	  opts->x_ix86_tune_string = "generic";
	}
    }

  if (opts->x_ix86_stringop_alg == rep_prefix_8_byte
      && !TARGET_64BIT_P (opts->x_ix86_isa_flags))
    {
      /* rep; movq isn't available in 32-bit code.  */
      error ("-mstringop-strategy=rep_8byte not supported for 32-bit code");
      opts->x_ix86_stringop_alg = no_stringop;
    }

  if (!opts->x_ix86_arch_string)
    opts->x_ix86_arch_string
      = TARGET_64BIT_P (opts->x_ix86_isa_flags)
	? "x86-64" : SUBTARGET32_DEFAULT_CPU;
  else
    ix86_arch_specified = 1;

  if (opts_set->x_ix86_pmode)
    {
      if ((TARGET_LP64_P (opts->x_ix86_isa_flags)
	   && opts->x_ix86_pmode == PMODE_SI)
	  || (!TARGET_64BIT_P (opts->x_ix86_isa_flags)
	       && opts->x_ix86_pmode == PMODE_DI))
	error ("address mode %qs not supported in the %s bit mode",
	       TARGET_64BIT_P (opts->x_ix86_isa_flags) ? "short" : "long",
	       TARGET_64BIT_P (opts->x_ix86_isa_flags) ? "64" : "32");
    }
  else
    opts->x_ix86_pmode = TARGET_LP64_P (opts->x_ix86_isa_flags)
			 ? PMODE_DI : PMODE_SI;

  if (!opts_set->x_ix86_abi)
    opts->x_ix86_abi = DEFAULT_ABI;

  if (opts->x_ix86_abi == MS_ABI && TARGET_X32_P (opts->x_ix86_isa_flags))
    error ("-mabi=ms not supported with X32 ABI");
  gcc_assert (opts->x_ix86_abi == SYSV_ABI || opts->x_ix86_abi == MS_ABI);

  /* For targets using ms ABI enable ms-extensions, if not
     explicit turned off.  For non-ms ABI we turn off this
     option.  */
  if (!opts_set->x_flag_ms_extensions)
    opts->x_flag_ms_extensions = (MS_ABI == DEFAULT_ABI);

  if (opts_set->x_ix86_cmodel)
    {
      switch (opts->x_ix86_cmodel)
	{
	case CM_SMALL:
	case CM_SMALL_PIC:
	  if (opts->x_flag_pic)
	    opts->x_ix86_cmodel = CM_SMALL_PIC;
	  if (!TARGET_64BIT_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in the %s bit mode",
		   "small", "32");
	  break;

	case CM_MEDIUM:
	case CM_MEDIUM_PIC:
	  if (opts->x_flag_pic)
	    opts->x_ix86_cmodel = CM_MEDIUM_PIC;
	  if (!TARGET_64BIT_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in the %s bit mode",
		   "medium", "32");
	  else if (TARGET_X32_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in x32 mode",
		   "medium");
	  break;

	case CM_LARGE:
	case CM_LARGE_PIC:
	  if (opts->x_flag_pic)
	    opts->x_ix86_cmodel = CM_LARGE_PIC;
	  if (!TARGET_64BIT_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in the %s bit mode",
		   "large", "32");
	  else if (TARGET_X32_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in x32 mode",
		   "large");
	  break;

	case CM_32:
	  if (opts->x_flag_pic)
	    error ("code model %s does not support PIC mode", "32");
	  if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in the %s bit mode",
		   "32", "64");
	  break;

	case CM_KERNEL:
	  if (opts->x_flag_pic)
	    {
	      error ("code model %s does not support PIC mode", "kernel");
	      opts->x_ix86_cmodel = CM_32;
	    }
	  if (!TARGET_64BIT_P (opts->x_ix86_isa_flags))
	    error ("code model %qs not supported in the %s bit mode",
		   "kernel", "32");
	  break;

	default:
	  gcc_unreachable ();
	}
    }
  else
    {
      /* For TARGET_64BIT and MS_ABI, force pic on, in order to enable the
	 use of rip-relative addressing.  This eliminates fixups that
	 would otherwise be needed if this object is to be placed in a
	 DLL, and is essentially just as efficient as direct addressing.  */
      if (TARGET_64BIT_P (opts->x_ix86_isa_flags)
	  && (TARGET_RDOS || TARGET_PECOFF))
	opts->x_ix86_cmodel = CM_MEDIUM_PIC, opts->x_flag_pic = 1;
      else if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
	opts->x_ix86_cmodel = opts->x_flag_pic ? CM_SMALL_PIC : CM_SMALL;
      else
	opts->x_ix86_cmodel = CM_32;
    }
  if (TARGET_MACHO && opts->x_ix86_asm_dialect == ASM_INTEL)
    {
      error ("-masm=intel not supported in this configuration");
      opts->x_ix86_asm_dialect = ASM_ATT;
    }
  if ((TARGET_64BIT_P (opts->x_ix86_isa_flags) != 0)
      != ((opts->x_ix86_isa_flags & OPTION_MASK_ISA_64BIT) != 0))
    sorry ("%i-bit mode not compiled in",
	   (opts->x_ix86_isa_flags & OPTION_MASK_ISA_64BIT) ? 64 : 32);

  for (i = 0; i < pta_size; i++)
    if (! strcmp (opts->x_ix86_arch_string, processor_alias_table[i].name))
      {
	if (!strcmp (opts->x_ix86_arch_string, "generic"))
	  {
	    error (main_args_p
		   ? G_("%<generic%> CPU can be used only for %<-mtune=%> "
			"switch")
		   : G_("%<generic%> CPU can be used only for "
			"%<target(\"tune=\")%> attribute"));
	    return false;
	  }
	else if (!strcmp (opts->x_ix86_arch_string, "intel"))
	  {
	    error (main_args_p
		   ? G_("%<intel%> CPU can be used only for %<-mtune=%> "
			"switch")
		   : G_("%<intel%> CPU can be used only for "
			"%<target(\"tune=\")%> attribute"));
	    return false;
	  }

	if (TARGET_64BIT_P (opts->x_ix86_isa_flags)
	    && !(processor_alias_table[i].flags & PTA_64BIT))
	  {
	    error ("CPU you selected does not support x86-64 "
		   "instruction set");
	    return false;
	  }

	ix86_schedule = processor_alias_table[i].schedule;
	ix86_arch = processor_alias_table[i].processor;
	/* Default cpu tuning to the architecture.  */
	ix86_tune = ix86_arch;

	if (processor_alias_table[i].flags & PTA_MMX
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_MMX))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_MMX;
	if (processor_alias_table[i].flags & PTA_3DNOW
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_3DNOW))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_3DNOW;
	if (processor_alias_table[i].flags & PTA_3DNOW_A
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_3DNOW_A))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_3DNOW_A;
	if (processor_alias_table[i].flags & PTA_SSE
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSE))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSE;
	if (processor_alias_table[i].flags & PTA_SSE2
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSE2))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSE2;
	if (processor_alias_table[i].flags & PTA_SSE3
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSE3))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSE3;
	if (processor_alias_table[i].flags & PTA_SSSE3
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSSE3))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSSE3;
	if (processor_alias_table[i].flags & PTA_SSE4_1
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSE4_1))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSE4_1;
	if (processor_alias_table[i].flags & PTA_SSE4_2
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSE4_2))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSE4_2;
	if (processor_alias_table[i].flags & PTA_AVX
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX;
	if (processor_alias_table[i].flags & PTA_AVX2
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX2))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX2;
	if (processor_alias_table[i].flags & PTA_FMA
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_FMA))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_FMA;
	if (processor_alias_table[i].flags & PTA_SSE4A
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SSE4A))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SSE4A;
	if (processor_alias_table[i].flags & PTA_FMA4
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_FMA4))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_FMA4;
	if (processor_alias_table[i].flags & PTA_XOP
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_XOP))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_XOP;
	if (processor_alias_table[i].flags & PTA_LWP
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_LWP))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_LWP;
	if (processor_alias_table[i].flags & PTA_ABM
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_ABM))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_ABM;
	if (processor_alias_table[i].flags & PTA_BMI
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_BMI))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_BMI;
	if (processor_alias_table[i].flags & (PTA_LZCNT | PTA_ABM)
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_LZCNT))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_LZCNT;
	if (processor_alias_table[i].flags & PTA_TBM
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_TBM))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_TBM;
	if (processor_alias_table[i].flags & PTA_BMI2
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_BMI2))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_BMI2;
	if (processor_alias_table[i].flags & PTA_CX16
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_CX16))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_CX16;
	if (processor_alias_table[i].flags & (PTA_POPCNT | PTA_ABM)
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_POPCNT))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_POPCNT;
	if (!(TARGET_64BIT_P (opts->x_ix86_isa_flags)
	    && (processor_alias_table[i].flags & PTA_NO_SAHF))
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_SAHF))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_SAHF;
	if (processor_alias_table[i].flags & PTA_MOVBE
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_MOVBE))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_MOVBE;
	if (processor_alias_table[i].flags & PTA_AES
	    && !(ix86_isa_flags_explicit & OPTION_MASK_ISA_AES))
	  ix86_isa_flags |= OPTION_MASK_ISA_AES;
	if (processor_alias_table[i].flags & PTA_SHA
	    && !(ix86_isa_flags_explicit & OPTION_MASK_ISA_SHA))
	  ix86_isa_flags |= OPTION_MASK_ISA_SHA;
	if (processor_alias_table[i].flags & PTA_PCLMUL
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_PCLMUL))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_PCLMUL;
	if (processor_alias_table[i].flags & PTA_FSGSBASE
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_FSGSBASE))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_FSGSBASE;
	if (processor_alias_table[i].flags & PTA_RDRND
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_RDRND))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_RDRND;
	if (processor_alias_table[i].flags & PTA_F16C
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_F16C))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_F16C;
	if (processor_alias_table[i].flags & PTA_RTM
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_RTM))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_RTM;
	if (processor_alias_table[i].flags & PTA_HLE
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_HLE))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_HLE;
	if (processor_alias_table[i].flags & PTA_PRFCHW
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_PRFCHW))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_PRFCHW;
	if (processor_alias_table[i].flags & PTA_RDSEED
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_RDSEED))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_RDSEED;
	if (processor_alias_table[i].flags & PTA_ADX
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_ADX))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_ADX;
	if (processor_alias_table[i].flags & PTA_FXSR
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_FXSR))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_FXSR;
	if (processor_alias_table[i].flags & PTA_XSAVE
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_XSAVE))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_XSAVE;
	if (processor_alias_table[i].flags & PTA_XSAVEOPT
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_XSAVEOPT))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_XSAVEOPT;
	if (processor_alias_table[i].flags & PTA_AVX512F
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512F))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512F;
	if (processor_alias_table[i].flags & PTA_AVX512ER
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512ER))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512ER;
	if (processor_alias_table[i].flags & PTA_AVX512PF
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512PF))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512PF;
	if (processor_alias_table[i].flags & PTA_AVX512CD
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512CD))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512CD;
	if (processor_alias_table[i].flags & PTA_PREFETCHWT1
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_PREFETCHWT1))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_PREFETCHWT1;
	if (processor_alias_table[i].flags & PTA_CLWB
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_CLWB))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_CLWB;
	if (processor_alias_table[i].flags & PTA_CLFLUSHOPT
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_CLFLUSHOPT))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_CLFLUSHOPT;
	if (processor_alias_table[i].flags & PTA_CLZERO
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_CLZERO))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_CLZERO;
	if (processor_alias_table[i].flags & PTA_XSAVEC
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_XSAVEC))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_XSAVEC;
	if (processor_alias_table[i].flags & PTA_XSAVES
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_XSAVES))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_XSAVES;
	if (processor_alias_table[i].flags & PTA_AVX512DQ
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512DQ))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512DQ;
	if (processor_alias_table[i].flags & PTA_AVX512BW
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512BW))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512BW;
	if (processor_alias_table[i].flags & PTA_AVX512VL
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512VL))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512VL;
        if (processor_alias_table[i].flags & PTA_MPX
            && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_MPX))
          opts->x_ix86_isa_flags |= OPTION_MASK_ISA_MPX;
	if (processor_alias_table[i].flags & PTA_AVX512VBMI
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512VBMI))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512VBMI;
	if (processor_alias_table[i].flags & PTA_AVX512IFMA
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_AVX512IFMA))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_AVX512IFMA;

	if (processor_alias_table[i].flags & PTA_AVX5124VNNIW
	    && !(opts->x_ix86_isa_flags2_explicit & OPTION_MASK_ISA_AVX5124VNNIW))
	  opts->x_ix86_isa_flags2 |= OPTION_MASK_ISA_AVX5124VNNIW;
	if (processor_alias_table[i].flags & PTA_AVX5124FMAPS
	    && !(opts->x_ix86_isa_flags2_explicit & OPTION_MASK_ISA_AVX5124FMAPS))
	  opts->x_ix86_isa_flags2 |= OPTION_MASK_ISA_AVX5124FMAPS;
	if (processor_alias_table[i].flags & PTA_AVX512VPOPCNTDQ
	    && !(opts->x_ix86_isa_flags2_explicit & OPTION_MASK_ISA_AVX512VPOPCNTDQ))
	  opts->x_ix86_isa_flags2 |= OPTION_MASK_ISA_AVX512VPOPCNTDQ;
	if (processor_alias_table[i].flags & PTA_SGX
	    && !(opts->x_ix86_isa_flags2_explicit & OPTION_MASK_ISA_SGX))
	  opts->x_ix86_isa_flags2 |= OPTION_MASK_ISA_SGX;

	if (processor_alias_table[i].flags & (PTA_PREFETCH_SSE | PTA_SSE))
	  x86_prefetch_sse = true;
	if (processor_alias_table[i].flags & PTA_MWAITX
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_MWAITX))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_MWAITX;
	if (processor_alias_table[i].flags & PTA_PKU
	    && !(opts->x_ix86_isa_flags_explicit & OPTION_MASK_ISA_PKU))
	  opts->x_ix86_isa_flags |= OPTION_MASK_ISA_PKU;

	/* Don't enable x87 instructions if only
	   general registers are allowed.  */
	if (!(opts_set->x_ix86_target_flags & OPTION_MASK_GENERAL_REGS_ONLY)
	    && !(opts_set->x_target_flags & MASK_80387))
	  {
	    if (processor_alias_table[i].flags & PTA_NO_80387)
	      opts->x_target_flags &= ~MASK_80387;
	    else
	      opts->x_target_flags |= MASK_80387;
	  }
	break;
      }

  if (TARGET_X32 && (opts->x_ix86_isa_flags & OPTION_MASK_ISA_MPX))
    error ("Intel MPX does not support x32");

  if (TARGET_X32 && (ix86_isa_flags & OPTION_MASK_ISA_MPX))
    error ("Intel MPX does not support x32");

  if (i == pta_size)
    {
      error (main_args_p
	     ? G_("bad value (%qs) for %<-march=%> switch")
	     : G_("bad value (%qs) for %<target(\"arch=\")%> attribute"),
	     opts->x_ix86_arch_string);

      auto_vec <const char *> candidates;
      for (i = 0; i < pta_size; i++)
	if (strcmp (processor_alias_table[i].name, "generic")
	    && strcmp (processor_alias_table[i].name, "intel")
	    && (!TARGET_64BIT_P (opts->x_ix86_isa_flags)
		|| (processor_alias_table[i].flags & PTA_64BIT)))
	  candidates.safe_push (processor_alias_table[i].name);

      char *s;
      const char *hint
	= candidates_list_and_hint (opts->x_ix86_arch_string, s, candidates);
      if (hint)
	inform (input_location,
		main_args_p
		? G_("valid arguments to %<-march=%> switch are: "
		     "%s; did you mean %qs?")
		: G_("valid arguments to %<target(\"arch=\")%> attribute are: "
		     "%s; did you mean %qs?"), s, hint);
      else
	inform (input_location,
		main_args_p
		? G_("valid arguments to %<-march=%> switch are: %s")
		: G_("valid arguments to %<target(\"arch=\")%> attribute "
		     "are: %s"), s);
      XDELETEVEC (s);
    }

  ix86_arch_mask = 1u << ix86_arch;
  for (i = 0; i < X86_ARCH_LAST; ++i)
    ix86_arch_features[i] = !!(initial_ix86_arch_features[i] & ix86_arch_mask);

  for (i = 0; i < pta_size; i++)
    if (! strcmp (opts->x_ix86_tune_string, processor_alias_table[i].name))
      {
	ix86_schedule = processor_alias_table[i].schedule;
	ix86_tune = processor_alias_table[i].processor;
	if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
	  {
	    if (!(processor_alias_table[i].flags & PTA_64BIT))
	      {
		if (ix86_tune_defaulted)
		  {
		    opts->x_ix86_tune_string = "x86-64";
		    for (i = 0; i < pta_size; i++)
		      if (! strcmp (opts->x_ix86_tune_string,
				    processor_alias_table[i].name))
			break;
		    ix86_schedule = processor_alias_table[i].schedule;
		    ix86_tune = processor_alias_table[i].processor;
		  }
		else
		  error ("CPU you selected does not support x86-64 "
			 "instruction set");
	      }
	  }
	/* Intel CPUs have always interpreted SSE prefetch instructions as
	   NOPs; so, we can enable SSE prefetch instructions even when
	   -mtune (rather than -march) points us to a processor that has them.
	   However, the VIA C3 gives a SIGILL, so we only do that for i686 and
	   higher processors.  */
	if (TARGET_CMOV
	    && (processor_alias_table[i].flags & (PTA_PREFETCH_SSE | PTA_SSE)))
	  x86_prefetch_sse = true;
	break;
      }

  if (ix86_tune_specified && i == pta_size)
    {
      error (main_args_p
	     ? G_("bad value (%qs) for %<-mtune=%> switch")
	     : G_("bad value (%qs) for %<target(\"tune=\")%> attribute"),
	     opts->x_ix86_tune_string);

      auto_vec <const char *> candidates;
      for (i = 0; i < pta_size; i++)
	if (!TARGET_64BIT_P (opts->x_ix86_isa_flags)
	    || (processor_alias_table[i].flags & PTA_64BIT))
	  candidates.safe_push (processor_alias_table[i].name);

      char *s;
      const char *hint
	= candidates_list_and_hint (opts->x_ix86_tune_string, s, candidates);
      if (hint)
	inform (input_location,
		main_args_p
		? G_("valid arguments to %<-mtune=%> switch are: "
		     "%s; did you mean %qs?")
		: G_("valid arguments to %<target(\"tune=\")%> attribute are: "
		     "%s; did you mean %qs?"), s, hint);
      else
	inform (input_location,
		main_args_p
		? G_("valid arguments to %<-mtune=%> switch are: %s")
		: G_("valid arguments to %<target(\"tune=\")%> attribute "
		     "are: %s"), s);
      XDELETEVEC (s);
    }

  set_ix86_tune_features (ix86_tune, opts->x_ix86_dump_tunes);

#ifndef USE_IX86_FRAME_POINTER
#define USE_IX86_FRAME_POINTER 0
#endif

#ifndef USE_X86_64_FRAME_POINTER
#define USE_X86_64_FRAME_POINTER 0
#endif

  /* Set the default values for switches whose default depends on TARGET_64BIT
     in case they weren't overwritten by command line options.  */
  if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
    {
      if (opts->x_optimize >= 1 && !opts_set->x_flag_omit_frame_pointer)
	opts->x_flag_omit_frame_pointer = !USE_X86_64_FRAME_POINTER;
      if (opts->x_flag_asynchronous_unwind_tables
	  && !opts_set->x_flag_unwind_tables
	  && TARGET_64BIT_MS_ABI)
	opts->x_flag_unwind_tables = 1;
      if (opts->x_flag_asynchronous_unwind_tables == 2)
	opts->x_flag_unwind_tables
	  = opts->x_flag_asynchronous_unwind_tables = 1;
      if (opts->x_flag_pcc_struct_return == 2)
	opts->x_flag_pcc_struct_return = 0;
    }
  else
    {
      if (opts->x_optimize >= 1 && !opts_set->x_flag_omit_frame_pointer)
	opts->x_flag_omit_frame_pointer
	  = !(USE_IX86_FRAME_POINTER || opts->x_optimize_size);
      if (opts->x_flag_asynchronous_unwind_tables == 2)
	opts->x_flag_asynchronous_unwind_tables = !USE_IX86_FRAME_POINTER;
      if (opts->x_flag_pcc_struct_return == 2)
	{
	  /* Intel MCU psABI specifies that -freg-struct-return should
	     be on.  Instead of setting DEFAULT_PCC_STRUCT_RETURN to 1,
	     we check -miamcu so that -freg-struct-return is always
	     turned on if -miamcu is used.  */
	  if (TARGET_IAMCU_P (opts->x_target_flags))
	    opts->x_flag_pcc_struct_return = 0;
	  else
	    opts->x_flag_pcc_struct_return = DEFAULT_PCC_STRUCT_RETURN;
	}
    }

  ix86_tune_cost = processor_target_table[ix86_tune].cost;
  /* TODO: ix86_cost should be chosen at instruction or function granuality
     so for cold code we use size_cost even in !optimize_size compilation.  */
  if (opts->x_optimize_size)
    ix86_cost = &ix86_size_cost;
  else
    ix86_cost = ix86_tune_cost;

  /* Arrange to set up i386_stack_locals for all functions.  */
  init_machine_status = ix86_init_machine_status;

  /* Validate -mregparm= value.  */
  if (opts_set->x_ix86_regparm)
    {
      if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
	warning (0, "-mregparm is ignored in 64-bit mode");
      else if (TARGET_IAMCU_P (opts->x_target_flags))
	warning (0, "-mregparm is ignored for Intel MCU psABI");
      if (opts->x_ix86_regparm > REGPARM_MAX)
	{
	  error ("-mregparm=%d is not between 0 and %d",
		 opts->x_ix86_regparm, REGPARM_MAX);
	  opts->x_ix86_regparm = 0;
	}
    }
  if (TARGET_IAMCU_P (opts->x_target_flags)
      || TARGET_64BIT_P (opts->x_ix86_isa_flags))
    opts->x_ix86_regparm = REGPARM_MAX;

  /* Default align_* from the processor table.  */
  ix86_default_align (opts);

  /* Provide default for -mbranch-cost= value.  */
  if (!opts_set->x_ix86_branch_cost)
    opts->x_ix86_branch_cost = ix86_tune_cost->branch_cost;

  if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
    {
      opts->x_target_flags
	|= TARGET_SUBTARGET64_DEFAULT & ~opts_set->x_target_flags;

      /* Enable by default the SSE and MMX builtins.  Do allow the user to
	 explicitly disable any of these.  In particular, disabling SSE and
	 MMX for kernel code is extremely useful.  */
      if (!ix86_arch_specified)
      opts->x_ix86_isa_flags
	|= ((OPTION_MASK_ISA_SSE2 | OPTION_MASK_ISA_SSE | OPTION_MASK_ISA_MMX
	     | TARGET_SUBTARGET64_ISA_DEFAULT)
            & ~opts->x_ix86_isa_flags_explicit);

      if (TARGET_RTD_P (opts->x_target_flags))
	warning (0,
		 main_args_p
		 ? G_("%<-mrtd%> is ignored in 64bit mode")
		 : G_("%<target(\"rtd\")%> is ignored in 64bit mode"));
    }
  else
    {
      opts->x_target_flags
	|= TARGET_SUBTARGET32_DEFAULT & ~opts_set->x_target_flags;

      if (!ix86_arch_specified)
        opts->x_ix86_isa_flags
	  |= TARGET_SUBTARGET32_ISA_DEFAULT & ~opts->x_ix86_isa_flags_explicit;

      /* i386 ABI does not specify red zone.  It still makes sense to use it
         when programmer takes care to stack from being destroyed.  */
      if (!(opts_set->x_target_flags & MASK_NO_RED_ZONE))
        opts->x_target_flags |= MASK_NO_RED_ZONE;
    }

  /* Keep nonleaf frame pointers.  */
  if (opts->x_flag_omit_frame_pointer)
    opts->x_target_flags &= ~MASK_OMIT_LEAF_FRAME_POINTER;
  else if (TARGET_OMIT_LEAF_FRAME_POINTER_P (opts->x_target_flags))
    opts->x_flag_omit_frame_pointer = 1;

  /* If we're doing fast math, we don't care about comparison order
     wrt NaNs.  This lets us use a shorter comparison sequence.  */
  if (opts->x_flag_finite_math_only)
    opts->x_target_flags &= ~MASK_IEEE_FP;

  /* If the architecture always has an FPU, turn off NO_FANCY_MATH_387,
     since the insns won't need emulation.  */
  if (ix86_tune_features [X86_TUNE_ALWAYS_FANCY_MATH_387])
    opts->x_target_flags &= ~MASK_NO_FANCY_MATH_387;

  /* Likewise, if the target doesn't have a 387, or we've specified
     software floating point, don't use 387 inline intrinsics.  */
  if (!TARGET_80387_P (opts->x_target_flags))
    opts->x_target_flags |= MASK_NO_FANCY_MATH_387;

  /* Turn on MMX builtins for -msse.  */
  if (TARGET_SSE_P (opts->x_ix86_isa_flags))
    opts->x_ix86_isa_flags
      |= OPTION_MASK_ISA_MMX & ~opts->x_ix86_isa_flags_explicit;

  /* Enable SSE prefetch.  */
  if (TARGET_SSE_P (opts->x_ix86_isa_flags)
      || (TARGET_PRFCHW_P (opts->x_ix86_isa_flags)
	  && !TARGET_3DNOW_P (opts->x_ix86_isa_flags))
      || TARGET_PREFETCHWT1_P (opts->x_ix86_isa_flags))
    x86_prefetch_sse = true;

  /* Enable popcnt instruction for -msse4.2 or -mabm.  */
  if (TARGET_SSE4_2_P (opts->x_ix86_isa_flags)
      || TARGET_ABM_P (opts->x_ix86_isa_flags))
    opts->x_ix86_isa_flags
      |= OPTION_MASK_ISA_POPCNT & ~opts->x_ix86_isa_flags_explicit;

  /* Enable lzcnt instruction for -mabm.  */
  if (TARGET_ABM_P(opts->x_ix86_isa_flags))
    opts->x_ix86_isa_flags
      |= OPTION_MASK_ISA_LZCNT & ~opts->x_ix86_isa_flags_explicit;

  /* Disable BMI, BMI2 and TBM instructions for -m16.  */
  if (TARGET_16BIT_P(opts->x_ix86_isa_flags))
    opts->x_ix86_isa_flags
      &= ~((OPTION_MASK_ISA_BMI | OPTION_MASK_ISA_BMI2 | OPTION_MASK_ISA_TBM)
	   & ~opts->x_ix86_isa_flags_explicit);

  /* Validate -mpreferred-stack-boundary= value or default it to
     PREFERRED_STACK_BOUNDARY_DEFAULT.  */
  ix86_preferred_stack_boundary = PREFERRED_STACK_BOUNDARY_DEFAULT;
  if (opts_set->x_ix86_preferred_stack_boundary_arg)
    {
      int min = TARGET_64BIT_P (opts->x_ix86_isa_flags)? 3 : 2;
      int max = TARGET_SEH ? 4 : 12;

      if (opts->x_ix86_preferred_stack_boundary_arg < min
	  || opts->x_ix86_preferred_stack_boundary_arg > max)
	{
	  if (min == max)
	    error ("-mpreferred-stack-boundary is not supported "
		   "for this target");
	  else
	    error ("-mpreferred-stack-boundary=%d is not between %d and %d",
		   opts->x_ix86_preferred_stack_boundary_arg, min, max);
	}
      else
	ix86_preferred_stack_boundary
	  = (1 << opts->x_ix86_preferred_stack_boundary_arg) * BITS_PER_UNIT;
    }

  /* Set the default value for -mstackrealign.  */
  if (!opts_set->x_ix86_force_align_arg_pointer)
    opts->x_ix86_force_align_arg_pointer = STACK_REALIGN_DEFAULT;

  ix86_default_incoming_stack_boundary = PREFERRED_STACK_BOUNDARY;

  /* Validate -mincoming-stack-boundary= value or default it to
     MIN_STACK_BOUNDARY/PREFERRED_STACK_BOUNDARY.  */
  ix86_incoming_stack_boundary = ix86_default_incoming_stack_boundary;
  if (opts_set->x_ix86_incoming_stack_boundary_arg)
    {
      int min = TARGET_64BIT_P (opts->x_ix86_isa_flags) ? 3 : 2;

      if (opts->x_ix86_incoming_stack_boundary_arg < min
	  || opts->x_ix86_incoming_stack_boundary_arg > 12)
	error ("-mincoming-stack-boundary=%d is not between %d and 12",
	       opts->x_ix86_incoming_stack_boundary_arg, min);
      else
	{
	  ix86_user_incoming_stack_boundary
	    = (1 << opts->x_ix86_incoming_stack_boundary_arg) * BITS_PER_UNIT;
	  ix86_incoming_stack_boundary
	    = ix86_user_incoming_stack_boundary;
	}
    }

#ifndef NO_PROFILE_COUNTERS
  if (flag_nop_mcount)
    error ("-mnop-mcount is not compatible with this target");
#endif
  if (flag_nop_mcount && flag_pic)
    error ("-mnop-mcount is not implemented for -fPIC");

  /* Accept -msseregparm only if at least SSE support is enabled.  */
  if (TARGET_SSEREGPARM_P (opts->x_target_flags)
      && ! TARGET_SSE_P (opts->x_ix86_isa_flags))
    error (main_args_p
	   ? G_("%<-msseregparm%> used without SSE enabled")
	   : G_("%<target(\"sseregparm\")%> used without SSE enabled"));

  if (opts_set->x_ix86_fpmath)
    {
      if (opts->x_ix86_fpmath & FPMATH_SSE)
	{
	  if (!TARGET_SSE_P (opts->x_ix86_isa_flags))
	    {
	      if (TARGET_80387_P (opts->x_target_flags))
		{
		  warning (0, "SSE instruction set disabled, using 387 arithmetics");
		  opts->x_ix86_fpmath = FPMATH_387;
		}
	    }
	  else if ((opts->x_ix86_fpmath & FPMATH_387)
		   && !TARGET_80387_P (opts->x_target_flags))
	    {
	      warning (0, "387 instruction set disabled, using SSE arithmetics");
	      opts->x_ix86_fpmath = FPMATH_SSE;
	    }
	}
    }
  /* For all chips supporting SSE2, -mfpmath=sse performs better than
     fpmath=387.  The second is however default at many targets since the
     extra 80bit precision of temporaries is considered to be part of ABI.
     Overwrite the default at least for -ffast-math. 
     TODO: -mfpmath=both seems to produce same performing code with bit
     smaller binaries.  It is however not clear if register allocation is
     ready for this setting.
     Also -mfpmath=387 is overall a lot more compact (bout 4-5%) than SSE
     codegen.  We may switch to 387 with -ffast-math for size optimized
     functions. */
  else if (fast_math_flags_set_p (&global_options)
	   && TARGET_SSE2_P (opts->x_ix86_isa_flags))
    opts->x_ix86_fpmath = FPMATH_SSE;
  else
    opts->x_ix86_fpmath = TARGET_FPMATH_DEFAULT_P (opts->x_ix86_isa_flags);

  /* Use external vectorized library in vectorizing intrinsics.  */
  if (opts_set->x_ix86_veclibabi_type)
    switch (opts->x_ix86_veclibabi_type)
      {
      case ix86_veclibabi_type_svml:
	ix86_veclib_handler = ix86_veclibabi_svml;
	break;

      case ix86_veclibabi_type_acml:
	ix86_veclib_handler = ix86_veclibabi_acml;
	break;

      default:
	gcc_unreachable ();
      }

  if (ix86_tune_features [X86_TUNE_ACCUMULATE_OUTGOING_ARGS]
      && !(opts_set->x_target_flags & MASK_ACCUMULATE_OUTGOING_ARGS))
    opts->x_target_flags |= MASK_ACCUMULATE_OUTGOING_ARGS;

  /* If stack probes are required, the space used for large function
     arguments on the stack must also be probed, so enable
     -maccumulate-outgoing-args so this happens in the prologue.  */
  if (TARGET_STACK_PROBE_P (opts->x_target_flags)
      && !(opts->x_target_flags & MASK_ACCUMULATE_OUTGOING_ARGS))
    {
      if (opts_set->x_target_flags & MASK_ACCUMULATE_OUTGOING_ARGS)
	warning (0,
		 main_args_p
		 ? G_("stack probing requires %<-maccumulate-outgoing-args%> "
		      "for correctness")
		 : G_("stack probing requires "
		      "%<target(\"accumulate-outgoing-args\")%> for "
		      "correctness"));
      opts->x_target_flags |= MASK_ACCUMULATE_OUTGOING_ARGS;
    }

  /* Stack realignment without -maccumulate-outgoing-args requires %ebp,
     so enable -maccumulate-outgoing-args when %ebp is fixed.  */
  if (fixed_regs[BP_REG]
      && !(opts->x_target_flags & MASK_ACCUMULATE_OUTGOING_ARGS))
    {
      if (opts_set->x_target_flags & MASK_ACCUMULATE_OUTGOING_ARGS)
	warning (0,
		 main_args_p
		 ? G_("fixed ebp register requires "
		      "%<-maccumulate-outgoing-args%>")
		 : G_("fixed ebp register requires "
		      "%<target(\"accumulate-outgoing-args\")%>"));
      opts->x_target_flags |= MASK_ACCUMULATE_OUTGOING_ARGS;
    }

  /* Figure out what ASM_GENERATE_INTERNAL_LABEL builds as a prefix.  */
  {
    char *p;
    ASM_GENERATE_INTERNAL_LABEL (internal_label_prefix, "LX", 0);
    p = strchr (internal_label_prefix, 'X');
    internal_label_prefix_len = p - internal_label_prefix;
    *p = '\0';
  }

  /* When scheduling description is not available, disable scheduler pass
     so it won't slow down the compilation and make x87 code slower.  */
  if (!TARGET_SCHEDULE)
    opts->x_flag_schedule_insns_after_reload = opts->x_flag_schedule_insns = 0;

  maybe_set_param_value (PARAM_SIMULTANEOUS_PREFETCHES,
			 ix86_tune_cost->simultaneous_prefetches,
			 opts->x_param_values,
			 opts_set->x_param_values);
  maybe_set_param_value (PARAM_L1_CACHE_LINE_SIZE,
			 ix86_tune_cost->prefetch_block,
			 opts->x_param_values,
			 opts_set->x_param_values);
  maybe_set_param_value (PARAM_L1_CACHE_SIZE,
			 ix86_tune_cost->l1_cache_size,
			 opts->x_param_values,
			 opts_set->x_param_values);
  maybe_set_param_value (PARAM_L2_CACHE_SIZE,
			 ix86_tune_cost->l2_cache_size,
			 opts->x_param_values,
			 opts_set->x_param_values);

  /* Enable sw prefetching at -O3 for CPUS that prefetching is helpful.  */
  if (opts->x_flag_prefetch_loop_arrays < 0
      && HAVE_prefetch
      && (opts->x_optimize >= 3 || opts->x_flag_profile_use)
      && !opts->x_optimize_size
      && TARGET_SOFTWARE_PREFETCHING_BENEFICIAL)
    opts->x_flag_prefetch_loop_arrays = 1;

  /* If using typedef char *va_list, signal that __builtin_va_start (&ap, 0)
     can be opts->x_optimized to ap = __builtin_next_arg (0).  */
  if (!TARGET_64BIT_P (opts->x_ix86_isa_flags) && !opts->x_flag_split_stack)
    targetm.expand_builtin_va_start = NULL;

  if (TARGET_64BIT_P (opts->x_ix86_isa_flags))
    {
      ix86_gen_leave = gen_leave_rex64;
      if (Pmode == DImode)
	{
	  ix86_gen_tls_global_dynamic_64 = gen_tls_global_dynamic_64_di;
	  ix86_gen_tls_local_dynamic_base_64
	    = gen_tls_local_dynamic_base_64_di;
	}
      else
	{
	  ix86_gen_tls_global_dynamic_64 = gen_tls_global_dynamic_64_si;
	  ix86_gen_tls_local_dynamic_base_64
	    = gen_tls_local_dynamic_base_64_si;
	}
    }
  else
    ix86_gen_leave = gen_leave;

  if (Pmode == DImode)
    {
      ix86_gen_add3 = gen_adddi3;
      ix86_gen_sub3 = gen_subdi3;
      ix86_gen_sub3_carry = gen_subdi3_carry;
      ix86_gen_one_cmpl2 = gen_one_cmpldi2;
      ix86_gen_andsp = gen_anddi3;
      ix86_gen_allocate_stack_worker = gen_allocate_stack_worker_probe_di;
      ix86_gen_adjust_stack_and_probe = gen_adjust_stack_and_probedi;
      ix86_gen_probe_stack_range = gen_probe_stack_rangedi;
      ix86_gen_monitor = gen_sse3_monitor_di;
      ix86_gen_monitorx = gen_monitorx_di;
      ix86_gen_clzero = gen_clzero_di;
    }
  else
    {
      ix86_gen_add3 = gen_addsi3;
      ix86_gen_sub3 = gen_subsi3;
      ix86_gen_sub3_carry = gen_subsi3_carry;
      ix86_gen_one_cmpl2 = gen_one_cmplsi2;
      ix86_gen_andsp = gen_andsi3;
      ix86_gen_allocate_stack_worker = gen_allocate_stack_worker_probe_si;
      ix86_gen_adjust_stack_and_probe = gen_adjust_stack_and_probesi;
      ix86_gen_probe_stack_range = gen_probe_stack_rangesi;
      ix86_gen_monitor = gen_sse3_monitor_si;
      ix86_gen_monitorx = gen_monitorx_si;
      ix86_gen_clzero = gen_clzero_si;
    }

#ifdef USE_IX86_CLD
  /* Use -mcld by default for 32-bit code if configured with --enable-cld.  */
  if (!TARGET_64BIT_P (opts->x_ix86_isa_flags))
    opts->x_target_flags |= MASK_CLD & ~opts_set->x_target_flags;
#endif

  /* Set the default value for -mfentry.  */
  if (!opts_set->x_flag_fentry)
    opts->x_flag_fentry = TARGET_SEH;
  else
    {
      if (!TARGET_64BIT_P (opts->x_ix86_isa_flags) && opts->x_flag_pic
	  && opts->x_flag_fentry)
	sorry ("-mfentry isn%'t supported for 32-bit in combination "
	       "with -fpic");
      else if (TARGET_SEH && !opts->x_flag_fentry)
	sorry ("-mno-fentry isn%'t compatible with SEH");
    }

  if (TARGET_SEH && TARGET_CALL_MS2SYSV_XLOGUES)
    sorry ("-mcall-ms2sysv-xlogues isn%'t currently supported with SEH");

  if (!(opts_set->x_target_flags & MASK_VZEROUPPER))
    opts->x_target_flags |= MASK_VZEROUPPER;
  if (!(opts_set->x_target_flags & MASK_STV))
    opts->x_target_flags |= MASK_STV;
  /* Disable STV if -mpreferred-stack-boundary={2,3} or
     -mincoming-stack-boundary={2,3} or -mstackrealign - the needed
     stack realignment will be extra cost the pass doesn't take into
     account and the pass can't realign the stack.  */
  if (ix86_preferred_stack_boundary < 128
      || ix86_incoming_stack_boundary < 128
      || opts->x_ix86_force_align_arg_pointer)
    opts->x_target_flags &= ~MASK_STV;
  if (!ix86_tune_features[X86_TUNE_AVX256_UNALIGNED_LOAD_OPTIMAL]
      && !(opts_set->x_target_flags & MASK_AVX256_SPLIT_UNALIGNED_LOAD))
    opts->x_target_flags |= MASK_AVX256_SPLIT_UNALIGNED_LOAD;
  if (!ix86_tune_features[X86_TUNE_AVX256_UNALIGNED_STORE_OPTIMAL]
      && !(opts_set->x_target_flags & MASK_AVX256_SPLIT_UNALIGNED_STORE))
    opts->x_target_flags |= MASK_AVX256_SPLIT_UNALIGNED_STORE;
  /* Enable 128-bit AVX instruction generation
     for the auto-vectorizer.  */
  if (TARGET_AVX128_OPTIMAL
      && !(opts_set->x_target_flags & MASK_PREFER_AVX128))
    opts->x_target_flags |= MASK_PREFER_AVX128;

  if (opts->x_ix86_recip_name)
    {
      char *p = ASTRDUP (opts->x_ix86_recip_name);
      char *q;
      unsigned int mask, i;
      bool invert;

      while ((q = strtok (p, ",")) != NULL)
	{
	  p = NULL;
	  if (*q == '!')
	    {
	      invert = true;
	      q++;
	    }
	  else
	    invert = false;

	  if (!strcmp (q, "default"))
	    mask = RECIP_MASK_ALL;
	  else
	    {
	      for (i = 0; i < ARRAY_SIZE (recip_options); i++)
		if (!strcmp (q, recip_options[i].string))
		  {
		    mask = recip_options[i].mask;
		    break;
		  }

	      if (i == ARRAY_SIZE (recip_options))
		{
		  error ("unknown option for -mrecip=%s", q);
		  invert = false;
		  mask = RECIP_MASK_NONE;
		}
	    }

	  opts->x_recip_mask_explicit |= mask;
	  if (invert)
	    opts->x_recip_mask &= ~mask;
	  else
	    opts->x_recip_mask |= mask;
	}
    }

  if (TARGET_RECIP_P (opts->x_target_flags))
    opts->x_recip_mask |= RECIP_MASK_ALL & ~opts->x_recip_mask_explicit;
  else if (opts_set->x_target_flags & MASK_RECIP)
    opts->x_recip_mask &= ~(RECIP_MASK_ALL & ~opts->x_recip_mask_explicit);

  /* Default long double to 64-bit for 32-bit Bionic and to __float128
     for 64-bit Bionic.  Also default long double to 64-bit for Intel
     MCU psABI.  */
  if ((TARGET_HAS_BIONIC || TARGET_IAMCU)
      && !(opts_set->x_target_flags
	   & (MASK_LONG_DOUBLE_64 | MASK_LONG_DOUBLE_128)))
    opts->x_target_flags |= (TARGET_64BIT
			     ? MASK_LONG_DOUBLE_128
			     : MASK_LONG_DOUBLE_64);

  /* Only one of them can be active.  */
  gcc_assert ((opts->x_target_flags & MASK_LONG_DOUBLE_64) == 0
	      || (opts->x_target_flags & MASK_LONG_DOUBLE_128) == 0);

  /* Handle stack protector */
  if (!opts_set->x_ix86_stack_protector_guard)
    opts->x_ix86_stack_protector_guard
      = TARGET_HAS_BIONIC ? SSP_GLOBAL : SSP_TLS;

#ifdef TARGET_THREAD_SSP_OFFSET
  ix86_stack_protector_guard_offset = TARGET_THREAD_SSP_OFFSET;
#endif

  if (global_options_set.x_ix86_stack_protector_guard_offset_str)
    {
      char *endp;
      const char *str = ix86_stack_protector_guard_offset_str;

      errno = 0;
      int64_t offset;

#if defined(INT64_T_IS_LONG)
      offset = strtol (str, &endp, 0);
#else
      offset = strtoll (str, &endp, 0);
#endif

      if (!*str || *endp || errno)
	error ("%qs is not a valid number "
	       "in -mstack-protector-guard-offset=", str);

      if (!IN_RANGE (offset, HOST_WIDE_INT_C (-0x80000000),
		     HOST_WIDE_INT_C (0x7fffffff)))
	error ("%qs is not a valid offset "
	       "in -mstack-protector-guard-offset=", str);

      ix86_stack_protector_guard_offset = offset;
    }

  ix86_stack_protector_guard_reg = DEFAULT_TLS_SEG_REG;

  /* The kernel uses a different segment register for performance
     reasons; a system call would not have to trash the userspace
     segment register, which would be expensive.  */
  if (ix86_cmodel == CM_KERNEL)
    ix86_stack_protector_guard_reg = ADDR_SPACE_SEG_GS;

  if (global_options_set.x_ix86_stack_protector_guard_reg_str)
    {
      const char *str = ix86_stack_protector_guard_reg_str;
      addr_space_t seg = ADDR_SPACE_GENERIC;

      /* Discard optional register prefix.  */
      if (str[0] == '%')
	str++;

      if (strlen (str) == 2 && str[1] == 's')
	{
	  if (str[0] == 'f')
	    seg = ADDR_SPACE_SEG_FS;
	  else if (str[0] == 'g')
	    seg = ADDR_SPACE_SEG_GS;
	}

      if (seg == ADDR_SPACE_GENERIC)
	error ("%qs is not a valid base register "
	       "in -mstack-protector-guard-reg=",
	       ix86_stack_protector_guard_reg_str);

      ix86_stack_protector_guard_reg = seg;
    }

  /* Handle -mmemcpy-strategy= and -mmemset-strategy=  */
  if (opts->x_ix86_tune_memcpy_strategy)
    {
      char *str = xstrdup (opts->x_ix86_tune_memcpy_strategy);
      ix86_parse_stringop_strategy_string (str, false);
      free (str);
    }

  if (opts->x_ix86_tune_memset_strategy)
    {
      char *str = xstrdup (opts->x_ix86_tune_memset_strategy);
      ix86_parse_stringop_strategy_string (str, true);
      free (str);
    }

  /* Save the initial options in case the user does function specific
     options.  */
  if (main_args_p)
    target_option_default_node = target_option_current_node
      = build_target_option_node (opts);

  return true;
}

/* Implement the TARGET_OPTION_OVERRIDE hook.  */

static void
ix86_option_override (void)
{
  ix86_option_override_internal (true, &global_options, &global_options_set);
}

/* Implement the TARGET_OFFLOAD_OPTIONS hook.  */
static char *
ix86_offload_options (void)
{
  if (TARGET_LP64)
    return xstrdup ("-foffload-abi=lp64");
  return xstrdup ("-foffload-abi=ilp32");
}

/* Update register usage after having seen the compiler flags.  */

static void
ix86_conditional_register_usage (void)
{
  int i, c_mask;

  /* If there are no caller-saved registers, preserve all registers.
     except fixed_regs and registers used for function return value
     since aggregate_value_p checks call_used_regs[regno] on return
     value.  */
  if (cfun && cfun->machine->no_caller_saved_registers)
    for (i = 0; i < FIRST_PSEUDO_REGISTER; i++)
      if (!fixed_regs[i] && !ix86_function_value_regno_p (i))
	call_used_regs[i] = 0;

  /* For 32-bit targets, squash the REX registers.  */
  if (! TARGET_64BIT)
    {
      for (i = FIRST_REX_INT_REG; i <= LAST_REX_INT_REG; i++)
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";
      for (i = FIRST_REX_SSE_REG; i <= LAST_REX_SSE_REG; i++)
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";
      for (i = FIRST_EXT_REX_SSE_REG; i <= LAST_EXT_REX_SSE_REG; i++)
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";
    }

  /*  See the definition of CALL_USED_REGISTERS in i386.h.  */
  c_mask = CALL_USED_REGISTERS_MASK (TARGET_64BIT_MS_ABI);
  
  CLEAR_HARD_REG_SET (reg_class_contents[(int)CLOBBERED_REGS]);

  for (i = 0; i < FIRST_PSEUDO_REGISTER; i++)
    {
      /* Set/reset conditionally defined registers from
	 CALL_USED_REGISTERS initializer.  */
      if (call_used_regs[i] > 1)
	call_used_regs[i] = !!(call_used_regs[i] & c_mask);

      /* Calculate registers of CLOBBERED_REGS register set
	 as call used registers from GENERAL_REGS register set.  */
      if (TEST_HARD_REG_BIT (reg_class_contents[(int)GENERAL_REGS], i)
	  && call_used_regs[i])
	SET_HARD_REG_BIT (reg_class_contents[(int)CLOBBERED_REGS], i);
    }

  /* If MMX is disabled, squash the registers.  */
  if (! TARGET_MMX)
    for (i = 0; i < FIRST_PSEUDO_REGISTER; i++)
      if (TEST_HARD_REG_BIT (reg_class_contents[(int)MMX_REGS], i))
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";

  /* If SSE is disabled, squash the registers.  */
  if (! TARGET_SSE)
    for (i = 0; i < FIRST_PSEUDO_REGISTER; i++)
      if (TEST_HARD_REG_BIT (reg_class_contents[(int)SSE_REGS], i))
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";

  /* If the FPU is disabled, squash the registers.  */
  if (! (TARGET_80387 || TARGET_FLOAT_RETURNS_IN_80387))
    for (i = 0; i < FIRST_PSEUDO_REGISTER; i++)
      if (TEST_HARD_REG_BIT (reg_class_contents[(int)FLOAT_REGS], i))
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";

  /* If AVX512F is disabled, squash the registers.  */
  if (! TARGET_AVX512F)
    {
      for (i = FIRST_EXT_REX_SSE_REG; i <= LAST_EXT_REX_SSE_REG; i++)
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";

      for (i = FIRST_MASK_REG; i <= LAST_MASK_REG; i++)
	fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";
    }

  /* If MPX is disabled, squash the registers.  */
  if (! TARGET_MPX)
    for (i = FIRST_BND_REG; i <= LAST_BND_REG; i++)
      fixed_regs[i] = call_used_regs[i] = 1, reg_names[i] = "";
}


/* Save the current options */

static void
ix86_function_specific_save (struct cl_target_option *ptr,
			     struct gcc_options *opts)
{
  ptr->arch = ix86_arch;
  ptr->schedule = ix86_schedule;
  ptr->prefetch_sse = x86_prefetch_sse;
  ptr->tune = ix86_tune;
  ptr->branch_cost = ix86_branch_cost;
  ptr->tune_defaulted = ix86_tune_defaulted;
  ptr->arch_specified = ix86_arch_specified;
  ptr->x_ix86_isa_flags_explicit = opts->x_ix86_isa_flags_explicit;
  ptr->x_ix86_isa_flags2_explicit = opts->x_ix86_isa_flags2_explicit;
  ptr->x_recip_mask_explicit = opts->x_recip_mask_explicit;
  ptr->x_ix86_arch_string = opts->x_ix86_arch_string;
  ptr->x_ix86_tune_string = opts->x_ix86_tune_string;
  ptr->x_ix86_cmodel = opts->x_ix86_cmodel;
  ptr->x_ix86_abi = opts->x_ix86_abi;
  ptr->x_ix86_asm_dialect = opts->x_ix86_asm_dialect;
  ptr->x_ix86_branch_cost = opts->x_ix86_branch_cost;
  ptr->x_ix86_dump_tunes = opts->x_ix86_dump_tunes;
  ptr->x_ix86_force_align_arg_pointer = opts->x_ix86_force_align_arg_pointer;
  ptr->x_ix86_force_drap = opts->x_ix86_force_drap;
  ptr->x_ix86_incoming_stack_boundary_arg = opts->x_ix86_incoming_stack_boundary_arg;
  ptr->x_ix86_pmode = opts->x_ix86_pmode;
  ptr->x_ix86_preferred_stack_boundary_arg = opts->x_ix86_preferred_stack_boundary_arg;
  ptr->x_ix86_recip_name = opts->x_ix86_recip_name;
  ptr->x_ix86_regparm = opts->x_ix86_regparm;
  ptr->x_ix86_section_threshold = opts->x_ix86_section_threshold;
  ptr->x_ix86_sse2avx = opts->x_ix86_sse2avx;
  ptr->x_ix86_stack_protector_guard = opts->x_ix86_stack_protector_guard;
  ptr->x_ix86_stringop_alg = opts->x_ix86_stringop_alg;
  ptr->x_ix86_tls_dialect = opts->x_ix86_tls_dialect;
  ptr->x_ix86_tune_ctrl_string = opts->x_ix86_tune_ctrl_string;
  ptr->x_ix86_tune_memcpy_strategy = opts->x_ix86_tune_memcpy_strategy;
  ptr->x_ix86_tune_memset_strategy = opts->x_ix86_tune_memset_strategy;
  ptr->x_ix86_tune_no_default = opts->x_ix86_tune_no_default;
  ptr->x_ix86_veclibabi_type = opts->x_ix86_veclibabi_type;

  /* The fields are char but the variables are not; make sure the
     values fit in the fields.  */
  gcc_assert (ptr->arch == ix86_arch);
  gcc_assert (ptr->schedule == ix86_schedule);
  gcc_assert (ptr->tune == ix86_tune);
  gcc_assert (ptr->branch_cost == ix86_branch_cost);
}

/* Restore the current options */

static void
ix86_function_specific_restore (struct gcc_options *opts,
				struct cl_target_option *ptr)
{
  enum processor_type old_tune = ix86_tune;
  enum processor_type old_arch = ix86_arch;
  unsigned int ix86_arch_mask;
  int i;

  /* We don't change -fPIC.  */
  opts->x_flag_pic = flag_pic;

  ix86_arch = (enum processor_type) ptr->arch;
  ix86_schedule = (enum attr_cpu) ptr->schedule;
  ix86_tune = (enum processor_type) ptr->tune;
  x86_prefetch_sse = ptr->prefetch_sse;
  opts->x_ix86_branch_cost = ptr->branch_cost;
  ix86_tune_defaulted = ptr->tune_defaulted;
  ix86_arch_specified = ptr->arch_specified;
  opts->x_ix86_isa_flags_explicit = ptr->x_ix86_isa_flags_explicit;
  opts->x_ix86_isa_flags2_explicit = ptr->x_ix86_isa_flags2_explicit;
  opts->x_recip_mask_explicit = ptr->x_recip_mask_explicit;
  opts->x_ix86_arch_string = ptr->x_ix86_arch_string;
  opts->x_ix86_tune_string = ptr->x_ix86_tune_string;
  opts->x_ix86_cmodel = ptr->x_ix86_cmodel;
  opts->x_ix86_abi = ptr->x_ix86_abi;
  opts->x_ix86_asm_dialect = ptr->x_ix86_asm_dialect;
  opts->x_ix86_branch_cost = ptr->x_ix86_branch_cost;
  opts->x_ix86_dump_tunes = ptr->x_ix86_dump_tunes;
  opts->x_ix86_force_align_arg_pointer = ptr->x_ix86_force_align_arg_pointer;
  opts->x_ix86_force_drap = ptr->x_ix86_force_drap;
  opts->x_ix86_incoming_stack_boundary_arg = ptr->x_ix86_incoming_stack_boundary_arg;
  opts->x_ix86_pmode = ptr->x_ix86_pmode;
  opts->x_ix86_preferred_stack_boundary_arg = ptr->x_ix86_preferred_stack_boundary_arg;
  opts->x_ix86_recip_name = ptr->x_ix86_recip_name;
  opts->x_ix86_regparm = ptr->x_ix86_regparm;
  opts->x_ix86_section_threshold = ptr->x_ix86_section_threshold;
  opts->x_ix86_sse2avx = ptr->x_ix86_sse2avx;
  opts->x_ix86_stack_protector_guard = ptr->x_ix86_stack_protector_guard;
  opts->x_ix86_stringop_alg = ptr->x_ix86_stringop_alg;
  opts->x_ix86_tls_dialect = ptr->x_ix86_tls_dialect;
  opts->x_ix86_tune_ctrl_string = ptr->x_ix86_tune_ctrl_string;
  opts->x_ix86_tune_memcpy_strategy = ptr->x_ix86_tune_memcpy_strategy;
  opts->x_ix86_tune_memset_strategy = ptr->x_ix86_tune_memset_strategy;
  opts->x_ix86_tune_no_default = ptr->x_ix86_tune_no_default;
  opts->x_ix86_veclibabi_type = ptr->x_ix86_veclibabi_type;
  ix86_tune_cost = processor_target_table[ix86_tune].cost;
  /* TODO: ix86_cost should be chosen at instruction or function granuality
     so for cold code we use size_cost even in !optimize_size compilation.  */
  if (opts->x_optimize_size)
    ix86_cost = &ix86_size_cost;
  else
    ix86_cost = ix86_tune_cost;

  /* Recreate the arch feature tests if the arch changed */
  if (old_arch != ix86_arch)
    {
      ix86_arch_mask = 1u << ix86_arch;
      for (i = 0; i < X86_ARCH_LAST; ++i)
	ix86_arch_features[i]
	  = !!(initial_ix86_arch_features[i] & ix86_arch_mask);
    }

  /* Recreate the tune optimization tests */
  if (old_tune != ix86_tune)
    set_ix86_tune_features (ix86_tune, false);
}

/* Adjust target options after streaming them in.  This is mainly about
   reconciling them with global options.  */

static void
ix86_function_specific_post_stream_in (struct cl_target_option *ptr)
{
  /* flag_pic is a global option, but ix86_cmodel is target saved option
     partly computed from flag_pic.  If flag_pic is on, adjust x_ix86_cmodel
     for PIC, or error out.  */
  if (flag_pic)
    switch (ptr->x_ix86_cmodel)
      {
      case CM_SMALL:
	ptr->x_ix86_cmodel = CM_SMALL_PIC;
	break;

      case CM_MEDIUM:
	ptr->x_ix86_cmodel = CM_MEDIUM_PIC;
	break;

      case CM_LARGE:
	ptr->x_ix86_cmodel = CM_LARGE_PIC;
	break;

      case CM_KERNEL:
	error ("code model %s does not support PIC mode", "kernel");
	break;

      default:
	break;
      }
  else
    switch (ptr->x_ix86_cmodel)
      {
      case CM_SMALL_PIC:
	ptr->x_ix86_cmodel = CM_SMALL;
	break;

      case CM_MEDIUM_PIC:
	ptr->x_ix86_cmodel = CM_MEDIUM;
	break;

      case CM_LARGE_PIC:
	ptr->x_ix86_cmodel = CM_LARGE;
	break;

      default:
	break;
      }
}

/* Print the current options */

static void
ix86_function_specific_print (FILE *file, int indent,
			      struct cl_target_option *ptr)
{
  char *target_string
    = ix86_target_string (ptr->x_ix86_isa_flags, ptr->x_ix86_isa_flags2,
			  ptr->x_target_flags, ptr->x_ix86_target_flags,
			  NULL, NULL, ptr->x_ix86_fpmath, false);

  gcc_assert (ptr->arch < PROCESSOR_max);
  fprintf (file, "%*sarch = %d (%s)\n",
	   indent, "",
	   ptr->arch, processor_target_table[ptr->arch].name);

  gcc_assert (ptr->tune < PROCESSOR_max);
  fprintf (file, "%*stune = %d (%s)\n",
	   indent, "",
	   ptr->tune, processor_target_table[ptr->tune].name);

  fprintf (file, "%*sbranch_cost = %d\n", indent, "", ptr->branch_cost);

  if (target_string)
    {
      fprintf (file, "%*s%s\n", indent, "", target_string);
      free (target_string);
    }
}


/* Inner function to process the attribute((target(...))), take an argument and
   set the current options from the argument. If we have a list, recursively go
   over the list.  */

static bool
ix86_valid_target_attribute_inner_p (tree args, char *p_strings[],
				     struct gcc_options *opts,
				     struct gcc_options *opts_set,
				     struct gcc_options *enum_opts_set)
{
  char *next_optstr;
  bool ret = true;

#define IX86_ATTR_ISA(S,O)   { S, sizeof (S)-1, ix86_opt_isa, O, 0 }
#define IX86_ATTR_STR(S,O)   { S, sizeof (S)-1, ix86_opt_str, O, 0 }
#define IX86_ATTR_ENUM(S,O)  { S, sizeof (S)-1, ix86_opt_enum, O, 0 }
#define IX86_ATTR_YES(S,O,M) { S, sizeof (S)-1, ix86_opt_yes, O, M }
#define IX86_ATTR_NO(S,O,M)  { S, sizeof (S)-1, ix86_opt_no,  O, M }

  enum ix86_opt_type
  {
    ix86_opt_unknown,
    ix86_opt_yes,
    ix86_opt_no,
    ix86_opt_str,
    ix86_opt_enum,
    ix86_opt_isa
  };

  static const struct
  {
    const char *string;
    size_t len;
    enum ix86_opt_type type;
    int opt;
    int mask;
  } attrs[] = {
    /* isa options */
    IX86_ATTR_ISA ("sgx",	OPT_msgx),
    IX86_ATTR_ISA ("avx5124fmaps", OPT_mavx5124fmaps),
    IX86_ATTR_ISA ("avx5124vnniw", OPT_mavx5124vnniw),
    IX86_ATTR_ISA ("avx512vpopcntdq", OPT_mavx512vpopcntdq),

    IX86_ATTR_ISA ("avx512vbmi", OPT_mavx512vbmi),
    IX86_ATTR_ISA ("avx512ifma", OPT_mavx512ifma),
    IX86_ATTR_ISA ("avx512vl",	OPT_mavx512vl),
    IX86_ATTR_ISA ("avx512bw",	OPT_mavx512bw),
    IX86_ATTR_ISA ("avx512dq",	OPT_mavx512dq),
    IX86_ATTR_ISA ("avx512er",	OPT_mavx512er),
    IX86_ATTR_ISA ("avx512pf",	OPT_mavx512pf),
    IX86_ATTR_ISA ("avx512cd",	OPT_mavx512cd),
    IX86_ATTR_ISA ("avx512f",	OPT_mavx512f),
    IX86_ATTR_ISA ("avx2",	OPT_mavx2),
    IX86_ATTR_ISA ("fma",	OPT_mfma),
    IX86_ATTR_ISA ("xop",	OPT_mxop),
    IX86_ATTR_ISA ("fma4",	OPT_mfma4),
    IX86_ATTR_ISA ("f16c",	OPT_mf16c),
    IX86_ATTR_ISA ("avx",	OPT_mavx),
    IX86_ATTR_ISA ("sse4",	OPT_msse4),
    IX86_ATTR_ISA ("sse4.2",	OPT_msse4_2),
    IX86_ATTR_ISA ("sse4.1",	OPT_msse4_1),
    IX86_ATTR_ISA ("sse4a",	OPT_msse4a),
    IX86_ATTR_ISA ("ssse3",	OPT_mssse3),
    IX86_ATTR_ISA ("sse3",	OPT_msse3),
    IX86_ATTR_ISA ("aes",	OPT_maes),
    IX86_ATTR_ISA ("sha",	OPT_msha),
    IX86_ATTR_ISA ("pclmul",	OPT_mpclmul),
    IX86_ATTR_ISA ("sse2",	OPT_msse2),
    IX86_ATTR_ISA ("sse",	OPT_msse),
    IX86_ATTR_ISA ("3dnowa",	OPT_m3dnowa),
    IX86_ATTR_ISA ("3dnow",	OPT_m3dnow),
    IX86_ATTR_ISA ("mmx",	OPT_mmmx),
    IX86_ATTR_ISA ("rtm",	OPT_mrtm),
    IX86_ATTR_ISA ("prfchw",	OPT_mprfchw),
    IX86_ATTR_ISA ("rdseed",	OPT_mrdseed),
    IX86_ATTR_ISA ("adx",	OPT_madx),
    IX86_ATTR_ISA ("prefetchwt1", OPT_mprefetchwt1),
    IX86_ATTR_ISA ("clflushopt", OPT_mclflushopt),
    IX86_ATTR_ISA ("xsaves",	OPT_mxsaves),
    IX86_ATTR_ISA ("xsavec",	OPT_mxsavec),
    IX86_ATTR_ISA ("xsaveopt",	OPT_mxsaveopt),
    IX86_ATTR_ISA ("xsave",	OPT_mxsave),
    IX86_ATTR_ISA ("abm",	OPT_mabm),
    IX86_ATTR_ISA ("bmi",	OPT_mbmi),
    IX86_ATTR_ISA ("bmi2",	OPT_mbmi2),
    IX86_ATTR_ISA ("lzcnt",	OPT_mlzcnt),
    IX86_ATTR_ISA ("tbm",	OPT_mtbm),
    IX86_ATTR_ISA ("popcnt",	OPT_mpopcnt),
    IX86_ATTR_ISA ("cx16",	OPT_mcx16),
    IX86_ATTR_ISA ("sahf",	OPT_msahf),
    IX86_ATTR_ISA ("movbe",	OPT_mmovbe),
    IX86_ATTR_ISA ("crc32",	OPT_mcrc32),
    IX86_ATTR_ISA ("fsgsbase",	OPT_mfsgsbase),
    IX86_ATTR_ISA ("rdrnd",	OPT_mrdrnd),
    IX86_ATTR_ISA ("mwaitx",	OPT_mmwaitx),
    IX86_ATTR_ISA ("clzero",	OPT_mclzero),
    IX86_ATTR_ISA ("pku",	OPT_mpku),
    IX86_ATTR_ISA ("lwp",	OPT_mlwp),
    IX86_ATTR_ISA ("hle",	OPT_mhle),
    IX86_ATTR_ISA ("fxsr",	OPT_mfxsr),
    IX86_ATTR_ISA ("mpx",	OPT_mmpx),
    IX86_ATTR_ISA ("clwb",	OPT_mclwb),
    IX86_ATTR_ISA ("rdpid",	OPT_mrdpid),

    /* enum options */
    IX86_ATTR_ENUM ("fpmath=",	OPT_mfpmath_),

    /* string options */
    IX86_ATTR_STR ("arch=",	IX86_FUNCTION_SPECIFIC_ARCH),
    IX86_ATTR_STR ("tune=",	IX86_FUNCTION_SPECIFIC_TUNE),

    /* flag options */
    IX86_ATTR_YES ("cld",
		   OPT_mcld,
		   MASK_CLD),

    IX86_ATTR_NO ("fancy-math-387",
		  OPT_mfancy_math_387,
		  MASK_NO_FANCY_MATH_387),

    IX86_ATTR_YES ("ieee-fp",
		   OPT_mieee_fp,
		   MASK_IEEE_FP),

    IX86_ATTR_YES ("inline-all-stringops",
		   OPT_minline_all_stringops,
		   MASK_INLINE_ALL_STRINGOPS),

    IX86_ATTR_YES ("inline-stringops-dynamically",
		   OPT_minline_stringops_dynamically,
		   MASK_INLINE_STRINGOPS_DYNAMICALLY),

    IX86_ATTR_NO ("align-stringops",
		  OPT_mno_align_stringops,
		  MASK_NO_ALIGN_STRINGOPS),

    IX86_ATTR_YES ("recip",
		   OPT_mrecip,
		   MASK_RECIP),

  };

  /* If this is a list, recurse to get the options.  */
  if (TREE_CODE (args) == TREE_LIST)
    {
      bool ret = true;

      for (; args; args = TREE_CHAIN (args))
	if (TREE_VALUE (args)
	    && !ix86_valid_target_attribute_inner_p (TREE_VALUE (args),
						     p_strings, opts, opts_set,
						     enum_opts_set))
	  ret = false;

      return ret;
    }

  else if (TREE_CODE (args) != STRING_CST)
    {
      error ("attribute %<target%> argument not a string");
      return false;
    }

  /* Handle multiple arguments separated by commas.  */
  next_optstr = ASTRDUP (TREE_STRING_POINTER (args));

  while (next_optstr && *next_optstr != '\0')
    {
      char *p = next_optstr;
      char *orig_p = p;
      char *comma = strchr (next_optstr, ',');
      const char *opt_string;
      size_t len, opt_len;
      int opt;
      bool opt_set_p;
      char ch;
      unsigned i;
      enum ix86_opt_type type = ix86_opt_unknown;
      int mask = 0;

      if (comma)
	{
	  *comma = '\0';
	  len = comma - next_optstr;
	  next_optstr = comma + 1;
	}
      else
	{
	  len = strlen (p);
	  next_optstr = NULL;
	}

      /* Recognize no-xxx.  */
      if (len > 3 && p[0] == 'n' && p[1] == 'o' && p[2] == '-')
	{
	  opt_set_p = false;
	  p += 3;
	  len -= 3;
	}
      else
	opt_set_p = true;

      /* Find the option.  */
      ch = *p;
      opt = N_OPTS;
      for (i = 0; i < ARRAY_SIZE (attrs); i++)
	{
	  type = attrs[i].type;
	  opt_len = attrs[i].len;
	  if (ch == attrs[i].string[0]
	      && ((type != ix86_opt_str && type != ix86_opt_enum)
		  ? len == opt_len
		  : len > opt_len)
	      && memcmp (p, attrs[i].string, opt_len) == 0)
	    {
	      opt = attrs[i].opt;
	      mask = attrs[i].mask;
	      opt_string = attrs[i].string;
	      break;
	    }
	}

      /* Process the option.  */
      if (opt == N_OPTS)
	{
	  error ("attribute(target(\"%s\")) is unknown", orig_p);
	  ret = false;
	}

      else if (type == ix86_opt_isa)
	{
	  struct cl_decoded_option decoded;

	  generate_option (opt, NULL, opt_set_p, CL_TARGET, &decoded);
	  ix86_handle_option (opts, opts_set,
			      &decoded, input_location);
	}

      else if (type == ix86_opt_yes || type == ix86_opt_no)
	{
	  if (type == ix86_opt_no)
	    opt_set_p = !opt_set_p;

	  if (opt_set_p)
	    opts->x_target_flags |= mask;
	  else
	    opts->x_target_flags &= ~mask;
	}

      else if (type == ix86_opt_str)
	{
	  if (p_strings[opt])
	    {
	      error ("option(\"%s\") was already specified", opt_string);
	      ret = false;
	    }
	  else
	    p_strings[opt] = xstrdup (p + opt_len);
	}

      else if (type == ix86_opt_enum)
	{
	  bool arg_ok;
	  int value;

	  arg_ok = opt_enum_arg_to_value (opt, p + opt_len, &value, CL_TARGET);
	  if (arg_ok)
	    set_option (opts, enum_opts_set, opt, value,
			p + opt_len, DK_UNSPECIFIED, input_location,
			global_dc);
	  else
	    {
	      error ("attribute(target(\"%s\")) is unknown", orig_p);
	      ret = false;
	    }
	}

      else
	gcc_unreachable ();
    }

  return ret;
}

/* Release allocated strings.  */
static void
release_options_strings (char **option_strings)
{
  /* Free up memory allocated to hold the strings */
  for (unsigned i = 0; i < IX86_FUNCTION_SPECIFIC_MAX; i++)
    free (option_strings[i]);
}

/* Return a TARGET_OPTION_NODE tree of the target options listed or NULL.  */

tree
ix86_valid_target_attribute_tree (tree args,
				  struct gcc_options *opts,
				  struct gcc_options *opts_set)
{
  const char *orig_arch_string = opts->x_ix86_arch_string;
  const char *orig_tune_string = opts->x_ix86_tune_string;
  enum fpmath_unit orig_fpmath_set = opts_set->x_ix86_fpmath;
  int orig_tune_defaulted = ix86_tune_defaulted;
  int orig_arch_specified = ix86_arch_specified;
  char *option_strings[IX86_FUNCTION_SPECIFIC_MAX] = { NULL, NULL };
  tree t = NULL_TREE;
  struct cl_target_option *def
    = TREE_TARGET_OPTION (target_option_default_node);
  struct gcc_options enum_opts_set;

  memset (&enum_opts_set, 0, sizeof (enum_opts_set));

  /* Process each of the options on the chain.  */
  if (! ix86_valid_target_attribute_inner_p (args, option_strings, opts,
					     opts_set, &enum_opts_set))
    return error_mark_node;

  /* If the changed options are different from the default, rerun
     ix86_option_override_internal, and then save the options away.
     The string options are attribute options, and will be undone
     when we copy the save structure.  */
  if (opts->x_ix86_isa_flags != def->x_ix86_isa_flags
      || opts->x_ix86_isa_flags2 != def->x_ix86_isa_flags2
      || opts->x_target_flags != def->x_target_flags
      || option_strings[IX86_FUNCTION_SPECIFIC_ARCH]
      || option_strings[IX86_FUNCTION_SPECIFIC_TUNE]
      || enum_opts_set.x_ix86_fpmath)
    {
      /* If we are using the default tune= or arch=, undo the string assigned,
	 and use the default.  */
      if (option_strings[IX86_FUNCTION_SPECIFIC_ARCH])
	{
	  opts->x_ix86_arch_string
	    = ggc_strdup (option_strings[IX86_FUNCTION_SPECIFIC_ARCH]);

	  /* If arch= is set,  clear all bits in x_ix86_isa_flags,
	     except for ISA_64BIT, ABI_64, ABI_X32, and CODE16.  */
	  opts->x_ix86_isa_flags &= (OPTION_MASK_ISA_64BIT
				     | OPTION_MASK_ABI_64
				     | OPTION_MASK_ABI_X32
				     | OPTION_MASK_CODE16);
	  opts->x_ix86_isa_flags2 = 0;
	}
      else if (!orig_arch_specified)
	opts->x_ix86_arch_string = NULL;

      if (option_strings[IX86_FUNCTION_SPECIFIC_TUNE])
	opts->x_ix86_tune_string
	  = ggc_strdup (option_strings[IX86_FUNCTION_SPECIFIC_TUNE]);
      else if (orig_tune_defaulted)
	opts->x_ix86_tune_string = NULL;

      /* If fpmath= is not set, and we now have sse2 on 32-bit, use it.  */
      if (enum_opts_set.x_ix86_fpmath)
	opts_set->x_ix86_fpmath = (enum fpmath_unit) 1;

      /* Do any overrides, such as arch=xxx, or tune=xxx support.  */
      bool r = ix86_option_override_internal (false, opts, opts_set);
      if (!r)
	{
	  release_options_strings (option_strings);
	  return error_mark_node;
	}

      /* Add any builtin functions with the new isa if any.  */
      ix86_add_new_builtins (opts->x_ix86_isa_flags, opts->x_ix86_isa_flags2);

      /* Save the current options unless we are validating options for
	 #pragma.  */
      t = build_target_option_node (opts);

      opts->x_ix86_arch_string = orig_arch_string;
      opts->x_ix86_tune_string = orig_tune_string;
      opts_set->x_ix86_fpmath = orig_fpmath_set;

      release_options_strings (option_strings);
    }

  return t;
}

/* Hook to validate attribute((target("string"))).  */

static bool
ix86_valid_target_attribute_p (tree fndecl,
			       tree ARG_UNUSED (name),
			       tree args,
			       int ARG_UNUSED (flags))
{
  struct gcc_options func_options;
  tree new_target, new_optimize;
  bool ret = true;

  /* attribute((target("default"))) does nothing, beyond
     affecting multi-versioning.  */
  if (TREE_VALUE (args)
      && TREE_CODE (TREE_VALUE (args)) == STRING_CST
      && TREE_CHAIN (args) == NULL_TREE
      && strcmp (TREE_STRING_POINTER (TREE_VALUE (args)), "default") == 0)
    return true;

  tree old_optimize = build_optimization_node (&global_options);

  /* Get the optimization options of the current function.  */  
  tree func_optimize = DECL_FUNCTION_SPECIFIC_OPTIMIZATION (fndecl);
 
  if (!func_optimize)
    func_optimize = old_optimize;

  /* Init func_options.  */
  memset (&func_options, 0, sizeof (func_options));
  init_options_struct (&func_options, NULL);
  lang_hooks.init_options_struct (&func_options);
 
  cl_optimization_restore (&func_options,
			   TREE_OPTIMIZATION (func_optimize));

  /* Initialize func_options to the default before its target options can
     be set.  */
  cl_target_option_restore (&func_options,
			    TREE_TARGET_OPTION (target_option_default_node));

  new_target = ix86_valid_target_attribute_tree (args, &func_options,
						 &global_options_set);

  new_optimize = build_optimization_node (&func_options);

  if (new_target == error_mark_node)
    ret = false;

  else if (fndecl && new_target)
    {
      DECL_FUNCTION_SPECIFIC_TARGET (fndecl) = new_target;

      if (old_optimize != new_optimize)
	DECL_FUNCTION_SPECIFIC_OPTIMIZATION (fndecl) = new_optimize;
    }

  finalize_options_struct (&func_options);

  return ret;
}


/* Hook to determine if one function can safely inline another.  */

static bool
ix86_can_inline_p (tree caller, tree callee)
{
  tree caller_tree = DECL_FUNCTION_SPECIFIC_TARGET (caller);
  tree callee_tree = DECL_FUNCTION_SPECIFIC_TARGET (callee);
  if (!callee_tree)
    callee_tree = target_option_default_node;
  if (!caller_tree)
    caller_tree = target_option_default_node;
  if (callee_tree == caller_tree)
    return true;

  struct cl_target_option *caller_opts = TREE_TARGET_OPTION (caller_tree);
  struct cl_target_option *callee_opts = TREE_TARGET_OPTION (callee_tree);
  bool ret = false;

  /* Callee's isa options should be a subset of the caller's, i.e. a SSE4
     function can inline a SSE2 function but a SSE2 function can't inline
     a SSE4 function.  */
  if (((caller_opts->x_ix86_isa_flags & callee_opts->x_ix86_isa_flags)
       != callee_opts->x_ix86_isa_flags)
      || ((caller_opts->x_ix86_isa_flags2 & callee_opts->x_ix86_isa_flags2)
	  != callee_opts->x_ix86_isa_flags2))
    ret = false;

  /* See if we have the same non-isa options.  */
  else if (caller_opts->x_target_flags != callee_opts->x_target_flags)
    ret = false;

  /* See if arch, tune, etc. are the same.  */
  else if (caller_opts->arch != callee_opts->arch)
    ret = false;

  else if (caller_opts->tune != callee_opts->tune)
    ret = false;

  else if (caller_opts->x_ix86_fpmath != callee_opts->x_ix86_fpmath
	   /* If the calle doesn't use FP expressions differences in
	      ix86_fpmath can be ignored.  We are called from FEs
	      for multi-versioning call optimization, so beware of
	      ipa_fn_summaries not available.  */
	   && (! ipa_fn_summaries
	       || ipa_fn_summaries->get
	       (cgraph_node::get (callee))->fp_expressions))
    ret = false;

  else if (caller_opts->branch_cost != callee_opts->branch_cost)
    ret = false;

  else
    ret = true;

  return ret;
}


/* Remember the last target of ix86_set_current_function.  */
static GTY(()) tree ix86_previous_fndecl;

/* Set targets globals to the default (or current #pragma GCC target
   if active).  Invalidate ix86_previous_fndecl cache.  */

void
ix86_reset_previous_fndecl (void)
{
  tree new_tree = target_option_current_node;
  cl_target_option_restore (&global_options, TREE_TARGET_OPTION (new_tree));
  if (TREE_TARGET_GLOBALS (new_tree))
    restore_target_globals (TREE_TARGET_GLOBALS (new_tree));
  else if (new_tree == target_option_default_node)
    restore_target_globals (&default_target_globals);
  else
    TREE_TARGET_GLOBALS (new_tree) = save_target_globals_default_opts ();
  ix86_previous_fndecl = NULL_TREE;
}

/* Set the func_type field from the function FNDECL.  */

static void
ix86_set_func_type (tree fndecl)
{
  if (cfun->machine->func_type == TYPE_UNKNOWN)
    {
      if (lookup_attribute ("interrupt",
			    TYPE_ATTRIBUTES (TREE_TYPE (fndecl))))
	{
	  if (ix86_function_naked (fndecl))
	    error_at (DECL_SOURCE_LOCATION (fndecl),
		      "interrupt and naked attributes are not compatible");

	  int nargs = 0;
	  for (tree arg = DECL_ARGUMENTS (fndecl);
	       arg;
	       arg = TREE_CHAIN (arg))
	    nargs++;
	  cfun->machine->no_caller_saved_registers = true;
	  cfun->machine->func_type
	    = nargs == 2 ? TYPE_EXCEPTION : TYPE_INTERRUPT;

	  ix86_optimize_mode_switching[X86_DIRFLAG] = 1;

	  /* Only dwarf2out.c can handle -WORD(AP) as a pointer argument.  */
	  if (write_symbols != NO_DEBUG && write_symbols != DWARF2_DEBUG)
	    sorry ("Only DWARF debug format is supported for interrupt "
		   "service routine.");
	}
      else
	{
	  cfun->machine->func_type = TYPE_NORMAL;
	  if (lookup_attribute ("no_caller_saved_registers",
				TYPE_ATTRIBUTES (TREE_TYPE (fndecl))))
	    cfun->machine->no_caller_saved_registers = true;
	}
    }
}

/* Establish appropriate back-end context for processing the function
   FNDECL.  The argument might be NULL to indicate processing at top
   level, outside of any function scope.  */
static void
ix86_set_current_function (tree fndecl)
{
  /* Only change the context if the function changes.  This hook is called
     several times in the course of compiling a function, and we don't want to
     slow things down too much or call target_reinit when it isn't safe.  */
  if (fndecl == ix86_previous_fndecl)
    {
      /* There may be 2 function bodies for the same function FNDECL,
	 one is extern inline and one isn't.  Call ix86_set_func_type
	 to set the func_type field.  */
      if (fndecl != NULL_TREE)
	ix86_set_func_type (fndecl);
      return;
    }

  tree old_tree;
  if (ix86_previous_fndecl == NULL_TREE)
    old_tree = target_option_current_node;
  else if (DECL_FUNCTION_SPECIFIC_TARGET (ix86_previous_fndecl))
    old_tree = DECL_FUNCTION_SPECIFIC_TARGET (ix86_previous_fndecl);
  else
    old_tree = target_option_default_node;

  if (fndecl == NULL_TREE)
    {
      if (old_tree != target_option_current_node)
	ix86_reset_previous_fndecl ();
      return;
    }

  ix86_set_func_type (fndecl);

  tree new_tree = DECL_FUNCTION_SPECIFIC_TARGET (fndecl);
  if (new_tree == NULL_TREE)
    new_tree = target_option_default_node;

  if (old_tree != new_tree)
    {
      cl_target_option_restore (&global_options, TREE_TARGET_OPTION (new_tree));
      if (TREE_TARGET_GLOBALS (new_tree))
	restore_target_globals (TREE_TARGET_GLOBALS (new_tree));
      else if (new_tree == target_option_default_node)
	restore_target_globals (&default_target_globals);
      else
	TREE_TARGET_GLOBALS (new_tree) = save_target_globals_default_opts ();
    }
  ix86_previous_fndecl = fndecl;

  static bool prev_no_caller_saved_registers;

  /* 64-bit MS and SYSV ABI have different set of call used registers.
     Avoid expensive re-initialization of init_regs each time we switch
     function context.  */
  if (TARGET_64BIT
      && (call_used_regs[SI_REG]
	  == (cfun->machine->call_abi == MS_ABI)))
    reinit_regs ();
  /* Need to re-initialize init_regs if caller-saved registers are
     changed.  */
  else if (prev_no_caller_saved_registers
	   != cfun->machine->no_caller_saved_registers)
    reinit_regs ();

  if (cfun->machine->func_type != TYPE_NORMAL
      || cfun->machine->no_caller_saved_registers)
    {
      /* Don't allow MPX, SSE, MMX nor x87 instructions since they
	 may change processor state.  */
      const char *isa;
      if (TARGET_MPX)
	isa = "MPX";
      else if (TARGET_SSE)
	isa = "SSE";
      else if (TARGET_MMX)
	isa = "MMX/3Dnow";
      else if (TARGET_80387)
	isa = "80387";
      else
	isa = NULL;
      if (isa != NULL)
	{
	  if (cfun->machine->func_type != TYPE_NORMAL)
	    sorry ("%s instructions aren't allowed in %s service routine",
		   isa, (cfun->machine->func_type == TYPE_EXCEPTION
			 ? "exception" : "interrupt"));
	  else
	    sorry ("%s instructions aren't allowed in function with "
		   "no_caller_saved_registers attribute", isa);
	  /* Don't issue the same error twice.  */
	  cfun->machine->func_type = TYPE_NORMAL;
	  cfun->machine->no_caller_saved_registers = false;
	}
    }

  prev_no_caller_saved_registers
    = cfun->machine->no_caller_saved_registers;
}


/* Return true if this goes in large data/bss.  */

static bool
ix86_in_large_data_p (tree exp)
{
  if (ix86_cmodel != CM_MEDIUM && ix86_cmodel != CM_MEDIUM_PIC)
    return false;

  if (exp == NULL_TREE)
    return false;

  /* Functions are never large data.  */
  if (TREE_CODE (exp) == FUNCTION_DECL)
    return false;

  /* Automatic variables are never large data.  */
  if (VAR_P (exp) && !is_global_var (exp))
    return false;

  if (VAR_P (exp) && DECL_SECTION_NAME (exp))
    {
      const char *section = DECL_SECTION_NAME (exp);
      if (strcmp (section, ".ldata") == 0
	  || strcmp (section, ".lbss") == 0)
	return true;
      return false;
    }
  else
    {
      HOST_WIDE_INT size = int_size_in_bytes (TREE_TYPE (exp));

      /* If this is an incomplete type with size 0, then we can't put it
	 in data because it might be too big when completed.  Also,
	 int_size_in_bytes returns -1 if size can vary or is larger than
	 an integer in which case also it is safer to assume that it goes in
	 large data.  */
      if (size <= 0 || size > ix86_section_threshold)
	return true;
    }

  return false;
}

/* i386-specific section flag to mark large sections.  */
#define SECTION_LARGE SECTION_MACH_DEP

/* Switch to the appropriate section for output of DECL.
   DECL is either a `VAR_DECL' node or a constant of some sort.
   RELOC indicates whether forming the initial value of DECL requires
   link-time relocations.  */

ATTRIBUTE_UNUSED static section *
x86_64_elf_select_section (tree decl, int reloc,
			   unsigned HOST_WIDE_INT align)
{
  if (ix86_in_large_data_p (decl))
    {
      const char *sname = NULL;
      unsigned int flags = SECTION_WRITE | SECTION_LARGE;
      switch (categorize_decl_for_section (decl, reloc))
	{
	case SECCAT_DATA:
	  sname = ".ldata";
	  break;
	case SECCAT_DATA_REL:
	  sname = ".ldata.rel";
	  break;
	case SECCAT_DATA_REL_LOCAL:
	  sname = ".ldata.rel.local";
	  break;
	case SECCAT_DATA_REL_RO:
	  sname = ".ldata.rel.ro";
	  break;
	case SECCAT_DATA_REL_RO_LOCAL:
	  sname = ".ldata.rel.ro.local";
	  break;
	case SECCAT_BSS:
	  sname = ".lbss";
	  flags |= SECTION_BSS;
	  break;
	case SECCAT_RODATA:
	case SECCAT_RODATA_MERGE_STR:
	case SECCAT_RODATA_MERGE_STR_INIT:
	case SECCAT_RODATA_MERGE_CONST:
	  sname = ".lrodata";
	  flags &= ~SECTION_WRITE;
	  break;
	case SECCAT_SRODATA:
	case SECCAT_SDATA:
	case SECCAT_SBSS:
	  gcc_unreachable ();
	case SECCAT_TEXT:
	case SECCAT_TDATA:
	case SECCAT_TBSS:
	  /* We don't split these for medium model.  Place them into
	     default sections and hope for best.  */
	  break;
	}
      if (sname)
	{
	  /* We might get called with string constants, but get_named_section
	     doesn't like them as they are not DECLs.  Also, we need to set
	     flags in that case.  */
	  if (!DECL_P (decl))
	    return get_section (sname, flags, NULL);
	  return get_named_section (decl, sname, reloc);
	}
    }
  return default_elf_select_section (decl, reloc, align);
}

/* Select a set of attributes for section NAME based on the properties
   of DECL and whether or not RELOC indicates that DECL's initializer
   might contain runtime relocations.  */

static unsigned int ATTRIBUTE_UNUSED
x86_64_elf_section_type_flags (tree decl, const char *name, int reloc)
{
  unsigned int flags = default_section_type_flags (decl, name, reloc);

  if (ix86_in_large_data_p (decl))
    flags |= SECTION_LARGE;

  if (decl == NULL_TREE
      && (strcmp (name, ".ldata.rel.ro") == 0
	  || strcmp (name, ".ldata.rel.ro.local") == 0))
    flags |= SECTION_RELRO;

  if (strcmp (name, ".lbss") == 0
      || strncmp (name, ".lbss.", 5) == 0
      || strncmp (name, ".gnu.linkonce.lb.", 16) == 0)
    flags |= SECTION_BSS;

  return flags;
}

/* Build up a unique section name, expressed as a
   STRING_CST node, and assign it to DECL_SECTION_NAME (decl).
   RELOC indicates whether the initial value of EXP requires
   link-time relocations.  */

static void ATTRIBUTE_UNUSED
x86_64_elf_unique_section (tree decl, int reloc)
{
  if (ix86_in_large_data_p (decl))
    {
      const char *prefix = NULL;
      /* We only need to use .gnu.linkonce if we don't have COMDAT groups.  */
      bool one_only = DECL_COMDAT_GROUP (decl) && !HAVE_COMDAT_GROUP;

      switch (categorize_decl_for_section (decl, reloc))
	{
	case SECCAT_DATA:
	case SECCAT_DATA_REL:
	case SECCAT_DATA_REL_LOCAL:
	case SECCAT_DATA_REL_RO:
	case SECCAT_DATA_REL_RO_LOCAL:
          prefix = one_only ? ".ld" : ".ldata";
	  break;
	case SECCAT_BSS:
          prefix = one_only ? ".lb" : ".lbss";
	  break;
	case SECCAT_RODATA:
	case SECCAT_RODATA_MERGE_STR:
	case SECCAT_RODATA_MERGE_STR_INIT:
	case SECCAT_RODATA_MERGE_CONST:
          prefix = one_only ? ".lr" : ".lrodata";
	  break;
	case SECCAT_SRODATA:
	case SECCAT_SDATA:
	case SECCAT_SBSS:
	  gcc_unreachable ();
	case SECCAT_TEXT:
	case SECCAT_TDATA:
	case SECCAT_TBSS:
	  /* We don't split these for medium model.  Place them into
	     default sections and hope for best.  */
	  break;
	}
      if (prefix)
	{
	  const char *name, *linkonce;
	  char *string;

	  name = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));
	  name = targetm.strip_name_encoding (name);

	  /* If we're using one_only, then there needs to be a .gnu.linkonce
     	     prefix to the section name.  */
	  linkonce = one_only ? ".gnu.linkonce" : "";

	  string = ACONCAT ((linkonce, prefix, ".", name, NULL));

	  set_decl_section_name (decl, string);
	  return;
	}
    }
  default_unique_section (decl, reloc);
}

#ifdef COMMON_ASM_OP

#ifndef LARGECOMM_SECTION_ASM_OP
#define LARGECOMM_SECTION_ASM_OP "\t.largecomm\t"
#endif

/* This says how to output assembler code to declare an
   uninitialized external linkage data object.

   For medium model x86-64 we need to use LARGECOMM_SECTION_ASM_OP opcode for
   large objects.  */
void
x86_elf_aligned_decl_common (FILE *file, tree decl,
			const char *name, unsigned HOST_WIDE_INT size,
			int align)
{
  if ((ix86_cmodel == CM_MEDIUM || ix86_cmodel == CM_MEDIUM_PIC)
      && size > (unsigned int)ix86_section_threshold)
    {
      switch_to_section (get_named_section (decl, ".lbss", 0));
      fputs (LARGECOMM_SECTION_ASM_OP, file);
    }
  else
    fputs (COMMON_ASM_OP, file);
  assemble_name (file, name);
  fprintf (file, "," HOST_WIDE_INT_PRINT_UNSIGNED ",%u\n",
	   size, align / BITS_PER_UNIT);
}
#endif

/* Utility function for targets to use in implementing
   ASM_OUTPUT_ALIGNED_BSS.  */

void
x86_output_aligned_bss (FILE *file, tree decl, const char *name,
		       	unsigned HOST_WIDE_INT size, int align)
{
  if ((ix86_cmodel == CM_MEDIUM || ix86_cmodel == CM_MEDIUM_PIC)
      && size > (unsigned int)ix86_section_threshold)
    switch_to_section (get_named_section (decl, ".lbss", 0));
  else
    switch_to_section (bss_section);
  ASM_OUTPUT_ALIGN (file, floor_log2 (align / BITS_PER_UNIT));
#ifdef ASM_DECLARE_OBJECT_NAME
  last_assemble_variable_decl = decl;
  ASM_DECLARE_OBJECT_NAME (file, name, decl);
#else
  /* Standard thing is just output label for the object.  */
  ASM_OUTPUT_LABEL (file, name);
#endif /* ASM_DECLARE_OBJECT_NAME */
  ASM_OUTPUT_SKIP (file, size ? size : 1);
}

/* Decide whether we must probe the stack before any space allocation
   on this target.  It's essentially TARGET_STACK_PROBE except when
   -fstack-check causes the stack to be already probed differently.  */

bool
ix86_target_stack_probe (void)
{
  /* Do not probe the stack twice if static stack checking is enabled.  */
  if (flag_stack_check == STATIC_BUILTIN_STACK_CHECK)
    return false;

  return TARGET_STACK_PROBE;
}

/* Decide whether we can make a sibling call to a function.  DECL is the
   declaration of the function being targeted by the call and EXP is the
   CALL_EXPR representing the call.  */

static bool
ix86_function_ok_for_sibcall (tree decl, tree exp)
{
  tree type, decl_or_type;
  rtx a, b;
  bool bind_global = decl && !targetm.binds_local_p (decl);

  if (ix86_function_naked (current_function_decl))
    return false;

  /* Sibling call isn't OK if there are no caller-saved registers
     since all registers must be preserved before return.  */
  if (cfun->machine->no_caller_saved_registers)
    return false;

  /* If we are generating position-independent code, we cannot sibcall
     optimize direct calls to global functions, as the PLT requires
     %ebx be live. (Darwin does not have a PLT.)  */
  if (!TARGET_MACHO
      && !TARGET_64BIT
      && flag_pic
      && flag_plt
      && bind_global)
    return false;

  /* If we need to align the outgoing stack, then sibcalling would
     unalign the stack, which may break the called function.  */
  if (ix86_minimum_incoming_stack_boundary (true)
      < PREFERRED_STACK_BOUNDARY)
    return false;

  if (decl)
    {
      decl_or_type = decl;
      type = TREE_TYPE (decl);
    }
  else
    {
      /* We're looking at the CALL_EXPR, we need the type of the function.  */
      type = CALL_EXPR_FN (exp);		/* pointer expression */
      type = TREE_TYPE (type);			/* pointer type */
      type = TREE_TYPE (type);			/* function type */
      decl_or_type = type;
    }

  /* Check that the return value locations are the same.  Like
     if we are returning floats on the 80387 register stack, we cannot
     make a sibcall from a function that doesn't return a float to a
     function that does or, conversely, from a function that does return
     a float to a function that doesn't; the necessary stack adjustment
     would not be executed.  This is also the place we notice
     differences in the return value ABI.  Note that it is ok for one
     of the functions to have void return type as long as the return
     value of the other is passed in a register.  */
  a = ix86_function_value (TREE_TYPE (exp), decl_or_type, false);
  b = ix86_function_value (TREE_TYPE (DECL_RESULT (cfun->decl)),
			   cfun->decl, false);
  if (STACK_REG_P (a) || STACK_REG_P (b))
    {
      if (!rtx_equal_p (a, b))
	return false;
    }
  else if (VOID_TYPE_P (TREE_TYPE (DECL_RESULT (cfun->decl))))
    ;
  else if (!rtx_equal_p (a, b))
    return false;

  if (TARGET_64BIT)
    {
      /* The SYSV ABI has more call-clobbered registers;
	 disallow sibcalls from MS to SYSV.  */
      if (cfun->machine->call_abi == MS_ABI
	  && ix86_function_type_abi (type) == SYSV_ABI)
	return false;
    }
  else
    {
      /* If this call is indirect, we'll need to be able to use a
	 call-clobbered register for the address of the target function.
	 Make sure that all such registers are not used for passing
	 parameters.  Note that DLLIMPORT functions and call to global
	 function via GOT slot are indirect.  */
      if (!decl
	  || (bind_global && flag_pic && !flag_plt)
	  || (TARGET_DLLIMPORT_DECL_ATTRIBUTES && DECL_DLLIMPORT_P (decl)))
	{
	  /* Check if regparm >= 3 since arg_reg_available is set to
	     false if regparm == 0.  If regparm is 1 or 2, there is
	     always a call-clobbered register available.

	     ??? The symbol indirect call doesn't need a call-clobbered
	     register.  But we don't know if this is a symbol indirect
	     call or not here.  */
	  if (ix86_function_regparm (type, NULL) >= 3
	      && !cfun->machine->arg_reg_available)
	    return false;
	}
    }

  /* Otherwise okay.  That also includes certain types of indirect calls.  */
  return true;
}

/* Handle "cdecl", "stdcall", "fastcall", "regparm", "thiscall",
   and "sseregparm" calling convention attributes;
   arguments as in struct attribute_spec.handler.  */

static tree
ix86_handle_cconv_attribute (tree *node, tree name,
				   tree args,
				   int,
				   bool *no_add_attrs)
{
  if (TREE_CODE (*node) != FUNCTION_TYPE
      && TREE_CODE (*node) != METHOD_TYPE
      && TREE_CODE (*node) != FIELD_DECL
      && TREE_CODE (*node) != TYPE_DECL)
    {
      warning (OPT_Wattributes, "%qE attribute only applies to functions",
	       name);
      *no_add_attrs = true;
      return NULL_TREE;
    }

  /* Can combine regparm with all attributes but fastcall, and thiscall.  */
  if (is_attribute_p ("regparm", name))
    {
      tree cst;

      if (lookup_attribute ("fastcall", TYPE_ATTRIBUTES (*node)))
        {
	  error ("fastcall and regparm attributes are not compatible");
	}

      if (lookup_attribute ("thiscall", TYPE_ATTRIBUTES (*node)))
	{
	  error ("regparam and thiscall attributes are not compatible");
	}

      cst = TREE_VALUE (args);
      if (TREE_CODE (cst) != INTEGER_CST)
	{
	  warning (OPT_Wattributes,
		   "%qE attribute requires an integer constant argument",
		   name);
	  *no_add_attrs = true;
	}
      else if (compare_tree_int (cst, REGPARM_MAX) > 0)
	{
	  warning (OPT_Wattributes, "argument to %qE attribute larger than %d",
		   name, REGPARM_MAX);
	  *no_add_attrs = true;
	}

      return NULL_TREE;
    }

  if (TARGET_64BIT)
    {
      /* Do not warn when emulating the MS ABI.  */
      if ((TREE_CODE (*node) != FUNCTION_TYPE
	   && TREE_CODE (*node) != METHOD_TYPE)
	  || ix86_function_type_abi (*node) != MS_ABI)
	warning (OPT_Wattributes, "%qE attribute ignored",
	         name);
      *no_add_attrs = true;
      return NULL_TREE;
    }

  /* Can combine fastcall with stdcall (redundant) and sseregparm.  */
  if (is_attribute_p ("fastcall", name))
    {
      if (lookup_attribute ("cdecl", TYPE_ATTRIBUTES (*node)))
        {
	  error ("fastcall and cdecl attributes are not compatible");
	}
      if (lookup_attribute ("stdcall", TYPE_ATTRIBUTES (*node)))
        {
	  error ("fastcall and stdcall attributes are not compatible");
	}
      if (lookup_attribute ("regparm", TYPE_ATTRIBUTES (*node)))
        {
	  error ("fastcall and regparm attributes are not compatible");
	}
      if (lookup_attribute ("thiscall", TYPE_ATTRIBUTES (*node)))
	{
	  error ("fastcall and thiscall attributes are not compatible");
	}
    }

  /* Can combine stdcall with fastcall (redundant), regparm and
     sseregparm.  */
  else if (is_attribute_p ("stdcall", name))
    {
      if (lookup_attribute ("cdecl", TYPE_ATTRIBUTES (*node)))
        {
	  error ("stdcall and cdecl attributes are not compatible");
	}
      if (lookup_attribute ("fastcall", TYPE_ATTRIBUTES (*node)))
        {
	  error ("stdcall and fastcall attributes are not compatible");
	}
      if (lookup_attribute ("thiscall", TYPE_ATTRIBUTES (*node)))
	{
	  error ("stdcall and thiscall attributes are not compatible");
	}
    }

  /* Can combine cdecl with regparm and sseregparm.  */
  else if (is_attribute_p ("cdecl", name))
    {
      if (lookup_attribute ("stdcall", TYPE_ATTRIBUTES (*node)))
        {
	  error ("stdcall and cdecl attributes are not compatible");
	}
      if (lookup_attribute ("fastcall", TYPE_ATTRIBUTES (*node)))
        {
	  error ("fastcall and cdecl attributes are not compatible");
	}
      if (lookup_attribute ("thiscall", TYPE_ATTRIBUTES (*node)))
	{
	  error ("cdecl and thiscall attributes are not compatible");
	}
    }
  else if (is_attribute_p ("thiscall", name))
    {
      if (TREE_CODE (*node) != METHOD_TYPE && pedantic)
	warning (OPT_Wattributes, "%qE attribute is used for non-class method",
	         name);
      if (lookup_attribute ("stdcall", TYPE_ATTRIBUTES (*node)))
	{
	  error ("stdcall and thiscall attributes are not compatible");
	}
      if (lookup_attribute ("fastcall", TYPE_ATTRIBUTES (*node)))
	{
	  error ("fastcall and thiscall attributes are not compatible");
	}
      if (lookup_attribute ("cdecl", TYPE_ATTRIBUTES (*node)))
	{
	  error ("cdecl and thiscall attributes are not compatible");
	}
    }

  /* Can combine sseregparm with all attributes.  */

  return NULL_TREE;
}

/* The transactional memory builtins are implicitly regparm or fastcall
   depending on the ABI.  Override the generic do-nothing attribute that
   these builtins were declared with, and replace it with one of the two
   attributes that we expect elsewhere.  */

static tree
ix86_handle_tm_regparm_attribute (tree *node, tree, tree,
				  int flags, bool *no_add_attrs)
{
  tree alt;

  /* In no case do we want to add the placeholder attribute.  */
  *no_add_attrs = true;

  /* The 64-bit ABI is unchanged for transactional memory.  */
  if (TARGET_64BIT)
    return NULL_TREE;

  /* ??? Is there a better way to validate 32-bit windows?  We have
     cfun->machine->call_abi, but that seems to be set only for 64-bit.  */
  if (CHECK_STACK_LIMIT > 0)
    alt = tree_cons (get_identifier ("fastcall"), NULL, NULL);
  else
    {
      alt = tree_cons (NULL, build_int_cst (NULL, 2), NULL);
      alt = tree_cons (get_identifier ("regparm"), alt, NULL);
    }
  decl_attributes (node, alt, flags);

  return NULL_TREE;
}

/* This function determines from TYPE the calling-convention.  */

unsigned int
ix86_get_callcvt (const_tree type)
{
  unsigned int ret = 0;
  bool is_stdarg;
  tree attrs;

  if (TARGET_64BIT)
    return IX86_CALLCVT_CDECL;

  attrs = TYPE_ATTRIBUTES (type);
  if (attrs != NULL_TREE)
    {
      if (lookup_attribute ("cdecl", attrs))
	ret |= IX86_CALLCVT_CDECL;
      else if (lookup_attribute ("stdcall", attrs))
	ret |= IX86_CALLCVT_STDCALL;
      else if (lookup_attribute ("fastcall", attrs))
	ret |= IX86_CALLCVT_FASTCALL;
      else if (lookup_attribute ("thiscall", attrs))
	ret |= IX86_CALLCVT_THISCALL;

      /* Regparam isn't allowed for thiscall and fastcall.  */
      if ((ret & (IX86_CALLCVT_THISCALL | IX86_CALLCVT_FASTCALL)) == 0)
	{
	  if (lookup_attribute ("regparm", attrs))
	    ret |= IX86_CALLCVT_REGPARM;
	  if (lookup_attribute ("sseregparm", attrs))
	    ret |= IX86_CALLCVT_SSEREGPARM;
	}

      if (IX86_BASE_CALLCVT(ret) != 0)
	return ret;
    }

  is_stdarg = stdarg_p (type);
  if (TARGET_RTD && !is_stdarg)
    return IX86_CALLCVT_STDCALL | ret;

  if (ret != 0
      || is_stdarg
      || TREE_CODE (type) != METHOD_TYPE
      || ix86_function_type_abi (type) != MS_ABI)
    return IX86_CALLCVT_CDECL | ret;

  return IX86_CALLCVT_THISCALL;
}

/* Return 0 if the attributes for two types are incompatible, 1 if they
   are compatible, and 2 if they are nearly compatible (which causes a
   warning to be generated).  */

static int
ix86_comp_type_attributes (const_tree type1, const_tree type2)
{
  unsigned int ccvt1, ccvt2;

  if (TREE_CODE (type1) != FUNCTION_TYPE
      && TREE_CODE (type1) != METHOD_TYPE)
    return 1;

  ccvt1 = ix86_get_callcvt (type1);
  ccvt2 = ix86_get_callcvt (type2);
  if (ccvt1 != ccvt2)
    return 0;
  if (ix86_function_regparm (type1, NULL)
      != ix86_function_regparm (type2, NULL))
    return 0;

  return 1;
}

/* Return the regparm value for a function with the indicated TYPE and DECL.
   DECL may be NULL when calling function indirectly
   or considering a libcall.  */

static int
ix86_function_regparm (const_tree type, const_tree decl)
{
  tree attr;
  int regparm;
  unsigned int ccvt;

  if (TARGET_64BIT)
    return (ix86_function_type_abi (type) == SYSV_ABI
	    ? X86_64_REGPARM_MAX : X86_64_MS_REGPARM_MAX);
  ccvt = ix86_get_callcvt (type);
  regparm = ix86_regparm;

  if ((ccvt & IX86_CALLCVT_REGPARM) != 0)
    {
      attr = lookup_attribute ("regparm", TYPE_ATTRIBUTES (type));
      if (attr)
	{
	  regparm = TREE_INT_CST_LOW (TREE_VALUE (TREE_VALUE (attr)));
	  return regparm;
	}
    }
  else if ((ccvt & IX86_CALLCVT_FASTCALL) != 0)
    return 2;
  else if ((ccvt & IX86_CALLCVT_THISCALL) != 0)
    return 1;

  /* Use register calling convention for local functions when possible.  */
  if (decl
      && TREE_CODE (decl) == FUNCTION_DECL)
    {
      cgraph_node *target = cgraph_node::get (decl);
      if (target)
	target = target->function_symbol ();

      /* Caller and callee must agree on the calling convention, so
	 checking here just optimize means that with
	 __attribute__((optimize (...))) caller could use regparm convention
	 and callee not, or vice versa.  Instead look at whether the callee
	 is optimized or not.  */
      if (target && opt_for_fn (target->decl, optimize)
	  && !(profile_flag && !flag_fentry))
	{
	  cgraph_local_info *i = &target->local;
	  if (i && i->local && i->can_change_signature)
	    {
	      int local_regparm, globals = 0, regno;

	      /* Make sure no regparm register is taken by a
		 fixed register variable.  */
	      for (local_regparm = 0; local_regparm < REGPARM_MAX;
		   local_regparm++)
		if (fixed_regs[local_regparm])
		  break;

	      /* We don't want to use regparm(3) for nested functions as
		 these use a static chain pointer in the third argument.  */
	      if (local_regparm == 3 && DECL_STATIC_CHAIN (target->decl))
		local_regparm = 2;

	      /* Save a register for the split stack.  */
	      if (flag_split_stack)
		{
		  if (local_regparm == 3)
		    local_regparm = 2;
		  else if (local_regparm == 2
			   && DECL_STATIC_CHAIN (target->decl))
		    local_regparm = 1;
		}

	      /* Each fixed register usage increases register pressure,
		 so less registers should be used for argument passing.
		 This functionality can be overriden by an explicit
		 regparm value.  */
	      for (regno = AX_REG; regno <= DI_REG; regno++)
		if (fixed_regs[regno])
		  globals++;

	      local_regparm
		= globals < local_regparm ? local_regparm - globals : 0;

	      if (local_regparm > regparm)
		regparm = local_regparm;
	    }
	}
    }

  return regparm;
}

/* Return 1 or 2, if we can pass up to SSE_REGPARM_MAX SFmode (1) and
   DFmode (2) arguments in SSE registers for a function with the
   indicated TYPE and DECL.  DECL may be NULL when calling function
   indirectly or considering a libcall.  Return -1 if any FP parameter
   should be rejected by error.  This is used in siutation we imply SSE
   calling convetion but the function is called from another function with
   SSE disabled. Otherwise return 0.  */

static int
ix86_function_sseregparm (const_tree type, const_tree decl, bool warn)
{
  gcc_assert (!TARGET_64BIT);

  /* Use SSE registers to pass SFmode and DFmode arguments if requested
     by the sseregparm attribute.  */
  if (TARGET_SSEREGPARM
      || (type && lookup_attribute ("sseregparm", TYPE_ATTRIBUTES (type))))
    {
      if (!TARGET_SSE)
	{
	  if (warn)
	    {
	      if (decl)
		error ("calling %qD with attribute sseregparm without "
		       "SSE/SSE2 enabled", decl);
	      else
		error ("calling %qT with attribute sseregparm without "
		       "SSE/SSE2 enabled", type);
	    }
	  return 0;
	}

      return 2;
    }

  if (!decl)
    return 0;

  cgraph_node *target = cgraph_node::get (decl);
  if (target)
    target = target->function_symbol ();

  /* For local functions, pass up to SSE_REGPARM_MAX SFmode
     (and DFmode for SSE2) arguments in SSE registers.  */
  if (target
      /* TARGET_SSE_MATH */
      && (target_opts_for_fn (target->decl)->x_ix86_fpmath & FPMATH_SSE)
      && opt_for_fn (target->decl, optimize)
      && !(profile_flag && !flag_fentry))
    {
      cgraph_local_info *i = &target->local;
      if (i && i->local && i->can_change_signature)
	{
	  /* Refuse to produce wrong code when local function with SSE enabled
	     is called from SSE disabled function.
	     FIXME: We need a way to detect these cases cross-ltrans partition
	     and avoid using SSE calling conventions on local functions called
	     from function with SSE disabled.  For now at least delay the
	     warning until we know we are going to produce wrong code.
	     See PR66047  */
	  if (!TARGET_SSE && warn)
	    return -1;
	  return TARGET_SSE2_P (target_opts_for_fn (target->decl)
				->x_ix86_isa_flags) ? 2 : 1;
	}
    }

  return 0;
}

/* Return true if EAX is live at the start of the function.  Used by
   ix86_expand_prologue to determine if we need special help before
   calling allocate_stack_worker.  */

static bool
ix86_eax_live_at_start_p (void)
{
  /* Cheat.  Don't bother working forward from ix86_function_regparm
     to the function type to whether an actual argument is located in
     eax.  Instead just look at cfg info, which is still close enough
     to correct at this point.  This gives false positives for broken
     functions that might use uninitialized data that happens to be
     allocated in eax, but who cares?  */
  return REGNO_REG_SET_P (df_get_live_out (ENTRY_BLOCK_PTR_FOR_FN (cfun)), 0);
}

static bool
ix86_keep_aggregate_return_pointer (tree fntype)
{
  tree attr;

  if (!TARGET_64BIT)
    {
      attr = lookup_attribute ("callee_pop_aggregate_return",
			       TYPE_ATTRIBUTES (fntype));
      if (attr)
	return (TREE_INT_CST_LOW (TREE_VALUE (TREE_VALUE (attr))) == 0);

      /* For 32-bit MS-ABI the default is to keep aggregate
         return pointer.  */
      if (ix86_function_type_abi (fntype) == MS_ABI)
	return true;
    }
  return KEEP_AGGREGATE_RETURN_POINTER != 0;
}

/* Value is the number of bytes of arguments automatically
   popped when returning from a subroutine call.
   FUNDECL is the declaration node of the function (as a tree),
   FUNTYPE is the data type of the function (as a tree),
   or for a library call it is an identifier node for the subroutine name.
   SIZE is the number of bytes of arguments passed on the stack.

   On the 80386, the RTD insn may be used to pop them if the number
     of args is fixed, but if the number is variable then the caller
     must pop them all.  RTD can't be used for library calls now
     because the library is compiled with the Unix compiler.
   Use of RTD is a selectable option, since it is incompatible with
   standard Unix calling sequences.  If the option is not selected,
   the caller must always pop the args.

   The attribute stdcall is equivalent to RTD on a per module basis.  */

static int
ix86_return_pops_args (tree fundecl, tree funtype, int size)
{
  unsigned int ccvt;

  /* None of the 64-bit ABIs pop arguments.  */
  if (TARGET_64BIT)
    return 0;

  ccvt = ix86_get_callcvt (funtype);

  if ((ccvt & (IX86_CALLCVT_STDCALL | IX86_CALLCVT_FASTCALL
	       | IX86_CALLCVT_THISCALL)) != 0
      && ! stdarg_p (funtype))
    return size;

  /* Lose any fake structure return argument if it is passed on the stack.  */
  if (aggregate_value_p (TREE_TYPE (funtype), fundecl)
      && !ix86_keep_aggregate_return_pointer (funtype))
    {
      int nregs = ix86_function_regparm (funtype, fundecl);
      if (nregs == 0)
	return GET_MODE_SIZE (Pmode);
    }

  return 0;
}

/* Implement the TARGET_LEGITIMATE_COMBINED_INSN hook.  */

static bool
ix86_legitimate_combined_insn (rtx_insn *insn)
{
  int i;

  /* Check operand constraints in case hard registers were propagated
     into insn pattern.  This check prevents combine pass from
     generating insn patterns with invalid hard register operands.
     These invalid insns can eventually confuse reload to error out
     with a spill failure.  See also PRs 46829 and 46843.  */

  gcc_assert (INSN_CODE (insn) >= 0);

  extract_insn (insn);
  preprocess_constraints (insn);

  int n_operands = recog_data.n_operands;
  int n_alternatives = recog_data.n_alternatives;
  for (i = 0; i < n_operands; i++)
    {
      rtx op = recog_data.operand[i];
      machine_mode mode = GET_MODE (op);
      const operand_alternative *op_alt;
      int offset = 0;
      bool win;
      int j;

      /* A unary operator may be accepted by the predicate, but it
	 is irrelevant for matching constraints.  */
      if (UNARY_P (op))
	op = XEXP (op, 0);

      if (SUBREG_P (op))
	{
	  if (REG_P (SUBREG_REG (op))
	      && REGNO (SUBREG_REG (op)) < FIRST_PSEUDO_REGISTER)
	    offset = subreg_regno_offset (REGNO (SUBREG_REG (op)),
					  GET_MODE (SUBREG_REG (op)),
					  SUBREG_BYTE (op),
					  GET_MODE (op));
	  op = SUBREG_REG (op);
	}

      if (!(REG_P (op) && HARD_REGISTER_P (op)))
	continue;

      op_alt = recog_op_alt;

      /* Operand has no constraints, anything is OK.  */
      win = !n_alternatives;

      alternative_mask preferred = get_preferred_alternatives (insn);
      for (j = 0; j < n_alternatives; j++, op_alt += n_operands)
	{
	  if (!TEST_BIT (preferred, j))
	    continue;
	  if (op_alt[i].anything_ok
	      || (op_alt[i].matches != -1
		  && operands_match_p
		  (recog_data.operand[i],
		   recog_data.operand[op_alt[i].matches]))
	      || reg_fits_class_p (op, op_alt[i].cl, offset, mode))
	    {
	      win = true;
	      break;
	    }
	}

      if (!win)
	return false;
    }

  return true;
}

/* Implement the TARGET_ASAN_SHADOW_OFFSET hook.  */

static unsigned HOST_WIDE_INT
ix86_asan_shadow_offset (void)
{
  return TARGET_LP64 ? (TARGET_MACHO ? (HOST_WIDE_INT_1 << 44)
				     : HOST_WIDE_INT_C (0x7fff8000))
		     : (HOST_WIDE_INT_1 << 29);
}

/* Argument support functions.  */

/* Return true when register may be used to pass function parameters.  */
bool
ix86_function_arg_regno_p (int regno)
{
  int i;
  enum calling_abi call_abi;
  const int *parm_regs;

  if (TARGET_MPX && BND_REGNO_P (regno))
    return true;

  if (!TARGET_64BIT)
    {
      if (TARGET_MACHO)
        return (regno < REGPARM_MAX
                || (TARGET_SSE && SSE_REGNO_P (regno) && !fixed_regs[regno]));
      else
        return (regno < REGPARM_MAX
	        || (TARGET_MMX && MMX_REGNO_P (regno)
	  	    && (regno < FIRST_MMX_REG + MMX_REGPARM_MAX))
	        || (TARGET_SSE && SSE_REGNO_P (regno)
		    && (regno < FIRST_SSE_REG + SSE_REGPARM_MAX)));
    }

  if (TARGET_SSE && SSE_REGNO_P (regno)
      && (regno < FIRST_SSE_REG + SSE_REGPARM_MAX))
    return true;

  /* TODO: The function should depend on current function ABI but
     builtins.c would need updating then. Therefore we use the
     default ABI.  */
  call_abi = ix86_cfun_abi ();

  /* RAX is used as hidden argument to va_arg functions.  */
  if (call_abi == SYSV_ABI && regno == AX_REG)
    return true;

  if (call_abi == MS_ABI)
    parm_regs = x86_64_ms_abi_int_parameter_registers;
  else
    parm_regs = x86_64_int_parameter_registers;

  for (i = 0; i < (call_abi == MS_ABI
		   ? X86_64_MS_REGPARM_MAX : X86_64_REGPARM_MAX); i++)
    if (regno == parm_regs[i])
      return true;
  return false;
}

/* Return if we do not know how to pass TYPE solely in registers.  */

static bool
ix86_must_pass_in_stack (machine_mode mode, const_tree type)
{
  if (must_pass_in_stack_var_size_or_pad (mode, type))
    return true;

  /* For 32-bit, we want TImode aggregates to go on the stack.  But watch out!
     The layout_type routine is crafty and tries to trick us into passing
     currently unsupported vector types on the stack by using TImode.  */
  return (!TARGET_64BIT && mode == TImode
	  && type && TREE_CODE (type) != VECTOR_TYPE);
}

/* It returns the size, in bytes, of the area reserved for arguments passed
   in registers for the function represented by fndecl dependent to the used
   abi format.  */
int
ix86_reg_parm_stack_space (const_tree fndecl)
{
  enum calling_abi call_abi = SYSV_ABI;
  if (fndecl != NULL_TREE && TREE_CODE (fndecl) == FUNCTION_DECL)
    call_abi = ix86_function_abi (fndecl);
  else
    call_abi = ix86_function_type_abi (fndecl);
  if (TARGET_64BIT && call_abi == MS_ABI)
    return 32;
  return 0;
}

/* We add this as a workaround in order to use libc_has_function
   hook in i386.md.  */
bool
ix86_libc_has_function (enum function_class fn_class)
{
  return targetm.libc_has_function (fn_class);
}

/* Returns value SYSV_ABI, MS_ABI dependent on fntype,
   specifying the call abi used.  */
enum calling_abi
ix86_function_type_abi (const_tree fntype)
{
  enum calling_abi abi = ix86_abi;

  if (fntype == NULL_TREE || TYPE_ATTRIBUTES (fntype) == NULL_TREE)
    return abi;

  if (abi == SYSV_ABI
      && lookup_attribute ("ms_abi", TYPE_ATTRIBUTES (fntype)))
    {
      static int warned;
      if (TARGET_X32 && !warned)
	{
	  error ("X32 does not support ms_abi attribute");
	  warned = 1;
	}

      abi = MS_ABI;
    }
  else if (abi == MS_ABI
	   && lookup_attribute ("sysv_abi", TYPE_ATTRIBUTES (fntype)))
    abi = SYSV_ABI;

  return abi;
}

static enum calling_abi
ix86_function_abi (const_tree fndecl)
{
  return fndecl ? ix86_function_type_abi (TREE_TYPE (fndecl)) : ix86_abi;
}

/* Returns value SYSV_ABI, MS_ABI dependent on cfun,
   specifying the call abi used.  */
enum calling_abi
ix86_cfun_abi (void)
{
  return cfun ? cfun->machine->call_abi : ix86_abi;
}

static bool
ix86_function_ms_hook_prologue (const_tree fn)
{
  if (fn && lookup_attribute ("ms_hook_prologue", DECL_ATTRIBUTES (fn)))
    {
      if (decl_function_context (fn) != NULL_TREE)
	error_at (DECL_SOURCE_LOCATION (fn),
		  "ms_hook_prologue is not compatible with nested function");
      else
        return true;
    }
  return false;
}

static bool
ix86_function_naked (const_tree fn)
{
  if (fn && lookup_attribute ("naked", DECL_ATTRIBUTES (fn)))
    return true;

  return false;
}

/* Write the extra assembler code needed to declare a function properly.  */

void
ix86_asm_output_function_label (FILE *asm_out_file, const char *fname,
				tree decl)
{
  bool is_ms_hook = ix86_function_ms_hook_prologue (decl);

  if (is_ms_hook)
    {
      int i, filler_count = (TARGET_64BIT ? 32 : 16);
      unsigned int filler_cc = 0xcccccccc;

      for (i = 0; i < filler_count; i += 4)
        fprintf (asm_out_file, ASM_LONG " %#x\n", filler_cc);
    }

#ifdef SUBTARGET_ASM_UNWIND_INIT
  SUBTARGET_ASM_UNWIND_INIT (asm_out_file);
#endif

  ASM_OUTPUT_LABEL (asm_out_file, fname);

  /* Output magic byte marker, if hot-patch attribute is set.  */
  if (is_ms_hook)
    {
      if (TARGET_64BIT)
	{
	  /* leaq [%rsp + 0], %rsp  */
	  fputs (ASM_BYTE "0x48, 0x8d, 0xa4, 0x24, 0x00, 0x00, 0x00, 0x00\n",
		 asm_out_file);
	}
      else
	{
          /* movl.s %edi, %edi
	     push   %ebp
	     movl.s %esp, %ebp */
	  fputs (ASM_BYTE "0x8b, 0xff, 0x55, 0x8b, 0xec\n", asm_out_file);
	}
    }
}

/* Implementation of call abi switching target hook. Specific to FNDECL
   the specific call register sets are set.  See also
   ix86_conditional_register_usage for more details.  */
void
ix86_call_abi_override (const_tree fndecl)
{
  cfun->machine->call_abi = ix86_function_abi (fndecl);
}

/* Return 1 if pseudo register should be created and used to hold
   GOT address for PIC code.  */
bool
ix86_use_pseudo_pic_reg (void)
{
  if ((TARGET_64BIT
       && (ix86_cmodel == CM_SMALL_PIC
	   || TARGET_PECOFF))
      || !flag_pic)
    return false;
  return true;
}

/* Initialize large model PIC register.  */

static rtx_code_label *
ix86_init_large_pic_reg (unsigned int tmp_regno)
{
  rtx_code_label *label;
  rtx tmp_reg;

  gcc_assert (Pmode == DImode);
  label = gen_label_rtx ();
  emit_label (label);
  LABEL_PRESERVE_P (label) = 1;
  tmp_reg = gen_rtx_REG (Pmode, tmp_regno);
  gcc_assert (REGNO (pic_offset_table_rtx) != tmp_regno);
  emit_insn (gen_set_rip_rex64 (pic_offset_table_rtx,
				label));
  emit_insn (gen_set_got_offset_rex64 (tmp_reg, label));
  emit_insn (ix86_gen_add3 (pic_offset_table_rtx,
			    pic_offset_table_rtx, tmp_reg));
  return label;
}

/* Create and initialize PIC register if required.  */
static void
ix86_init_pic_reg (void)
{
  edge entry_edge;
  rtx_insn *seq;
  rtx_code_label *label = NULL;

  if (!ix86_use_pseudo_pic_reg ())
    return;

  start_sequence ();

  if (TARGET_64BIT)
    {
      if (ix86_cmodel == CM_LARGE_PIC)
	label = ix86_init_large_pic_reg (R11_REG);
      else
	emit_insn (gen_set_got_rex64 (pic_offset_table_rtx));
    }
  else
    {
      /*  If there is future mcount call in the function it is more profitable
	  to emit SET_GOT into ABI defined REAL_PIC_OFFSET_TABLE_REGNUM.  */
      rtx reg = crtl->profile
		? gen_rtx_REG (Pmode, REAL_PIC_OFFSET_TABLE_REGNUM)
		: pic_offset_table_rtx;
      rtx_insn *insn = emit_insn (gen_set_got (reg));
      RTX_FRAME_RELATED_P (insn) = 1;
      if (crtl->profile)
        emit_move_insn (pic_offset_table_rtx, reg);
      add_reg_note (insn, REG_CFA_FLUSH_QUEUE, NULL_RTX);
    }

  seq = get_insns ();
  end_sequence ();

  entry_edge = single_succ_edge (ENTRY_BLOCK_PTR_FOR_FN (cfun));
  insert_insn_on_edge (seq, entry_edge);
  commit_one_edge_insertion (entry_edge);

  if (label)
    {
      basic_block bb = BLOCK_FOR_INSN (label);
      rtx_insn *bb_note = PREV_INSN (label);
      /* If the note preceding the label starts a basic block, and the
	 label is a member of the same basic block, interchange the two.  */
      if (bb_note != NULL_RTX
	  && NOTE_INSN_BASIC_BLOCK_P (bb_note)
	  && bb != NULL
	  && bb == BLOCK_FOR_INSN (bb_note))
	{
	  reorder_insns_nobb (bb_note, bb_note, label);
	  BB_HEAD (bb) = label;
	}
    }
}

/* Initialize a variable CUM of type CUMULATIVE_ARGS
   for a call to a function whose data type is FNTYPE.
   For a library call, FNTYPE is 0.  */

void
init_cumulative_args (CUMULATIVE_ARGS *cum,  /* Argument info to initialize */
		      tree fntype,	/* tree ptr for function decl */
		      rtx libname,	/* SYMBOL_REF of library name or 0 */
		      tree fndecl,
		      int caller)
{
  struct cgraph_local_info *i = NULL;
  struct cgraph_node *target = NULL;

  memset (cum, 0, sizeof (*cum));

  if (fndecl)
    {
      target = cgraph_node::get (fndecl);
      if (target)
	{
	  target = target->function_symbol ();
	  i = cgraph_node::local_info (target->decl);
	  cum->call_abi = ix86_function_abi (target->decl);
	}
      else
	cum->call_abi = ix86_function_abi (fndecl);
    }
  else
    cum->call_abi = ix86_function_type_abi (fntype);

  cum->caller = caller;

  /* Set up the number of registers to use for passing arguments.  */
  cum->nregs = ix86_regparm;
  if (TARGET_64BIT)
    {
      cum->nregs = (cum->call_abi == SYSV_ABI
                   ? X86_64_REGPARM_MAX
                   : X86_64_MS_REGPARM_MAX);
    }
  if (TARGET_SSE)
    {
      cum->sse_nregs = SSE_REGPARM_MAX;
      if (TARGET_64BIT)
        {
          cum->sse_nregs = (cum->call_abi == SYSV_ABI
                           ? X86_64_SSE_REGPARM_MAX
                           : X86_64_MS_SSE_REGPARM_MAX);
        }
    }
  if (TARGET_MMX)
    cum->mmx_nregs = MMX_REGPARM_MAX;
  cum->warn_avx512f = true;
  cum->warn_avx = true;
  cum->warn_sse = true;
  cum->warn_mmx = true;

  /* Because type might mismatch in between caller and callee, we need to
     use actual type of function for local calls.
     FIXME: cgraph_analyze can be told to actually record if function uses
     va_start so for local functions maybe_vaarg can be made aggressive
     helping K&R code.
     FIXME: once typesytem is fixed, we won't need this code anymore.  */
  if (i && i->local && i->can_change_signature)
    fntype = TREE_TYPE (target->decl);
  cum->stdarg = stdarg_p (fntype);
  cum->maybe_vaarg = (fntype
		      ? (!prototype_p (fntype) || stdarg_p (fntype))
		      : !libname);

  cum->bnd_regno = FIRST_BND_REG;
  cum->bnds_in_bt = 0;
  cum->force_bnd_pass = 0;
  cum->decl = fndecl;

  if (!TARGET_64BIT)
    {
      /* If there are variable arguments, then we won't pass anything
         in registers in 32-bit mode. */
      if (stdarg_p (fntype))
	{
	  cum->nregs = 0;
	  /* Since in 32-bit, variable arguments are always passed on
	     stack, there is scratch register available for indirect
	     sibcall.  */
	  cfun->machine->arg_reg_available = true;
	  cum->sse_nregs = 0;
	  cum->mmx_nregs = 0;
	  cum->warn_avx512f = false;
	  cum->warn_avx = false;
	  cum->warn_sse = false;
	  cum->warn_mmx = false;
	  return;
	}

      /* Use ecx and edx registers if function has fastcall attribute,
	 else look for regparm information.  */
      if (fntype)
	{
	  unsigned int ccvt = ix86_get_callcvt (fntype);
	  if ((ccvt & IX86_CALLCVT_THISCALL) != 0)
	    {
	      cum->nregs = 1;
	      cum->fastcall = 1; /* Same first register as in fastcall.  */
	    }
	  else if ((ccvt & IX86_CALLCVT_FASTCALL) != 0)
	    {
	      cum->nregs = 2;
	      cum->fastcall = 1;
	    }
	  else
	    cum->nregs = ix86_function_regparm (fntype, fndecl);
	}

      /* Set up the number of SSE registers used for passing SFmode
	 and DFmode arguments.  Warn for mismatching ABI.  */
      cum->float_in_sse = ix86_function_sseregparm (fntype, fndecl, true);
    }

  cfun->machine->arg_reg_available = (cum->nregs > 0);
}

#endif

#define MAX_CLASSES 8

/* Return the "natural" mode for TYPE.  In most cases, this is just TYPE_MODE.
   But in the case of vector types, it is some vector mode.

   When we have only some of our vector isa extensions enabled, then there
   are some modes for which vector_mode_supported_p is false.  For these
   modes, the generic vector support in gcc will choose some non-vector mode
   in order to implement the type.  By computing the natural mode, we'll
   select the proper ABI location for the operand and not depend on whatever
   the middle-end decides to do with these vector types.

   The midde-end can't deal with the vector types > 16 bytes.  In this
   case, we return the original mode and warn ABI change if CUM isn't
   NULL. 

   If INT_RETURN is true, warn ABI change if the vector mode isn't
   available for function return value.  */

static machine_mode
type_natural_mode (const_tree type, const CUMULATIVE_ARGS *cum,
		   bool in_return = false)
{
  machine_mode mode = TYPE_MODE (type);

  if (TREE_CODE (type) == VECTOR_TYPE && !VECTOR_MODE_P (mode))
    {
      HOST_WIDE_INT size = int_size_in_bytes (type);
      if ((size == 8 || size == 16 || size == 32 || size == 64)
	  /* ??? Generic code allows us to create width 1 vectors.  Ignore.  */
	  && TYPE_VECTOR_SUBPARTS (type) > 1)
	{
	  machine_mode innermode = TYPE_MODE (TREE_TYPE (type));

	  /* There are no XFmode vector modes.  */
	  if (innermode == XFmode)
	    return mode;

	  if (TREE_CODE (TREE_TYPE (type)) == REAL_TYPE)
	    mode = MIN_MODE_VECTOR_FLOAT;
	  else
	    mode = MIN_MODE_VECTOR_INT;

	  /* Get the mode which has this inner mode and number of units.  */
	  FOR_EACH_MODE_FROM (mode, mode)
	    if (GET_MODE_NUNITS (mode) == TYPE_VECTOR_SUBPARTS (type)
		&& GET_MODE_INNER (mode) == innermode)
	      {
		if (size == 64 && !TARGET_AVX512F && !TARGET_IAMCU)
		  {
		    static bool warnedavx512f;
		    static bool warnedavx512f_ret;

		    if (cum && cum->warn_avx512f && !warnedavx512f)
		      {
			if (warning (OPT_Wpsabi, "AVX512F vector argument "
				     "without AVX512F enabled changes the ABI"))
			  warnedavx512f = true;
		      }
		    else if (in_return && !warnedavx512f_ret)
		      {
			if (warning (OPT_Wpsabi, "AVX512F vector return "
				     "without AVX512F enabled changes the ABI"))
			  warnedavx512f_ret = true;
		      }

		    return TYPE_MODE (type);
		  }
		else if (size == 32 && !TARGET_AVX && !TARGET_IAMCU)
		  {
		    static bool warnedavx;
		    static bool warnedavx_ret;

		    if (cum && cum->warn_avx && !warnedavx)
		      {
			if (warning (OPT_Wpsabi, "AVX vector argument "
				     "without AVX enabled changes the ABI"))
			  warnedavx = true;
		      }
		    else if (in_return && !warnedavx_ret)
		      {
			if (warning (OPT_Wpsabi, "AVX vector return "
				     "without AVX enabled changes the ABI"))
			  warnedavx_ret = true;
		      }

		    return TYPE_MODE (type);
		  }
		else if (((size == 8 && TARGET_64BIT) || size == 16)
			 && !TARGET_SSE
			 && !TARGET_IAMCU)
		  {
		    static bool warnedsse;
		    static bool warnedsse_ret;

		    if (cum && cum->warn_sse && !warnedsse)
		      {
			if (warning (OPT_Wpsabi, "SSE vector argument "
				     "without SSE enabled changes the ABI"))
			  warnedsse = true;
		      }
		    else if (!TARGET_64BIT && in_return && !warnedsse_ret)
		      {
			if (warning (OPT_Wpsabi, "SSE vector return "
				     "without SSE enabled changes the ABI"))
			  warnedsse_ret = true;
		      }
		  }
		else if ((size == 8 && !TARGET_64BIT)
			 && (!cfun
			     || cfun->machine->func_type == TYPE_NORMAL)
			 && !TARGET_MMX
			 && !TARGET_IAMCU)
		  {
		    static bool warnedmmx;
		    static bool warnedmmx_ret;

		    if (cum && cum->warn_mmx && !warnedmmx)
		      {
			if (warning (OPT_Wpsabi, "MMX vector argument "
				     "without MMX enabled changes the ABI"))
			  warnedmmx = true;
		      }
		    else if (in_return && !warnedmmx_ret)
		      {
			if (warning (OPT_Wpsabi, "MMX vector return "
				     "without MMX enabled changes the ABI"))
			  warnedmmx_ret = true;
		      }
		  }
		return mode;
	      }

	  gcc_unreachable ();
	}
    }

  return mode;
}

#if 0
/* We want to pass a value in REGNO whose "natural" mode is MODE.  However,
   this may not agree with the mode that the type system has chosen for the
   register, which is ORIG_MODE.  If ORIG_MODE is not BLKmode, then we can
   go ahead and use it.  Otherwise we have to build a PARALLEL instead.  */

static rtx
gen_reg_or_parallel (machine_mode mode, machine_mode orig_mode,
		     unsigned int regno)
{
  rtx tmp;

  if (orig_mode != BLKmode)
    tmp = gen_rtx_REG (orig_mode, regno);
  else
    {
      tmp = gen_rtx_REG (mode, regno);
      tmp = gen_rtx_EXPR_LIST (VOIDmode, tmp, const0_rtx);
      tmp = gen_rtx_PARALLEL (orig_mode, gen_rtvec (1, tmp));
    }

  return tmp;
}
#endif

/* x86-64 register passing implementation.  See x86-64 ABI for details.  Goal
   of this code is to classify each 8bytes of incoming argument by the register
   class and assign registers accordingly.  */

/* Return the union class of CLASS1 and CLASS2.
   See the x86-64 PS ABI for details.  */

static enum x86_64_reg_class
merge_classes (enum x86_64_reg_class class1, enum x86_64_reg_class class2)
{
  /* Rule #1: If both classes are equal, this is the resulting class.  */
  if (class1 == class2)
    return class1;

  /* Rule #2: If one of the classes is NO_CLASS, the resulting class is
     the other class.  */
  if (class1 == X86_64_NO_CLASS)
    return class2;
  if (class2 == X86_64_NO_CLASS)
    return class1;

  /* Rule #3: If one of the classes is MEMORY, the result is MEMORY.  */
  if (class1 == X86_64_MEMORY_CLASS || class2 == X86_64_MEMORY_CLASS)
    return X86_64_MEMORY_CLASS;

  /* Rule #4: If one of the classes is INTEGER, the result is INTEGER.  */
  if ((class1 == X86_64_INTEGERSI_CLASS && class2 == X86_64_SSESF_CLASS)
      || (class2 == X86_64_INTEGERSI_CLASS && class1 == X86_64_SSESF_CLASS))
    return X86_64_INTEGERSI_CLASS;
  if (class1 == X86_64_INTEGER_CLASS || class1 == X86_64_INTEGERSI_CLASS
      || class2 == X86_64_INTEGER_CLASS || class2 == X86_64_INTEGERSI_CLASS)
    return X86_64_INTEGER_CLASS;

  /* Rule #5: If one of the classes is X87, X87UP, or COMPLEX_X87 class,
     MEMORY is used.  */
  if (class1 == X86_64_X87_CLASS
      || class1 == X86_64_X87UP_CLASS
      || class1 == X86_64_COMPLEX_X87_CLASS
      || class2 == X86_64_X87_CLASS
      || class2 == X86_64_X87UP_CLASS
      || class2 == X86_64_COMPLEX_X87_CLASS)
    return X86_64_MEMORY_CLASS;

  /* Rule #6: Otherwise class SSE is used.  */
  return X86_64_SSE_CLASS;
}

/* Classify the argument of type TYPE and mode MODE.
   CLASSES will be filled by the register class used to pass each word
   of the operand.  The number of words is returned.  In case the parameter
   should be passed in memory, 0 is returned. As a special case for zero
   sized containers, classes[0] will be NO_CLASS and 1 is returned.

   BIT_OFFSET is used internally for handling records and specifies offset
   of the offset in bits modulo 512 to avoid overflow cases.

   See the x86-64 PS ABI for details.
*/

static int
classify_argument (machine_mode mode, const_tree type,
		   enum x86_64_reg_class classes[MAX_CLASSES], int bit_offset)
{
  HOST_WIDE_INT bytes =
    (mode == BLKmode) ? int_size_in_bytes (type) : (int) GET_MODE_SIZE (mode);
  int words = CEIL (bytes + (bit_offset % 64) / 8, UNITS_PER_WORD);

  /* Variable sized entities are always passed/returned in memory.  */
  if (bytes < 0)
    return 0;

  if (mode != VOIDmode
      && targetm.calls.must_pass_in_stack (mode, type))
    return 0;

  if (type && AGGREGATE_TYPE_P (type))
    {
      int i;
      tree field;
      enum x86_64_reg_class subclasses[MAX_CLASSES];

      /* On x86-64 we pass structures larger than 64 bytes on the stack.  */
      if (bytes > 64)
	return 0;

      for (i = 0; i < words; i++)
	classes[i] = X86_64_NO_CLASS;

      /* Zero sized arrays or structures are NO_CLASS.  We return 0 to
	 signalize memory class, so handle it as special case.  */
      if (!words)
	{
	  classes[0] = X86_64_NO_CLASS;
	  return 1;
	}

      /* Classify each field of record and merge classes.  */
      switch (TREE_CODE (type))
	{
	case RECORD_TYPE:
	  /* And now merge the fields of structure.  */
	  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
	    {
	      if (TREE_CODE (field) == FIELD_DECL)
		{
		  int num;

		  if (TREE_TYPE (field) == error_mark_node)
		    continue;

		  /* Bitfields are always classified as integer.  Handle them
		     early, since later code would consider them to be
		     misaligned integers.  */
		  if (DECL_BIT_FIELD (field))
		    {
		      for (i = (int_bit_position (field)
				+ (bit_offset % 64)) / 8 / 8;
			   i < ((int_bit_position (field) + (bit_offset % 64))
			        + tree_to_shwi (DECL_SIZE (field))
				+ 63) / 8 / 8; i++)
			classes[i] =
			  merge_classes (X86_64_INTEGER_CLASS,
					 classes[i]);
		    }
		  else
		    {
		      int pos;

		      type = TREE_TYPE (field);

		      /* Flexible array member is ignored.  */
		      if (TYPE_MODE (type) == BLKmode
			  && TREE_CODE (type) == ARRAY_TYPE
			  && TYPE_SIZE (type) == NULL_TREE
			  && TYPE_DOMAIN (type) != NULL_TREE
			  && (TYPE_MAX_VALUE (TYPE_DOMAIN (type))
			      == NULL_TREE))
			{
			  static bool warned;

			  if (!warned && warn_psabi)
			    {
			      warned = true;
			      inform (input_location,
				      "the ABI of passing struct with"
				      " a flexible array member has"
				      " changed in GCC 4.4");
			    }
			  continue;
			}
		      num = classify_argument (TYPE_MODE (type), type,
					       subclasses,
					       (int_bit_position (field)
						+ bit_offset) % 512);
		      if (!num)
			return 0;
		      pos = (int_bit_position (field)
			     + (bit_offset % 64)) / 8 / 8;
		      for (i = 0; i < num && (i + pos) < words; i++)
			classes[i + pos] =
			  merge_classes (subclasses[i], classes[i + pos]);
		    }
		}
	    }
	  break;

	case ARRAY_TYPE:
	  /* Arrays are handled as small records.  */
	  {
	    int num;
	    num = classify_argument (TYPE_MODE (TREE_TYPE (type)),
				     TREE_TYPE (type), subclasses, bit_offset);
	    if (!num)
	      return 0;

	    /* The partial classes are now full classes.  */
	    if (subclasses[0] == X86_64_SSESF_CLASS && bytes != 4)
	      subclasses[0] = X86_64_SSE_CLASS;
	    if (subclasses[0] == X86_64_INTEGERSI_CLASS
		&& !((bit_offset % 64) == 0 && bytes == 4))
	      subclasses[0] = X86_64_INTEGER_CLASS;

	    for (i = 0; i < words; i++)
	      classes[i] = subclasses[i % num];

	    break;
	  }
	case UNION_TYPE:
	case QUAL_UNION_TYPE:
	  /* Unions are similar to RECORD_TYPE but offset is always 0.
	     */
	  for (field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
	    {
	      if (TREE_CODE (field) == FIELD_DECL)
		{
		  int num;

		  if (TREE_TYPE (field) == error_mark_node)
		    continue;

		  num = classify_argument (TYPE_MODE (TREE_TYPE (field)),
					   TREE_TYPE (field), subclasses,
					   bit_offset);
		  if (!num)
		    return 0;
		  for (i = 0; i < num && i < words; i++)
		    classes[i] = merge_classes (subclasses[i], classes[i]);
		}
	    }
	  break;

	default:
	  gcc_unreachable ();
	}

      if (words > 2)
	{
	  /* When size > 16 bytes, if the first one isn't
	     X86_64_SSE_CLASS or any other ones aren't
	     X86_64_SSEUP_CLASS, everything should be passed in
	     memory.  */
	  if (classes[0] != X86_64_SSE_CLASS)
	      return 0;

	  for (i = 1; i < words; i++)
	    if (classes[i] != X86_64_SSEUP_CLASS)
	      return 0;
	}

      /* Final merger cleanup.  */
      for (i = 0; i < words; i++)
	{
	  /* If one class is MEMORY, everything should be passed in
	     memory.  */
	  if (classes[i] == X86_64_MEMORY_CLASS)
	    return 0;

	  /* The X86_64_SSEUP_CLASS should be always preceded by
	     X86_64_SSE_CLASS or X86_64_SSEUP_CLASS.  */
	  if (classes[i] == X86_64_SSEUP_CLASS
	      && classes[i - 1] != X86_64_SSE_CLASS
	      && classes[i - 1] != X86_64_SSEUP_CLASS)
	    {
	      /* The first one should never be X86_64_SSEUP_CLASS.  */
	      gcc_assert (i != 0);
	      classes[i] = X86_64_SSE_CLASS;
	    }

	  /*  If X86_64_X87UP_CLASS isn't preceded by X86_64_X87_CLASS,
	       everything should be passed in memory.  */
	  if (classes[i] == X86_64_X87UP_CLASS
	      && (classes[i - 1] != X86_64_X87_CLASS))
	    {
	      static bool warned;

	      /* The first one should never be X86_64_X87UP_CLASS.  */
	      gcc_assert (i != 0);
	      if (!warned && warn_psabi)
		{
		  warned = true;
		  inform (input_location,
			  "the ABI of passing union with long double"
			  " has changed in GCC 4.4");
		}
	      return 0;
	    }
	}
      return words;
    }

  /* Compute alignment needed.  We align all types to natural boundaries with
     exception of XFmode that is aligned to 64bits.  */
  if (mode != VOIDmode && mode != BLKmode)
    {
      int mode_alignment = GET_MODE_BITSIZE (mode);

      if (mode == XFmode)
	mode_alignment = 128;
      else if (mode == XCmode)
	mode_alignment = 256;
      if (COMPLEX_MODE_P (mode))
	mode_alignment /= 2;
      /* Misaligned fields are always returned in memory.  */
      if (bit_offset % mode_alignment)
	return 0;
    }

  /* for V1xx modes, just use the base mode */
  if (VECTOR_MODE_P (mode) && mode != V1DImode && mode != V1TImode
      && GET_MODE_UNIT_SIZE (mode) == bytes)
    mode = GET_MODE_INNER (mode);

  /* Classification of atomic types.  */
  switch (mode)
    {
    case E_SDmode:
    case E_DDmode:
      classes[0] = X86_64_SSE_CLASS;
      return 1;
    case E_TDmode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      return 2;
    case E_DImode:
    case E_SImode:
    case E_HImode:
    case E_QImode:
    case E_CSImode:
    case E_CHImode:
    case E_CQImode:
      {
	int size = bit_offset + (int) GET_MODE_BITSIZE (mode);

	/* Analyze last 128 bits only.  */
	size = (size - 1) & 0x7f;

	if (size < 32)
	  {
	    classes[0] = X86_64_INTEGERSI_CLASS;
	    return 1;
	  }
	else if (size < 64)
	  {
	    classes[0] = X86_64_INTEGER_CLASS;
	    return 1;
	  }
	else if (size < 64+32)
	  {
	    classes[0] = X86_64_INTEGER_CLASS;
	    classes[1] = X86_64_INTEGERSI_CLASS;
	    return 2;
	  }
	else if (size < 64+64)
	  {
	    classes[0] = classes[1] = X86_64_INTEGER_CLASS;
	    return 2;
	  }
	else
	  gcc_unreachable ();
      }
    case E_CDImode:
    case E_TImode:
      classes[0] = classes[1] = X86_64_INTEGER_CLASS;
      return 2;
    case E_COImode:
    case E_OImode:
      /* OImode shouldn't be used directly.  */
      gcc_unreachable ();
    case E_CTImode:
      return 0;
    case E_SFmode:
      if (!(bit_offset % 64))
	classes[0] = X86_64_SSESF_CLASS;
      else
	classes[0] = X86_64_SSE_CLASS;
      return 1;
    case E_DFmode:
      classes[0] = X86_64_SSEDF_CLASS;
      return 1;
    case E_XFmode:
      classes[0] = X86_64_X87_CLASS;
      classes[1] = X86_64_X87UP_CLASS;
      return 2;
    case E_TFmode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      return 2;
    case E_SCmode:
      classes[0] = X86_64_SSE_CLASS;
      if (!(bit_offset % 64))
	return 1;
      else
	{
	  static bool warned;

	  if (!warned && warn_psabi)
	    {
	      warned = true;
	      inform (input_location,
		      "the ABI of passing structure with complex float"
		      " member has changed in GCC 4.4");
	    }
	  classes[1] = X86_64_SSESF_CLASS;
	  return 2;
	}
    case E_DCmode:
      classes[0] = X86_64_SSEDF_CLASS;
      classes[1] = X86_64_SSEDF_CLASS;
      return 2;
    case E_XCmode:
      classes[0] = X86_64_COMPLEX_X87_CLASS;
      return 1;
    case E_TCmode:
      /* This modes is larger than 16 bytes.  */
      return 0;
    case E_V8SFmode:
    case E_V8SImode:
    case E_V32QImode:
    case E_V16HImode:
    case E_V4DFmode:
    case E_V4DImode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      classes[2] = X86_64_SSEUP_CLASS;
      classes[3] = X86_64_SSEUP_CLASS;
      return 4;
    case E_V8DFmode:
    case E_V16SFmode:
    case E_V8DImode:
    case E_V16SImode:
    case E_V32HImode:
    case E_V64QImode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      classes[2] = X86_64_SSEUP_CLASS;
      classes[3] = X86_64_SSEUP_CLASS;
      classes[4] = X86_64_SSEUP_CLASS;
      classes[5] = X86_64_SSEUP_CLASS;
      classes[6] = X86_64_SSEUP_CLASS;
      classes[7] = X86_64_SSEUP_CLASS;
      return 8;
    case E_V4SFmode:
    case E_V4SImode:
    case E_V16QImode:
    case E_V8HImode:
    case E_V2DFmode:
    case E_V2DImode:
      classes[0] = X86_64_SSE_CLASS;
      classes[1] = X86_64_SSEUP_CLASS;
      return 2;
    case E_V1TImode:
    case E_V1DImode:
    case E_V2SFmode:
    case E_V2SImode:
    case E_V4HImode:
    case E_V8QImode:
      classes[0] = X86_64_SSE_CLASS;
      return 1;
    case E_BLKmode:
    case E_VOIDmode:
      return 0;
    default:
      gcc_assert (VECTOR_MODE_P (mode));

      if (bytes > 16)
	return 0;

      gcc_assert (GET_MODE_CLASS (GET_MODE_INNER (mode)) == MODE_INT);

      if (bit_offset + GET_MODE_BITSIZE (mode) <= 32)
	classes[0] = X86_64_INTEGERSI_CLASS;
      else
	classes[0] = X86_64_INTEGER_CLASS;
      classes[1] = X86_64_INTEGER_CLASS;
      return 1 + (bytes > 8);
    }
}

/* Examine the argument and return set number of register required in each
   class.  Return true iff parameter should be passed in memory.  */

bool
examine_argument (machine_mode mode, const_tree type, int in_return,
		  int *int_nregs, int *sse_nregs)
{
  enum x86_64_reg_class regclass[MAX_CLASSES];
  int n = classify_argument (mode, type, regclass, 0);

  *int_nregs = 0;
  *sse_nregs = 0;

  if (!n)
    return true;
  for (n--; n >= 0; n--)
    switch (regclass[n])
      {
      case X86_64_INTEGER_CLASS:
      case X86_64_INTEGERSI_CLASS:
	(*int_nregs)++;
	break;
      case X86_64_SSE_CLASS:
      case X86_64_SSESF_CLASS:
      case X86_64_SSEDF_CLASS:
	(*sse_nregs)++;
	break;
      case X86_64_NO_CLASS:
      case X86_64_SSEUP_CLASS:
	break;
      case X86_64_X87_CLASS:
      case X86_64_X87UP_CLASS:
      case X86_64_COMPLEX_X87_CLASS:
	if (!in_return)
	  return true;
	break;
      case X86_64_MEMORY_CLASS:
	gcc_unreachable ();
      }

  return false;
}
