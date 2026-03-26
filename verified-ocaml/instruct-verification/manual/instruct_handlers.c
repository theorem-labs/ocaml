/* instruct_handlers.c -- Standalone instruction handlers extracted from
   OCaml 4.14 runtime/interp.c for VST verification.

   Each handler takes a pointer to interpreter state and returns a status code:
     0 = Step (continue), 1 = Halt, 2 = Error, 3 = CCall

   The original interp.c uses local variables (pc, sp, accu, env, extra_args)
   and goto-based dispatch. Here each handler is a standalone function that
   reads/writes through an interp_state struct.

   Reference: system-ocaml-compiler/runtime/interp.c (OCaml 4.14) */

#include "instruct_defs.h"

/* ================================================================
   Stack operations: ACC, PUSH, PUSHACC, POP, ASSIGN
   ================================================================ */

/* ACC n: accu = sp[n] */
int instr_ACC(interp_state *s, int n) {
    s->accu = s->sp[n];
    s->pc++;
    return STATUS_STEP;
}

/* PUSH: *--sp = accu (same as PUSHACC0) */
int instr_PUSH(interp_state *s) {
    *--(s->sp) = s->accu;
    s->pc++;
    return STATUS_STEP;
}

/* PUSHACC n: push accu, then accu = sp[n] (after push) */
int instr_PUSHACC(interp_state *s, int n) {
    *--(s->sp) = s->accu;
    s->accu = s->sp[n];
    s->pc++;
    return STATUS_STEP;
}

/* POP n: sp += n */
int instr_POP(interp_state *s, int n) {
    s->sp += n;
    s->pc++;
    return STATUS_STEP;
}

/* ASSIGN n: sp[n] = accu; accu = Val_unit */
int instr_ASSIGN(interp_state *s, int n) {
    s->sp[n] = s->accu;
    s->accu = Val_unit;
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Constants: CONST0-3, CONSTINT, PUSHCONST0-3, PUSHCONSTINT
   ================================================================ */

int instr_CONSTINT(interp_state *s, intptr_t n) {
    s->accu = Val_int(n);
    s->pc++;
    return STATUS_STEP;
}

int instr_PUSHCONSTINT(interp_state *s, intptr_t n) {
    *--(s->sp) = s->accu;
    s->accu = Val_int(n);
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Arithmetic: NEGINT, ADDINT, SUBINT, MULINT, DIVINT, MODINT,
               ANDINT, ORINT, XORINT, LSLINT, LSRINT, ASRINT
   ================================================================ */

/* NEGINT: accu = 2 - accu (tagged negation) */
int instr_NEGINT(interp_state *s) {
    s->accu = (value)(2 - (intptr_t)s->accu);
    s->pc++;
    return STATUS_STEP;
}

/* ADDINT: accu = accu + *sp++ - 1 (tagged addition) */
int instr_ADDINT(interp_state *s) {
    s->accu = (value)((intptr_t)s->accu + (intptr_t)*s->sp++ - 1);
    s->pc++;
    return STATUS_STEP;
}

/* SUBINT: accu = accu - *sp++ + 1 (tagged subtraction) */
int instr_SUBINT(interp_state *s) {
    s->accu = (value)((intptr_t)s->accu - (intptr_t)*s->sp++ + 1);
    s->pc++;
    return STATUS_STEP;
}

/* MULINT: accu = Val_long(Long_val(accu) * Long_val(*sp++)) */
int instr_MULINT(interp_state *s) {
    s->accu = Val_long(Long_val(s->accu) * Long_val(*s->sp++));
    s->pc++;
    return STATUS_STEP;
}

/* DIVINT: accu = Val_long(Long_val(accu) / divisor), or error if divisor==0 */
int instr_DIVINT(interp_state *s) {
    intptr_t divisor = Long_val(*s->sp++);
    if (divisor == 0) return STATUS_ERROR;
    s->accu = Val_long(Long_val(s->accu) / divisor);
    s->pc++;
    return STATUS_STEP;
}

/* MODINT: accu = Val_long(Long_val(accu) % divisor), or error if divisor==0 */
int instr_MODINT(interp_state *s) {
    intptr_t divisor = Long_val(*s->sp++);
    if (divisor == 0) return STATUS_ERROR;
    s->accu = Val_long(Long_val(s->accu) % divisor);
    s->pc++;
    return STATUS_STEP;
}

/* ANDINT: accu = accu & *sp++ (tagged AND preserves tag bit) */
int instr_ANDINT(interp_state *s) {
    s->accu = (value)((intptr_t)s->accu & (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

/* ORINT: accu = accu | *sp++ (tagged OR preserves tag bit) */
int instr_ORINT(interp_state *s) {
    s->accu = (value)((intptr_t)s->accu | (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

/* XORINT: accu = (accu ^ *sp++) | 1 (tagged XOR, restore tag bit) */
int instr_XORINT(interp_state *s) {
    s->accu = (value)(((intptr_t)s->accu ^ (intptr_t)*s->sp++) | 1);
    s->pc++;
    return STATUS_STEP;
}

/* LSLINT: accu = ((accu - 1) << Long_val(*sp++)) + 1 */
int instr_LSLINT(interp_state *s) {
    s->accu = (value)((((intptr_t)s->accu - 1) << Long_val(*s->sp++)) + 1);
    s->pc++;
    return STATUS_STEP;
}

/* LSRINT: accu = (((uintptr_t)accu) >> Long_val(*sp++)) | 1 */
int instr_LSRINT(interp_state *s) {
    s->accu = (value)((((uintptr_t)s->accu) >> Long_val(*s->sp++)) | 1);
    s->pc++;
    return STATUS_STEP;
}

/* ASRINT: accu = (((intptr_t)accu) >> Long_val(*sp++)) | 1 */
int instr_ASRINT(interp_state *s) {
    s->accu = (value)((((intptr_t)s->accu) >> Long_val(*s->sp++)) | 1);
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Comparison: EQ, NEQ, LTINT, LEINT, GTINT, GEINT, ULTINT, UGEINT
   ================================================================ */

int instr_EQ(interp_state *s) {
    s->accu = Val_int((intptr_t)s->accu == (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_NEQ(interp_state *s) {
    s->accu = Val_int((intptr_t)s->accu != (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_LTINT(interp_state *s) {
    s->accu = Val_int((intptr_t)s->accu < (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_LEINT(interp_state *s) {
    s->accu = Val_int((intptr_t)s->accu <= (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_GTINT(interp_state *s) {
    s->accu = Val_int((intptr_t)s->accu > (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_GEINT(interp_state *s) {
    s->accu = Val_int((intptr_t)s->accu >= (intptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_ULTINT(interp_state *s) {
    s->accu = Val_int((uintptr_t)s->accu < (uintptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

int instr_UGEINT(interp_state *s) {
    s->accu = Val_int((uintptr_t)s->accu >= (uintptr_t)*s->sp++);
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Branch: BRANCH, BRANCHIF, BRANCHIFNOT
   ================================================================ */

/* BRANCH: pc += *pc (offset is at current pc position) */
int instr_BRANCH(interp_state *s, int32_t offset) {
    s->pc += offset;
    return STATUS_STEP;
}

/* BRANCHIF: if accu != Val_false then pc += offset else pc++ */
int instr_BRANCHIF(interp_state *s, int32_t offset) {
    if (s->accu != Val_false) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

/* BRANCHIFNOT: if accu == Val_false then pc += offset else pc++ */
int instr_BRANCHIFNOT(interp_state *s, int32_t offset) {
    if (s->accu == Val_false) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

/* ================================================================
   Integer branch comparisons: BEQ, BNEQ, BLTINT, BLEINT,
                                BGTINT, BGEINT, BULTINT, BUGEINT
   ================================================================ */

/* BEQ: if val == Long_val(accu) then pc += offset else pc++ */
int instr_BEQ(interp_state *s, intptr_t val, int32_t offset) {
    if (val == Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BNEQ(interp_state *s, intptr_t val, int32_t offset) {
    if (val != Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BLTINT(interp_state *s, intptr_t val, int32_t offset) {
    if (val < Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BLEINT(interp_state *s, intptr_t val, int32_t offset) {
    if (val <= Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BGTINT(interp_state *s, intptr_t val, int32_t offset) {
    if (val > Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BGEINT(interp_state *s, intptr_t val, int32_t offset) {
    if (val >= Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BULTINT(interp_state *s, uintptr_t val, int32_t offset) {
    if (val < (uintptr_t)Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

int instr_BUGEINT(interp_state *s, uintptr_t val, int32_t offset) {
    if (val >= (uintptr_t)Long_val(s->accu)) {
        s->pc += offset;
    } else {
        s->pc++;
    }
    return STATUS_STEP;
}

/* ================================================================
   Blocks: ATOM, PUSHATOM, MAKEBLOCK, MAKEBLOCK1-3,
           GETFIELD0-3, GETFIELD, SETFIELD0-3, SETFIELD
   ================================================================ */

/* ATOM tag: accu = Atom(tag) */
int instr_ATOM(interp_state *s, int tag) {
    s->accu = Atom(tag);
    s->pc++;
    return STATUS_STEP;
}

/* PUSHATOM tag: push accu, accu = Atom(tag) */
int instr_PUSHATOM(interp_state *s, int tag) {
    *--(s->sp) = s->accu;
    s->accu = Atom(tag);
    s->pc++;
    return STATUS_STEP;
}

/* MAKEBLOCK wosize tag: accu=field0, pop (wosize-1) fields from stack.
   NOTE: In the real runtime this calls Alloc_small. We model allocation
   abstractly -- the caller must provide the allocated block pointer. */
int instr_MAKEBLOCK(interp_state *s, int wosize, int tag, value block) {
    Field(block, 0) = s->accu;
    for (int i = 1; i < wosize; i++) {
        Field(block, i) = *s->sp++;
    }
    s->accu = block;
    s->pc++;
    return STATUS_STEP;
}

/* MAKEBLOCK1 tag: 1-field block, field0 = accu */
int instr_MAKEBLOCK1(interp_state *s, int tag, value block) {
    Field(block, 0) = s->accu;
    s->accu = block;
    s->pc++;
    return STATUS_STEP;
}

/* MAKEBLOCK2 tag: 2-field block, field0=accu, field1=sp[0] */
int instr_MAKEBLOCK2(interp_state *s, int tag, value block) {
    Field(block, 0) = s->accu;
    Field(block, 1) = s->sp[0];
    s->sp += 1;
    s->accu = block;
    s->pc++;
    return STATUS_STEP;
}

/* MAKEBLOCK3 tag: 3-field block, field0=accu, field1=sp[0], field2=sp[1] */
int instr_MAKEBLOCK3(interp_state *s, int tag, value block) {
    Field(block, 0) = s->accu;
    Field(block, 1) = s->sp[0];
    Field(block, 2) = s->sp[1];
    s->sp += 2;
    s->accu = block;
    s->pc++;
    return STATUS_STEP;
}

/* GETFIELD n: accu = Field(accu, n) */
int instr_GETFIELD(interp_state *s, int n) {
    s->accu = Field(s->accu, n);
    s->pc++;
    return STATUS_STEP;
}

/* SETFIELD n: Field(accu, n) = *sp++; accu = Val_unit */
int instr_SETFIELD(interp_state *s, int n) {
    Field(s->accu, n) = *s->sp++;
    s->accu = Val_unit;
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Closures: CLOSURE, CLOSUREREC, OFFSETCLOSURE, PUSHOFFSETCLOSURE
   ================================================================ */

/* CLOSURE nvars code_offset:
   if nvars>0 push accu; allocate closure; fill vars from stack;
   Code_val = pc + code_offset; sp += nvars.
   NOTE: allocation is abstracted -- caller provides block pointer. */
int instr_CLOSURE(interp_state *s, int nvars, int32_t code_offset, value block) {
    if (nvars > 0) *--(s->sp) = s->accu;
    /* Fill environment variables from stack */
    for (int i = 0; i < nvars; i++) {
        Field(block, i + 2) = s->sp[i];
    }
    Code_val(block) = s->pc + code_offset;
    /* Closinfo_val(block) omitted -- handled by allocation */
    s->sp += nvars;
    s->accu = block;
    s->pc++;
    return STATUS_STEP;
}

/* CLOSUREREC: complex multi-closure allocation.
   Simplified: we model the flat block layout.
   Allocation is abstracted. */
int instr_CLOSUREREC(interp_state *s, int nfuncs, int nvars, value block) {
    int envofs = nfuncs * 3 - 1;
    int i;
    value *p;

    if (nvars > 0) *--(s->sp) = s->accu;

    /* Fill environment variables at end of block */
    p = &Field(block, envofs);
    for (i = 0; i < nvars; i++, p++) *p = s->sp[i];
    s->sp += nvars;

    /* Push base closure, fill code pointers */
    *--(s->sp) = block;
    p = &Field(block, 0);
    *p++ = (value)(s->pc + s->pc[0]);  /* code pointer for first function */
    *p++ = 0;  /* closinfo placeholder */
    for (i = 1; i < nfuncs; i++) {
        *p++ = 0;  /* infix header placeholder */
        *--(s->sp) = (value)p;
        *p++ = (value)(s->pc + s->pc[i]);  /* code pointer */
        *p++ = 0;  /* closinfo placeholder */
    }
    s->pc += nfuncs;
    return STATUS_STEP;
}

/* OFFSETCLOSURE ofs: accu = env + ofs * sizeof(value) */
int instr_OFFSETCLOSURE(interp_state *s, int ofs) {
    s->accu = s->env + ofs * sizeof(value);
    s->pc++;
    return STATUS_STEP;
}

/* PUSHOFFSETCLOSURE ofs: push accu, then OFFSETCLOSURE */
int instr_PUSHOFFSETCLOSURE(interp_state *s, int ofs) {
    *--(s->sp) = s->accu;
    s->accu = s->env + ofs * sizeof(value);
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Application: APPLY, APPLY1, APPLY2, APPLY3, RETURN, GRAB, RESTART
   ================================================================ */

/* APPLY n: extra_args = n-1, pc = Code_val(accu), env = accu */
int instr_APPLY(interp_state *s, int n) {
    s->extra_args = n - 1;
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    return STATUS_STEP;
}

/* APPLY1: save return frame, call closure with 1 arg */
int instr_APPLY1(interp_state *s) {
    value arg1 = s->sp[0];
    s->sp -= 3;
    s->sp[0] = arg1;
    s->sp[1] = (value)s->pc;
    s->sp[2] = s->env;
    s->sp[3] = Val_long(s->extra_args);
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args = 0;
    return STATUS_STEP;
}

/* APPLY2: save return frame, call closure with 2 args */
int instr_APPLY2(interp_state *s) {
    value arg1 = s->sp[0];
    value arg2 = s->sp[1];
    s->sp -= 3;
    s->sp[0] = arg1;
    s->sp[1] = arg2;
    s->sp[2] = (value)s->pc;
    s->sp[3] = s->env;
    s->sp[4] = Val_long(s->extra_args);
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args = 1;
    return STATUS_STEP;
}

/* APPLY3: save return frame, call closure with 3 args */
int instr_APPLY3(interp_state *s) {
    value arg1 = s->sp[0];
    value arg2 = s->sp[1];
    value arg3 = s->sp[2];
    s->sp -= 3;
    s->sp[0] = arg1;
    s->sp[1] = arg2;
    s->sp[2] = arg3;
    s->sp[3] = (value)s->pc;
    s->sp[4] = s->env;
    s->sp[5] = Val_long(s->extra_args);
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args = 2;
    return STATUS_STEP;
}

/* RETURN stacksize: pop locals, then either tail-call or restore frame */
int instr_RETURN(interp_state *s, int stacksize) {
    s->sp += stacksize;
    if (s->extra_args > 0) {
        s->extra_args--;
        s->pc = Code_val(s->accu);
        s->env = s->accu;
    } else {
        s->pc = (code_t)(s->sp[0]);
        s->env = s->sp[1];
        s->extra_args = Long_val(s->sp[2]);
        s->sp += 3;
    }
    return STATUS_STEP;
}

/* GRAB required: if enough args, consume; else build partial closure and return */
int instr_GRAB(interp_state *s, int required, value partial_closure) {
    if (s->extra_args >= required) {
        s->extra_args -= required;
        s->pc++;
        return STATUS_STEP;
    } else {
        /* Build partial application closure */
        intptr_t num_args = 1 + s->extra_args;
        Field(partial_closure, 2) = s->env;
        for (intptr_t i = 0; i < num_args; i++) {
            Field(partial_closure, i + 3) = s->sp[i];
        }
        Code_val(partial_closure) = s->pc - 1;  /* point to preceding RESTART */
        s->sp += num_args;
        s->accu = partial_closure;
        s->pc = (code_t)(s->sp[0]);
        s->env = s->sp[1];
        s->extra_args = Long_val(s->sp[2]);
        s->sp += 3;
        return STATUS_STEP;
    }
}

/* RESTART: restore args from partial application closure env */
int instr_RESTART(interp_state *s) {
    int num_args = Wosize_val(s->env) - 3;
    s->sp -= num_args;
    for (int i = 0; i < num_args; i++) {
        s->sp[i] = Field(s->env, i + 3);
    }
    s->env = Field(s->env, 2);
    s->extra_args += num_args;
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Globals: GETGLOBAL, PUSHGETGLOBAL, GETGLOBALFIELD,
            PUSHGETGLOBALFIELD, SETGLOBAL
   ================================================================ */

int instr_GETGLOBAL(interp_state *s, int n) {
    s->accu = Field((value)s->global_data, n);
    s->pc++;
    return STATUS_STEP;
}

int instr_PUSHGETGLOBAL(interp_state *s, int n) {
    *--(s->sp) = s->accu;
    s->accu = Field((value)s->global_data, n);
    s->pc++;
    return STATUS_STEP;
}

int instr_GETGLOBALFIELD(interp_state *s, int n, int p) {
    s->accu = Field((value)s->global_data, n);
    s->accu = Field(s->accu, p);
    s->pc++;
    return STATUS_STEP;
}

int instr_PUSHGETGLOBALFIELD(interp_state *s, int n, int p) {
    *--(s->sp) = s->accu;
    s->accu = Field((value)s->global_data, n);
    s->accu = Field(s->accu, p);
    s->pc++;
    return STATUS_STEP;
}

int instr_SETGLOBAL(interp_state *s, int n) {
    Field((value)s->global_data, n) = s->accu;
    s->accu = Val_unit;
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   Control: STOP, CHECK_SIGNALS
   ================================================================ */

int instr_STOP(interp_state *s) {
    /* Return value is in accu */
    return STATUS_HALT;
}

int instr_CHECK_SIGNALS(interp_state *s) {
    /* Simplified: no signal handling, just advance pc */
    s->pc++;
    return STATUS_STEP;
}

/* ================================================================
   C calls: C_CALL1-5, C_CALLN
   These return STATUS_CCALL; actual primitive dispatch is external.
   ================================================================ */

int instr_C_CALL1(interp_state *s, int prim_idx) {
    /* In the real runtime: Setup_for_c_call, call Primitive1, Restore.
       Here we signal the need for a C call. The caller handles dispatch. */
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL2(interp_state *s, int prim_idx) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL3(interp_state *s, int prim_idx) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL4(interp_state *s, int prim_idx) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL5(interp_state *s, int prim_idx) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALLN(interp_state *s, int nargs, int prim_idx) {
    *--(s->sp) = s->accu;
    /* Actual C call would happen here; we signal STATUS_CCALL */
    s->pc++;
    return STATUS_CCALL;
}

/* ================================================================
   Exceptions: PUSHTRAP, POPTRAP, RAISE, RERAISE, RAISE_NOTRACE
   ================================================================ */

/* PUSHTRAP handler_offset: push trap frame, set trap_sp */
int instr_PUSHTRAP(interp_state *s, int32_t handler_offset) {
    s->sp -= 4;
    s->sp[0] = (value)(s->pc + handler_offset);  /* Trap_pc */
    s->sp[1] = Val_long(s->trap_sp - s->sp);     /* Trap_link (relative offset) */
    s->sp[2] = s->env;
    s->sp[3] = Val_long(s->extra_args);
    s->trap_sp = s->sp;
    s->pc++;
    return STATUS_STEP;
}

/* POPTRAP: restore trap_sp, pop 4 words */
int instr_POPTRAP(interp_state *s) {
    s->trap_sp = s->sp + Long_val(s->sp[1]);
    s->sp += 4;
    s->pc++;
    return STATUS_STEP;
}

/* raise_notrace: common raise implementation */
static int do_raise(interp_state *s) {
    /* In the real runtime, this checks trap_sp against stack_high.
       We simplify: if trap_sp is NULL, unhandled exception. */
    if (s->trap_sp == NULL) return STATUS_ERROR;
    s->sp = s->trap_sp;
    s->pc = (code_t)(s->sp[0]);
    s->trap_sp = s->sp + Long_val(s->sp[1]);
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;
    return STATUS_STEP;
}

int instr_RAISE(interp_state *s) {
    /* accu already holds the exception value */
    return do_raise(s);
}

int instr_RERAISE(interp_state *s) {
    return do_raise(s);
}

int instr_RAISE_NOTRACE(interp_state *s) {
    return do_raise(s);
}
