#!/bin/bash
# extract_handlers.sh — Extract Instruct() handlers from OCaml's interp.c
# into standalone C functions suitable for clightgen/VST verification.
#
# Usage: ./extract_handlers.sh path/to/interp.c > gen/instruct_handlers.c
#
# Section 2 handlers are produced by a cpp shim (gen/extract_shim.h) that
# redefines interp.c's dispatch macros; see EXTRACT_SIMPLIFICATION_PLAN.md.
# Section 1 handlers are hand-written because they diverge semantically
# from interp.c (simplified RAISE, C_CALL stubs, debugger no-ops, etc.).

set -euo pipefail

INTERP="${1:?Usage: $0 path/to/interp.c}"
[ -f "$INTERP" ] || { echo "Error: $INTERP not found" >&2; exit 1; }

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SHIM="${SCRIPT_DIR}/extract_shim.h"
INLINE_AWK="${SCRIPT_DIR}/inline_fallthroughs.awk"
[ -f "$SHIM" ]       || { echo "Error: $SHIM not found" >&2; exit 1; }
[ -f "$INLINE_AWK" ] || { echo "Error: $INLINE_AWK not found" >&2; exit 1; }

# --- Generate header ---
cat << 'HEADER'
/* instruct_handlers.c — Auto-generated from OCaml runtime/interp.c
   Do not edit manually. Regenerate with: ./extract_handlers.sh */

#include <stdint.h>
#include <string.h>

typedef intptr_t value;
typedef intptr_t intnat;
typedef uintptr_t uintnat;
typedef uintptr_t mlsize_t;
typedef unsigned char tag_t;
typedef int32_t code_t;

#define STATUS_STEP  0
#define STATUS_HALT  1
#define STATUS_ERROR 2
#define STATUS_CCALL 3

#define Val_long(x)    (((intptr_t)(x) << 1) + 1)
#define Long_val(x)    ((intptr_t)(x) >> 1)
#define Val_int(x)     Val_long(x)
#define Int_val(x)     Long_val(x)
#define Val_unit       Val_long(0)
#define Val_true       Val_long(1)
#define Val_false      Val_long(0)
#define Val_not(x)     (4 - (x))
#define Is_long(x)     ((x) & 1)
#define Is_block(x)    (((x) & 1) == 0)
#define Tag_val(x)     (((unsigned char*)(x))[-sizeof(value)] & 0xFF)
#define Wosize_val(x)  (((intptr_t*)(x))[-1] >> 10)
#define Field(x,i)     (((value*)(x))[i])
#define Code_val(x)    (((code_t**)(x))[0])
#define Byte_u(x,i)    (((unsigned char*)(x))[i])
#define Closure_tag    247
#define Infix_tag      249
#define Double_tag     253
#define Double_array_tag 254
#define Double_wosize  (sizeof(double) / sizeof(value))
#define Atom(tag)      ((value)((tag) << 10))

/* Trap frame accessors */
#define Trap_pc(sp)            (((code_t **)(sp))[0])
#define Trap_link_offset(sp)   (((value *)(sp))[1])

/* Closinfo encoding (simplified — arity=0, start_env=start) */
#define Make_closinfo(arity, start) ((value)((start) << 1) | 1)
#define Closinfo_val(x)   (((value*)(x))[1])

/* Make_header for infix blocks (simplified: wsz << 10 | tag) */
#define Make_header(wsz, tag, color) ((value)((wsz) << 10 | (tag)))
#define Caml_white 0

/* Double field access (simplified — treats doubles as value-sized slots) */
#define Double_flat_field(x, i) (*((double*)(&Field(x, (i) * Double_wosize))))
#define Store_double_flat_field(x, i, d) (*((double*)(&Field(x, (i) * Double_wosize))) = (d))
#define Double_val(x)      (*((double *)(x)))
#define Store_double_val(x, d) (*((double *)(x)) = (d))

/* Max_young_wosize — simplified constant for allocation decisions */
#define Max_young_wosize 256

/* Use a named struct tag so clightgen preserves the identifier as
   _interp_state (stable) rather than generating __NNN (brittle). */
struct interp_state {
    code_t *pc;
    value   accu;
    value  *sp;
    value   env;
    intptr_t extra_args;
    value  *global_data;
    value  *trap_sp;
};

/* External functions for heap allocation, C calls, modification, exceptions */
extern value heap_alloc(struct interp_state *s, intptr_t nfields, intptr_t tag);
extern void caml_modify(value *fp, value val);
extern void caml_initialize(value *fp, value val);
extern value caml_alloc_shr(mlsize_t wosize, tag_t tag);
extern void caml_raise_zero_divide(void);

HEADER

# --- Helper: emit a handler (body already uses s-> notation) ---
emit_raw() {
    local NAME="$1" BODY="$2"
    local RET="STATUS_STEP"
    [ "$NAME" = "STOP" ] && RET="STATUS_HALT"
    echo "int instr_${NAME}(struct interp_state *s) {"
    echo "$BODY"
    echo "    return ${RET};"
    echo "}"
    echo ""
}

# ===================================================================
# SECTION 1: Manually defined simple/specialized handlers
# These are one-liners, have fallthroughs, or use macros that
# the sed approach can't handle cleanly.
# ===================================================================

# --- Basic stack operations ---

# ACC0-ACC7: accu = sp[N]
for i in 0 1 2 3 4 5 6 7; do
    emit_raw "ACC${i}" "    s->accu = s->sp[${i}];"
done

# PUSH (same as PUSHACC0)
emit_raw "PUSH" "    *--s->sp = s->accu;"

# PUSHACC1-7: push then accu = sp[N]
for i in 1 2 3 4 5 6 7; do
    emit_raw "PUSHACC${i}" "    *--s->sp = s->accu;
    s->accu = s->sp[${i}];"
done

# --- Environment access ---

# ENVACC1-ENVACC4: accu = Field(env, N)
for i in 1 2 3 4; do
    emit_raw "ENVACC${i}" "    s->accu = Field(s->env, ${i});"
done

# PUSHENVACC1-PUSHENVACC4: push then accu = Field(env, N)
for i in 1 2 3 4; do
    emit_raw "PUSHENVACC${i}" "    *--s->sp = s->accu;
    s->accu = Field(s->env, ${i});"
done

# --- Integer constants ---

# CONST0-3
for i in 0 1 2 3; do
    emit_raw "CONST${i}" "    s->accu = Val_int(${i});"
done

# PUSHCONST0-3
for i in 0 1 2 3; do
    emit_raw "PUSHCONST${i}" "    *--s->sp = s->accu;
    s->accu = Val_int(${i});"
done

# --- Block field access ---

# GETFIELD0-3
for i in 0 1 2 3; do
    emit_raw "GETFIELD${i}" "    s->accu = Field(s->accu, ${i});"
done

# SETFIELD0-3
for i in 0 1 2 3; do
    emit_raw "SETFIELD${i}" "    Field(s->accu, ${i}) = *s->sp++;
    s->accu = Val_unit;"
done

# --- Offset closures (fallthroughs in interp.c) ---

# OFFSETCLOSURE: accu = env + *pc * sizeof(value)
emit_raw "OFFSETCLOSURE" "    s->accu = s->env + *s->pc++ * sizeof(value);"

# OFFSETCLOSUREM2 (interp.c calls it OFFSETCLOSUREM3: env - 3*sizeof(value))
emit_raw "OFFSETCLOSUREM2" "    s->accu = s->env - 3 * sizeof(value);"

# OFFSETCLOSURE0: accu = env
emit_raw "OFFSETCLOSURE0" "    s->accu = s->env;"

# OFFSETCLOSURE2 (interp.c calls it OFFSETCLOSURE3: env + 3*sizeof(value))
emit_raw "OFFSETCLOSURE2" "    s->accu = s->env + 3 * sizeof(value);"

# PUSHOFFSETCLOSURE variants: push then offset closure
emit_raw "PUSHOFFSETCLOSURE" "    *--s->sp = s->accu;
    s->accu = s->env + *s->pc++ * sizeof(value);"

emit_raw "PUSHOFFSETCLOSUREM2" "    *--s->sp = s->accu;
    s->accu = s->env - 3 * sizeof(value);"

emit_raw "PUSHOFFSETCLOSURE0" "    *--s->sp = s->accu;
    s->accu = s->env;"

emit_raw "PUSHOFFSETCLOSURE2" "    *--s->sp = s->accu;
    s->accu = s->env + 3 * sizeof(value);"

# --- Control: STOP and CHECK_SIGNALS ---

emit_raw "STOP" "    /* Halt execution */"
emit_raw "CHECK_SIGNALS" "    /* Signal check abstracted */"

# --- Integer comparisons (macro-generated in interp.c via Integer_comparison) ---

emit_raw "EQ"     "    s->accu = Val_int((intnat) s->accu == (intnat) *s->sp++);"
emit_raw "NEQ"    "    s->accu = Val_int((intnat) s->accu != (intnat) *s->sp++);"
emit_raw "LTINT"  "    s->accu = Val_int((intnat) s->accu < (intnat) *s->sp++);"
emit_raw "LEINT"  "    s->accu = Val_int((intnat) s->accu <= (intnat) *s->sp++);"
emit_raw "GTINT"  "    s->accu = Val_int((intnat) s->accu > (intnat) *s->sp++);"
emit_raw "GEINT"  "    s->accu = Val_int((intnat) s->accu >= (intnat) *s->sp++);"
emit_raw "ULTINT" "    s->accu = Val_int((uintnat) s->accu < (uintnat) *s->sp++);"
emit_raw "UGEINT" "    s->accu = Val_int((uintnat) s->accu >= (uintnat) *s->sp++);"

# --- Integer branch comparisons ---
# (macro-generated in interp.c via Integer_branch_comparison, manually expanded)
emit_raw "BEQ" "    if ((intnat) *s->pc++ == (intnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

emit_raw "BNEQ" "    if ((intnat) *s->pc++ != (intnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

emit_raw "BLTINT" "    if ((intnat) *s->pc++ < (intnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

emit_raw "BLEINT" "    if ((intnat) *s->pc++ <= (intnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

emit_raw "BGTINT" "    if ((intnat) *s->pc++ > (intnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

emit_raw "BGEINT" "    if ((intnat) *s->pc++ >= (intnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

# --- Unsigned integer branch comparisons ---
# (macro-generated in interp.c via Integer_branch_comparison)
emit_raw "BULTINT" "    if ((uintnat) *s->pc++ < (uintnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

emit_raw "BUGEINT" "    if ((uintnat) *s->pc++ >= (uintnat) Long_val(s->accu)) {
        s->pc += *s->pc;
    } else {
        s->pc++;
    }"

# --- String/Bytes operations (fallthroughs in interp.c) ---

# GETSTRINGCHAR and GETBYTESCHAR are identical in interp.c (fallthrough)
emit_raw "GETSTRINGCHAR" "    s->accu = Val_int(Byte_u(s->accu, Long_val(s->sp[0])));
    s->sp += 1;"

emit_raw "GETBYTESCHAR" "    s->accu = Val_int(Byte_u(s->accu, Long_val(s->sp[0])));
    s->sp += 1;"

emit_raw "SETBYTESCHAR" "    Byte_u(s->accu, Long_val(s->sp[0])) = Int_val(s->sp[1]);
    s->sp += 2;
    s->accu = Val_unit;"

# --- Function application ---

# PUSH_RETADDR: set up return frame
emit_raw "PUSH_RETADDR" "    s->sp -= 3;
    s->sp[0] = (value) (s->pc + *s->pc);
    s->sp[1] = s->env;
    s->sp[2] = Val_long(s->extra_args);
    s->pc++;"

# APPLY: generic apply (reads nargs from pc)
emit_raw "APPLY" "    s->extra_args = *s->pc - 1;
    s->pc = Code_val(s->accu);
    s->env = s->accu;"

# APPLY1: apply with 1 argument
emit_raw "APPLY1" "    {
    value arg1 = s->sp[0];
    s->sp -= 3;
    s->sp[0] = arg1;
    s->sp[1] = (value)s->pc;
    s->sp[2] = s->env;
    s->sp[3] = Val_long(s->extra_args);
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args = 0;
    }"

# APPLY2: apply with 2 arguments
emit_raw "APPLY2" "    {
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
    }"

# APPLY3: apply with 3 arguments
emit_raw "APPLY3" "    {
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
    }"

# APPTERM: tail apply with nargs and slotsize
emit_raw "APPTERM" "    {
    int nargs = *s->pc++;
    int slotsize = *s->pc;
    value *newsp;
    int i;
    newsp = s->sp + slotsize - nargs;
    for (i = nargs - 1; i >= 0; i--) newsp[i] = s->sp[i];
    s->sp = newsp;
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args += nargs - 1;
    }"

# APPTERM1: tail apply with 1 argument
emit_raw "APPTERM1" "    {
    value arg1 = s->sp[0];
    s->sp = s->sp + *s->pc - 1;
    s->sp[0] = arg1;
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    }"

# APPTERM2: tail apply with 2 arguments
emit_raw "APPTERM2" "    {
    value arg1 = s->sp[0];
    value arg2 = s->sp[1];
    s->sp = s->sp + *s->pc - 2;
    s->sp[0] = arg1;
    s->sp[1] = arg2;
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args += 1;
    }"

# APPTERM3: tail apply with 3 arguments
emit_raw "APPTERM3" "    {
    value arg1 = s->sp[0];
    value arg2 = s->sp[1];
    value arg3 = s->sp[2];
    s->sp = s->sp + *s->pc - 3;
    s->sp[0] = arg1;
    s->sp[1] = arg2;
    s->sp[2] = arg3;
    s->pc = Code_val(s->accu);
    s->env = s->accu;
    s->extra_args += 2;
    }"

# RETURN: return from function
emit_raw "RETURN" "    s->sp += *s->pc++;
    if (s->extra_args > 0) {
        s->extra_args--;
        s->pc = Code_val(s->accu);
        s->env = s->accu;
    } else {
        s->pc = (code_t*)(s->sp[0]);
        s->env = s->sp[1];
        s->extra_args = Long_val(s->sp[2]);
        s->sp += 3;
    }"

# RESTART: restart a closure application (copies env fields to stack)
emit_raw "RESTART" "    {
    int num_args = Wosize_val(s->env) - 3;
    int i;
    s->sp -= num_args;
    for (i = 0; i < num_args; i++) s->sp[i] = Field(s->env, i + 3);
    s->env = Field(s->env, 2);
    s->extra_args += num_args;
    }"

# GRAB: grab required number of arguments, or build a partial closure
# Simplified: allocation uses heap_alloc instead of Alloc_small
emit_raw "GRAB" "    {
    int required = *s->pc++;
    if (s->extra_args >= required) {
        s->extra_args -= required;
    } else {
        /* Build partial application closure */
        mlsize_t num_args, i;
        value block;
        num_args = 1 + s->extra_args;
        block = heap_alloc(s, num_args + 3, Closure_tag);
        Field(block, 2) = s->env;
        for (i = 0; i < num_args; i++) Field(block, i + 3) = s->sp[i];
        Code_val(block) = s->pc - 3;
        Closinfo_val(block) = Make_closinfo(0, 2);
        s->accu = block;
        s->sp += num_args;
        s->pc = (code_t*)(s->sp[0]);
        s->env = s->sp[1];
        s->extra_args = Long_val(s->sp[2]);
        s->sp += 3;
    }
    }"

# --- Closures ---

# CLOSURE: create a closure with nvars captured variables
# Simplified: uses heap_alloc for allocation
emit_raw "CLOSURE" "    {
    int nvars = *s->pc++;
    int i;
    value block;
    if (nvars > 0) *--s->sp = s->accu;
    block = heap_alloc(s, 2 + nvars, Closure_tag);
    for (i = 0; i < nvars; i++) Field(block, i + 2) = s->sp[i];
    Code_val(block) = s->pc + *s->pc;
    Closinfo_val(block) = Make_closinfo(0, 2);
    s->pc++;
    s->sp += nvars;
    s->accu = block;
    }"

# CLOSUREREC: create mutually recursive closures
# Simplified: uses heap_alloc for allocation, omits major-heap path
emit_raw "CLOSUREREC" "    {
    int nfuncs = *s->pc++;
    int nvars = *s->pc++;
    mlsize_t envofs = nfuncs * 3 - 1;
    mlsize_t blksize = envofs + nvars;
    int i;
    value *p;
    value block;
    if (nvars > 0) *--s->sp = s->accu;
    block = heap_alloc(s, blksize, Closure_tag);
    p = &Field(block, envofs);
    for (i = 0; i < nvars; i++) { *p = s->sp[i]; p++; }
    s->sp += nvars;
    *--s->sp = block;
    s->accu = block;
    p = &Field(block, 0);
    *p++ = (value) (s->pc + s->pc[0]);
    *p++ = Make_closinfo(0, envofs);
    for (i = 1; i < nfuncs; i++) {
        *p++ = Make_header(i * 3, Infix_tag, Caml_white);
        *--s->sp = (value) p;
        *p++ = (value) (s->pc + s->pc[i]);
        envofs -= 3;
        *p++ = Make_closinfo(0, envofs);
    }
    s->pc += nfuncs;
    }"

# --- Global variable access (with field) ---

# GETGLOBALFIELD: accu = Field(Field(global_data, n), p)
emit_raw "GETGLOBALFIELD" "    s->accu = Field(s->global_data, *s->pc);
    s->pc++;
    s->accu = Field(s->accu, *s->pc);
    s->pc++;"

# PUSHGETGLOBALFIELD: push then getglobalfield
emit_raw "PUSHGETGLOBALFIELD" "    *--s->sp = s->accu;
    s->accu = Field(s->global_data, *s->pc);
    s->pc++;
    s->accu = Field(s->accu, *s->pc);
    s->pc++;"

# --- Block allocation ---

# MAKEBLOCK: generic block allocation (wosize from pc, tag from pc)
# Simplified: uses heap_alloc
emit_raw "MAKEBLOCK" "    {
    mlsize_t wosize = *s->pc++;
    tag_t tag = *s->pc++;
    mlsize_t i;
    value block;
    block = heap_alloc(s, wosize, tag);
    Field(block, 0) = s->accu;
    for (i = 1; i < wosize; i++) Field(block, i) = *s->sp++;
    s->accu = block;
    }"

# MAKEBLOCK1: allocate 1-field block
emit_raw "MAKEBLOCK1" "    {
    tag_t tag = *s->pc++;
    value block;
    block = heap_alloc(s, 1, tag);
    Field(block, 0) = s->accu;
    s->accu = block;
    }"

# MAKEBLOCK2: allocate 2-field block
emit_raw "MAKEBLOCK2" "    {
    tag_t tag = *s->pc++;
    value block;
    block = heap_alloc(s, 2, tag);
    Field(block, 0) = s->accu;
    Field(block, 1) = s->sp[0];
    s->sp += 1;
    s->accu = block;
    }"

# MAKEBLOCK3: allocate 3-field block
emit_raw "MAKEBLOCK3" "    {
    tag_t tag = *s->pc++;
    value block;
    block = heap_alloc(s, 3, tag);
    Field(block, 0) = s->accu;
    Field(block, 1) = s->sp[0];
    Field(block, 2) = s->sp[1];
    s->sp += 2;
    s->accu = block;
    }"

# MAKEFLOATBLOCK: allocate float array block
# Simplified: uses heap_alloc, treats doubles as value-sized words
emit_raw "MAKEFLOATBLOCK" "    {
    mlsize_t size = *s->pc++;
    mlsize_t i;
    value block;
    block = heap_alloc(s, size * Double_wosize, Double_array_tag);
    Store_double_flat_field(block, 0, Double_val(s->accu));
    for (i = 1; i < size; i++) {
        Store_double_flat_field(block, i, Double_val(*s->sp));
        ++s->sp;
    }
    s->accu = block;
    }"

# --- Float field access ---

# GETFLOATFIELD: extract a float field, box it
# Simplified: uses heap_alloc for boxing
emit_raw "GETFLOATFIELD" "    {
    double d = Double_flat_field(s->accu, *s->pc++);
    value block = heap_alloc(s, Double_wosize, Double_tag);
    Store_double_val(block, d);
    s->accu = block;
    }"

# SETFLOATFIELD: store a float into a float field
emit_raw "SETFLOATFIELD" "    Store_double_flat_field(s->accu, *s->pc, Double_val(*s->sp));
    s->accu = Val_unit;
    s->sp++;
    s->pc++;"

# --- Exception handling ---

# PUSHTRAP: push a trap frame
emit_raw "PUSHTRAP" "    s->sp -= 4;
    Trap_pc(s->sp) = s->pc + *s->pc;
    Trap_link_offset(s->sp) = Val_long(s->trap_sp - s->sp);
    s->sp[2] = s->env;
    s->sp[3] = Val_long(s->extra_args);
    s->trap_sp = s->sp;
    s->pc++;"

# POPTRAP: pop the current trap frame
# Simplified: omits signal check (handled abstractly)
emit_raw "POPTRAP" "    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->sp += 4;"

# RAISE: raise an exception (with backtrace)
# Simplified: skips backtrace, just does the trap unwind
emit_raw "RAISE" "    /* Simplified: skip backtrace, unwind to trap frame */
    s->sp = s->trap_sp;
    s->pc = Trap_pc(s->sp);
    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;"

# RERAISE: re-raise (same semantics as RAISE for verification purposes)
# Simplified: same trap unwind as RAISE
emit_raw "RERAISE" "    /* Simplified: same as RAISE — skip backtrace, unwind to trap frame */
    s->sp = s->trap_sp;
    s->pc = Trap_pc(s->sp);
    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;"

# RAISE_NOTRACE: raise without backtrace (same unwind)
emit_raw "RAISE_NOTRACE" "    /* Unwind to trap frame, no backtrace */
    s->sp = s->trap_sp;
    s->pc = Trap_pc(s->sp);
    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;"

# --- C calls ---
# All C_CALL variants return STATUS_CCALL to signal the caller should
# handle the external call. The primitive index is in *pc.
# Simplified: we don't actually call the primitive; we signal STATUS_CCALL.

cat << 'CCALLS'
int instr_C_CALL1(struct interp_state *s) {
    /* Primitive index at *s->pc; 1 argument in accu */
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL2(struct interp_state *s) {
    /* Primitive index at *s->pc; 2 arguments: accu and sp[0] */
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL3(struct interp_state *s) {
    /* Primitive index at *s->pc; 3 arguments: accu, sp[0], sp[1] */
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL4(struct interp_state *s) {
    /* Primitive index at *s->pc; 4 arguments */
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL5(struct interp_state *s) {
    /* Primitive index at *s->pc; 5 arguments */
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALLN(struct interp_state *s) {
    /* nargs at *s->pc, primitive index at pc[1] */
    int nargs = *s->pc++;
    (void)nargs;
    s->pc++;
    return STATUS_CCALL;
}

CCALLS

# --- SWITCH ---
# Simplified: reads the sizes word, dispatches on integer or block tag.
# The jump table offsets follow the sizes word in the code stream.
emit_raw "SWITCH" "    {
    uint32_t sizes = *s->pc++;
    if (Is_block(s->accu)) {
        intnat index = Tag_val(s->accu);
        s->pc += s->pc[(sizes & 0xFFFF) + index];
    } else {
        intnat index = Long_val(s->accu);
        s->pc += s->pc[index];
    }
    }"

# --- ATOM0 / PUSHATOM0 (specialized, have fallthroughs in interp.c) ---
emit_raw "ATOM0" "    s->accu = Atom(0);"
emit_raw "PUSHATOM0" "    *--s->sp = s->accu;
    s->accu = Atom(0);"

# --- Object-oriented operations ---

# GETMETHOD: accu = Field(Field(sp[0], 0), Int_val(accu))
emit_raw "GETMETHOD" "    s->accu = Field(Field(s->sp[0], 0), Int_val(s->accu));"

# GETPUBMET: method lookup with cache
# Simplified: does a binary search (skips cache optimization for verification)
emit_raw "GETPUBMET" "    {
    /* accu == object, pc[0] == tag, pc[1] == cache */
    value meths = Field(s->accu, 0);
    int li, hi, mi;
    *--s->sp = s->accu;
    s->accu = Val_int(*s->pc++);
    /* Skip cache slot */
    s->pc++;
    /* Binary search for the method */
    li = 3;
    hi = Field(meths, 0);
    while (li < hi) {
        mi = ((li + hi) >> 1) | 1;
        if (s->accu < Field(meths, mi)) hi = mi - 2;
        else li = mi;
    }
    s->accu = Field(meths, li - 1);
    }"

# GETDYNMET: dynamic method lookup (binary search)
emit_raw "GETDYNMET" "    {
    /* accu == tag, sp[0] == object */
    value meths = Field(s->sp[0], 0);
    int li = 3, hi = Field(meths, 0), mi;
    while (li < hi) {
        mi = ((li + hi) >> 1) | 1;
        if (s->accu < Field(meths, mi)) hi = mi - 2;
        else li = mi;
    }
    s->accu = Field(meths, li - 1);
    }"

# --- Debug instructions ---
# EVENT and BREAK are debugger-only; simplified to no-ops for verification.
emit_raw "EVENT" "    /* Debugger event — no-op for verification */"
emit_raw "BREAK" "    /* Debugger breakpoint — no-op for verification */"

# --- Effect handlers (OCaml 5.x placeholders, present in AST.v) ---
# These are no-ops / stubs since OCaml 4.14 does not have them.
emit_raw "PERFORM"       "    /* Effect handler (OCaml 5.x) — not in 4.14, no-op */"
emit_raw "RESUME"        "    /* Effect handler (OCaml 5.x) — not in 4.14, no-op */"
emit_raw "RESUMETERM"    "    s->pc++; /* skip nargs operand */
    /* Effect handler (OCaml 5.x) — not in 4.14, no-op */"
emit_raw "REPERFORMTERM" "    s->pc++; /* skip nargs operand */
    /* Effect handler (OCaml 5.x) — not in 4.14, no-op */"

# ===================================================================
# SECTION 2: Handlers extracted from interp.c via the cpp shim
# (gen/extract_shim.h). Produces byte-identical Clight to the old
# sed-based extractor for every handler in $EXTRACT.
# ===================================================================

EXTRACT="ACC POP ASSIGN CONSTINT PUSHCONSTINT
NEGINT ADDINT SUBINT MULINT DIVINT MODINT
ANDINT ORINT XORINT LSLINT LSRINT ASRINT
ISINT BOOLNOT OFFSETINT OFFSETREF
BRANCH BRANCHIF BRANCHIFNOT
ATOM PUSHATOM
GETFIELD SETFIELD
VECTLENGTH GETVECTITEM SETVECTITEM
GETGLOBAL PUSHGETGLOBAL SETGLOBAL
ENVACC PUSHENVACC
"

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# 1. Slice the dispatch body (between the first Instruct of the dispatch
#    switch and the last handler before `default:`). Anchored by comments
#    that delimit the region in upstream interp.c.
awk '
    /\/\* Basic stack operations \*\//    { on=1 }
    on                                   { print }
    on && /Instruct\(BREAK\):/           { in_break=1 }
    in_break && /^[[:space:]]*Restart_curr_instr;[[:space:]]*$/ { exit }
' "$INTERP" > "$TMP/dispatch.c"

# 2. Rewrite Caml_state->trapsp to a bare identifier that cpp can expand.
sed -i 's/Caml_state->trapsp/Caml_state_trapsp/g' "$TMP/dispatch.c"

# 3. Strip the trailing `:` from each `Instruct(X):` so the cpp shim's
#    Instruct macro doesn't leave a stray colon inside the function body.
sed -i 's/Instruct(\([A-Z0-9_]\+\)):/Instruct(\1)/g' "$TMP/dispatch.c"

# 4. Normalize the dispatch body (inline fallthroughs, flatten block-form
#    handlers so `Instruct(X): { ... }` becomes a flat body).
awk -f "$INLINE_AWK" "$TMP/dispatch.c" > "$TMP/dispatch_norm.c"

# 5. Wrap with a dummy `__head` function so the first Instruct macro has a
#    preceding function to close, and append a final `return STATUS_STEP; }`
#    so the last handler closes cleanly.
{
    echo 'int __head(struct interp_state *s) {'
    cat "$TMP/dispatch_norm.c"
    echo 'return STATUS_STEP; }'
} > "$TMP/wrapped.c"

# 6. Expand via cpp with the shim.
cpp -E -P -include "$SHIM" "$TMP/wrapped.c" > "$TMP/expanded.c" 2>/dev/null

# 7. Split so each `int instr_X(` starts on its own line.
sed -E -e 's/(return STATUS_STEP; \})( int instr_)/\1\n\2/g' \
       -e 's/(int instr_[A-Z0-9_]+\(struct interp_state \*s\) \{)/\n\1/g' \
       "$TMP/expanded.c" > "$TMP/split.c"

# 8. Emit each requested Section 2 handler from the cpp output.
for INSTR in $EXTRACT; do
    awk -v NAME="$INSTR" '
        $0 ~ "^int instr_"NAME"\\(" { in_func=1; print; next }
        in_func && /^int instr_[A-Z0-9_]+\(/ { exit }
        in_func && NF>0 { print }
    ' "$TMP/split.c"
    echo ""
done
