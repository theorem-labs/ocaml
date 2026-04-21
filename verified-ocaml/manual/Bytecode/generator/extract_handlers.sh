#!/bin/bash
# extract_handlers.sh — Extract Instruct() handlers from OCaml's interp.c
# into standalone C functions suitable for clightgen/VST verification.
#
# Usage: ./extract_handlers.sh path/to/interp.c > gen/instruct_handlers.c
#
# To regenerate the Clight AST used by the Rocq build:
#   cd verified-ocaml/manual/Bytecode/generator
#   make ../Generated/instruct_handlers.v
#
# Most handlers are produced by a cpp shim (extract_shim.h) that redefines
# interp.c's dispatch macros so each handler becomes a standalone function.
# A small number remain hand-written because they diverge semantically from
# interp.c (RAISE skips backtrace, C_CALL returns STATUS_CCALL, POPTRAP
# omits signal restart, STOP returns STATUS_HALT).

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

/* External functions for heap allocation and exceptions */
extern value heap_alloc(struct interp_state *s, intptr_t nfields, intptr_t tag);
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

# --- cpp shim pipeline: run once, emit handlers on demand ---

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# Slice the dispatch body (anchored by the "Basic stack operations" comment
# at the top of the switch and `Restart_curr_instr;` at the end of BREAK).
awk '
    /\/\* Basic stack operations \*\//    { on=1 }
    on                                   { print }
    on && /Instruct\(BREAK\):/           { in_break=1 }
    in_break && /^[[:space:]]*Restart_curr_instr;[[:space:]]*$/ { exit }
' "$INTERP" > "$TMP/dispatch.c"

# Rewrite Caml_state->trapsp so cpp can expand it; strip trailing `:` from
# `Instruct(X):` so the shim's Instruct macro doesn't leave a stray colon
# inside the function body; split same-line stacked labels
# (`Instruct(X) Instruct(Y)`) onto separate lines so each gets its own body;
# delete interp.c's own Integer_{,branch_}comparison #define blocks so the
# shim's colon-free versions survive through cpp expansion.
sed -i -e 's/Caml_state->trapsp/Caml_state_trapsp/g' \
       -e 's/Instruct(\([A-Z0-9_]\+\)):/Instruct(\1)/g' \
       -e ':a' \
       -e 's/\(Instruct([A-Z0-9_]\+)\)[ \t]\+\(Instruct(\)/\1\n    \2/' \
       -e 'ta' \
       -e '/^#define Integer_comparison(/,/Next;$/d' \
       -e '/^#define Integer_branch_comparison(/,/Next;$/d' \
       -e 's/goto check_stacks;/Next;/g' \
       -e 's/goto process_actions;/Next;/g' \
       -e '/^[[:space:]]*process_actions:/d' \
       -e '/^#define CAML_METHOD_CACHE$/d' "$TMP/dispatch.c"

# Inline `/* Fallthrough */` bodies and flatten block-form handlers.
awk -f "$INLINE_AWK" "$TMP/dispatch.c" > "$TMP/dispatch_norm.c"

# Prepend a dummy function so the first Instruct has one to close; append
# a final `}` so the last handler closes cleanly.
{
    echo 'int __head(struct interp_state *s) {'
    cat "$TMP/dispatch_norm.c"
    echo 'return STATUS_STEP; }'
} > "$TMP/wrapped.c"

# Expand via cpp with the shim, then split so each `int instr_X(` starts
# on its own line.
cpp -E -P -include "$SHIM" "$TMP/wrapped.c" 2>/dev/null \
  | sed -E -e 's/(return STATUS_STEP; \})( int instr_)/\1\n\2/g' \
           -e 's/(int instr_[A-Z0-9_]+\(struct interp_state \*s\) \{)/\n\1/g' \
  > "$TMP/split.c"

# --- Helper: emit a handler extracted from the cpp output ---
emit_cpp() {
    local NAME="$1"
    awk -v NAME="$NAME" '
        $0 ~ "^int instr_"NAME"\\(" { in_func=1; print; next }
        in_func && /^int instr_[A-Z0-9_]+\(/ { exit }
        in_func && NF>0 { print }
    ' "$TMP/split.c"
    echo ""
}

# Emit a cpp-extracted handler but replace its return code.
emit_cpp_ret() {
    local NAME="$1" RET="$2"
    emit_cpp "$NAME" | sed "s/return STATUS_STEP;/return ${RET};/"
}

# ===================================================================
# SECTION 1: Handlers extracted from interp.c via the cpp shim.
# The shim rewrites Alloc_small→heap_alloc, caml_modify→direct store,
# caml_alloc_shr→heap_alloc, caml_initialize→direct store, erases GC
# and debugger boundaries, and expands Integer_{,branch_}comparison.
# ===================================================================

# --- Basic stack operations ---
for i in 0 1 2 3 4 5 6 7; do emit_cpp "ACC${i}";       done
emit_cpp "PUSH"
for i in 1 2 3 4 5 6 7;   do emit_cpp "PUSHACC${i}";   done

# --- Environment access ---
for i in 1 2 3 4; do emit_cpp "ENVACC${i}";     done
for i in 1 2 3 4; do emit_cpp "PUSHENVACC${i}"; done

# --- Integer constants ---
for i in 0 1 2 3; do emit_cpp "CONST${i}";      done
for i in 0 1 2 3; do emit_cpp "PUSHCONST${i}";  done

# --- Block field access ---
for i in 0 1 2 3; do emit_cpp "GETFIELD${i}";   done
for i in 0 1 2 3; do emit_cpp "SETFIELD${i}";   done

# --- Offset closures (fallthroughs inlined by awk) ---
emit_cpp "OFFSETCLOSURE"
emit_cpp "OFFSETCLOSUREM3"
emit_cpp "OFFSETCLOSURE0"
emit_cpp "OFFSETCLOSURE3"
emit_cpp "PUSHOFFSETCLOSURE"
emit_cpp "PUSHOFFSETCLOSUREM3"
emit_cpp "PUSHOFFSETCLOSURE0"
emit_cpp "PUSHOFFSETCLOSURE3"

# --- Control ---
emit_cpp "CHECK_SIGNALS"

# --- Integer comparisons and branch comparisons ---
for OP in EQ NEQ LTINT LEINT GTINT GEINT ULTINT UGEINT \
          BEQ BNEQ BLTINT BLEINT BGTINT BGEINT BULTINT BUGEINT; do
    emit_cpp "$OP"
done

# --- String/Bytes operations ---
emit_cpp "GETSTRINGCHAR"
emit_cpp "GETBYTESCHAR"
emit_cpp "SETBYTESCHAR"

# --- Function application (goto check_stacks → Next via sed) ---
emit_cpp "PUSH_RETADDR"
emit_cpp "APPLY"
emit_cpp "APPLY1"
emit_cpp "APPLY2"
emit_cpp "APPLY3"
emit_cpp "APPTERM"
emit_cpp "APPTERM1"
emit_cpp "APPTERM2"
emit_cpp "APPTERM3"
emit_cpp "RETURN"
emit_cpp "RESTART"
emit_cpp "GRAB"

# --- Closures (Alloc_small→heap_alloc, caml_alloc_shr→heap_alloc via shim) ---
emit_cpp "CLOSURE"
emit_cpp "CLOSUREREC"

# --- Global variable access ---
emit_cpp "GETGLOBALFIELD"
emit_cpp "PUSHGETGLOBALFIELD"

# --- Block allocation (Alloc_small→heap_alloc, caml_alloc_shr→heap_alloc) ---
emit_cpp "MAKEBLOCK"
emit_cpp "MAKEBLOCK1"
emit_cpp "MAKEBLOCK2"
emit_cpp "MAKEBLOCK3"
emit_cpp "MAKEFLOATBLOCK"

# --- Float field access ---
emit_cpp "GETFLOATFIELD"
emit_cpp "SETFLOATFIELD"

# --- Exception handling ---
emit_cpp "PUSHTRAP"

# --- Atoms ---
emit_cpp "ATOM0"
emit_cpp "PUSHATOM0"

# --- Object-oriented operations ---
emit_cpp "GETMETHOD"
# GETPUBMET: the #else path (no CAML_TEST_CACHE) falls through to GETDYNMET.
emit_cpp "GETPUBMET"
emit_cpp "GETDYNMET"

# --- SWITCH (CAMLassert erased by shim) ---
emit_cpp "SWITCH"

# --- Bulk extraction: general-form opcodes ---
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

for INSTR in $EXTRACT; do
    emit_cpp "$INSTR"
done

# ===================================================================
# SECTION 2: Handlers that must stay hand-written because they diverge
# semantically from interp.c (different return codes, backtrace
# skipping, signal-restart omission, C-call stubs).
# ===================================================================

# --- STOP: returns STATUS_HALT; interp.c does callback bookkeeping we skip ---
emit_raw "STOP" "    /* Halt execution */"

# --- POPTRAP: omits signal-check restart ---
emit_raw "POPTRAP" "    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->sp += 4;"

# --- RAISE family: skip backtrace, skip callback-boundary check ---
emit_raw "RAISE" "    s->sp = s->trap_sp;
    s->pc = Trap_pc(s->sp);
    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;"

emit_raw "RERAISE" "    s->sp = s->trap_sp;
    s->pc = Trap_pc(s->sp);
    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;"

emit_raw "RAISE_NOTRACE" "    s->sp = s->trap_sp;
    s->pc = Trap_pc(s->sp);
    s->trap_sp = s->sp + Long_val(Trap_link_offset(s->sp));
    s->env = s->sp[2];
    s->extra_args = Long_val(s->sp[3]);
    s->sp += 4;"

# --- C calls: return STATUS_CCALL instead of invoking primitives ---
cat << 'CCALLS'
int instr_C_CALL1(struct interp_state *s) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL2(struct interp_state *s) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL3(struct interp_state *s) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL4(struct interp_state *s) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALL5(struct interp_state *s) {
    s->pc++;
    return STATUS_CCALL;
}

int instr_C_CALLN(struct interp_state *s) {
    int nargs = *s->pc++;
    (void)nargs;
    s->pc++;
    return STATUS_CCALL;
}

CCALLS
