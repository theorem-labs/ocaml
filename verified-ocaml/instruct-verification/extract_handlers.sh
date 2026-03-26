#!/bin/bash
# extract_handlers.sh — Extract Instruct() handlers from OCaml's interp.c
# into standalone C functions suitable for clightgen/VST verification.
#
# Usage: ./extract_handlers.sh path/to/interp.c > gen/instruct_handlers.c

set -euo pipefail

INTERP="${1:?Usage: $0 path/to/interp.c}"
[ -f "$INTERP" ] || { echo "Error: $INTERP not found" >&2; exit 1; }

# --- Generate header ---
cat << 'HEADER'
/* instruct_handlers.c — Auto-generated from OCaml runtime/interp.c
   Do not edit manually. Regenerate with: ./extract_handlers.sh */

#include <stdint.h>

typedef intptr_t value;
typedef intptr_t intnat;
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
#define Is_long(x)     ((x) & 1)
#define Tag_val(x)     (((unsigned char*)(x))[-sizeof(value)] & 0xFF)
#define Wosize_val(x)  (((intptr_t*)(x))[-1] >> 10)
#define Field(x,i)     (((value*)(x))[i])
#define Code_val(x)    (((code_t**)(x))[0])
#define Closure_tag    247
#define Double_array_tag 254
#define Double_wosize  (sizeof(double) / sizeof(value))

typedef struct {
    code_t *pc;
    value   accu;
    value  *sp;
    value   env;
    intptr_t extra_args;
    value  *global_data;
    value  *trap_sp;
} interp_state;

extern value heap_alloc(interp_state *s, intptr_t nfields, intptr_t tag);

HEADER

# --- Helper: emit a handler (body already uses s-> notation) ---
emit_raw() {
    local NAME="$1" BODY="$2"
    local RET="STATUS_STEP"
    [ "$NAME" = "STOP" ] && RET="STATUS_HALT"
    echo "int instr_${NAME}(interp_state *s) {"
    echo "$BODY"
    echo "    return ${RET};"
    echo "}"
    echo ""
}

# --- Helper: emit a handler extracted from interp.c (rewrite register vars) ---
emit_extract() {
    local NAME="$1" BODY="$2"
    BODY=$(echo "$BODY" | sed \
        -e 's/\baccu\b/s->accu/g' \
        -e 's/\bsp\b/s->sp/g' \
        -e 's/\bpc\b/s->pc/g' \
        -e 's/\benv\b/s->env/g' \
        -e 's/\bextra_args\b/s->extra_args/g' \
        -e 's/Setup_for_gc;//g' \
        -e 's/Restore_after_gc;//g' \
        -e 's/Setup_for_c_call;//g' \
        -e 's/Restore_after_c_call;//g' \
        -e 's/Caml_state->trapsp/s->trap_sp/g' \
        -e 's/caml_global_data/s->global_data/g' \
        -e '/Instruct(/d' \
    )
    emit_raw "$NAME" "$BODY"
}

# --- Manually define the simple/specialized handlers ---
# These are one-liners or have fallthroughs that the sed approach can't handle cleanly.

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

# CONST0-3
for i in 0 1 2 3; do
    emit_raw "CONST${i}" "    s->accu = Val_int(${i});"
done

# PUSHCONST0-3
for i in 0 1 2 3; do
    emit_raw "PUSHCONST${i}" "    *--s->sp = s->accu;
    s->accu = Val_int(${i});"
done

# GETFIELD0-3
for i in 0 1 2 3; do
    emit_raw "GETFIELD${i}" "    s->accu = Field(s->accu, ${i});"
done

# SETFIELD0-3
for i in 0 1 2 3; do
    emit_raw "SETFIELD${i}" "    Field(s->accu, ${i}) = *s->sp++;
    s->accu = Val_unit;"
done

# STOP: just halt
emit_raw "STOP" "    /* Halt execution */"
emit_raw "CHECK_SIGNALS" "    /* Signal check abstracted */"
# --- Extract remaining handlers from interp.c using sed ---
# These are multi-line handlers that don't have fallthroughs.

EXTRACT="ACC POP ASSIGN CONSTINT PUSHCONSTINT
NEGINT ADDINT SUBINT MULINT DIVINT MODINT
ANDINT ORINT XORINT LSLINT LSRINT ASRINT
EQ NEQ LTINT LEINT GTINT GEINT ULTINT UGEINT
ISINT BOOLNOT OFFSETINT OFFSETREF
BRANCH BRANCHIF BRANCHIFNOT
BEQ BNEQ BLTINT BLEINT BGTINT BGEINT
ATOM PUSHATOM MAKEBLOCK1 MAKEBLOCK2 MAKEBLOCK3
GETFIELD SETFIELD
VECTLENGTH GETVECTITEM SETVECTITEM
GETGLOBAL PUSHGETGLOBAL SETGLOBAL
"

for INSTR in $EXTRACT; do
    BODY=$(sed -n "/^[[:space:]]*Instruct($INSTR):/,/Next;/{
        /Instruct($INSTR):/d
        /Next;/d
        p
    }" "$INTERP" 2>/dev/null)

    [ -z "$BODY" ] && continue
    emit_extract "$INSTR" "$BODY"
done
