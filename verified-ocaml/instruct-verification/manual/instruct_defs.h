/* instruct_defs.h -- Simplified OCaml runtime types for VST verification.
   Mirrors the relevant parts of caml/mlvalues.h and the interpreter state. */

#ifndef INSTRUCT_DEFS_H
#define INSTRUCT_DEFS_H

#include <stdint.h>
#include <stddef.h>

/* OCaml value representation.
   On 64-bit: value = intptr_t (63-bit tagged integers, block pointers). */
typedef intptr_t value;
typedef uintptr_t uvalue;
typedef int32_t opcode_t;
typedef opcode_t *code_t;

/* ---- Value tagging (matches caml/mlvalues.h) ---- */

#define Val_long(x)    (((intptr_t)(x) << 1) + 1)
#define Long_val(x)    ((intptr_t)(x) >> 1)
#define Val_int(x)     Val_long(x)
#define Int_val(x)     Long_val(x)
#define Is_long(x)     (((x) & 1) != 0)
#define Is_block(x)    (((x) & 1) == 0)

#define Val_unit       Val_int(0)
#define Val_false      Val_int(0)
#define Val_true       Val_int(1)
#define Val_not(x)     (Val_true + Val_false - (x))
#define Val_bool(x)    ((x) ? Val_true : Val_false)

/* ---- Block operations (simplified) ----
   In the real runtime, blocks are heap-allocated with a header word
   at offset -1 containing tag + size. We simplify for verification. */

/* Header layout: [wosize(54 bits) | color(2 bits) | tag(8 bits)] */
#define Tag_hd(hd)     ((hd) & 0xFF)
#define Wosize_hd(hd)  ((hd) >> 10)

/* Access header from block pointer (header is one word before the pointer) */
#define Hd_val(v)      (((value *)(v))[-1])
#define Tag_val(v)     Tag_hd(Hd_val(v))
#define Wosize_val(v)  Wosize_hd(Hd_val(v))

/* Field access: blocks are arrays of value starting at the pointer */
#define Field(x,i)     (((value *)(x))[i])

/* Code pointer is Field 0 of a closure.
   Defined as an lvalue-compatible macro so it can appear on both sides
   of an assignment. */
#define Code_val(v)    (*((code_t *) &Field(v, 0)))

/* Closure tag */
#define Closure_tag    247
#define Infix_tag      249
#define Double_tag     253
#define Double_array_tag 254

/* Atom: pointer to a statically allocated zero-size block with given tag */
extern value caml_atom_table[];
#define Atom(tag)      ((value)(&caml_atom_table[(tag)]))

/* ---- Interpreter state ----
   Abstracted from interp.c's local variables and Caml_state fields. */

typedef struct {
    code_t   pc;           /* program counter */
    value    accu;         /* accumulator */
    value   *sp;           /* stack pointer (grows downward) */
    value    env;          /* heap-allocated environment (closure) */
    intptr_t extra_args;   /* number of extra arguments */
    value   *global_data;  /* pointer to global data array */
    value   *trap_sp;      /* pointer to current trap frame on stack */
} interp_state;

/* Status codes returned by instruction handlers */
#define STATUS_STEP    0   /* Continue to next instruction */
#define STATUS_HALT    1   /* STOP instruction reached */
#define STATUS_ERROR   2   /* Runtime error */
#define STATUS_CCALL   3   /* C primitive call requested */

#endif /* INSTRUCT_DEFS_H */
