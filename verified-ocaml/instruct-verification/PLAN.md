# Instruct-Verification Plan

## Goal

Prove that each `Instruct(X)` handler in OCaml's `runtime/interp.c` computes the same state transition as the corresponding case in our Rocq `Interpret.v` step function, using VST (Verified Software Toolchain).

## Architecture

```
system-ocaml-compiler/runtime/interp.c   (source of truth: real OCaml)
        |
        | extract_handlers.sh (simple sed/awk script)
        v
instruct-verification/gen/instruct_handlers.c  (generated: standalone C functions)
        |
        | clightgen -normalize
        v
instruct-verification/gen/instruct_handlers.v  (generated: Clight AST)
        |
        |   + manual/theories/Bytecode/Interpret.v (Rocq spec, refactored into per-handler defs)
        |
        v
instruct-verification/theories/InstructSpec.v  (hand-written: Module Type relating C ↔ Rocq)
```

### Key principle: no static C files

The only C files are **generated** by `extract_handlers.sh` from the real `interp.c`.
If OCaml updates `interp.c`, re-running the script regenerates the C and Clight.
The only hand-written artifacts are:

1. `extract_handlers.sh` — extracts handlers into standalone C functions
2. `theories/InstructSpec.v` — relates Clight AST to Rocq handlers
3. Refactored `Interpret.v` — exposes per-instruction handler definitions

## Step 1: extract_handlers.sh

A shell script that:

1. Takes `interp.c` as input
2. Preprocesses: `#undef THREADED_CODE` so `Instruct(X)` = `case X`, `Next` = `break`
3. Extracts each `Instruct(X): { body } Next;` block
4. Wraps each in a standalone C function:
   ```c
   int instr_ACC(interp_state *s) {
       s->accu = s->sp[*s->pc++];
       return STATUS_STEP;
   }
   ```
5. Replaces runtime macros with simplified equivalents:
   - `accu` → `s->accu`, `sp` → `s->sp`, `pc` → `s->pc`, `env` → `s->env`
   - `extra_args` → `s->extra_args`
   - `Val_long(x)` → `((intptr_t)(x) << 1) + 1`
   - `Long_val(x)` → `((intptr_t)(x) >> 1)`
   - `Field(x,i)` → `((value*)(x))[i]`
   - `Alloc_small(v,n,t)` → `v = heap_alloc(s, n, t)`
   - `Setup_for_gc/Restore_after_gc` → removed (abstracted)
   - `Setup_for_c_call/Restore_after_c_call` → removed
   - `Caml_state->trapsp` → `s->trap_sp`
   - `Next` → `return STATUS_STEP`
6. Prepends `instruct_defs.h` (also generated, containing the struct and macro definitions)

The script does NOT need to handle every handler perfectly. Handlers involving GC or C-calls can be left as stubs initially. The script evolves incrementally.

## Step 2: instruct_defs.h (generated preamble)

```c
#include <stdint.h>
typedef intptr_t value;
typedef int32_t code_t;

#define STATUS_STEP  0
#define STATUS_HALT  1
#define STATUS_ERROR 2
#define STATUS_CCALL 3

#define Val_long(x)  (((intptr_t)(x) << 1) + 1)
#define Long_val(x)  ((intptr_t)(x) >> 1)
#define Val_int(x)   Val_long(x)
#define Int_val(x)   Long_val(x)
#define Val_unit     Val_long(0)
#define Is_long(x)   ((x) & 1)

#define Field(x,i)   (((value*)(x))[i])
#define Code_val(x)  (((code_t**)(x))[0])
#define Tag_val(x)   (((unsigned char*)(x))[-sizeof(value)] & 0xFF)

typedef struct {
    code_t *pc;
    value accu;
    value *sp;
    value env;
    intptr_t extra_args;
    value *global_data;
    value *trap_sp;
} interp_state;

value heap_alloc(interp_state *s, intptr_t nfields, intptr_t tag);
```

## Step 3: Makefile

```makefile
INTERP_C = ../../system-ocaml-compiler/runtime/interp.c

gen/instruct_handlers.c: $(INTERP_C) extract_handlers.sh
    ./extract_handlers.sh $(INTERP_C) > gen/instruct_handlers.c

gen/instruct_handlers.v: gen/instruct_handlers.c
    clightgen -normalize gen/instruct_handlers.c

theories/build: gen/instruct_handlers.v
    dune build theories/
```

## Step 4: Refactor Interpret.v

Currently `Interpret.v` has one monolithic `step` function:

```coq
Definition step (code : code_array) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | ACC n => ...
  | PUSH => ...
  | ADDINT => ...
  ...
  end.
```

Refactor into per-instruction handler functions:

```coq
(* Per-instruction handlers *)
Definition handle_ACC (n : nat) (s : state) : step_result :=
  let v := nth n s.(stack) (Val_int 0) in
  Step (s <|pc := s.(pc) + 2|> <|accu := v|>).

Definition handle_PUSH (s : state) : step_result :=
  Step (s <|pc := s.(pc) + 1|> <|stack := s.(accu) :: s.(stack)|>).

Definition handle_ADDINT (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest =>
    Step (s <|pc := s.(pc) + 1|> <|accu := Val_int (a + b)|> <|stack := rest|>)
  | _, _ => Error "ADDINT: bad args"
  end.

(* Dispatch function — equivalent to the old monolithic step *)
Definition step (code : code_array) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | ACC n => handle_ACC n s
  | PUSH => handle_PUSH s
  | ADDINT => handle_ADDINT s
  ...
  end.
```

This refactoring:
- Preserves the existing `step` API (backward compatible)
- Exposes each handler for independent verification
- Each `handle_X` can be proven equivalent to the C `instr_X`

## Step 5: InstructSpec.v

A Module Type declaring the correspondence. Each axiom says: "if the abstraction relation holds, the C handler produces the same abstract state transition as the Rocq handler."

```coq
From compcert Require Import Clight Ctypes.
From VST Require Import floyd.proofauto.
Require Import instruct_handlers. (* generated Clight AST *)
From OCamlInterp.Manual.Bytecode Require Import AST Machine Interpret.

(* Abstraction: C interp_state ↔ Rocq state *)
Parameter abs_rel : val -> state -> mpred.

Module Type InstructSpec.

  (* ACC: C instr_ACC matches Rocq handle_ACC *)
  Axiom verify_ACC : forall n cs rs,
    abs_rel cs rs ->
    semax ... (call f_instr_ACC [cs]) ...
    (* postcondition: abs_rel cs' (handle_ACC n rs) *)

  (* PUSH: C instr_PUSH matches Rocq handle_PUSH *)
  Axiom verify_PUSH : forall cs rs,
    abs_rel cs rs ->
    semax ... (call f_instr_PUSH [cs]) ...

  (* ... one axiom per instruction ... *)

End InstructSpec.
```

The axioms will be replaced by proofs as verification proceeds.

## Phased Execution

### Phase 0: Infrastructure (this PR)
- [x] Write `extract_handlers.sh` (start with 5 simple instructions)
- [ ] Write `instruct_defs.h` generation
- [ ] Verify `clightgen` succeeds on the output
- [ ] Add Makefile
- [ ] Stub `InstructSpec.v`

### Phase 1: Stack + Arithmetic (20 instructions)
- Refactor Interpret.v: extract `handle_ACC`, `handle_PUSH`, `handle_POP`, `handle_ASSIGN`
- Refactor: `handle_ADDINT`, `handle_SUBINT`, `handle_MULINT`, `handle_DIVINT`, ...
- Expand `extract_handlers.sh` to cover these
- Write VST proofs for each

### Phase 2: Constants + Branches (20 instructions)
- `handle_CONSTINT`, `handle_BRANCH`, `handle_BRANCHIF`, comparison ops

### Phase 3: Blocks + Globals (15 instructions)
- `handle_MAKEBLOCK1`, `handle_GETFIELD`, `handle_SETFIELD`
- `handle_GETGLOBAL`, `handle_SETGLOBAL`
- Requires heap abstraction relation

### Phase 4: Closures + Application (15 instructions)
- `handle_CLOSURE`, `handle_APPLY1`, `handle_RETURN`, `handle_GRAB`
- Most complex: closure layout, stack frames

### Phase 5: Exceptions + C-calls (10 instructions)
- `handle_PUSHTRAP`, `handle_POPTRAP`, `handle_RAISE`
- `handle_C_CALL1` through `handle_C_CALLN`
