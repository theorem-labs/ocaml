# Plan: Simplify `extract_handlers.sh`

## Goal

Shrink `extract_handlers.sh` (currently 785 LoC, mostly Section 1 hand-transcribed handlers) by pushing work into:
- the C preprocessor,
- a smarter awk/python extractor,
- parametric handlers + lemmas,
- small renames in the Rocq model so fewer translations are needed.

Target: bring the script down to ~200 LoC, with hand-written entries only for handlers whose semantics genuinely diverge from `interp.c` (C_CALL stubs, simplified exceptions, OCaml 5 stubs, debugger no-ops).

## Non-goals

- No change to which opcodes are verified, or to the correctness claims.
- No change to `instruct_handlers.v` beyond what round-trips through `clightgen -normalize`.
- No change to the Module Type / per-handler proof split.

## Context

`interp.c` expresses most handlers via two macros:

```c
#define Instruct(X)  case X
#define Next         goto *jumptable[*pc++]

#define Integer_comparison(typ,opname,tst) \
    Instruct(opname): accu = Val_int((typ) accu tst (typ) *sp++); Next;
#define Integer_branch_comparison(typ,opname,tst,debug) \
    Instruct(opname): if (*pc++ tst (typ) Long_val(accu)) ...

#define Alloc_small(x,n,t) ...     /* + Setup_for_gc / Restore_after_gc */
#define Setup_for_c_call ...
```

The current script works around these macros by hand-rewriting 60+ handlers
in Section 1. A `cpp`-driven shim reinterprets the same macros to emit
standalone functions, which the extractor can then consume uniformly.

## Approach

Four orthogonal axes, in descending order of payoff per unit risk:

1. **(a) `cpp` shim** — reinterpret `interp.c`'s own macros to produce
   per-opcode functions directly.
2. **(d) small Rocq renames** — drop the `s->` indirection and align
   field names with `interp.c` so `emit_extract`'s sed wall disappears.
3. **(b) awk/python extractor** — replace `emit_extract`'s line-oriented
   sed with a brace-balanced pass that also handles stacked fallthrough
   labels.
4. **(c) parametric handlers** — unify opcode families (ACC0-7, OFFSETCLOSURE*,
   C_CALL1-5, RAISE/RERAISE/RAISE_NOTRACE, PERFORM/RESUME/…) behind one C
   function + one general lemma, specialized per opcode. Touches Rocq proofs;
   pairs with the CLOSURE/CLOSUREREC generalization in `PLAN.md`.

Do (a)+(d) first — highest payoff, proof-preserving. Then (b). Then (c)
if the residual script is still larger than we want.

---

## Step 1 — (a) `cpp` shim

Write `gen/extract_shim.h`:

```c
/* Redefine interp.c's dispatch macros so each Instruct/Next pair
   becomes a standalone C function that clightgen can process. */

/* Close previous function, open next. The first Instruct is preceded
   by a leading `int __dummy__(struct interp_state *s) {` from the shim. */
#define Instruct(X) \
    return STATUS_STEP; } \
    int instr_##X(struct interp_state *s) {

#define Next   return STATUS_STEP;

/* Replace GC / signal / trapsp plumbing with the model's notion. */
#define Setup_for_gc          /* empty */
#define Restore_after_gc      /* empty */
#define Setup_for_c_call      /* empty */
#define Restore_after_c_call  /* empty */
#define Alloc_small(x,n,t)    (x) = heap_alloc(s, (n), (t))
#define Caml_state_trapsp     (s->trap_sp)  /* paired with a textual sub of
                                               Caml_state->trapsp below */
#define caml_global_data      (s->global_data)

/* Register-variable aliases so the handler bodies reference struct fields. */
#define accu        (s->accu)
#define sp          (s->sp)
#define pc          (s->pc)
#define env         (s->env)
#define extra_args  (s->extra_args)
```

Build flow becomes:

1. Run a one-line `sed 's/Caml_state->trapsp/Caml_state_trapsp/g'` on
   `interp.c` (or redefine `Caml_state` as a struct pointer in the shim).
2. Slice out just the `caml_interprete` dispatch body (between known
   anchor comments) — this is the only sed we keep.
3. Run `cpp -E -include gen/extract_shim.h -` over that slice.
4. Post-process: drop the dummy head/tail, prepend a proper header
   (typedefs, `heap_alloc` extern decl, etc.).

What collapses in the script:

- Integer_comparison: 8 hand emits → 0 (expanded by cpp).
- Integer_branch_comparison: 8 hand emits → 0.
- All handlers that now just need `Alloc_small` rewritten (CLOSURE,
  CLOSUREREC, GRAB, MAKEBLOCK, MAKEBLOCK1/2/3, MAKEFLOATBLOCK,
  GETFLOATFIELD): ~180 LoC → 0.
- Every single-line `Instruct(X): stmt; Next;` handler (ACC0-7, ENVACC1-4,
  CONST0-3, GETFIELD0-3, OFFSETCLOSURE*, ATOM0, STOP): ~50 LoC → 0.

Verification: `clightgen -normalize` must produce a Clight AST byte-for-byte
equivalent to the current `gen/instruct_handlers.v` for every handler that
was already extracted via sed in Section 2. Check by running the whole
`dune build instruct-verification/` on a switch with the new pipeline —
all 118 clean proofs must still go through unchanged.

Files touched: `extract_handlers.sh`, new `gen/extract_shim.h`, `Makefile`.

## Step 2 — (d) Rocq model renames

Goal: remove `emit_extract`'s rewrite wall so the same `cpp` shim (or sed)
doesn't need post-hoc translation.

Renames in `manual/theories/Bytecode/Machine.v` and downstream:

| Rocq now            | Rename to           | Why                              |
|---------------------|---------------------|----------------------------------|
| `Machine.trap_sp`   | `Machine.trapsp`    | matches `Caml_state->trapsp`     |
| `Machine.global_data` | `Machine.caml_global_data` | matches interp.c global name |
| `OFFSETCLOSURE2`    | `OFFSETCLOSURE3`    | matches interp.c opcode name     |
| `OFFSETCLOSUREM2`   | `OFFSETCLOSUREM3`   | matches interp.c opcode name     |
| `PUSHOFFSETCLOSURE2` | `PUSHOFFSETCLOSURE3` | matches interp.c opcode name |
| `PUSHOFFSETCLOSUREM2` | `PUSHOFFSETCLOSUREM3` | matches interp.c opcode name |

Affected files (mechanical rename):

- `manual/theories/Utils/` — any references.
- `manual/theories/Bytecode/AST.v`, `Machine.v`, `Interpret.v`, `Encode.v`.
- `automatic/theories/Bytecode/Decode.v`.
- `instruct-verification/theories/InstructSpec.v`, `InstructVerification.v`.
- All 8 affected `<OP>_correct.v` files.
- Any references in `manual/test/` (interp_extracted will regenerate).

Separate decision: **drop the `struct interp_state` indirection**. Either

- keep `struct interp_state` but rely on the shim's `#define accu (s->accu)`
  aliases (what Step 1 already does — no further Rocq change), OR
- remove the struct and generate handlers that take register-variable locals
  directly; the Rocq `abs_rel` predicate changes shape.

Recommend the first: the struct is stable and helps Clight normalization;
the shim's accu/sp/pc/env aliases handle the ergonomics.

## Step 3 — (b) awk/python extractor

After Steps 1-2, everything `interp.c` expresses via the standard pattern
is extracted by `cpp`. What remains:

- **Stacked fallthrough labels** — `Instruct(GETSTRINGCHAR): Instruct(GETBYTESCHAR): body`.
  The `cpp` shim produces `} int instr_GETSTRINGCHAR(…) { } int instr_GETBYTESCHAR(…) { body`,
  i.e. an empty function for the first label. Fix in a post-processing awk
  pass: when an `instr_X` function body is a single `return STATUS_STEP;`,
  rewrite it to call the next handler:
  `int instr_X(struct interp_state *s) { return instr_Y(s); }`.

- **Multi-line handlers with nested braces** — the old sed extractor
  matched `^\s*Next;` to close the body, which breaks on APPLY/APPTERM
  internal blocks. With `cpp` the Instruct-to-Instruct delimiting does
  the work, so this stops mattering.

Write a small awk pass (~30 lines) that:

1. Reads the cpp output.
2. Detects empty-body-then-next pattern (fallthrough).
3. Emits the forward call for the first, keeps the body on the second.

Avoid python unless the logic gets complicated — awk stays in the
existing shell pipeline without a new dep.

## Step 4 — (c) parametric handlers

Only do this if the script is still too big after Steps 1-3, or if the
underlying proofs are worth unifying for other reasons.

Candidates (ordered by payoff):

### 4a. OFFSETCLOSURE family (8 handlers → 2)

- Generate one `instr_OFFSETCLOSURE_ofs(struct interp_state *s, intnat ofs)`
  and one `instr_PUSHOFFSETCLOSURE_ofs(...)`.
- Dispatch maps each specialized opcode (OFFSETCLOSURE0/2/M2/generic) to the
  common function with the appropriate `ofs`.
- Rocq: prove one `correct_OFFSETCLOSURE_ofs` over arbitrary `ofs`; the four
  Module Type parameters become one-line instantiations.
- Deletes 8 entries in the script and 8 `_correct.v` files (or reduces each
  to a `Definition correct_OFFSETCLOSURE0 := correct_OFFSETCLOSURE_ofs 0.`).

### 4b. RAISE / RERAISE / RAISE_NOTRACE (3 → 1)

- All three have identical simplified bodies. Point all three dispatch
  entries at one `instr_raise_common`.
- One proof, three `Definition` aliases.

### 4c. C_CALL1-5 and C_CALLN (6 → 2)

- C_CALL1-5 have identical bodies; one `instr_c_call_stub`.
- C_CALLN advances pc twice; own function.
- Script drops from a `cat <<CCALLS … CCALLS` block to two emits.

### 4d. Effect handler stubs (4 → 1)

- PERFORM / RESUME / RESUMETERM / REPERFORMTERM are no-op stubs
  (RESUMETERM/REPERFORMTERM advance pc once). Two functions suffice.

### 4e. ACC0-7, PUSHACC1-7, ENVACC1-4, CONST0-3, GETFIELD0-3, SETFIELD0-3, PUSHCONST0-3

After Steps 1-3 these are already extracted automatically from `interp.c`
by `cpp`, so no script savings. **The proof-side unification is a separate
task** and belongs in `PLAN.md`, not here.

## Order and dependencies

1. Step 1 (cpp shim) — prerequisite for Step 3, independent of Steps 2/4.
2. Step 2 (Rocq renames) — can be done in parallel with Step 1 on a
   separate branch; merge order doesn't matter.
3. Step 3 (awk fallthrough pass) — depends on Step 1 output shape.
4. Step 4 (parametric handlers) — independent, touches both script and
   Rocq proofs; sequence with the CLOSURE/CLOSUREREC generalization in
   `PLAN.md` to avoid conflicting edits to `InstructSpec.v`.

## Verification at each step

- After Step 1: `make gen/instruct_handlers.v` must be byte-identical to
  the prior output for the 30-odd handlers the old Section 2 covered.
  For handlers moved out of Section 1, diff the new Clight AST against
  the old one and justify any differences (normalization artifacts only;
  no semantic drift).
- After Step 2: full `dune build instruct-verification/` must succeed
  with 0 Admitted added.
- After Step 3: regenerated file must compile and all 118 clean proofs
  still go through.
- After Step 4 (per family): `Print Assumptions correct_OFFSETCLOSURE_ofs.`
  (etc.) must show zero axioms; the Module Type ascription in
  `InstructVerification.v` must continue to check.

## Estimated impact

| Step | Script LoC removed | Rocq changes                          |
|------|--------------------|---------------------------------------|
| 1    | ~250               | none                                  |
| 2    | ~30                | mechanical rename, ~8 files           |
| 3    | ~40 (sed logic)    | none                                  |
| 4a   | ~30                | 1 new lemma, 8 handler files shrink   |
| 4b   | ~25                | 1 new lemma, 3 handler files shrink   |
| 4c   | ~30                | 1 new lemma, 6 handler files shrink   |
| 4d   | ~10                | 1 new lemma, 4 handler files shrink   |

Totals: ~415 LoC removed from the 785-line script if all steps land;
~200 LoC likely after Steps 1-3 alone.
