# Plan: Generalize CLOSURE/CLOSUREREC + Fix Trivial Error Predicates

## Context

Two issues in `InstructVerificationSpec` (InstructSpec.v):

**Issue 1 — CLOSURE/CLOSUREREC restricted to trivial cases:**
- **CLOSURE**: Only `nvars=0` (no captured environment variables). Real OCaml closures almost always capture variables.
- **CLOSUREREC**: Only `nfuncs=1, nvars=0` (single recursive function, no captured variables). Mutual recursion (`let rec f ... and g ...`) and captured variables are common.

Both restrictions exist because the C handlers contain `for`-loops (copying env vars, building infix headers) that require loop reasoning. The existing proofs avoid this by specializing to cases where loops execute 0 iterations.

The established pattern for handling loops (from `MAKEBLOCK_correct.v`) is to **assume the loop's cumulative effect as an exec_stmt hypothesis in the step_pre**, rather than proving loop correctness inductively. This keeps proofs tractable.

**Issue 2 — 15 handlers have trivially `True` error predicates:**

In `handler_correct`, the error predicate `P_error` must hold for ALL states where the handler returns `Error`. Using `(fun _ _ => True)` means the spec makes zero claims about error behavior — it's vacuously satisfied. This is unjustified when the handler CAN error and the spec should characterize when.

Affected handlers (13 can actually error, 2 never error):

| Handler | Can error? | Should be |
|---------|-----------|-----------|
| BGEINT | Yes ("not an integer") | Same pattern as BLTINT |
| BGTINT | Yes ("not an integer") | Same pattern as BLTINT |
| BLEINT | Yes ("not an integer") | Same pattern as BLTINT |
| BUGEINT | Yes ("not an integer") | Same pattern as BULTINT with unsigned |
| BULTINT | Yes ("not an integer") | Same pattern as BULTINT with unsigned |
| BOOLNOT | **No** (always Step) | `(fun _ _ => False)` |
| ISINT | **No** (always Step) | `(fun _ _ => False)` |
| OFFSETCLOSURE0 | Yes (invalid env) | Characterize env conditions |
| OFFSETCLOSURE3 | Yes (invalid env) | Characterize env conditions |
| OFFSETCLOSUREM3 | Yes (invalid env) | Characterize env conditions |
| OFFSETCLOSURE | Yes (invalid env) | Characterize env conditions |
| PUSHOFFSETCLOSURE0 | Yes (invalid env) | Characterize env conditions |
| PUSHOFFSETCLOSURE3 | Yes (invalid env) | Characterize env conditions |
| PUSHOFFSETCLOSUREM3 | Yes (invalid env) | Characterize env conditions |
| PUSHOFFSETCLOSURE | Yes (invalid env) | Characterize env conditions |
| GETDYNMET | Yes (3 paths) | Characterize each |
| GETPUBMET | Yes (2 paths) | Characterize each |
| GETMETHOD | Yes (4 paths) | Characterize each — currently `match msg with _ => True end` |
| SWITCH | Yes (4 paths) | Characterize each |

Reference: BLTINT already has the correct pattern (line 2885):
```coq
(fun msg s => msg = "BLTINT: not an integer"%string /\
  match Machine.accu s with Val_int _ => False | _ => True end)
```

## Approach

Follow the MAKEBLOCK pattern: define named Clight AST fragments for each loop, then add loop postcondition hypotheses to the step_pre definitions. The proofs stitch together the pre-loop code, the assumed loop execution, and the post-loop code.

## Step-by-step plan

### Step 1: Define Clight loop ASTs in InstructSpec.v

Extract the loop body/increment ASTs from `instruct_handlers.v` into named definitions, mirroring `makeblock_loop_body`/`makeblock_loop_incr`/`makeblock_loop` (lines 1500-1535).

**CLOSURE env copy loop** (from instruct_handlers.v lines 4823-4851):
```
Definition closure_env_loop_body : statement := ...
Definition closure_env_loop_incr : statement := ...
Definition closure_env_loop : statement := Sloop closure_env_loop_body closure_env_loop_incr.
```
This loop copies `nvars` values from the stack to `block[2..nvars+1]`.

**CLOSUREREC env copy loop** (from instruct_handlers.v lines 5029-5058):
```
Definition closurerec_env_loop_body : statement := ...
Definition closurerec_env_loop_incr : statement := ...
Definition closurerec_env_loop : statement := Sloop ...
```
This loop copies `nvars` values via pointer `_p` starting at `block + envofs`.

**CLOSUREREC infix header loop** (from instruct_handlers.v lines 5162-5297):
```
Definition closurerec_infix_loop_body : statement := ...
Definition closurerec_infix_loop_incr : statement := ...
Definition closurerec_infix_loop : statement := Sloop ...
```
This loop builds infix headers + code pointers for functions 1..nfuncs-1 and pushes closures onto the stack.

### Step 2: Define generalized step_pre in InstructSpec.v

**closure_general_step_pre** (new, for arbitrary nvars):
- Code buffer: `nvars` at PC, `code_ofs` at PC+1
- `nvars` in signed int range, `code_ofs` in signed int range
- If `nvars > 0`: SP has room for push (`sp_at_least 16`)
- Heap alloc: size = `2 + nvars`, tag = 247
- Store chain: field 0 (code ptr) + field 1 (closinfo) storeable
- **Loop postcondition hypothesis** (MAKEBLOCK pattern): assumes `exec_stmt` for `closure_env_loop` after field 0/1 are stored, yielding a post-loop memory where fields 2..nvars+1 contain the stack values and SP is advanced by nvars
- SP restoration postcondition

**closurerec_general_step_pre** (replace existing `closurerec_step_pre`, for arbitrary nfuncs, nvars):
- Code buffer: `nfuncs` at PC, `nvars` at PC+1, `code_offsets[0..nfuncs-1]` at PC+2..
- All code offsets in signed int range
- If `nvars > 0`: SP has room for push
- Heap alloc: size = `3*nfuncs - 1 + nvars`, tag = 247
- **Env copy loop postcondition**: assumes `exec_stmt` for `closurerec_env_loop` copying nvars values to block
- **Infix header loop postcondition**: assumes `exec_stmt` for `closurerec_infix_loop` building headers for functions 1..nfuncs-1 and pushing closures
- SP/stack state after both loops

### Step 3: Update Module Type parameters in InstructSpec.v

Change the two existing Parameter declarations:

```coq
(* Before *)
Parameter correct_CLOSURE :
  forall code_ofs, ... ->
  handler_correct (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE ...

(* After *)
Parameter correct_CLOSURE :
  forall nvars code_ofs, ... ->
  handler_correct (handle_CLOSURE nvars code_ofs) f_instr_CLOSURE
    (closure_general_step_pre nvars code_ofs)
    ... .
```

```coq
(* Before *)
Parameter correct_CLOSUREREC :
  forall code_ofs, ... ->
  handler_correct (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC ...

(* After *)
Parameter correct_CLOSUREREC :
  forall nfuncs nvars code_offsets, ... ->
  handler_correct (handle_CLOSUREREC nfuncs nvars code_offsets) f_instr_CLOSUREREC
    (closurerec_general_step_pre nfuncs nvars code_offsets)
    ... .
```

### Step 4: Write generalized CLOSURE_correct.v proof

Structure (following MAKEBLOCK_correct pattern):
1. **Pre-loop**: PC reads (nvars, code_ofs), conditional push (`if nvars > 0`), heap_alloc call, store field 0 (code ptr), store field 1 (closinfo)
2. **Loop**: Invoke the loop postcondition hypothesis from step_pre — this gives us `exec_stmt` for the env copy loop and the resulting memory state
3. **Post-loop**: PC advance, SP restoration (`sp += nvars`), accu = block, return 0
4. **abs_rel preservation**: Construct the extended heap map, prove all 8 state fields match

The conditional `if nvars > 0` creates two branches in the Clight:
- `nvars = 0`: Skip push, skip loop (loop condition `0 < 0` is false, immediate break)
- `nvars > 0`: Push accu, run loop, advance SP

### Step 5: Write generalized CLOSUREREC_correct.v proof

Structure:
1. **Pre-loop**: PC reads (nfuncs, nvars), conditional push, heap_alloc call
2. **Env copy loop**: Invoke env loop postcondition from step_pre
3. **SP advance + push block onto stack**: `sp += nvars; *--sp = block`
4. **Store code_ptr[0] and closinfo[0]**: First function's fields
5. **Infix header loop**: Invoke infix loop postcondition from step_pre
6. **PC advance by nfuncs**: `pc += nfuncs`
7. **abs_rel preservation**: Extended heap map with all closures

### Step 6: Update InstructVerification.v

Wire the new proof theorems into the module:
```coq
Definition correct_CLOSURE := verify_CLOSURE_general_correct.
Definition correct_CLOSUREREC := verify_CLOSUREREC_general_correct.
```

### Step 7: Fix trivial error predicates in InstructSpec.v

Derive each error predicate from the corresponding `handle_X` in `Interpret.v`. The predicate must characterize exactly which `(msg, s)` pairs arise from `Error msg` — not `True`.

**Group A — Branch comparisons (5 handlers): BGEINT, BGTINT, BLEINT, BUGEINT, BULTINT**

Same pattern as existing BLTINT (InstructSpec.v:2885). Replace `(fun _ _ => True)` with:
```coq
(fun msg s => msg = "BGEINT: not an integer"%string /\
  match Machine.accu s with Val_int _ => False | _ => True end)
```
(Substitute the handler name in the string for each.) These handlers error iff accu is not `Val_int`.

**Group B — Never-error handlers (2 handlers): BOOLNOT, ISINT**

Replace `(fun _ _ => True)` with `(fun _ _ => False)`. These handlers always return `Step`, never `Error`. The proof obligation becomes vacuously true in the *correct* direction — no error state exists to satisfy.

**Group C — Offset closure handlers (8 handlers)**

`handle_OFFSETCLOSURE ofs` errors in two cases (Interpret.v:370-380):
1. `"OFFSETCLOSURE: non-zero offset on non-closure env"` — env is `Val_block` and `ofs != 0`
2. `"OFFSETCLOSURE: invalid env"` — env is neither `Val_closure` nor `Val_block`

For fixed-offset variants, specialize:
- **OFFSETCLOSURE0** (ofs=0): Only error path 2 — Val_block with ofs=0 succeeds.
  ```coq
  (fun msg s => msg = "OFFSETCLOSURE: invalid env"%string /\
    match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end)
  ```
- **OFFSETCLOSURE3, OFFSETCLOSUREM3** (ofs!=0): Both error paths possible.
  ```coq
  (fun msg s =>
    (msg = "OFFSETCLOSURE: non-zero offset on non-closure env"%string /\
     match Machine.env s with Val_block _ _ => True | _ => False end) \/
    (msg = "OFFSETCLOSURE: invalid env"%string /\
     match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end))
  ```
- **OFFSETCLOSURE** (generic ofs): General form with both paths.

Same pattern for **PUSHOFFSETCLOSURE0, PUSHOFFSETCLOSURE3, PUSHOFFSETCLOSUREM3, PUSHOFFSETCLOSURE** — push happens before the env check, doesn't affect error conditions. Use `"PUSHOFFSETCLOSURE: ..."` messages.

**Group D — Method lookup (3 handlers): GETMETHOD, GETPUBMET, GETDYNMET**

Error conditions involve heap lookups (`field_or_heap`, `scan` loop) whose state characterization is complex. Characterize by message strings, which is still non-trivial (proves the proof must actually reach the Error branch with the right message):

- **GETMETHOD** (Interpret.v:817-833) — 4 error messages:
  ```coq
  (fun msg _ => msg = "GETMETHOD: stack underflow"%string \/
    msg = "GETMETHOD: no class table"%string \/
    msg = "GETMETHOD: not an integer index"%string \/
    msg = "GETMETHOD: method not found"%string)
  ```
- **GETPUBMET** (Interpret.v:842-867) — 2 error messages:
  ```coq
  (fun msg _ => msg = "GETPUBMET: no class table"%string \/
    msg = "GETPUBMET: method not found"%string)
  ```
- **GETDYNMET** (Interpret.v:870-898) — 3 error messages:
  ```coq
  (fun msg _ => msg = "GETDYNMET: stack underflow"%string \/
    msg = "GETDYNMET: no class table"%string \/
    msg = "GETDYNMET: method not found"%string)
  ```

**Group E — SWITCH (1 handler)**

`handle_SWITCH` (Interpret.v:618-639) has 3 error messages. Characterize both message and accu structure:
```coq
(fun msg s =>
  (msg = "SWITCH: constant index out of range"%string /\
   match Machine.accu s with Val_int _ => True | _ => False end) \/
  (msg = "SWITCH: block tag out of range"%string) \/
  (msg = "SWITCH: dangling pointer"%string /\
   match Machine.accu s with Val_ptr _ | Val_closure _ _ => True | _ => False end))
```

### Step 8: Update proof files for changed error predicates

For each handler whose error predicate changes from `True` to a specific characterization, the corresponding `_correct.v` proof file must be updated. The Error branch of `handler_correct` now requires proving the specific predicate instead of `True`.

- **Groups A, B**: Simple — destruct the handler match, read off the error message string.
- **Group C**: Destruct `Machine.env s`, case-split on ofs=0 vs ofs!=0 where relevant.
- **Groups D, E**: Destruct the nested matches, read off the message for each Error branch.

These proofs are typically short (a few lines of `simpl; destruct; auto`) since the Error branches in the handler definition directly produce the characterized message.

### Step 9: Update InstructVerification.v for changed signatures

If any Parameter signature changes (it will for all 19 handlers), verify that the corresponding proof in InstructVerification.v still type-checks. The proof term itself shouldn't change — only the type it must satisfy.

## Files to modify

Source locations after the instruct-verification reorganization:

- `InstructSpec.v` — `manual/Bytecode/InstructSpec.v`
- `<OP>_correct.v` files — `automatic/Bytecode/InstructVerification/`
- `InstructVerification` module ascription — `checker/Bytecode/InstructChecker.v`
  (`Module InstructVerification <: InstructVerificationSpec`).

| File | Action |
|------|--------|
| `manual/Bytecode/InstructSpec.v` | Add loop AST defs, closure/closurerec general step_pre; fix 19 error predicates in Parameter declarations |
| `CLOSURE_correct.v` | Rewrite: generalize from nvars=0 to arbitrary nvars |
| `CLOSUREREC_correct.v` | Rewrite: generalize from nfuncs=1,nvars=0 to arbitrary nfuncs,nvars |
| `BGEINT_correct.v` | Update Error branch proof for new predicate |
| `BGTINT_correct.v` | Update Error branch proof for new predicate |
| `BLEINT_correct.v` | Update Error branch proof for new predicate |
| `BUGEINT_correct.v` | Update Error branch proof for new predicate |
| `BULTINT_correct.v` | Update Error branch proof for new predicate |
| `BOOLNOT_correct.v` | Update Error branch proof for `False` predicate |
| `ISINT_correct.v` | Update Error branch proof for `False` predicate |
| `OFFSETCLOSURE0_correct.v` | Update Error branch proof |
| `OFFSETCLOSURE3_correct.v` | Update Error branch proof |
| `OFFSETCLOSUREM3_correct.v` | Update Error branch proof |
| `OFFSETCLOSURE_correct.v` | Update Error branch proof |
| `PUSHOFFSETCLOSURE0_correct.v` | Update Error branch proof |
| `PUSHOFFSETCLOSURE3_correct.v` | Update Error branch proof |
| `PUSHOFFSETCLOSUREM3_correct.v` | Update Error branch proof |
| `PUSHOFFSETCLOSURE_correct.v` | Update Error branch proof |
| `GETDYNMET_correct.v` | Update Error branch proof |
| `GETPUBMET_correct.v` | Update Error branch proof |
| `GETMETHOD_correct.v` | Update Error branch proof |
| `SWITCH_correct.v` | Update Error branch proof |
| `checker/Bytecode/InstructChecker.v` | Verify all 151 bindings type-check with new signatures |

## Key patterns to reuse

- `makeblock_step_pre` loop postcondition pattern (InstructSpec.v:2294-2330)
- `heap_alloc_with_stores` / `heap_alloc_pre` building blocks (InstructSpec.v:800-824, 913-930)
- `alloc_store_2` for the 2-field base case; inline store chain for variable-size blocks
- `HandlerLemmas.v` memory store/load lemmas
- `ExternalCallSpecs.v` heap_alloc specification
- `StepToBigstep.v` comp_eval_stmt + eval_stmt_to_exec pattern for non-loop code

## Verification

1. Build from `verified-ocaml/` with the `coq_makefile` flow (see CLAUDE.md
   "Verifying Rocq compilation"), naming only the specific `.vo` targets
   — never run a bare `make -f Makefile.coq.*` over a whole tier (it
   rebuilds every file in the tier and times out):
   ```bash
   make Makefile.coq.checker
   make -f Makefile.coq.checker checker/Bytecode/InstructChecker.vo
   ```
   `InstructChecker.vo` transitively pulls in `manual/Bytecode/InstructSpec.vo`
   and every per-handler `_correct.vo` that the module ascription uses,
   so this is the right single target to drive.
2. The `Module InstructVerification <: InstructVerificationSpec` declaration
   in `checker/Bytecode/InstructChecker.v` is the machine-checked proof
   that all 151 parameters are satisfied.
3. Check `Print Assumptions verify_CLOSURE_general_correct.` and
   `Print Assumptions verify_CLOSUREREC_general_correct.` to confirm
   0 axioms/admitted.

## Ordering / dependencies

1. **Error predicate fixes first** (Steps 7-9): These are localized changes to `manual/Bytecode/InstructSpec.v` + corresponding `_correct.v` files. Each is independent — can be done in any order. Do these before CLOSURE/CLOSUREREC since they touch `InstructSpec.v` and we want a clean baseline.
2. **CLOSURE generalization** (Steps 1-4, 6): One loop, simpler layout. Serves as warm-up and template.
3. **CLOSUREREC generalization** (Steps 1-2, 3, 5-6): Two loops, infix headers, pointer arithmetic. Builds on CLOSURE pattern.
4. **Final build**: from `verified-ocaml/`, `make Makefile.coq.checker && make -f Makefile.coq.checker checker/Bytecode/InstructChecker.vo` confirms all 151 parameters satisfied with 0 Admitted.
