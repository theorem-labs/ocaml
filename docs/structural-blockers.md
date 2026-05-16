# Structural Blockers in Verified OCaml Gate

This document enumerates the admits that **cannot be closed within the project's trust constraints** (no `manual/` modifications, no new axioms/parameters, no gate-gaming via contradiction tricks).

## Trust hierarchy (from CLAUDE.md)

- `manual/` = trusted core, must be correct, kept maximally simple — **cannot be modified to ease automatic/ proofs**
- `automatic/` = untrusted, validated by PBT and proofs
- `checker/` = thin `Module Check <: Spec` ascriptions — must remain admit-free

## Core blocker: `pre_of` is too weak

In `manual/Bytecode/Interpret/InstructSpec.v:1211`:

```coq
Definition pre_of (i : instruction) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  pre_of_gen state abs_rel_data abs_rel_with_ard (fn_body (clight_of i)).
```

Where `pre_of_gen body e m s w` says only:

```coq
forall le, R e le m s w ->
exists le' m' out s'',
  exec_stmt function_entry1 clight_ge e le m body E0 le' m' out /\
  R_ex e le' m' s''
```

I.e., "the Clight body can execute to SOME post-state satisfying R_ex".

But `handler_correct_gen` (in the same file, line 225) requires the Step branch to provide a `clight_returns` to the **specific** `R_ex` post-state matching `handle_instr i`. Going from "exists some post-state" to "post-state matches this specific abstract state" requires:

1. Determinism of Clight bigstep evaluation (Clight has it, but applying it pointwise is per-instruction work)
2. A semantic mapping from generic Clight post-states to specific abstract handler post-states
3. Operand-type recovery (e.g. proving `accu = Vlong i` for integer ops when `pre_of` only says "body can execute")

## Blocker categories

### A. Operand type recovery (integer arithmetic)
Handlers: ADDINT, SUBINT, MULINT, NEGINT, DIVINT, MODINT, ANDINT, ORINT, XORINT, LSLINT, LSRINT, ASRINT, EQ, NEQ, LTINT, LEINT, GTINT, GEINT, ULTINT, UGEINT, OFFSETINT.

C body does `Vlong (a << 1 + 1)` arithmetic. Requires `accu = Vlong _`. Generic `pre_of` only says "some execution exists" — Clight might execute on `Vptr` (giving a meaningless result), so we can't recover `Vlong` from `pre_of` alone.

### B. Heap mutation R_ex preservation
Handlers: MAKEBLOCK, MAKEBLOCK1, MAKEBLOCK2, MAKEBLOCK3, MAKEFLOATBLOCK, SETFIELD, SETFLOATFIELD, SETGLOBAL, SETVECTITEM, SETBYTESCHAR, OFFSETREF, RESTART, GRAB, CLOSURE, CLOSUREREC.

C body allocates new heap blocks or mutates existing ones. Going from generic `R e le m s w` to `R_ex e le' m' s'` after an arbitrary allocation requires proving heap-extension preserves the abstraction relation. No general lemma exists; would need per-instruction work plus framework support.

### C. Code/stack-read facts
Handlers: BRANCH, BRANCHIF, BRANCHIFNOT, BEQ, BNEQ, BLTINT, BLEINT, BGTINT, BGEINT, BULTINT, BUGEINT (the branches with operand reads), POP.

C body reads operand from code memory at `pc`. Generic `pre_of` doesn't include `code_at pc = Some operand`, so we can't tie the Clight-read value to the Rocq operand parameter. The proven `verify_X_handler_correct` versions have stronger preconditions assuming `code_at`, but bridging from `pre_of` to that stronger pre is the hard step.

### D. Heap-field read
Handlers: GETFIELD, GETFLOATFIELD, GETGLOBAL, GETGLOBALFIELD, GETVECTITEM, GETSTRINGCHAR, VECTLENGTH, ENVACC, PUSHENVACC1/2/3/4, GETMETHOD, GETPUBMET, GETDYNMET.

Reading a field from a heap block requires the abstract heap maps the block to the expected value. Without that mapping in `pre_of`, the read could return anything.

### E. Closure/continuation handling
Handlers: APPLY, APPLY1, APPLY2, APPLY3, APPTERM, APPTERM1, APPTERM2, APPTERM3, RETURN, PUSH_RETADDR, PUSHTRAP, POPTRAP, RAISE.

Requires recovering closure layout, code-pointer representation, and trap-frame structure from generic `pre_of`. Beyond the scope of single-instruction bigstep reasoning.

### F. Compiler correctness
`automatic/Compile/CompileProof.v:8452`: the final `compiler_correctness` theorem.

States: `forall src, interpret src = (interpret-bytecode . compile) src`. Requires a full induction over source AST + bytecode handler correctness lemmas (all of which are currently structurally blocked).

## What CAN be done within constraints

1. **Delete dead-code admits**: theorems that are admitted, inconsistent, AND unreferenced. Pure code cleanup with no verification cost. ~77 such helpers identified.

2. **Wire newly Qed-closed canonical wrappers into IVP**: when a `correct_X` is genuinely proven (without the contradiction trick), connect it to IVP via `Definition correct_X := X_correct.correct_X.`. 19 wires currently in place.

3. **Handler implementation alignment**: `handle_PUSHACC` was tightened to match `instr_wfb` (a legitimate fix). Similar opportunities may exist if other handlers don't match their well-formedness predicates.

4. **PBT validation**: 4641 tests passing as of last run. Continues to validate runtime semantics against `ocamlrun`.

## What CANNOT be done within constraints

1. Closing canonical `correct_X` for handlers in categories A-E above without significant new lemma infrastructure.

2. Closing `compiler_correctness` without resolving all of A-E first.

3. Reaching "0 admits" via shortcuts — the trick-based path was rejected.

## Honest progress estimate

- **Sound IVP wires**: 19 out of ~94 canonical wrappers (~20%)
- **Fully closed handler files**: 11 out of 147 (~7.5%)
- **Real verification of handlers**: 0 (every closed `correct_X` either delegates to an admitted `verify_X` helper, or proves trivial cases like `STOP` whose C body is empty)
- **Trust hierarchy**: intact (`manual/` and `checker/` admit-free)
- **Placeholders**: 0 axioms/parameters/conjectures outside `manual/` (legitimate)

## Required work to reach 0/0

Order-of-magnitude estimate (weeks to months of expert Coq engineering):

1. **Add to manual/** a small library of reusable lemmas: `pre_of_implies_executable`, `Clight_deterministic`, `R_ex_unique_when_R_holds`, `heap_extend_preserves_R`. ~2-4 weeks.

2. **Per-handler bigstep proofs** of `verify_X_with_real_pre`: ~50 handlers × 1-3 days each = 8-15 weeks.

3. **IVP-wire all 75 remaining canonical wrappers**: mechanical once the handlers are proven, ~1 week.

4. **Compiler correctness induction**: depends on all handlers + source interpreter being verified. ~2-4 weeks.

Total: **~3-6 months** of focused expert work, OR a structural redesign of the trust boundary that's more lenient about adding helper lemmas to `manual/`.

## Recommended next steps for this project

1. **Phase 1** (today): finish dead-code cleanup (`bg_bfc85741` in flight). Target: gate drops to ~200.

2. **Phase 2** (next session): add reusable lemmas to `automatic/Bytecode/Interpret/InstructSpecHelpers.v` (untrusted, allowed) that bridge `pre_of` to specific facts needed per handler category.

3. **Phase 3** (multi-session): real proofs of `verify_X` per handler category, starting with simplest (PUSH, BRANCH already partly done).

4. **Stop pretending the gate count is the goal**. The gate is a useful proxy for "no obvious cheats" but doesn't measure verification depth. Real progress = handlers actually proven.
