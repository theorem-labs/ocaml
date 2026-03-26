# Verification Plan: interp.c Instruct() Handlers vs Interpret.v step Function

## Table of Contents

1. [Goal and Scope](#1-goal-and-scope)
2. [Structure Alignment](#2-structure-alignment)
3. [Abstraction Relation](#3-abstraction-relation)
4. [Instruction-by-Instruction Comparison Table](#4-instruction-by-instruction-comparison-table)
5. [Should Interpret.v Be Restructured?](#5-should-interpretv-be-restructured)
6. [The C-to-Clight Pipeline](#6-the-c-to-clight-pipeline)
7. [Per-Handler Verification Template](#7-per-handler-verification-template)
8. [Divergences Requiring Investigation](#8-divergences-requiring-investigation)
9. [Automation Opportunities](#9-automation-opportunities)
10. [Execution Roadmap](#10-execution-roadmap)

---

## 1. Goal and Scope

**Objective**: For every `Instruct(X)` handler in `runtime/interp.c` (OCaml 4.14), prove or validate that the corresponding case in `Interpret.v`'s `step` function computes an equivalent state transition under the abstraction relation.

**Files under analysis**:

| File | Path | Role |
|------|------|------|
| `interp.c` | `system-ocaml-compiler/runtime/interp.c` | C reference (1179 lines, ~137 Instruct handlers) |
| `Interpret.v` | `manual/theories/Bytecode/Interpret.v` | Rocq spec (~1027 lines, ~107 instruction cases) |
| `AST.v` | `manual/theories/Bytecode/AST.v` | Instruction inductive type (107 constructors) |
| `Machine.v` | `manual/theories/Bytecode/Machine.v` | State record, heap operations |
| `Value.v` | `manual/theories/Utils/Value.v` | Value representation |
| `instruct.h` | `system-ocaml-compiler/runtime/caml/instruct.h` | C opcode enum (149 opcodes before FIRST_UNIMPLEMENTED_OP) |

**Scope boundaries**: We verify semantic equivalence of the pure state-transition logic. The following C-side concerns are explicitly out of scope for the core verification (but must be documented as assumptions):

- Garbage collection (Setup_for_gc / Restore_after_gc, Alloc_small)
- Signal handling (caml_something_to_do, process_actions)
- Debugger interface (Setup_for_debugger, caml_debugger)
- Stack overflow checks (check_stacks, caml_realloc_stack)
- Backtrace collection (caml_stash_backtrace)
- Memory barrier / write barrier (caml_modify vs direct assignment)
- Threaded code dispatch (jumptable, Next macro)

---

## 2. Structure Alignment

### 2.1 C Structure

The C interpreter is a single function `caml_interprete` containing a switch/goto dispatch loop:

```c
while(1) {
  curr_instr = *pc++;
  switch(curr_instr) {
    Instruct(ACC0): accu = sp[0]; Next;
    Instruct(ACC1): accu = sp[1]; Next;
    ...
  }
}
```

Key patterns:
- **Specialized variants**: `ACC0..ACC7` are specialized versions of `ACC n`. Similarly `CONST0..CONST3`, `ENVACC1..ENVACC4`, `GETFIELD0..GETFIELD3`, `SETFIELD0..SETFIELD3`, `C_CALL1..C_CALL5`, `OFFSETCLOSURE0/3/M3`, `ATOM0`, `PUSHATOM0`.
- **Fallthrough**: Several instructions use C fallthrough: `PUSHACC` falls into `ACC`, `PUSHENVACC` falls into `ENVACC`, `PUSHGETGLOBAL` into `GETGLOBAL`, `PUSHOFFSETCLOSURE` into `OFFSETCLOSURE`, `PUSHCONSTINT` into `CONSTINT`, `PUSHATOM` into `ATOM`.
- **goto labels**: `check_stacks` (stack overflow + signal check), `process_actions` (signal handler), `raise_notrace` (shared raise logic).

### 2.2 Rocq Structure

The Rocq interpreter is a single `step` function:

```coq
Definition step (code : array instruction) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | None => Error "pc out of bounds"
  | Some instr =>
    let pc' := s.(pc) + 1 in
    match instr with
    | ACC n => ...
    | PUSH => ...
    ...
    end
  end.
```

Key patterns:
- **Generalized constructors**: `ACC n` covers `ACC0..ACC7` and `ACC`. The decoder/loader is responsible for mapping specialized C opcodes to generalized Rocq constructors (e.g., `ACC0` -> `ACC 0`).
- **No fallthrough**: Each case is self-contained.
- **Error as result**: Invalid operations return `Error msg` rather than crashing.
- **CCall_request**: C primitive calls suspend execution and return a request.

### 2.3 Opcode Count Reconciliation

The C `instruct.h` enum has 149 opcodes (before `FIRST_UNIMPLEMENTED_OP`). The Rocq `AST.v` has 107 constructors. The difference is accounted for by specialization folding:

| C Specialized Opcodes | Rocq Generalized Form | Count Absorbed |
|----------------------|----------------------|----------------|
| ACC0..ACC7 | ACC n | 8 -> 0 (ACC itself exists) |
| PUSHACC0..PUSHACC7 | PUSHACC n (+ PUSH for PUSHACC0) | 8 -> 0 |
| ENVACC1..ENVACC4 | ENVACC n | 4 -> 0 |
| PUSHENVACC1..PUSHENVACC4 | PUSHENVACC n | 4 -> 0 |
| CONST0..CONST3 | CONSTINT n | 4 -> 0 |
| PUSHCONST0..PUSHCONST3 | PUSHCONSTINT n | 4 -> 0 |
| GETFIELD0..GETFIELD3 | GETFIELD n | 4 -> 0 |
| SETFIELD0..SETFIELD3 | SETFIELD n | 4 -> 0 |
| OFFSETCLOSURE0, OFFSETCLOSURE3, OFFSETCLOSUREM3 | OFFSETCLOSURE n | 3 -> 0 |
| PUSHOFFSETCLOSURE0, PUSHOFFSETCLOSURE3, PUSHOFFSETCLOSUREM3 | PUSHOFFSETCLOSURE n | 3 -> 0 |
| ATOM0 | ATOM n | 1 -> 0 |
| PUSHATOM0 | PUSHATOM n | 1 -> 0 |
| C_CALL1..C_CALL5 | C_CALL nargs prim_idx | 5 -> 0 |

Total specialized opcodes folded: 8+8+4+4+4+4+4+4+3+3+1+1+5 = **53**. But the generalized forms (ACC, PUSHACC, ENVACC, etc.) each still exist, so net reduction = 53 - 13 generalized that also exist in C = **40** net opcodes absorbed. Plus `PUSH` and `PUSHACC0` are aliased in C (same handler), and Rocq has `PUSH` separately.

The Rocq AST also adds 4 constructors not in OCaml 4.14's `instruct.h`: `PERFORM`, `RESUME`, `RESUMETERM`, `REPERFORMTERM` (OCaml 5.x effect handlers, currently returning Error).

---

## 3. Abstraction Relation

### 3.1 Value Representation

| C Representation | Rocq Representation | Relation |
|-----------------|---------------------|----------|
| `Val_int(n)` = `2*n+1` (tagged integer) | `Val_int n` | `C_val = 2 * rocq_z + 1` |
| Heap pointer `p` (even, points to block) | `Val_ptr addr` | `C_ptr = base_of_heap + addr * word_size` |
| `p + ofs*sizeof(value)` (infix closure pointer) | `Val_closure addr ofs` | Interior pointer into block at `addr` |
| `Atom(t)` (pointer to preallocated zero-size block with tag t) | `Val_ptr addr` where `heap[addr] = (t, [])` | Rocq heap-allocates atoms; C uses static atoms |
| `Field(v, n)` | `field_or_heap s v n` | Dereferencing through heap indirection |
| Block header: `Wosize_val(v)`, `Tag_val(v)` | `heap_lookup` returning `(tag, fields)` with `length fields` | Size = list length, tag = first component |

### 3.2 State Mapping

| C State | Rocq State | Notes |
|---------|------------|-------|
| `pc` (code_t, pointer into bytecode array) | `s.(pc)` (Z, index into instruction array) | C uses byte-level pointer; Rocq uses instruction index |
| `accu` (value register) | `s.(accu)` (value) | Direct |
| `sp` (value*, grows downward) | `s.(stack)` (list value, head = top) | C: `sp[0]` = top. Rocq: `hd stack` = top |
| `env` (value, heap pointer to closure) | `s.(env)` (value) | Direct |
| `extra_args` (intnat) | `s.(extra_args)` (nat) | Direct (non-negative invariant) |
| `caml_global_data` (value, tuple of global slots) | `s.(global)` (list value) | `Field(caml_global_data, n)` = `nth_error global n` |
| `Caml_state->trapsp` (value*, stack pointer) | `s.(trap_sp)` (nat, stack depth at trap) | C: absolute pointer. Rocq: depth from bottom |
| Heap (GC-managed memory) | `s.(hp)` (PositiveMap nat (nat * list value)) | See below |
| Next free address | `s.(next_addr)` (nat) | C: implicit in allocator |

### 3.3 Heap Abstraction

The C heap is GC-managed memory where blocks are allocated with headers. The Rocq heap is a `PositiveMap` from addresses to `(tag, fields)` pairs.

**Critical invariant**: The Rocq `heap_alloc` function is deterministic -- it always uses `next_addr` as the new address and increments it. The C allocator (`Alloc_small`, `caml_alloc_shr`) may trigger GC which moves objects. The abstraction must account for this: after GC, the logical heap is unchanged (GC preserves reachable values), so the abstraction relation must be defined modulo GC.

### 3.4 PC Representation

The C interpreter uses `*pc++` to both read an opcode and advance the program counter. Operands are also read with `*pc++`. The Rocq interpreter uses `fetch_instr code s.(pc)` with `pc' := s.(pc) + 1`, then operands are already decoded into the instruction constructor (e.g., `ACC n` already has `n`).

This means: the **decoder/loader** is responsible for translating from the flat C byte stream (opcode, operand, operand, ...) to the Rocq instruction ADT. The `step` function itself does not need to parse operands. Branch targets in C are relative offsets (`pc += *pc`) while in Rocq they are absolute instruction indices (pre-resolved by the decoder).

### 3.5 Formal Abstraction Relation (Sketch)

```coq
(* The core abstraction relation *)
Record abs_rel (c_state : C_state) (r_state : state) : Prop := {
  (* Value correspondence *)
  val_repr : value -> C_value -> Prop;

  (* Register correspondence *)
  accu_rel : val_repr r_state.(accu) c_state.(c_accu);
  env_rel  : val_repr r_state.(env) c_state.(c_env);
  ea_rel   : r_state.(extra_args) = Z.to_nat c_state.(c_extra_args);

  (* Stack correspondence: Rocq list corresponds to C sp..stack_high *)
  stack_rel : Forall2 val_repr r_state.(stack)
                (c_stack_to_list c_state.(c_sp) c_state.(c_stack_high));

  (* Heap correspondence: every Rocq heap entry has a corresponding C block *)
  heap_rel : forall addr tag fields,
    heap_lookup r_state.(hp) addr = Some (tag, fields) ->
    exists c_ptr, c_ptr = addr_to_c_ptr addr /\
      Tag_val c_ptr = tag /\
      Wosize_val c_ptr = length fields /\
      Forall2 val_repr fields (c_block_fields c_ptr);

  (* PC correspondence *)
  pc_rel : c_state.(c_pc) = instr_addr_to_c_ptr r_state.(pc);
}.
```

---

## 4. Instruction-by-Instruction Comparison Table

### Legend

- **Identical**: Pure state transition is the same modulo abstraction
- **Abstracted**: C has GC/signals/debug that Rocq correctly ignores
- **Missing-C**: Instruction in Rocq but not in C (OCaml 5.x additions)
- **Missing-R**: Instruction in C but not in Rocq
- **Divergent**: Semantic difference requiring investigation

### 4.1 Stack Operations

| C Opcode(s) | Rocq Constructor | Status | Notes |
|-------------|-----------------|--------|-------|
| ACC0..ACC7, ACC | ACC n | Identical | C: `accu = sp[n]`. Rocq: `nth_error stack n` |
| PUSH, PUSHACC0 | PUSH | Identical | C: `*--sp = accu`. Rocq: `accu :: stack` |
| PUSHACC1..PUSHACC7, PUSHACC | PUSHACC n | Identical | Push then access |
| POP | POP n | Identical | C: `sp += n`. Rocq: `skipn n stack` |
| ASSIGN | ASSIGN n | Identical | C: `sp[n] = accu; accu = Val_unit`. Rocq: `set_nth stack n accu` |

### 4.2 Environment Access

| C Opcode(s) | Rocq Constructor | Status | Notes |
|-------------|-----------------|--------|-------|
| ENVACC1..ENVACC4, ENVACC | ENVACC n | Identical | C: `Field(env, n)`. Rocq: `field_or_heap s env n` |
| PUSHENVACC1..PUSHENVACC4, PUSHENVACC | PUSHENVACC n | Identical | Push then env access |

### 4.3 Function Application

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| PUSH_RETADDR | PUSH_RETADDR addr | Identical | Both push `[ret_addr, env, extra_args]`. C: `sp[0]=(value)(pc+*pc)`. Rocq: `Val_int ret_addr` (pre-resolved) |
| APPLY | APPLY n | Abstracted | C: `goto check_stacks` (stack overflow + signals). Rocq: pure Step |
| APPLY1 | APPLY1 | Abstracted | Same as APPLY but saves return frame. C: goto check_stacks |
| APPLY2 | APPLY2 | Abstracted | Same pattern |
| APPLY3 | APPLY3 | Abstracted | Same pattern |
| APPTERM | APPTERM nargs slotsize | Abstracted | C: manual slide loop + goto check_stacks. Rocq: `firstn/skipn/++` |
| APPTERM1 | APPTERM1 slotsize | Abstracted | Specialized slide |
| APPTERM2 | APPTERM2 slotsize | Abstracted | Specialized slide |
| APPTERM3 | APPTERM3 slotsize | Abstracted | Specialized slide |
| RETURN | RETURN stacksize | Identical | Both: pop locals, then either tail-call or restore return frame |
| RESTART | RESTART | Identical | Both: restore partial-application args from closure env |
| GRAB | GRAB required | Abstracted | C: Alloc_small for partial closure (GC). Rocq: heap_alloc |

### 4.4 Closures

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| CLOSURE | CLOSURE nvars code_ofs | Abstracted | C: Alloc_small or caml_alloc_shr (GC). Rocq: heap_alloc. C stores `Make_closinfo(0,2)` as closinfo; Rocq stores `Val_int 0`. **Divergence**: closinfo encoding differs but is opaque to other instructions |
| CLOSUREREC | CLOSUREREC nf nv offsets | Abstracted | Complex. C: allocates flat block, stores infix headers as raw `Make_header()`. Rocq: stores `Val_block Infix_tag []` as infix header. **Divergence**: infix header representation. See Section 8.1 |
| OFFSETCLOSURE0, OFFSETCLOSURE3, OFFSETCLOSUREM3, OFFSETCLOSURE | OFFSETCLOSURE ofs | **Divergent** | C: `accu = env + ofs * sizeof(value)` (pointer arithmetic). Rocq: constructs `Val_closure addr new_ofs`. The C version produces an interior pointer; Rocq tracks base address + offset. See Section 8.2 |
| PUSHOFFSETCLOSURE0, PUSHOFFSETCLOSURE3, PUSHOFFSETCLOSUREM3, PUSHOFFSETCLOSURE | PUSHOFFSETCLOSURE ofs | **Divergent** | Same as OFFSETCLOSURE with push |

### 4.5 Global Variables

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| GETGLOBAL | GETGLOBAL n | Identical | C: `Field(caml_global_data, *pc)`. Rocq: `nth_error global n` |
| PUSHGETGLOBAL | PUSHGETGLOBAL n | Identical | Push then getglobal |
| GETGLOBALFIELD | GETGLOBALFIELD n p | Identical | Two-level field access |
| PUSHGETGLOBALFIELD | PUSHGETGLOBALFIELD n p | Identical | Push then getglobalfield |
| SETGLOBAL | SETGLOBAL n | Identical | C: `caml_modify(...)` (write barrier). Rocq: `set_nth` |

### 4.6 Allocation

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| ATOM0, ATOM | ATOM t | **Divergent** | C: `Atom(t)` returns pointer to static preallocated atom. Rocq: `heap_alloc s t []` allocates a new heap entry. See Section 8.3 |
| PUSHATOM0, PUSHATOM | PUSHATOM t | **Divergent** | Same atom divergence with push |
| MAKEBLOCK | MAKEBLOCK t size | Abstracted | C: Alloc_small or caml_alloc_shr. Note C reads `wosize` then `tag`; Rocq constructor is `MAKEBLOCK t size` (tag first). Decoder must swap |
| MAKEBLOCK1 | MAKEBLOCK1 t | Abstracted | GC only |
| MAKEBLOCK2 | MAKEBLOCK2 t | Abstracted | GC only |
| MAKEBLOCK3 | MAKEBLOCK3 t | Abstracted | GC only |
| MAKEFLOATBLOCK | MAKEFLOATBLOCK n | **Divergent** | C: allocates `n * Double_wosize` words with `Double_array_tag`, stores actual float bits via `Store_double_flat_field`. Rocq: allocates with tag 254, stores values directly. See Section 8.4 |

### 4.7 Field Access

| C Opcode(s) | Rocq Constructor | Status | Notes |
|-------------|-----------------|--------|-------|
| GETFIELD0..GETFIELD3, GETFIELD | GETFIELD n | Identical | C: `Field(accu, n)`. Rocq: `field_or_heap s accu n` |
| GETFLOATFIELD | GETFLOATFIELD n | **Divergent** | C: reads `Double_flat_field`, then allocates a boxed float (`Alloc_small` with `Double_tag`). Rocq: just reads field. See Section 8.4 |
| SETFIELD0..SETFIELD3, SETFIELD | SETFIELD n | Identical | C: `caml_modify(...)`. Rocq: `set_nth` + `heap_update`. Note: Rocq pops from stack; C pops `*sp++`. Both set `accu = Val_unit` |
| SETFLOATFIELD | SETFLOATFIELD n | **Divergent** | C: `Store_double_flat_field`. Rocq: uses `set_nth`. Float representation differs. See Section 8.4 |

### 4.8 Array Operations

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| VECTLENGTH | VECTLENGTH | **Divergent** | C: `Wosize_val(accu)` with special case for `Double_array_tag` (divides by `Double_wosize`). Rocq: `size_or_heap` returns `length fields`. Float array sizes may differ. See Section 8.4 |
| GETVECTITEM | GETVECTITEM | Identical | C: `Field(accu, Long_val(sp[0]))`. Rocq: `field_or_heap` |
| SETVECTITEM | SETVECTITEM | Identical | C: `caml_modify(...)`. Rocq: `set_nth` + `heap_update` |

### 4.9 String/Bytes Operations

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| GETSTRINGCHAR, GETBYTESCHAR | GETSTRINGCHAR / GETBYTESCHAR | **Divergent** | C: `Byte_u(accu, Long_val(sp[0]))` reads a raw byte from the block's data area. Rocq: `field_or_heap` treats each character as a separate field `Val_int c`. See Section 8.5 |
| SETBYTESCHAR | SETBYTESCHAR | **Divergent** | C: `Byte_u(accu, Long_val(sp[0])) = Int_val(sp[1])`. Rocq: `set_nth` on field list. See Section 8.5 |

### 4.10 Branches

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| BRANCH | BRANCH target | Identical | C: `pc += *pc` (relative). Rocq: `pc := target` (absolute, pre-resolved) |
| BRANCHIF | BRANCHIF target | Identical | C: `accu != Val_false`. Rocq: `accu != Val_int 0` |
| BRANCHIFNOT | BRANCHIFNOT target | Identical | C: `accu == Val_false`. Rocq: `accu = Val_int 0` |
| SWITCH | SWITCH nc nb const_targets block_targets | Identical | Both dispatch on Is_block/tag vs integer index. C uses packed sizes word; Rocq receives pre-decoded lists |
| BOOLNOT | BOOLNOT | Identical | C: `Val_not(accu)`. Rocq: int 0 -> true, else -> false |

### 4.11 Exceptions

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| PUSHTRAP | PUSHTRAP handler_pc | Identical | Both push 4-word trap frame. C: `Trap_link_offset` stores relative offset. Rocq: stores absolute `trap_sp` |
| POPTRAP | POPTRAP | Abstracted | C: checks `caml_something_to_do` (signals). Rocq: pure pop |
| RAISE | RAISE | Abstracted | C: backtrace collection, debugger trap barrier. Rocq: `do_raise` |
| RERAISE | RERAISE | Abstracted | Same as RAISE with backtrace flag=1 |
| RAISE_NOTRACE | RAISE_NOTRACE | Abstracted | Same as RAISE without backtrace |

**Note**: All three raise variants share `raise_notrace` in C and `do_raise` in Rocq. The Rocq `do_raise` matches the C `raise_notrace` label: restore sp from trapsp, extract handler_pc/env/extra_args, pop 4. Correct.

### 4.12 Signals and C Calls

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| CHECK_SIGNALS | CHECK_SIGNALS | Abstracted | C: may call process_actions. Rocq: no-op (Step with pc') |
| C_CALL1..C_CALL5, C_CALLN | C_CALL nargs prim_idx | Abstracted | C: Setup_for_c_call, call primitive, Restore_after_c_call. Rocq: returns `CCall_request` to suspend. Rocq unifies all arities into one constructor |

### 4.13 Integer Constants

| C Opcode(s) | Rocq Constructor | Status | Notes |
|-------------|-----------------|--------|-------|
| CONST0..CONST3, CONSTINT | CONSTINT n | Identical | C: `Val_int(n)`. Rocq: `Val_int n` |
| PUSHCONST0..PUSHCONST3, PUSHCONSTINT | PUSHCONSTINT n | Identical | Push then constint |

### 4.14 Integer Arithmetic

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| NEGINT | NEGINT | Identical | C: `2 - (intnat)accu` on tagged repr. Rocq: `- n` on untagged Z. Equivalent: `2 - (2n+1) = -(2n-1) = 2*(-n)+1` |
| ADDINT | ADDINT | Identical | C: `accu + *sp - 1` (tagged). Rocq: `a + b` (untagged). `(2a+1)+(2b+1)-1 = 2(a+b)+1` |
| SUBINT | SUBINT | Identical | C: `accu - *sp + 1` (tagged). Rocq: `a - b` (untagged). `(2a+1)-(2b+1)+1 = 2(a-b)+1` |
| MULINT | MULINT | Identical | C: `Val_long(Long_val(accu) * Long_val(*sp))`. Rocq: `a * b` |
| DIVINT | DIVINT | Identical | Both raise Division_by_zero on zero divisor. C: `Long_val(accu) / divisor`. Rocq: `Z.quot a b`. Note: C integer division truncates toward zero, matching `Z.quot` |
| MODINT | MODINT | Identical | C: `%` operator. Rocq: `Z.rem`. Both truncate toward zero |
| ANDINT | ANDINT | Identical | C: `accu & *sp` (tagged). Rocq: `Z.land a b`. Tagged AND preserves tag bit |
| ORINT | ORINT | Identical | C: `accu \| *sp` (tagged). Rocq: `Z.lor a b`. Tagged OR preserves tag bit |
| XORINT | XORINT | Identical | C: `(accu ^ *sp) \| 1` (tagged, restore tag bit). Rocq: `Z.lxor a b` |
| LSLINT | LSLINT | Identical | C: `((accu-1) << shift) + 1` (remove tag, shift, restore). Rocq: `Z.shiftl a b` |
| LSRINT | LSRINT | Identical | C: `((uintnat)accu >> shift) \| 1` (unsigned shift, restore tag). Rocq: `z_lsr a b` (Z.shiftr of z_unsigned) |
| ASRINT | ASRINT | Identical | C: `((intnat)accu >> shift) \| 1`. Rocq: `Z.shiftr a b` |

### 4.15 Comparisons

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| EQ | EQ | **Divergent** | C: `(intnat)accu == (intnat)*sp` (physical equality on tagged values). Rocq: `value_phys_eqb`. C compares raw bits; Rocq has type-based dispatch. See Section 8.6 |
| NEQ | NEQ | **Divergent** | Same issue as EQ |
| LTINT | LTINT | Identical | C: `(intnat)accu < (intnat)*sp`. Rocq: `a <? b` |
| LEINT | LEINT | Identical | Both signed comparison |
| GTINT | GTINT | Identical | Both signed comparison |
| GEINT | GEINT | Identical | Both signed comparison |
| ULTINT | ULTINT | Identical | C: `(uintnat)accu < (uintnat)*sp`. Rocq: `z_flip_sign` then `Z.ltb` |
| UGEINT | UGEINT | Identical | C: `(uintnat)accu >= (uintnat)*sp`. Rocq: `z_flip_sign` then `Z.geb` |
| OFFSETINT | OFFSETINT n | Identical | C: `accu += *pc << 1`. Rocq: `a + n`. Tagged: adding `n<<1` to `2a+1` gives `2(a+n)+1` |
| OFFSETREF | OFFSETREF n | Identical | C: `Field(accu,0) += *pc << 1`. Rocq: reads heap, adds n, updates. Same arithmetic |
| ISINT | ISINT | Identical | C: `accu & 1`. Rocq: `is_int accu` |

### 4.16 Branch Comparisons

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| BEQ | BEQ n target | Identical | C: `*pc++ == Long_val(accu)`. Rocq: `Z.eqb a n` |
| BNEQ | BNEQ n target | Identical | Same pattern |
| BLTINT | BLTINT n target | Identical | C: `*pc++ < Long_val(accu)`. Rocq: `Z.ltb n a` (operand < accu) |
| BLEINT | BLEINT n target | Identical | Same pattern |
| BGTINT | BGTINT n target | Identical | Same pattern |
| BGEINT | BGEINT n target | Identical | Same pattern |
| BULTINT | BULTINT n target | Identical | Unsigned variant using z_flip_sign |
| BUGEINT | BUGEINT n target | Identical | Unsigned variant using z_flip_sign |

### 4.17 Object-Oriented Operations

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| GETMETHOD | GETMETHOD | Identical | C: `Lookup(sp[0], accu)` = `Field(Field(sp[0],0), Int_val(accu))`. Rocq: two-level field_or_heap |
| GETPUBMET | GETPUBMET tag | **Divergent** | C: binary search on method table with cache. Rocq: linear scan on pairs. Both find the same method but algorithm differs. See Section 8.7 |
| GETDYNMET | GETDYNMET | **Divergent** | C: binary search. Rocq: linear scan. Same result, different algorithm. See Section 8.7 |

### 4.18 Control

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| STOP | STOP | Identical | C: returns accu. Rocq: `Halt accu` |
| EVENT | EVENT | Abstracted | C: debugger event. Rocq: no-op (Step pc') |
| BREAK | BREAK | Abstracted | C: debugger breakpoint. Rocq: no-op (Step pc') |

### 4.19 Missing from Rocq (OCaml 5.x)

| C Opcode | Rocq Constructor | Status | Notes |
|----------|-----------------|--------|-------|
| (none in 4.14) | PERFORM | Missing-C | Returns Error. OCaml 5.x effect |
| (none in 4.14) | RESUME | Missing-C | Returns Error. OCaml 5.x effect |
| (none in 4.14) | RESUMETERM n | Missing-C | Returns Error. OCaml 5.x effect |
| (none in 4.14) | REPERFORMTERM n | Missing-C | Returns Error. OCaml 5.x effect |

### Summary Statistics

| Status | Count | Percentage |
|--------|-------|------------|
| Identical | ~65 instructions | ~61% |
| Abstracted (GC/signals/debug only) | ~25 instructions | ~23% |
| Divergent (needs investigation) | ~13 instructions | ~12% |
| Missing-C (Rocq-only, errors) | 4 instructions | ~4% |

---

## 5. Should Interpret.v Be Restructured?

### 5.1 Current Structure: Monolithic step

The current `step` function is a single ~900-line `match` expression. This has advantages for extraction (one function call, good for performance) but disadvantages for verification (proofs about individual handlers must unfold the entire match).

### 5.2 Proposed Structure: Individual Handler Functions

```coq
Definition handle_ACC (n : nat) (code : array instruction) (s : state) (pc' : Z) : step_result :=
  match nth_error s.(stack) n with
  | Some v => Step (s <|pc := pc'|> <|accu := v|>)
  | None => Error "ACC: stack underflow"
  end.

Definition handle_PUSH (code : array instruction) (s : state) (pc' : Z) : step_result :=
  Step (s <|pc := pc'|> <|stack := s.(accu) :: s.(stack)|>).

Definition handle_MAKEBLOCK1 (t : nat) (code : array instruction) (s : state) (pc' : Z) : step_result :=
  let '(s', ptr) := heap_alloc s t [s.(accu)] in
  Step (s' <|pc := pc'|> <|accu := ptr|>).

(* Dispatch function *)
Definition step (code : array instruction) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | None => Error "pc out of bounds"
  | Some instr =>
    let pc' := s.(pc) + 1 in
    match instr with
    | ACC n => handle_ACC n code s pc'
    | PUSH => handle_PUSH code s pc'
    | MAKEBLOCK1 t => handle_MAKEBLOCK1 t code s pc'
    ...
    end
  end.
```

### 5.3 Recommendation

**Restructure, but keep both**. The approach should be:

1. **Define individual handlers** in a new `Handlers.v` module.
2. **Define `step` as dispatch** to those handlers (as above).
3. **Prove equivalence** between the new dispatching `step` and the old monolithic `step` (trivial by unfolding).
4. **Verify each handler** independently against its C counterpart.

Benefits:
- Each handler verification is a self-contained lemma
- Handler functions can be given standalone specifications
- The dispatch proof is trivial
- Extraction performance is unaffected (inlining)

The monolithic `step` should remain available (via a compatibility lemma) so existing code and PBT infrastructure does not break.

### 5.4 Handler Signature

```coq
(* All handlers take the instruction's operands, the code array,
   the current state, and the pre-incremented pc. *)
(* Some handlers also need the original pc (e.g., GRAB stores pc-1). *)

(* Type alias for clarity *)
Definition handler_type := state -> Z (* pc' *) -> step_result.
```

Handlers that need the code array (none currently, since operands are pre-decoded) or the original pc (GRAB, CLOSUREREC) will take additional parameters.

---

## 6. The C-to-Clight Pipeline

### 6.1 Challenge

The `caml_interprete` function in `interp.c` is a single 900-line function with:
- Computed gotos (threaded code)
- Register allocation hints (`asm` annotations)
- Macros that expand to multi-statement blocks
- Shared goto labels (`check_stacks`, `raise_notrace`, `process_actions`)
- GC-related save/restore macros

Running `clightgen` directly on `interp.c` will produce one massive Clight function.

### 6.2 Strategy: Extract Individual Handler Functions

**Step 1: Preprocess interp.c**

```bash
# Expand macros, resolve #ifdefs (choose non-threaded, non-debug path)
gcc -E -DCAML_INTERNALS -DNO_THREADED_CODE runtime/interp.c > interp_expanded.c
```

**Step 2: Split into per-handler C files**

Write a script that parses the expanded switch/case structure and extracts each handler into a standalone C function with the signature:

```c
#include "handler_common.h"  /* shared type definitions */

/* State structure matching Rocq's state record */
typedef struct {
    int64_t pc;
    value accu;
    value *sp;       /* or: value *stack; int stack_len; */
    value env;
    int64_t extra_args;
    value *global;
    value *trapsp;
    /* heap abstracted via alloc/lookup functions */
} interp_state;

typedef enum { STEP, HALT, ERROR, CCALL } result_tag;
typedef struct { result_tag tag; interp_state state; value halt_val; /* ... */ } step_result;

step_result handle_ACC(interp_state s, int n) {
    s.accu = s.sp[n];
    s.pc++;
    return (step_result){ .tag = STEP, .state = s };
}
```

**Step 3: Run clightgen on each handler**

```bash
clightgen -normalize handle_ACC.c -o handle_ACC.v
```

This produces a Clight AST in Rocq that can be reasoned about with VST.

### 6.3 What the Clight AST Looks Like

For `handle_ACC`, the Clight AST would approximately be:

```coq
(* Simplified Clight for handle_ACC *)
Definition f_handle_ACC : Clight.function := {|
  fn_return := t_step_result;
  fn_params := [("s", t_interp_state); ("n", tint)];
  fn_body :=
    Ssequence
      (* s.accu = s.sp[n] *)
      (Sassign (Efield (Evar "s") "accu" tlong)
               (Ederef (Ebinop Oadd (Efield (Evar "s") "sp" (tptr tlong))
                                     (Evar "n") (tptr tlong)) tlong))
      (* s.pc++ *)
      (Sassign (Efield (Evar "s") "pc" tlong)
               (Ebinop Oadd (Efield (Evar "s") "pc" tlong) (Econst_int 1) tlong))
|}.
```

### 6.4 VST Proof Structure

Each handler verification would use the VST `forward` tactic to symbolically execute the Clight statements, then relate the result to the Rocq handler:

```coq
Lemma handle_ACC_correct : forall n s c_s,
  abs_rel c_s s ->
  n < length s.(stack) ->
  exists c_s',
    clight_eval f_handle_ACC c_s n = Some c_s' /\
    abs_rel c_s' (match handle_ACC n code s pc' with Step s' => s' | _ => s end).
```

### 6.5 Alternative: Direct C Semantics (Without VST)

If VST is too heavy, an alternative is to define a shallow embedding of each C handler as a Rocq function and prove equivalence directly. This avoids Clight entirely but requires manually transcribing the C logic:

```coq
(* Direct transcription of C handler for ACC *)
Definition c_handle_ACC (n : nat) (c : c_state) : c_state :=
  c <| c_accu := nth c.(c_sp) n |> <| c_pc := c.(c_pc) + 1 |>.

(* Then prove: *)
Lemma ACC_equiv : forall n s c,
  abs_rel c s ->
  abs_rel (c_handle_ACC n c) (handle_ACC n s).
```

This is less rigorous (the transcription is trusted) but much more practical as a first step.

---

## 7. Per-Handler Verification Template

### 7.1 Template Structure

For each instruction `INSTR`:

```
1. C handler text (verbatim from interp.c)
2. Rocq handler text (verbatim from Interpret.v)
3. Operand mapping (how C operands correspond to Rocq constructor args)
4. State transition comparison (line-by-line)
5. Abstraction concerns (GC, signals, etc.)
6. Verdict (Identical / Abstracted / Divergent)
7. If divergent: resolution plan
```

### 7.2 Example: ACC (Simplest Case)

**C handler** (interp.c lines 322-361):
```c
Instruct(ACC0): accu = sp[0]; Next;
Instruct(ACC1): accu = sp[1]; Next;
...
Instruct(ACC7): accu = sp[7]; Next;
Instruct(ACC):  accu = sp[*pc++]; Next;
```

**Rocq handler** (Interpret.v lines 106-110):
```coq
| ACC n =>
  match nth_error s.(stack) n with
  | Some v => Step (s <|pc := pc'|> <|accu := v|>)
  | None => Error "ACC: stack underflow"
  end
```

**Operand mapping**:
- C `ACC0..ACC7`: `n` is the opcode number (0-7), implicit
- C `ACC`: `n = *pc++`, read from bytecode stream
- Rocq: `n` is the constructor argument, decoded by loader

**State transition comparison**:

| Aspect | C | Rocq |
|--------|---|------|
| Read operand | `sp[n]` | `nth_error stack n` |
| Set accu | `accu = sp[n]` | `accu := v` where `v = nth_error stack n` |
| Advance pc | implicit (`*pc++` or `Next`) | `pc := pc'` where `pc' = pc + 1` |
| Stack | unchanged | unchanged |
| Error case | Undefined behavior (buffer overread) | `Error "ACC: stack underflow"` |

**Abstraction concerns**: None. Pure register/stack operation.

**Verdict**: **Identical**. Under the abstraction relation `sp[n] <-> nth_error stack n`, the state transitions match exactly. The Rocq version additionally handles the out-of-bounds case gracefully.

### 7.3 Example: MAKEBLOCK1 (Involves Heap)

**C handler** (interp.c lines 690-697):
```c
Instruct(MAKEBLOCK1): {
  tag_t tag = *pc++;
  value block;
  Alloc_small(block, 1, tag);
  Field(block, 0) = accu;
  accu = block;
  Next;
}
```

**Rocq handler** (Interpret.v lines 445-447):
```coq
| MAKEBLOCK1 t =>
  let '(s', ptr) := heap_alloc s t [s.(accu)] in
  Step (s' <|pc := pc'|> <|accu := ptr|>)
```

**Operand mapping**:
- C: `tag = *pc++` (read from bytecode)
- Rocq: `t` (constructor argument, pre-decoded)

**State transition comparison**:

| Aspect | C | Rocq |
|--------|---|------|
| Allocate block | `Alloc_small(block, 1, tag)` | `heap_alloc s t [accu]` |
| Set field 0 | `Field(block, 0) = accu` | included in `heap_alloc` call |
| Set accu | `accu = block` (pointer to new block) | `accu := ptr` (Val_ptr to new heap entry) |
| Advance pc | implicit (`Next`) | `pc := pc'` |
| Stack | unchanged | unchanged |
| Heap | new block in GC heap | new entry in PositiveMap |

**Abstraction concerns**:
- `Alloc_small` may trigger GC. After GC, all values in registers/stack may have been relocated. The abstraction relation must hold after GC (GC preserves the reachability-based equivalence).
- `Alloc_small` expands to a macro that calls `Setup_for_gc` / `Restore_after_gc` if minor heap is full.

**Verdict**: **Abstracted**. The pure state transition is equivalent: both create a 1-field block with the given tag containing `accu`, and set `accu` to point to it. The C version may trigger GC (which is transparent to the abstraction).

**Proof sketch**:
```coq
Lemma MAKEBLOCK1_correct : forall t s c_s,
  abs_rel c_s s ->
  let '(s', ptr) := heap_alloc s t [s.(accu)] in
  exists c_s',
    c_step_MAKEBLOCK1 t c_s = c_s' /\
    abs_rel c_s' (s' <|pc := s.(pc)+1|> <|accu := ptr|>).
Proof.
  (* Key steps:
     1. Show c_alloc produces a new block b with Tag(b)=t, Wosize(b)=1, Field(b,0)=c_accu
     2. Show heap_alloc produces (s', Val_ptr addr) with hp[addr]=(t, [accu])
     3. Show abs_rel is preserved: the new c_s' maps to the new Rocq state
     4. GC case: Alloc_small may trigger GC, but abs_rel is GC-stable *)
Admitted.
```

---

## 8. Divergences Requiring Investigation

### 8.1 CLOSUREREC: Infix Header Representation

**C**: Infix headers are stored as raw `Make_header(i*3, Infix_tag, Caml_white)` -- a word-level header value that the GC understands.

**Rocq**: Infix headers are stored as `Val_block Infix_tag []` -- a zero-field block.

**Impact**: Low. The infix header is only used for GC scanning and OFFSETCLOSURE navigation. In the Rocq model, closures are tracked via `Val_closure addr ofs` which carries the base address and field offset directly, so the header's exact bit pattern is irrelevant.

**Resolution**: Document as an abstraction decision. The `Val_block Infix_tag []` placeholder is never accessed by field operations in correct programs.

### 8.2 OFFSETCLOSURE: Pointer Arithmetic vs Tracking

**C**: `accu = env + ofs * sizeof(value)` -- produces an interior pointer into the existing closure block.

**Rocq**: Constructs `Val_closure addr new_ofs` where `new_ofs = base_ofs + ofs`.

**Impact**: Medium. The Rocq representation is strictly more structured. When `Val_closure addr ofs` is later used (e.g., `Code_val(accu)` in APPLY), the Rocq code looks up `heap[addr]` and reads `fields[ofs]`. The C code dereferences `((value*)accu)[0]` which is `Field(env+offset, 0)`.

**Resolution**: The abstraction relation must map `Val_closure addr ofs` to `env_base_ptr + ofs * sizeof(value)`, and prove that field access through this tracked representation gives the same result as C's pointer arithmetic. This is a key lemma.

### 8.3 ATOM: Static vs Dynamic Allocation

**C**: `Atom(t)` returns `(value)((header_t*)caml_atom_table + t + 1)` -- a pointer to a preallocated, zero-size block in a static table.

**Rocq**: `heap_alloc s t []` allocates a fresh heap entry every time.

**Impact**: Medium. If the program compares atoms with physical equality (EQ/NEQ), C would say two `Atom(0)` values are equal (same pointer), while Rocq would say they are different (`Val_ptr addr1 != Val_ptr addr2`).

**Resolution**: Two options:
1. **Add atom table to Rocq state**: Pre-allocate atoms 0..255 in the initial state and return existing entries for ATOM instructions.
2. **Prove atoms are not physically compared**: In well-typed OCaml programs, atoms (zero-size blocks) are compared structurally, not physically. The EQ instruction is only used when the compiler knows physical equality is safe (integers) or when the user explicitly uses `(==)`.

Option 1 is cleaner for verification. Option 2 relies on a well-typedness assumption.

### 8.4 Float Representation

**C**: Float arrays use `Double_array_tag` (tag 254) with `Double_wosize` words per float (2 on 32-bit, 1 on 64-bit). `MAKEFLOATBLOCK` stores raw float bits. `GETFLOATFIELD` reads float bits and boxes them (allocates a `Double_tag` block). `VECTLENGTH` divides by `Double_wosize` for float arrays.

**Rocq**: Treats float arrays like regular arrays. `MAKEFLOATBLOCK` allocates with tag 254 but stores values directly. `GETFLOATFIELD` just reads a field (no boxing). `VECTLENGTH` returns `length fields` directly.

**Impact**: High for programs that use floats. The Rocq model does not distinguish boxed from unboxed float representation.

**Resolution**: For correctness of non-float programs, this divergence is irrelevant. For float programs, either:
1. **Extend Value.v** with a `Val_float : float -> value` constructor and model boxing/unboxing explicitly.
2. **Treat floats as out-of-scope** for the current verification and document it as a known limitation.

Recommend option 2 for now, with option 1 as future work.

### 8.5 String/Bytes Representation

**C**: Strings are flat byte arrays stored in the block's data area. `Byte_u(v, i)` reads the i-th byte directly from memory. A string block's `Wosize_val` gives the number of *words*, not characters.

**Rocq**: Strings are modeled as `Val_block String_tag [Val_int c0; Val_int c1; ...]` where each character is a separate `Val_int` field.

**Impact**: Medium. The Rocq model uses O(n) memory per character instead of O(n/8). String operations work correctly at the logical level, but:
- `VECTLENGTH` on strings would give different results (character count vs word count)
- The byte layout within words is not modeled

**Resolution**: This is an intentional abstraction. String operations (`GETSTRINGCHAR`, `GETBYTESCHAR`, `SETBYTESCHAR`) operate on individual characters, which works correctly with the per-character model. The `VECTLENGTH` instruction is not used on strings by well-compiled OCaml code (string length is obtained via a C call to `caml_ml_string_length`).

### 8.6 EQ/NEQ: Physical Equality Semantics

**C**: `(intnat)accu == (intnat)*sp` -- raw bit comparison of tagged values. Two heap pointers are equal iff they point to the same address. Two integers are equal iff they have the same tagged representation.

**Rocq**: `value_phys_eqb` dispatches on value type:
- `Val_int/Val_int`: Z equality (correct)
- `Val_ptr/Val_ptr`: address equality (correct)
- `Val_closure/Val_closure`: address + offset equality (correct)
- `Val_block/Val_block`: always false (conservative)

**Impact**: The `Val_block/Val_block => false` case is the key issue. In C, if two values are the same pointer, EQ returns true regardless of type. But the Rocq model uses `Val_block` for inline (non-heap-allocated) blocks. Two different `Val_block` values represent different allocations, so returning `false` is correct: they cannot be the same C pointer. If they were the same object, they would share a `Val_ptr`.

**Resolution**: The current behavior is correct given the invariant that `Val_block` values represent distinct, non-aliased objects. This invariant should be formally stated and verified.

### 8.7 GETPUBMET/GETDYNMET: Binary Search vs Linear Scan

**C**: Uses binary search on the sorted method table (and a cache for GETPUBMET).

**Rocq**: Uses linear scan on pairs `(closure, tag)`.

**Impact**: Functional equivalence -- both find the same method (assuming the table is correctly sorted). Performance differs (O(log n) vs O(n)).

**Resolution**: Prove that for a correctly-formatted method table (sorted by tag), binary search and linear scan return the same result. This is a standard algorithms lemma. The cache in GETPUBMET is a pure optimization that does not affect semantics.

---

## 9. Automation Opportunities

### 9.1 Auto-Generate Comparison Table

**Feasibility**: High.

Write a script that:
1. Parses `instruct.h` to extract the opcode enum.
2. Parses `interp.c` to extract each `Instruct(X): { ... }; Next;` block.
3. Parses `AST.v` to extract the instruction inductive constructors.
4. Parses `Interpret.v` to extract each `| X => ...` case.
5. Matches by name and generates a Markdown comparison table.

```python
# Pseudocode for the matching script
c_handlers = parse_interp_c("interp.c")       # dict: opcode_name -> C_code_block
rocq_cases = parse_interpret_v("Interpret.v")  # dict: constructor_name -> Rocq_code_block
opcodes = parse_instruct_h("instruct.h")       # list of opcode names

# Folding map: C specialized -> Rocq generalized
folding = {
    "ACC0": "ACC", "ACC1": "ACC", ..., "ACC7": "ACC",
    "CONST0": "CONSTINT", ...,
    # etc.
}

for opcode in opcodes:
    rocq_name = folding.get(opcode, opcode)
    c_code = c_handlers.get(opcode)
    r_code = rocq_cases.get(rocq_name)
    emit_comparison(opcode, rocq_name, c_code, r_code)
```

### 9.2 Auto-Extract Handler Functions from interp.c

**Feasibility**: Medium.

The main challenges are:
- Macro expansion (need to preprocess first)
- Fallthrough handlers (PUSHACC falls into ACC)
- Shared goto labels (raise_notrace, check_stacks)
- GC save/restore macros that push/pop the C stack

Approach:
1. Preprocess with `gcc -E` to expand macros
2. Use a C parser (libclang, pycparser) to find case labels
3. Extract the AST subtree for each case
4. Wrap in a standalone function with explicit state parameter
5. Inline goto targets (check_stacks becomes a function call)

### 9.3 Auto-Generate VST Proof Stubs

**Feasibility**: Medium-High.

Given the Clight AST for each handler and the Rocq handler function, generate:

```coq
Lemma handle_INSTR_correct : forall <operands> s c_s,
  abs_rel c_s s ->
  <preconditions> ->
  exists c_s',
    clight_step handle_INSTR_clight c_s <operands> = Some c_s' /\
    abs_rel c_s' (proj_step (handle_INSTR <operands> s pc')).
Proof.
  intros. unfold handle_INSTR, handle_INSTR_clight.
  (* Auto-generated forward reasoning *)
  repeat (forward; auto).
  (* Manual: establish abs_rel for updated fields *)
  admit.
Qed.
```

The `forward` tactic can often handle simple handlers automatically. Complex handlers (CLOSUREREC, GRAB) will need manual proof steps.

### 9.4 Auto-Generate Rocq Handler Functions from Interpret.v

**Feasibility**: High.

Write a script that parses `Interpret.v` and mechanically extracts each case into a standalone definition:

```
Input:  | ACC n => match nth_error s.(stack) n with ...
Output: Definition handle_ACC (n : nat) (s : state) (pc' : Z) : step_result :=
          match nth_error s.(stack) n with ...
```

This is a syntactic transformation. The dispatch `step` function is then the match with each case calling the corresponding handler.

### 9.5 Differential Testing as Pre-Verification

Before formal verification, strengthen confidence with targeted differential testing:

```ocaml
(* For each instruction, generate random states, run both C and Rocq interpreters
   for one step, and compare results *)
let test_instruction instr =
  let state = random_state () in
  let c_result = c_step instr state in     (* via FFI to real interp.c *)
  let r_result = rocq_step instr state in  (* via extracted Rocq *)
  assert (equiv c_result r_result)
```

This is essentially what the existing PBT harness does at the program level, but instruction-level testing provides finer-grained coverage.

---

## 10. Execution Roadmap

### Phase 1: Foundation (Weeks 1-2)

1. **Auto-generate detailed comparison table** (Section 9.1)
   - Script to parse both files and produce machine-readable mapping
   - Human review to classify each pair as Identical/Abstracted/Divergent

2. **Restructure Interpret.v** (Section 5)
   - Create `Handlers.v` with individual handler functions
   - Redefine `step` as dispatch
   - Prove equivalence with old `step`

3. **Formalize abstraction relation** (Section 3)
   - Define `abs_rel` in a new `AbstractionRel.v`
   - Prove basic lemmas: stack correspondence, value correspondence

### Phase 2: Easy Handlers (Weeks 3-5)

Verify the "Identical" category handlers, starting with the simplest:

**Batch 1** (trivial state updates):
- ACC, PUSH, PUSHACC, POP, ASSIGN
- CONSTINT, PUSHCONSTINT
- BRANCH, BRANCHIF, BRANCHIFNOT
- BOOLNOT, ISINT
- STOP

**Batch 2** (arithmetic):
- NEGINT, ADDINT, SUBINT, MULINT, DIVINT, MODINT
- ANDINT, ORINT, XORINT, LSLINT, LSRINT, ASRINT
- LTINT, LEINT, GTINT, GEINT, ULTINT, UGEINT
- OFFSETINT, OFFSETREF
- BEQ, BNEQ, BLTINT, BLEINT, BGTINT, BGEINT, BULTINT, BUGEINT

**Batch 3** (environment and globals):
- ENVACC, PUSHENVACC
- GETGLOBAL, PUSHGETGLOBAL, GETGLOBALFIELD, PUSHGETGLOBALFIELD, SETGLOBAL
- GETFIELD, SETFIELD
- GETVECTITEM, SETVECTITEM

### Phase 3: Medium Handlers (Weeks 6-8)

Verify the "Abstracted" category (need GC abstraction lemma):

**Batch 4** (function calls):
- PUSH_RETADDR, APPLY, APPLY1, APPLY2, APPLY3
- APPTERM, APPTERM1, APPTERM2, APPTERM3
- RETURN, RESTART, GRAB

**Batch 5** (allocation):
- MAKEBLOCK, MAKEBLOCK1, MAKEBLOCK2, MAKEBLOCK3
- CLOSURE, CLOSUREREC

**Batch 6** (exceptions):
- PUSHTRAP, POPTRAP, RAISE, RERAISE, RAISE_NOTRACE

**Batch 7** (C calls):
- C_CALL, CHECK_SIGNALS

### Phase 4: Hard Handlers (Weeks 9-12)

Address the "Divergent" category:

1. **ATOM/PUSHATOM**: Decide on atom table approach (Section 8.3), implement, verify
2. **OFFSETCLOSURE/PUSHOFFSETCLOSURE**: Prove pointer arithmetic equivalence (Section 8.2)
3. **EQ/NEQ**: Formalize Val_block non-aliasing invariant (Section 8.6)
4. **GETPUBMET/GETDYNMET**: Prove binary search = linear scan on sorted tables (Section 8.7)
5. **Float operations**: Document as out-of-scope or extend Value.v (Section 8.4)
6. **String/Bytes operations**: Document abstraction decision (Section 8.5)
7. **SWITCH**: Verify pre-decoded target lists match C's packed-sizes dispatch

### Phase 5: Integration (Weeks 13-14)

1. **Compose handler correctness into step correctness**:
   ```coq
   Theorem step_correct : forall code s c_s,
     abs_rel c_s s ->
     exists c_s', c_step c_s = c_s' /\
       abs_rel_result c_s' (step code s).
   ```

2. **Lift to multi-step correctness** (run loop):
   ```coq
   Theorem run_correct : forall fuel code s c_s,
     abs_rel c_s s ->
     abs_rel_run_result (c_run fuel c_s) (run fuel code s handle_ccall).
   ```

3. **Connect to existing PBT** to validate the formal results empirically

### Phase 6: C-to-Clight Pipeline (Optional, Weeks 15+)

If full machine-checked verification against the actual C code is desired:

1. Extract handler functions from interp.c (Section 6.2)
2. Run clightgen on each (Section 6.3)
3. Write VST specifications (Section 6.4)
4. Prove each handler in VST

This phase is significantly more work and may not be necessary if the shallow embedding approach (Section 6.5) provides sufficient confidence.

---

## Appendix A: File Locations

| File | Absolute Path |
|------|---------------|
| interp.c | `/workspaces/theorem-work/theorem-ocaml/system-ocaml-compiler/runtime/interp.c` |
| instruct.h | `/workspaces/theorem-work/theorem-ocaml/system-ocaml-compiler/runtime/caml/instruct.h` |
| Interpret.v | `/workspaces/theorem-work/theorem-ocaml/verified-ocaml/manual/theories/Bytecode/Interpret.v` |
| AST.v | `/workspaces/theorem-work/theorem-ocaml/verified-ocaml/manual/theories/Bytecode/AST.v` |
| Machine.v | `/workspaces/theorem-work/theorem-ocaml/verified-ocaml/manual/theories/Bytecode/Machine.v` |
| Value.v | `/workspaces/theorem-work/theorem-ocaml/verified-ocaml/manual/theories/Utils/Value.v` |

## Appendix B: C Macros Reference

| Macro | Definition | Used In |
|-------|-----------|---------|
| `Val_int(n)` | `(2*(n)+1)` | Constants, comparisons |
| `Long_val(v)` | `((v) >> 1)` | Reading integer operands from stack |
| `Val_long(n)` | `Val_int(n)` (on 64-bit) | Storing integers |
| `Field(v, i)` | `((value*)(v))[i]` | Block field access |
| `Code_val(v)` | `((code_t)(Field(v, 0)))` | Getting code pointer from closure |
| `Closinfo_val(v)` | `Field(v, 1)` | Closure info word |
| `Tag_val(v)` | `(((header_t*)(v))[-1] & 0xFF)` | Block tag |
| `Wosize_val(v)` | `(((header_t*)(v))[-1] >> 10)` | Block size in words |
| `Is_block(v)` | `((v & 1) == 0)` | Block vs integer test |
| `Alloc_small(r, sz, tg)` | Minor heap allocation with GC trigger | MAKEBLOCK, CLOSURE, etc. |
| `Atom(t)` | `((value)(&caml_atom_table[t]))` | Zero-size block access |
| `Trap_pc(sp)` | `((code_t)(sp[0]))` | Exception handler PC |
| `Trap_link_offset(sp)` | `(sp[1])` | Trap link (relative offset) |
| `Setup_for_gc` | Push accu, env, pc to stack; sync sp | Before allocation |
| `Restore_after_gc` | Restore accu, env from stack; sync sp | After allocation |
| `Setup_for_c_call` | Push env, pc+1 to stack; sync sp | Before C primitive call |
| `Restore_after_c_call` | Restore env from stack; sync sp | After C primitive call |

## Appendix C: CLOSUREREC Block Layout

C layout for `CLOSUREREC nfuncs=3, nvars=2`:

```
Offset  Content                     Rocq Equivalent
------  -------                     ---------------
0       code_ptr_0                  Val_int code_ofs_0
1       Make_closinfo(0, 8)         Val_int 0
2       Make_header(3,Infix,White)  Val_block Infix_tag []
3       code_ptr_1                  Val_int code_ofs_1
4       Make_closinfo(0, 5)         Val_int 0
5       Make_header(6,Infix,White)  Val_block Infix_tag []
6       code_ptr_2                  Val_int code_ofs_2
7       Make_closinfo(0, 2)         Val_int 0
8       env_var_0                   <value>
9       env_var_1                   <value>
```

Total block size = `nfuncs * 3 - 1 + nvars` = `3*3 - 1 + 2` = `10`.

Closures returned:
- `closure_0 = Val_closure(addr, 0)` -- points to field 0
- `closure_1 = Val_closure(addr, 3)` -- points to field 3
- `closure_2 = Val_closure(addr, 6)` -- points to field 6
