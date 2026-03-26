(* InstructSpec.v — Specification relating Clight instruction handlers
   (from clightgen) to Rocq handle_X functions (from Interpret.v).

   Architecture:
   - instruct_handlers.v provides the Clight AST (f_instr_X definitions)
   - Interpret.v provides the Rocq handlers (handle_X definitions)
   - This file defines abs_rel (C state ↔ Rocq state) and declares
     per-handler correctness theorems as a Module Type.
   - A future Module : InstructSpec fills each theorem with a proof. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.

(* ================================================================== *)
(* Clight environment                                                  *)
(* ================================================================== *)

(* The global environment for the Clight program *)
Definition clight_ge : Clight.genv :=
  {| genv_genv := Globalenvs.Genv.globalenv prog;
     genv_cenv := prog_comp_env prog |}.

(* Shorthand *)
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* The struct type for interp_state (named __190 by clightgen) *)
Definition t_interp_state := Tstruct __190 noattr.

(* ================================================================== *)
(* Value representation                                                *)
(* ================================================================== *)

(* How a Rocq Value.value maps to a CompCert 64-bit word.
   OCaml runtime encoding:
   - Val_int z  → tagged integer: (z << 1) | 1
   - Val_ptr a  → pointer to heap block (even address)
   - Val_closure a ofs → pointer into closure block
   - Val_block  → should not appear at runtime (always heap-allocated) *)

Definition val_int_repr (z : Z) : val :=
  Vlong (Int64.repr (z * 2 + 1)).

(* For heap values, we parameterize over a heap representation since
   the mapping from Rocq heap addresses to C pointers depends on the
   concrete heap layout in memory. *)

(* ================================================================== *)
(* Abstraction relation                                                *)
(* ================================================================== *)

(* The abstraction relation connects a C memory state to a Rocq state.
   It asserts that:
   1. The temp_env contains a pointer _s to an interp_state struct
   2. Each struct field in memory corresponds to the Rocq state field
   3. Value fields satisfy the value representation *)

Record abs_rel_data := mk_abs_rel {
  (* The C pointer to the interp_state struct *)
  ar_sptr_block : block;
  ar_sptr_ofs   : ptrofs;

  (* Heap abstraction: maps Rocq heap addresses to C block pointers.
     This is defined per-proof since the heap layout is proof-specific. *)
  ar_heap_map : nat -> option (block * ptrofs);
}.

(* val_repr: a Rocq value corresponds to a CompCert value given a heap map *)
Inductive val_repr (hm : nat -> option (block * ptrofs)) : Value.value -> val -> Prop :=
  | vr_int : forall z,
      val_repr hm (Val_int z) (Vlong (Int64.repr (z * 2 + 1)))
  | vr_ptr : forall addr b ofs,
      hm addr = Some (b, ofs) ->
      val_repr hm (Val_ptr addr) (Vptr b ofs)
  | vr_closure : forall addr offset b ofs delta,
      hm addr = Some (b, ofs) ->
      delta = Ptrofs.repr (Z.of_nat offset * 8) ->
      val_repr hm (Val_closure addr offset) (Vptr b (Ptrofs.add ofs delta)).

(* stack_repr: the Rocq stack (list value) corresponds to a C stack
   region in memory starting at pointer (b, ofs), growing downward *)
Inductive stack_repr (hm : nat -> option (block * ptrofs)) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | sr_nil : forall b ofs,
      stack_repr hm m nil b ofs
  | sr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm v cv ->
      stack_repr hm m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      stack_repr hm m (v :: vs) b ofs.

(* The full abstraction relation *)
Definition abs_rel (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) : Prop :=
  exists (ard : abs_rel_data),
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in

  (* _s is a pointer in the temp env *)
  le ! _s = Some (Vptr sb so) /\

  (* pc field: s->pc points to code[s.(pc)] *)
  (exists pc_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr
    (* pc_ptr encodes s.(pc) — exact encoding is proof-specific *)) /\

  (* accu field: s->accu represents s.(accu) *)
  (exists accu_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v /\
    val_repr hm s.(accu) accu_v) /\

  (* sp field: s->sp points to the stack region *)
  (exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm m s.(stack) sp_b sp_ofs) /\

  (* env field: s->env represents s.(env) *)
  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm s.(Machine.env) env_v) /\

  (* extra_args field *)
  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (* global_data field *)
  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr) /\

  (* trap_sp field *)
  (exists ts_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr).

(* ================================================================== *)
(* Module Type: per-instruction correctness obligations                *)
(* ================================================================== *)

Module Type InstructSpec.

  (* --- Stack --- *)

  Axiom verify_ACC0 : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_ACC0.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_ACC.(fn_body) E0 le' m' out ->
    exists s', handle_ACC n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSH : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_PUSH.(fn_body) E0 le' m' out ->
    exists s', handle_PUSH (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_POP : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_POP.(fn_body) E0 le' m' out ->
    exists s', handle_POP n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ASSIGN : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_ASSIGN.(fn_body) E0 le' m' out ->
    exists s', handle_ASSIGN n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Constants --- *)

  Axiom verify_CONSTINT : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_CONSTINT.(fn_body) E0 le' m' out ->
    exists s', handle_CONSTINT n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHCONSTINT : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_PUSHCONSTINT.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHCONSTINT n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Arithmetic (handlers that use C directly, not macros) --- *)

  Axiom verify_DIVINT : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_DIVINT.(fn_body) E0 le' m' out ->
    exists s', handle_DIVINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MODINT : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_MODINT.(fn_body) E0 le' m' out ->
    exists s', handle_MODINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Boolean / misc --- *)

  Axiom verify_BOOLNOT : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_BOOLNOT.(fn_body) E0 le' m' out ->
    exists s', handle_BOOLNOT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ISINT : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_ISINT.(fn_body) E0 le' m' out ->
    exists s', handle_ISINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_OFFSETINT : forall e le m le' m' out s ofs,
    abs_rel e le m s ->
    exec e le m f_instr_OFFSETINT.(fn_body) E0 le' m' out ->
    exists s', handle_OFFSETINT ofs (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Branches --- *)

  Axiom verify_BRANCH : forall e le m le' m' out s target,
    abs_rel e le m s ->
    exec e le m f_instr_BRANCH.(fn_body) E0 le' m' out ->
    exists s', handle_BRANCH target s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_BRANCHIF : forall e le m le' m' out s target,
    abs_rel e le m s ->
    exec e le m f_instr_BRANCHIF.(fn_body) E0 le' m' out ->
    exists s', handle_BRANCHIF target (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_BRANCHIFNOT : forall e le m le' m' out s target,
    abs_rel e le m s ->
    exec e le m f_instr_BRANCHIFNOT.(fn_body) E0 le' m' out ->
    exists s', handle_BRANCHIFNOT target (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Blocks --- *)

  Axiom verify_MAKEBLOCK1 : forall e le m le' m' out s t,
    abs_rel e le m s ->
    exec e le m f_instr_MAKEBLOCK1.(fn_body) E0 le' m' out ->
    exists s', handle_MAKEBLOCK1 t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MAKEBLOCK2 : forall e le m le' m' out s t,
    abs_rel e le m s ->
    exec e le m f_instr_MAKEBLOCK2.(fn_body) E0 le' m' out ->
    exists s', handle_MAKEBLOCK2 t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MAKEBLOCK3 : forall e le m le' m' out s t,
    abs_rel e le m s ->
    exec e le m f_instr_MAKEBLOCK3.(fn_body) E0 le' m' out ->
    exists s', handle_MAKEBLOCK3 t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Fields --- *)

  Axiom verify_GETFIELD0 : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_GETFIELD0.(fn_body) E0 le' m' out ->
    exists s', handle_GETFIELD 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETFIELD : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_SETFIELD.(fn_body) E0 le' m' out ->
    exists s', handle_SETFIELD n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Globals --- *)

  Axiom verify_GETGLOBAL : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_GETGLOBAL.(fn_body) E0 le' m' out ->
    exists s', handle_GETGLOBAL n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETGLOBAL : forall e le m le' m' out s n,
    abs_rel e le m s ->
    exec e le m f_instr_SETGLOBAL.(fn_body) E0 le' m' out ->
    exists s', handle_SETGLOBAL n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Halt --- *)

  Axiom verify_STOP : forall e le m le' m' out s,
    abs_rel e le m s ->
    exec e le m f_instr_STOP.(fn_body) E0 le' m' out ->
    handle_STOP s = Halt s.(accu).

End InstructSpec.

(* ================================================================== *)
(* TODO: expand extract_handlers.sh to handle macro-expanded handlers  *)
(* (ADDINT, SUBINT, MULINT, NEGINT, ANDINT, ORINT, XORINT, LSLINT,   *)
(*  LSRINT, ASRINT, EQ, NEQ, LTINT, LEINT, GTINT, GEINT, GETFIELD)   *)
(* Then add corresponding Axioms to the Module Type above.             *)
(* ================================================================== *)
