(* InstructSpec.v — Specification relating Clight instruction handlers
   (from clightgen) to Rocq handle_X functions (from Interpret.v).

   Architecture:
   - instruct_handlers.v provides the Clight AST (f_instr_X definitions)
   - Interpret.v provides the Rocq handlers (handle_X definitions)
   - This file defines abs_rel (C state <-> Rocq state) and declares
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

Definition clight_ge : Clight.genv :=
  {| genv_genv := Globalenvs.Genv.globalenv prog;
     genv_cenv := prog_comp_env prog |}.

Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* The struct type for interp_state.  Using a named struct tag in the C
   source makes clightgen produce the stable identifier _interp_state. *)
Definition t_interp_state := Tstruct _interp_state noattr.

(* sizeof(code_t) = 4 bytes (int32_t in the C source) *)
Definition sizeof_code_t : Z := 4.

(* ================================================================== *)
(* Value representation                                                *)
(* ================================================================== *)

Definition val_int_repr (z : Z) : val :=
  Vlong (Int64.repr (z * 2 + 1)).

(* ================================================================== *)
(* Abstraction relation                                                *)
(* ================================================================== *)

Record abs_rel_data := mk_abs_rel {
  ar_sptr_block : block;
  ar_sptr_ofs   : ptrofs;
  ar_heap_map   : nat -> option (block * ptrofs);
  (* Code base pointer: C pc = code_base + rocq_pc * sizeof_code_t *)
  ar_code_base_block : block;
  ar_code_base_ofs   : ptrofs;
  (* Global data array base *)
  ar_global_block : block;
  ar_global_ofs   : ptrofs;
  (* Stack base (bottom) for trap_sp computation *)
  ar_stack_block    : block;
  ar_stack_base_ofs : ptrofs;
}.

(* val_repr: a Rocq value corresponds to a CompCert value *)
Inductive val_repr (hm : nat -> option (block * ptrofs))
    : Value.value -> val -> Prop :=
  | vr_int : forall z,
      val_repr hm (Val_int z) (Vlong (Int64.repr (z * 2 + 1)))
  | vr_ptr : forall addr b ofs,
      hm addr = Some (b, ofs) ->
      val_repr hm (Val_ptr addr) (Vptr b ofs)
  | vr_closure : forall addr offset b ofs delta,
      hm addr = Some (b, ofs) ->
      delta = Ptrofs.repr (Z.of_nat offset * 8) ->
      val_repr hm (Val_closure addr offset) (Vptr b (Ptrofs.add ofs delta))
  | vr_block_atom : forall tag,
      val_repr hm (Val_block tag nil)
        (Vlong (Int64.repr (Z.of_nat tag * 1024))).

(* stack_repr: Rocq stack (list value) corresponds to a C stack region *)
Inductive stack_repr (hm : nat -> option (block * ptrofs)) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | sr_nil : forall b ofs,
      stack_repr hm m nil b ofs
  | sr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm v cv ->
      stack_repr hm m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      stack_repr hm m (v :: vs) b ofs.

(* global_repr: Rocq global array corresponds to C memory region *)
Inductive global_repr (hm : nat -> option (block * ptrofs)) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | gr_nil : forall b ofs,
      global_repr hm m nil b ofs
  | gr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm v cv ->
      global_repr hm m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      global_repr hm m (v :: vs) b ofs.

(* pc_rel: C pc pointer encodes Rocq program counter *)
Definition pc_rel (pc_ptr : val)
    (code_base_b : block) (code_base_ofs : ptrofs) (rocq_pc : Z) : Prop :=
  pc_ptr = Vptr code_base_b
    (Ptrofs.add code_base_ofs (Ptrofs.repr (rocq_pc * sizeof_code_t))).

(* trap_sp_rel: C trap_sp pointer corresponds to Rocq trap_sp *)
Definition trap_sp_rel (ts_ptr : val)
    (sp_b : block) (sp_base_ofs : ptrofs) (rocq_trap_sp : nat) : Prop :=
  match rocq_trap_sp with
  | O => True
  | S _ =>
      ts_ptr = Vptr sp_b
        (Ptrofs.sub sp_base_ofs (Ptrofs.repr (Z.of_nat rocq_trap_sp * 8)))
  end.

(* abs_rel: the inter-instruction invariant (postcondition).
   C pc = code_base + s.(pc) * sizeof(code_t). *)
Definition abs_rel (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) : Prop :=
  exists (ard : abs_rel_data),
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let go := ar_global_ofs ard in
  let stk_b := ar_stack_block ard in
  let stk_base := ar_stack_base_ofs ard in

  le ! _s = Some (Vptr sb so) /\

  (exists pc_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr /\
    pc_rel pc_ptr cb co s.(pc)) /\

  (exists accu_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v /\
    val_repr hm s.(accu) accu_v) /\

  (exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm m s.(stack) sp_b sp_ofs) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm m s.(global) gb go) /\

  (exists ts_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr /\
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)).

(* abs_rel_pre: the handler precondition.
   The dispatch loop has advanced C pc past the opcode, so
   C pc = code_base + (s.(pc) + 1) * sizeof(code_t).
   All other fields are identical to abs_rel. *)
Definition abs_rel_pre (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) : Prop :=
  exists (ard : abs_rel_data),
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let go := ar_global_ofs ard in
  let stk_b := ar_stack_block ard in
  let stk_base := ar_stack_base_ofs ard in

  le ! _s = Some (Vptr sb so) /\

  (* pc: dispatch loop consumed opcode, so pc is one slot ahead *)
  (exists pc_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr /\
    pc_rel pc_ptr cb co (s.(pc) + 1)) /\

  (exists accu_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v /\
    val_repr hm s.(accu) accu_v) /\

  (exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm m s.(stack) sp_b sp_ofs) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm m s.(global) gb go) /\

  (exists ts_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr /\
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)).

(* ================================================================== *)
(* Module Type: per-instruction correctness obligations                *)
(* ================================================================== *)

Module Type InstructSpec.

  (* --- Stack (ACC family) --- *)

  Axiom verify_ACC0 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC0.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC1 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC1.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 1 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC2 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC2.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 2 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC3 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC3.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 3 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC4 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC4.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 4 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC5 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC5.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 5 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC6 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC6.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 6 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC7 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC7.(fn_body) E0 le' m' out ->
    exists s', handle_ACC 7 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ACC : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ACC.(fn_body) E0 le' m' out ->
    exists s', handle_ACC n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Stack (PUSH / PUSHACC family) --- *)

  Axiom verify_PUSH : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSH.(fn_body) E0 le' m' out ->
    exists s', handle_PUSH (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC1 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC1.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 1 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC2 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC2.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 2 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC3 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC3.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 3 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC4 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC4.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 4 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC5 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC5.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 5 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC6 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC6.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 6 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHACC7 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHACC7.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHACC 7 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_POP : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_POP.(fn_body) E0 le' m' out ->
    exists s', handle_POP n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ASSIGN : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ASSIGN.(fn_body) E0 le' m' out ->
    exists s', handle_ASSIGN n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Constants --- *)

  Axiom verify_CONST0 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_CONST0.(fn_body) E0 le' m' out ->
    exists s', handle_CONSTINT 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_CONST1 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_CONST1.(fn_body) E0 le' m' out ->
    exists s', handle_CONSTINT 1 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_CONST2 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_CONST2.(fn_body) E0 le' m' out ->
    exists s', handle_CONSTINT 2 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_CONST3 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_CONST3.(fn_body) E0 le' m' out ->
    exists s', handle_CONSTINT 3 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_CONSTINT : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_CONSTINT.(fn_body) E0 le' m' out ->
    exists s', handle_CONSTINT n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHCONST0 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHCONST0.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHCONSTINT 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHCONST1 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHCONST1.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHCONSTINT 1 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHCONST2 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHCONST2.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHCONSTINT 2 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHCONST3 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHCONST3.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHCONSTINT 3 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHCONSTINT : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHCONSTINT.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHCONSTINT n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Arithmetic (binary) --- *)

  Axiom verify_ADDINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ADDINT.(fn_body) E0 le' m' out ->
    exists s', handle_ADDINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SUBINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SUBINT.(fn_body) E0 le' m' out ->
    exists s', handle_SUBINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MULINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_MULINT.(fn_body) E0 le' m' out ->
    exists s', handle_MULINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_DIVINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_DIVINT.(fn_body) E0 le' m' out ->
    exists s', handle_DIVINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MODINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_MODINT.(fn_body) E0 le' m' out ->
    exists s', handle_MODINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ANDINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ANDINT.(fn_body) E0 le' m' out ->
    exists s', handle_ANDINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ORINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ORINT.(fn_body) E0 le' m' out ->
    exists s', handle_ORINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_XORINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_XORINT.(fn_body) E0 le' m' out ->
    exists s', handle_XORINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_LSLINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_LSLINT.(fn_body) E0 le' m' out ->
    exists s', handle_LSLINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_LSRINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_LSRINT.(fn_body) E0 le' m' out ->
    exists s', handle_LSRINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ASRINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ASRINT.(fn_body) E0 le' m' out ->
    exists s', handle_ASRINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Arithmetic (unary) --- *)

  Axiom verify_NEGINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_NEGINT.(fn_body) E0 le' m' out ->
    exists s', handle_NEGINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Comparisons --- *)

  Axiom verify_EQ : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_EQ.(fn_body) E0 le' m' out ->
    exists s', handle_EQ (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_NEQ : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_NEQ.(fn_body) E0 le' m' out ->
    exists s', handle_NEQ (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_LTINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_LTINT.(fn_body) E0 le' m' out ->
    exists s', handle_LTINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_LEINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_LEINT.(fn_body) E0 le' m' out ->
    exists s', handle_LEINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GTINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GTINT.(fn_body) E0 le' m' out ->
    exists s', handle_GTINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GEINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GEINT.(fn_body) E0 le' m' out ->
    exists s', handle_GEINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ULTINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ULTINT.(fn_body) E0 le' m' out ->
    exists s', handle_ULTINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_UGEINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_UGEINT.(fn_body) E0 le' m' out ->
    exists s', handle_UGEINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Boolean / misc --- *)

  Axiom verify_BOOLNOT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_BOOLNOT.(fn_body) E0 le' m' out ->
    exists s', handle_BOOLNOT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_ISINT : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ISINT.(fn_body) E0 le' m' out ->
    exists s', handle_ISINT (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_OFFSETINT : forall e le m le' m' out s ofs,
    abs_rel_pre e le m s ->
    exec e le m f_instr_OFFSETINT.(fn_body) E0 le' m' out ->
    exists s', handle_OFFSETINT ofs (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_OFFSETREF : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_OFFSETREF.(fn_body) E0 le' m' out ->
    exists s', handle_OFFSETREF n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Branches --- *)

  Axiom verify_BRANCH : forall e le m le' m' out s target,
    abs_rel_pre e le m s ->
    exec e le m f_instr_BRANCH.(fn_body) E0 le' m' out ->
    exists s', handle_BRANCH target s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_BRANCHIF : forall e le m le' m' out s target,
    abs_rel_pre e le m s ->
    exec e le m f_instr_BRANCHIF.(fn_body) E0 le' m' out ->
    exists s', handle_BRANCHIF target (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_BRANCHIFNOT : forall e le m le' m' out s target,
    abs_rel_pre e le m s ->
    exec e le m f_instr_BRANCHIFNOT.(fn_body) E0 le' m' out ->
    exists s', handle_BRANCHIFNOT target (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Blocks --- *)

  Axiom verify_ATOM : forall e le m le' m' out s t,
    abs_rel_pre e le m s ->
    exec e le m f_instr_ATOM.(fn_body) E0 le' m' out ->
    exists s', handle_ATOM t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHATOM : forall e le m le' m' out s t,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHATOM.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHATOM t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MAKEBLOCK1 : forall e le m le' m' out s t,
    abs_rel_pre e le m s ->
    exec e le m f_instr_MAKEBLOCK1.(fn_body) E0 le' m' out ->
    exists s', handle_MAKEBLOCK1 t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MAKEBLOCK2 : forall e le m le' m' out s t,
    abs_rel_pre e le m s ->
    exec e le m f_instr_MAKEBLOCK2.(fn_body) E0 le' m' out ->
    exists s', handle_MAKEBLOCK2 t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_MAKEBLOCK3 : forall e le m le' m' out s t,
    abs_rel_pre e le m s ->
    exec e le m f_instr_MAKEBLOCK3.(fn_body) E0 le' m' out ->
    exists s', handle_MAKEBLOCK3 t (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Fields --- *)

  Axiom verify_GETFIELD0 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETFIELD0.(fn_body) E0 le' m' out ->
    exists s', handle_GETFIELD 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GETFIELD1 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETFIELD1.(fn_body) E0 le' m' out ->
    exists s', handle_GETFIELD 1 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GETFIELD2 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETFIELD2.(fn_body) E0 le' m' out ->
    exists s', handle_GETFIELD 2 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GETFIELD3 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETFIELD3.(fn_body) E0 le' m' out ->
    exists s', handle_GETFIELD 3 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GETFIELD : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETFIELD.(fn_body) E0 le' m' out ->
    exists s', handle_GETFIELD n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETFIELD0 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETFIELD0.(fn_body) E0 le' m' out ->
    exists s', handle_SETFIELD 0 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETFIELD1 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETFIELD1.(fn_body) E0 le' m' out ->
    exists s', handle_SETFIELD 1 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETFIELD2 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETFIELD2.(fn_body) E0 le' m' out ->
    exists s', handle_SETFIELD 2 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETFIELD3 : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETFIELD3.(fn_body) E0 le' m' out ->
    exists s', handle_SETFIELD 3 (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETFIELD : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETFIELD.(fn_body) E0 le' m' out ->
    exists s', handle_SETFIELD n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Globals --- *)

  Axiom verify_GETGLOBAL : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETGLOBAL.(fn_body) E0 le' m' out ->
    exists s', handle_GETGLOBAL n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_PUSHGETGLOBAL : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_PUSHGETGLOBAL.(fn_body) E0 le' m' out ->
    exists s', handle_PUSHGETGLOBAL n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETGLOBAL : forall e le m le' m' out s n,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETGLOBAL.(fn_body) E0 le' m' out ->
    exists s', handle_SETGLOBAL n (s.(pc) + 2) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Vectors --- *)

  Axiom verify_VECTLENGTH : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_VECTLENGTH.(fn_body) E0 le' m' out ->
    exists s', handle_VECTLENGTH (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_GETVECTITEM : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_GETVECTITEM.(fn_body) E0 le' m' out ->
    exists s', handle_GETVECTITEM (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  Axiom verify_SETVECTITEM : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_SETVECTITEM.(fn_body) E0 le' m' out ->
    exists s', handle_SETVECTITEM (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Misc --- *)

  Axiom verify_CHECK_SIGNALS : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_CHECK_SIGNALS.(fn_body) E0 le' m' out ->
    exists s', handle_CHECK_SIGNALS (s.(pc) + 1) s = Step s' /\
               abs_rel e le' m' s'.

  (* --- Halt --- *)

  Axiom verify_STOP : forall e le m le' m' out s,
    abs_rel_pre e le m s ->
    exec e le m f_instr_STOP.(fn_body) E0 le' m' out ->
    handle_STOP s = Halt s.(accu).

End InstructSpec.
