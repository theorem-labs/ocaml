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
  (* Block separation: code block is distinct from struct, global blocks *)
  ar_code_ne_sptr   : ar_code_base_block <> ar_sptr_block;
  ar_code_ne_global : ar_code_base_block <> ar_global_block;
  (* Struct pointer offset representability *)
  ar_sptr_ofs_bound : Ptrofs.unsigned ar_sptr_ofs + 56 < Ptrofs.modulus;
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
    stack_repr hm m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm m s.(global) gb go /\
    gb <> sb) /\

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
    stack_repr hm m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm m s.(global) gb go /\
    gb <> sb) /\

  (exists ts_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr /\
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)).

(* ================================================================== *)
(* Uniform completeness statement                                      *)
(* ================================================================== *)

(* handler_correct: uniform correctness statement for instruction handlers.
   Takes a handler function and a Clight function, quantifies over all
   C environments and abstract machine states internally.
   The Step case is always the same: abs_rel on the pre-state implies the
   C body executes and abs_rel holds on the post-state.
   The Error / Halt / CCall_request cases are per-handler predicates. *)
Definition handler_correct
    (handler : Z -> state -> step_result)
    (f : function)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  forall e le m s,
    match handler s.(pc) s with
    | Step s' =>
        abs_rel e le m s ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m f.(fn_body) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => P_error msg s
    | Halt v => P_halt v
    | CCall_request nargs args s' => P_ccall nargs args s'
    end.

(* abs_rel_with_ard: exposes the abs_rel_data witness so that
   preconditions can refer to specific fields (code base, etc.). *)
Definition abs_rel_with_ard (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) (ard : abs_rel_data) : Prop :=
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
    stack_repr hm m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm m s.(global) gb go /\
    gb <> sb) /\

  (exists ts_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr /\
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)).

Lemma abs_rel_iff_with_ard : forall e le m s,
  abs_rel e le m s <-> exists ard, abs_rel_with_ard e le m s ard.
Proof.
  intros. unfold abs_rel, abs_rel_with_ard. reflexivity.
Qed.

(* handler_correct_with_pre: variant of handler_correct with an
   extra precondition on the Step case.  The precondition receives
   the abs_rel_data witness so it can refer to the concrete code
   base block, stack block, etc.

   Used for handlers that read operands from the code buffer
   (e.g. BRANCH reads the branch offset at *(s->pc)), or that
   require operand range constraints (e.g. LSLINT shift < 64).

   The Step case destructures abs_rel to get ard, then requires
   step_pre m s ard to hold for that specific ard. *)
Definition handler_correct_with_pre
    (handler : Z -> state -> step_result)
    (f : function)
    (step_pre : mem -> state -> abs_rel_data -> Prop)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  forall e le m s,
    match handler s.(pc) s with
    | Step s' =>
        forall ard,
        abs_rel_with_ard e le m s ard ->
        step_pre m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m f.(fn_body) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => P_error msg s
    | Halt v => P_halt v
    | CCall_request nargs args s' => P_ccall nargs args s'
    end.

(* handler_correct_with_pre_env: variant of handler_correct_with_pre
   where the precondition also receives the Clight environment e.
   Needed for handlers that reference global symbols (e.g. caml_modify)
   which require e ! symbol = None for eval_Evar_global. *)
Definition handler_correct_with_pre_env
    (handler : Z -> state -> step_result)
    (f : function)
    (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  forall e le m s,
    match handler s.(pc) s with
    | Step s' =>
        forall ard,
        abs_rel_with_ard e le m s ard ->
        step_pre e m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m f.(fn_body) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => P_error msg s
    | Halt v => P_halt v
    | CCall_request nargs args s' => P_ccall nargs args s'
    end.

(* ================================================================== *)
(* Module Type: per-instruction correctness obligations                *)
(* ================================================================== *)

Module Type InstructSpec.

  (* --- Stack (ACC family) --- *)

  Axiom verify_ACC0 :
    handler_correct (handle_ACC 0) f_instr_ACC0
      (fun _ s => s.(Machine.stack) = nil)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC1 :
    handler_correct (handle_ACC 1) f_instr_ACC1
      (fun _ s => nth_error s.(Machine.stack) 1 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC2 :
    handler_correct (handle_ACC 2) f_instr_ACC2
      (fun _ s => nth_error s.(Machine.stack) 2 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC3 :
    handler_correct (handle_ACC 3) f_instr_ACC3
      (fun _ s => nth_error s.(Machine.stack) 3 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC4 :
    handler_correct (handle_ACC 4) f_instr_ACC4
      (fun _ s => nth_error s.(Machine.stack) 4 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC5 :
    handler_correct (handle_ACC 5) f_instr_ACC5
      (fun _ s => nth_error s.(Machine.stack) 5 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC6 :
    handler_correct (handle_ACC 6) f_instr_ACC6
      (fun _ s => nth_error s.(Machine.stack) 6 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC7 :
    handler_correct (handle_ACC 7) f_instr_ACC7
      (fun _ s => nth_error s.(Machine.stack) 7 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ACC : forall n,
    handler_correct (handle_ACC n) f_instr_ACC
      (fun _ s => nth_error s.(Machine.stack) n = None)
      (fun _ => False) (fun _ _ _ => False).

  (* --- Stack (PUSH / PUSHACC family) --- *)

  Axiom verify_PUSH :
    handler_correct handle_PUSH f_instr_PUSH
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC1 :
    handler_correct (handle_PUSHACC 1) f_instr_PUSHACC1
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 1 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC2 :
    handler_correct (handle_PUSHACC 2) f_instr_PUSHACC2
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 2 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC3 :
    handler_correct (handle_PUSHACC 3) f_instr_PUSHACC3
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 3 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC4 :
    handler_correct (handle_PUSHACC 4) f_instr_PUSHACC4
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 4 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC5 :
    handler_correct (handle_PUSHACC 5) f_instr_PUSHACC5
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 5 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC6 :
    handler_correct (handle_PUSHACC 6) f_instr_PUSHACC6
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 6 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHACC7 :
    handler_correct (handle_PUSHACC 7) f_instr_PUSHACC7
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 7 = None)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_POP : forall n,
    handler_correct (handle_POP n) f_instr_POP
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ASSIGN : forall n,
    handler_correct (handle_ASSIGN n) f_instr_ASSIGN
      (fun _ s => set_nth s.(Machine.stack) n s.(Machine.accu) = None)
      (fun _ => False) (fun _ _ _ => False).

  (* --- Constants --- *)

  Axiom verify_CONST0 :
    handler_correct (handle_CONSTINT 0) f_instr_CONST0
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_CONST1 :
    handler_correct (handle_CONSTINT 1) f_instr_CONST1
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_CONST2 :
    handler_correct (handle_CONSTINT 2) f_instr_CONST2
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_CONST3 :
    handler_correct (handle_CONSTINT 3) f_instr_CONST3
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_CONSTINT : forall n,
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHCONST0 :
    handler_correct (handle_PUSHCONSTINT 0) f_instr_PUSHCONST0
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHCONST1 :
    handler_correct (handle_PUSHCONSTINT 1) f_instr_PUSHCONST1
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHCONST2 :
    handler_correct (handle_PUSHCONSTINT 2) f_instr_PUSHCONST2
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHCONST3 :
    handler_correct (handle_PUSHCONSTINT 3) f_instr_PUSHCONST3
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHCONSTINT : forall n,
    handler_correct (handle_PUSHCONSTINT n) f_instr_PUSHCONSTINT
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  (* --- Arithmetic (binary) --- *)

  Axiom verify_ADDINT :
    handler_correct handle_ADDINT f_instr_ADDINT
      (fun _ s => forall a b rest,
         s.(Machine.accu) = Val_int a ->
         s.(Machine.stack) = Val_int b :: rest -> False)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SUBINT :
    handler_correct handle_SUBINT f_instr_SUBINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_MULINT :
    handler_correct handle_MULINT f_instr_MULINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_DIVINT :
    handler_correct_with_pre handle_DIVINT f_instr_DIVINT
      (fun _ s _ =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             b <> 0%Z /\
             Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
             Int64.min_signed <= b * 2 + 1 <= Int64.max_signed
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_MODINT :
    handler_correct_with_pre handle_MODINT f_instr_MODINT
      (fun _ s _ =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int a, Val_int b :: _ =>
             b <> 0%Z /\
             Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
             Int64.min_signed <= b * 2 + 1 <= Int64.max_signed
         | _, _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ANDINT :
    handler_correct handle_ANDINT f_instr_ANDINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ORINT :
    handler_correct handle_ORINT f_instr_ORINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_XORINT :
    handler_correct handle_XORINT f_instr_XORINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  (* LSLINT: shift amount must be in range [0, 64) for CompCert's
     sem_shl guard (Int64.ltu shift_amt 64 = true) to hold.
     The shift amount is the untagged stack top: if stack top is
     Val_int b, we need 0 <= b < 64.  The ard parameter is unused. *)
  Axiom verify_LSLINT :
    handler_correct_with_pre handle_LSLINT f_instr_LSLINT
      (fun _ s _ =>
         match s.(Machine.stack) with
         | Val_int b :: _ => 0 <= b < 64
         | _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  (* LSRINT: shift amount must be in range [0, 64) for CompCert's
     sem_shr guard (Int64.ltu shift_amt 64 = true) to hold.
     The shift amount is the untagged stack top: if stack top is
     Val_int b, we need 0 <= b < 64.  The ard parameter is unused. *)
  Axiom verify_LSRINT :
    handler_correct_with_pre handle_LSRINT f_instr_LSRINT
      (fun _ s _ =>
         match s.(Machine.stack) with
         | Val_int b :: _ => 0 <= b < 64
         | _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ASRINT :
    handler_correct_with_pre handle_ASRINT f_instr_ASRINT
      (fun _ s _ =>
         match s.(Machine.stack) with
         | Val_int b :: _ => 0 <= b < 64
         | _ => True
         end)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  (* --- Arithmetic (unary) --- *)

  Axiom verify_NEGINT :
    handler_correct handle_NEGINT f_instr_NEGINT
      (fun _ s => forall n, s.(Machine.accu) <> Val_int n)
      (fun _ => False) (fun _ _ _ => False).

  (* --- Comparisons --- *)

  Axiom verify_EQ :
    handler_correct handle_EQ f_instr_EQ
      (fun _ s => s.(Machine.stack) = nil) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_NEQ :
    handler_correct handle_NEQ f_instr_NEQ
      (fun _ s => s.(Machine.stack) = nil) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_LTINT :
    handler_correct handle_LTINT f_instr_LTINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_LEINT :
    handler_correct handle_LEINT f_instr_LEINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GTINT :
    handler_correct handle_GTINT f_instr_GTINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GEINT :
    handler_correct handle_GEINT f_instr_GEINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ULTINT :
    handler_correct handle_ULTINT f_instr_ULTINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_UGEINT :
    handler_correct handle_UGEINT f_instr_UGEINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end) (fun _ => False) (fun _ _ _ => False).

  (* --- Boolean / misc --- *)

  Axiom verify_BOOLNOT :
    handler_correct handle_BOOLNOT f_instr_BOOLNOT
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_ISINT :
    handler_correct handle_ISINT f_instr_ISINT
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  (* OFFSETINT reads the operand from the code buffer and performs
     a 32-bit left shift by 1.  The precondition requires:
     1. The code buffer contains an int32 whose signed value is ofs.
     2. The 32-bit shift does not overflow (ofs*2 in signed range). *)
  Axiom verify_OFFSETINT : forall ofs,
    handler_correct_with_pre (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (fun m s ard =>
         exists (i : int),
           Mem.load Mint32 m (ar_code_base_block ard)
             (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint i) /\
           Int.signed i = ofs /\
           Int.min_signed <= Int.signed i * 2 <= Int.max_signed)
      (fun _ s => match s.(Machine.accu) with Val_int _ => False | _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_OFFSETREF : forall n,
    handler_correct (handle_OFFSETREF n) f_instr_OFFSETREF
      (fun _ s => match s.(Machine.accu) with
                  | Val_ptr addr =>
                    match heap_lookup s.(Machine.hp) addr with
                    | Some (_, Val_int _ :: _) => False
                    | _ => True
                    end
                  | _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  (* --- Branches --- *)

  (* BRANCH reads the branch offset from *(s->pc).  The precondition
     requires the code buffer at the current PC to be readable and
     contain a 32-bit integer.  The ard parameter comes from abs_rel. *)
  Axiom verify_BRANCH : forall target,
    handler_correct_with_pre (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      (fun m s ard =>
         exists v, Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint v))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_BRANCHIF : forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  (* BRANCHIFNOT requires preconditions:
     1. Code block is separate from struct pointer block
     2. Code buffer at current PC contains a valid branch offset
     3. Accu is representable: not Val_ptr/Val_closure (CompCert's
        sem_binary_operation Oeq is undefined for Vptr vs Vlong
        when both typed tlong), and integers are in 63-bit range *)
  Axiom verify_BRANCHIFNOT : forall target,
    handler_correct_with_pre (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      (fun m s ard =>
         ar_code_base_block ard <> ar_sptr_block ard /\
         (exists ofs_int,
           Mem.load Mint32 m (ar_code_base_block ard)
             (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr (Machine.pc s * sizeof_code_t)))) = Some (Vint ofs_int) /\
           Ptrofs.add
             (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr (Machine.pc s * sizeof_code_t)))
             (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                         (ptrofs_of_int Signed ofs_int))
           = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t))) /\
         match Machine.accu s with
         | Val_int n => -4611686018427387904 <= n <= 4611686018427387903
         | Val_block _ nil => True
         | Val_ptr _ | Val_closure _ _ => False
         | Val_block _ (_ :: _) => True
         end)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  (* --- Blocks --- *)

  Axiom verify_ATOM : forall t,
    handler_correct (handle_ATOM t) f_instr_ATOM
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHATOM : forall t,
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_MAKEBLOCK1 : forall t,
    handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_MAKEBLOCK2 : forall t,
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_MAKEBLOCK3 : forall t,
    handler_correct (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      (fun _ s => match s.(Machine.stack) with _ :: _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  (* --- Fields --- *)

  Axiom verify_GETFIELD0 :
    handler_correct (handle_GETFIELD 0) f_instr_GETFIELD0
      (fun _ s => field_or_heap s s.(Machine.accu) 0 = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GETFIELD1 :
    handler_correct (handle_GETFIELD 1) f_instr_GETFIELD1
      (fun _ s => field_or_heap s s.(Machine.accu) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GETFIELD2 :
    handler_correct (handle_GETFIELD 2) f_instr_GETFIELD2
      (fun _ s => field_or_heap s s.(Machine.accu) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GETFIELD3 :
    handler_correct (handle_GETFIELD 3) f_instr_GETFIELD3
      (fun _ s => field_or_heap s s.(Machine.accu) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GETFIELD : forall n,
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETFIELD0 :
    handler_correct (handle_SETFIELD 0) f_instr_SETFIELD0
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields 0 (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETFIELD1 :
    handler_correct (handle_SETFIELD 1) f_instr_SETFIELD1
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields 1 (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETFIELD2 :
    handler_correct (handle_SETFIELD 2) f_instr_SETFIELD2
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields 2 (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETFIELD3 :
    handler_correct (handle_SETFIELD 3) f_instr_SETFIELD3
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields 3 (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETFIELD : forall n,
    handler_correct (handle_SETFIELD n) f_instr_SETFIELD
      (fun _ s => match s.(Machine.stack) with
                  | newval :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields n newval = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  (* --- Globals --- *)

  Axiom verify_GETGLOBAL : forall n,
    handler_correct (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_PUSHGETGLOBAL : forall n,
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETGLOBAL : forall n,
    handler_correct_with_pre_env (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (fun e m s ard => True)  (* precondition specified in proof file *)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  (* --- Vectors --- *)

  Axiom verify_VECTLENGTH :
    handler_correct handle_VECTLENGTH f_instr_VECTLENGTH
      (fun _ s => size_or_heap s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_GETVECTITEM :
    handler_correct handle_GETVECTITEM f_instr_GETVECTITEM
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | _, Val_int idx :: _ =>
                    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = None
                  | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Axiom verify_SETVECTITEM :
    handler_correct handle_SETVECTITEM f_instr_SETVECTITEM
      (fun _ s => match s.(Machine.stack) with
                  | Val_int idx :: newval :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields (Z.to_nat idx) newval = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end) (fun _ => False) (fun _ _ _ => False).

  (* --- Misc --- *)

  Axiom verify_CHECK_SIGNALS :
    handler_correct handle_CHECK_SIGNALS f_instr_CHECK_SIGNALS
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  (* --- Halt --- *)

  Axiom verify_STOP :
    handler_correct (fun _ => handle_STOP) f_instr_STOP
      (fun _ _ => False) (fun _ => True) (fun _ _ _ => False).

End InstructSpec.
