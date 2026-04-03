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
  (* Global block is distinct from struct pointer block *)
  ar_global_ne_sptr : ar_global_block <> ar_sptr_block;
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
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
    Ptrofs.unsigned sp_ofs >= 8 /\
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)) < Ptrofs.modulus /\
    Mem.range_perm m sp_b 0
      (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
      Cur Writable /\
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs)) /\

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
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)) /\

  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56)
    Cur Writable.

(* abs_rel: the inter-instruction invariant (postcondition).
   C pc = code_base + s.(pc) * sizeof(code_t). *)
Definition abs_rel (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) : Prop :=
  exists (ard : abs_rel_data), abs_rel_with_ard e le m s ard.

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
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
    Ptrofs.unsigned sp_ofs >= 8 /\
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)) < Ptrofs.modulus /\
    Mem.range_perm m sp_b 0
      (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
      Cur Writable /\
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs)) /\

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
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)) /\

  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56)
    Cur Writable.

(* ================================================================== *)
(* Uniform completeness statement                                      *)
(* ================================================================== *)

(* handler_correct: unified correctness statement for instruction handlers.
   Takes a handler function, a Clight function, and a step precondition.
   The step precondition receives the Clight environment, memory, machine
   state, and abs_rel_data witness.  Use (fun _ _ _ _ => True) for
   handlers with no precondition.
   The Step case: abs_rel_with_ard on the pre-state AND step_pre imply
   the C body executes and abs_rel holds on the post-state.
   The Error / Halt / CCall_request cases are per-handler predicates. *)
Definition handler_correct
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

Lemma abs_rel_iff_with_ard : forall e le m s,
  abs_rel e le m s <-> exists ard, abs_rel_with_ard e le m s ard.
Proof.
  intros. unfold abs_rel, abs_rel_with_ard. reflexivity.
Qed.

(* handler_correct_with_pre: variant where step_pre omits the Clight env.
   Used for handlers whose precondition depends only on memory, machine
   state, and abs_rel_data (not the Clight local environment). *)
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

(* handler_verified: existential wrapper — the Module Type declares that
   a handler is correct for SOME step_pre, and the instantiation pins
   down the concrete precondition. *)
Definition handler_verified
    (handler : Z -> state -> step_result)
    (f : function)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  exists step_pre, handler_correct handler f step_pre P_error P_halt P_ccall.

Definition handler_with_pre_verified
    (handler : Z -> state -> step_result)
    (f : function)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  exists step_pre, handler_correct_with_pre handler f step_pre P_error P_halt P_ccall.

(* ================================================================== *)
(* Module Type: per-instruction correctness obligations                *)
(*                                                                      *)
(* Each Parameter asserts that a handler is correct for some step_pre. *)
(* InstructVerification.v instantiates this Module Type, providing     *)
(* the concrete preconditions from each handler's proof file.          *)
(* ================================================================== *)

(* WIP — Module Type under construction; uncomment when complete.

Module Type InstructVerificationSpec.

  Parameter verified_ACC0 :
    handler_verified
      (handle_ACC 0) f_instr_ACC0
      (fun _ s => s.(Machine.stack) = nil)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC1 :
    handler_verified
      (handle_ACC 1) f_instr_ACC1
      (fun _ s => nth_error s.(Machine.stack) 1 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC2 :
    handler_verified
      (handle_ACC 2) f_instr_ACC2
      (fun _ s => nth_error s.(Machine.stack) 2 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC3 :
    handler_verified
      (handle_ACC 3) f_instr_ACC3
      (fun _ s => nth_error s.(Machine.stack) 3 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC4 :
    handler_verified
      (handle_ACC 4) f_instr_ACC4
      (fun _ s => nth_error s.(Machine.stack) 4 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC5 :
    handler_verified
      (handle_ACC 5) f_instr_ACC5
      (fun _ s => nth_error s.(Machine.stack) 5 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC6 :
    handler_verified
      (handle_ACC 6) f_instr_ACC6
      (fun _ s => nth_error s.(Machine.stack) 6 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC7 :
    handler_verified
      (handle_ACC 7) f_instr_ACC7
      (fun _ s => nth_error s.(Machine.stack) 7 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ACC :
    forall n, handler_verified
      (handle_ACC n) f_instr_ACC
      (fun _ s => nth_error s.(Machine.stack) n = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ADDINT :
    handler_verified
      handle_ADDINT f_instr_ADDINT
      (fun _ s => forall a b rest,
         s.(Machine.accu) = Val_int a ->
         s.(Machine.stack) = Val_int b :: rest -> False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ANDINT :
    handler_verified
      handle_ANDINT f_instr_ANDINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_APPLY1 :
    handler_verified
      (fun pc' s => handle_APPLY1 pc' s) f_instr_APPLY1
      (fun msg s =>
         (msg = "APPLY1: accu is not a closure"%string /\
          get_code_ptr_s s s.(Machine.accu) = None) \/
         (msg = "APPLY1: stack underflow"%string))
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_APPLY3 :
    handler_verified
      (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      (fun msg s =>
        match s.(Machine.stack) with
        | _ :: _ :: _ :: _ =>
          get_code_ptr_s s s.(Machine.accu) = None
        | _ => True
        end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ASRINT :
    handler_verified
      handle_ASRINT f_instr_ASRINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ASSIGN :
    forall n, handler_verified
      (handle_ASSIGN n) f_instr_ASSIGN
      (fun _ s => set_nth s.(Machine.stack) n s.(Machine.accu) = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BEQ :
    forall n target, handler_verified
      (handle_BEQ n target) f_instr_BEQ
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BGEINT :
    forall n target, handler_verified
      (handle_BGEINT n target) f_instr_BGEINT
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BGTINT :
    forall n target, handler_verified
      (handle_BGTINT n target) f_instr_BGTINT
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BLEINT :
    forall n target, handler_verified
      (handle_BLEINT n target) f_instr_BLEINT
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BLTINT :
    forall n target, handler_verified
      (handle_BLTINT n target) f_instr_BLTINT
      (fun msg s =>
         msg = "BLTINT: not an integer"%string /\
         match Machine.accu s with Val_int _ => False | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BNEQ :
    forall n target, handler_verified
      (handle_BNEQ n target) f_instr_BNEQ
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BRANCHIFNOT :
    forall target, handler_with_pre_verified
      (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BRANCHIF :
    forall target, handler_with_pre_verified
      (handle_BRANCHIF target) f_instr_BRANCHIF
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BRANCH :
    forall target, handler_verified
      (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BREAK :
    handler_verified
      handle_BREAK f_instr_BREAK
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BUGEINT :
    forall n target, handler_verified
      (handle_BUGEINT n target) f_instr_BUGEINT
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_BULTINT :
    forall n target, handler_verified
      (handle_BULTINT n target) f_instr_BULTINT
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CHECK_SIGNALS :
    handler_verified
      handle_CHECK_SIGNALS f_instr_CHECK_SIGNALS
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CLOSUREREC :
    forall code_ofs, handler_verified
      (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC
      (fun msg _ => msg = "CLOSUREREC: no code offsets"%string -> False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CLOSURE :
    forall code_ofs, handler_verified
      (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CONST0 :
    handler_verified
      (handle_CONSTINT 0) f_instr_CONST0
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CONST1 :
    handler_verified
      (handle_CONSTINT 1) f_instr_CONST1
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CONST2 :
    handler_verified
      (handle_CONSTINT 2) f_instr_CONST2
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CONST3 :
    handler_verified
      (handle_CONSTINT 3) f_instr_CONST3
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_CONSTINT :
    forall n, handler_verified
      (handle_CONSTINT n) f_instr_CONSTINT
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_C_CALL1 :
    forall prim_idx, handler_verified
      (handle_C_CALL 1 prim_idx) f_instr_C_CALL1
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => True).

  Parameter verified_C_CALL2 :
    forall prim_idx, handler_verified
      (handle_C_CALL 2 prim_idx) f_instr_C_CALL2
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => True).

  Parameter verified_C_CALL3 :
    forall prim_idx, handler_verified
      (handle_C_CALL 3 prim_idx) f_instr_C_CALL3
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => True).

  Parameter verified_C_CALL4 :
    forall prim_idx, handler_verified
      (handle_C_CALL 4 prim_idx) f_instr_C_CALL4
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => True).

  Parameter verified_C_CALL5 :
    forall prim_idx, handler_verified
      (handle_C_CALL 5 prim_idx) f_instr_C_CALL5
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => True).

  Parameter verified_C_CALLN :
    forall nargs prim_idx, handler_verified
      (handle_C_CALL nargs prim_idx) f_instr_C_CALLN
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => True).

  Parameter verified_DIVINT :
    handler_with_pre_verified
      handle_DIVINT f_instr_DIVINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ENVACC :
    forall n, handler_verified
      (handle_ENVACC n) f_instr_ENVACC
      (fun _ s => field_or_heap s s.(Machine.env) n = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_EQ :
    handler_verified
      handle_EQ f_instr_EQ
      (fun _ s => s.(Machine.stack) = nil)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_EVENT :
    handler_verified
      handle_EVENT f_instr_EVENT
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GEINT :
    handler_verified
      handle_GEINT f_instr_GEINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETFIELD0 :
    handler_verified
      (handle_GETFIELD 0) f_instr_GETFIELD0
      (fun _ s => field_or_heap s s.(Machine.accu) 0 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETFIELD1 :
    handler_verified
      (handle_GETFIELD 1) f_instr_GETFIELD1
      (fun _ s => field_or_heap s s.(Machine.accu) 1 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETFIELD2 :
    handler_verified
      (handle_GETFIELD 2) f_instr_GETFIELD2
      (fun _ s => field_or_heap s s.(Machine.accu) 2 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETFIELD3 :
    handler_verified
      (handle_GETFIELD 3) f_instr_GETFIELD3
      (fun _ s => field_or_heap s s.(Machine.accu) 3 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETFIELD :
    forall n, handler_verified
      (handle_GETFIELD n) f_instr_GETFIELD
      (fun _ s => field_or_heap s s.(Machine.accu) n = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETFLOATFIELD :
    forall n, handler_verified
      (handle_GETFLOATFIELD n) f_instr_GETFLOATFIELD
      (fun _ s => field_or_heap s s.(Machine.accu) n = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETGLOBALFIELD :
    forall n p, handler_verified
      (handle_GETGLOBALFIELD n p) f_instr_GETGLOBALFIELD
      (fun msg s =>
         (nth_error s.(Machine.global) n = None /\ msg = "GETGLOBALFIELD: index out of bounds"%string) \/
         (exists glob, nth_error s.(Machine.global) n = Some glob /\
            field_or_heap s glob p = None /\ msg = "GETGLOBALFIELD: field access failed"%string))
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GETGLOBAL :
    forall n, handler_verified
      (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (fun _ s => nth_error s.(Machine.global) n = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GRAB :
    forall required, handler_verified
      (handle_GRAB required) f_instr_GRAB
      (fun msg s =>
         msg = "GRAB: malformed return frame"%string /\
         Nat.leb required (extra_args s) = false /\
         match skipn (S (extra_args s)) (Machine.stack s) with
         | Val_int _ :: _ :: Val_int _ :: _ => False
         | _ => True
         end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_GTINT :
    handler_verified
      handle_GTINT f_instr_GTINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_LEINT :
    handler_verified
      handle_LEINT f_instr_LEINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_LSLINT :
    handler_verified
      handle_LSLINT f_instr_LSLINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_LSRINT :
    handler_verified
      handle_LSRINT f_instr_LSRINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_LTINT :
    handler_verified
      handle_LTINT f_instr_LTINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MAKEBLOCK1 :
    forall t, handler_verified
      (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MAKEBLOCK2 :
    forall t, handler_verified
      (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MAKEBLOCK3 :
    forall t, handler_verified
      (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      (fun _ s => match s.(Machine.stack) with _ :: _ :: _ => False | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MAKEBLOCK :
    forall (t size : nat), (size >= 1)%nat ->
    handler_verified
      (handle_MAKEBLOCK t size) f_instr_MAKEBLOCK
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MAKEFLOATBLOCK :
    forall (n : nat), (n >= 1)%nat ->
    handler_verified
      (handle_MAKEFLOATBLOCK n) f_instr_MAKEFLOATBLOCK
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MODINT :
    handler_with_pre_verified
      handle_MODINT f_instr_MODINT
      (fun _ s =>
         match s.(Machine.accu), s.(Machine.stack) with
         | Val_int _, Val_int b :: _ => Z.eqb b 0 = true
         | _, _ => True
         end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_MULINT :
    handler_verified
      handle_MULINT f_instr_MULINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_NEGINT :
    handler_verified
      handle_NEGINT f_instr_NEGINT
      (fun _ s => forall n, s.(Machine.accu) <> Val_int n)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_NEQ :
    handler_verified
      handle_NEQ f_instr_NEQ
      (fun _ s => s.(Machine.stack) = nil)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_OFFSETCLOSURE0 :
    handler_verified
      (handle_OFFSETCLOSURE 0) f_instr_OFFSETCLOSURE0
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_OFFSETCLOSURE :
    forall n, handler_verified
      (handle_OFFSETCLOSURE n) f_instr_OFFSETCLOSURE
      (fun _ _ => True)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_OFFSETINT :
    forall ofs, handler_verified
      (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (fun _ s => match s.(Machine.accu) with Val_int _ => False | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_OFFSETREF :
    forall n, handler_verified
      (handle_OFFSETREF n) f_instr_OFFSETREF
      (fun _ s => match s.(Machine.accu) with
                  | Val_ptr addr =>
                    match heap_lookup s.(Machine.hp) addr with
                    | Some (_, Val_int _ :: _) => False
                    | _ => True
                    end
                  | _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ORINT :
    handler_verified
      handle_ORINT f_instr_ORINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_POPTRAP :
    handler_verified
      (handle_POPTRAP) f_instr_POPTRAP
      (fun msg _ => msg = "POPTRAP: malformed trap frame"%string)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_POP :
    forall n, handler_verified
      (handle_POP n) f_instr_POP
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC1 :
    handler_verified
      (handle_PUSHACC 1) f_instr_PUSHACC1
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 1 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC2 :
    handler_verified
      (handle_PUSHACC 2) f_instr_PUSHACC2
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 2 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC3 :
    handler_verified
      (handle_PUSHACC 3) f_instr_PUSHACC3
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 3 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC4 :
    handler_verified
      (handle_PUSHACC 4) f_instr_PUSHACC4
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 4 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC5 :
    handler_verified
      (handle_PUSHACC 5) f_instr_PUSHACC5
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 5 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC6 :
    handler_verified
      (handle_PUSHACC 6) f_instr_PUSHACC6
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 6 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHACC7 :
    handler_verified
      (handle_PUSHACC 7) f_instr_PUSHACC7
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 7 = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHCONST0 :
    handler_verified
      (handle_PUSHCONSTINT 0) f_instr_PUSHCONST0
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHCONST1 :
    handler_verified
      (handle_PUSHCONSTINT 1) f_instr_PUSHCONST1
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHCONST2 :
    handler_verified
      (handle_PUSHCONSTINT 2) f_instr_PUSHCONST2
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHCONST3 :
    handler_verified
      (handle_PUSHCONSTINT 3) f_instr_PUSHCONST3
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHCONSTINT :
    forall n, handler_verified
      (handle_PUSHCONSTINT n) f_instr_PUSHCONSTINT
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHGETGLOBALFIELD :
    forall n p, handler_verified
      (handle_PUSHGETGLOBALFIELD n p) f_instr_PUSHGETGLOBALFIELD
      (fun msg s =>
         nth_error s.(Machine.global) n = None \/
         (exists glob, nth_error s.(Machine.global) n = Some glob /\
                       field_or_heap s glob p = None))
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHGETGLOBAL :
    forall n, handler_verified
      (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (fun _ s => nth_error s.(Machine.global) n = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSHTRAP :
    forall handler_pc, handler_verified
      (handle_PUSHTRAP handler_pc) f_instr_PUSHTRAP
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSH_RETADDR :
    forall ret_addr, handler_verified
      (handle_PUSH_RETADDR ret_addr) f_instr_PUSH_RETADDR
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_PUSH :
    handler_verified
      handle_PUSH f_instr_PUSH
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_RAISE_NOTRACE :
    handler_verified
      (fun _pc s => do_raise s.(accu) s) f_instr_RAISE_NOTRACE
      (fun msg _ =>
         msg = "unhandled exception"%string \/
         msg = "RAISE: malformed trap frame"%string)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_RAISE :
    handler_verified
      (fun _pc s => do_raise s.(accu) s) f_instr_RAISE
      (fun msg _ =>
         msg = "unhandled exception"%string \/
         msg = "RAISE: malformed trap frame"%string)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_RERAISE :
    handler_verified
      (fun _pc s => do_raise s.(accu) s) f_instr_RERAISE
      (fun msg _ =>
         msg = "unhandled exception"%string \/
         msg = "RAISE: malformed trap frame"%string)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_RESTART :
    handler_verified
      handle_RESTART f_instr_RESTART
      (* P_error: precise characterization of every Error branch *)
      (fun msg s =>
         (msg = "RESTART: env is not a block"%string /\
          match Machine.env s with
          | Val_int _ | Val_ptr _ => True
          | _ => False
          end)
         \/
         (msg = "RESTART: dangling pointer"%string /\
          exists addr ofs, Machine.env s = Val_closure addr ofs /\
          heap_lookup s.(Machine.hp) addr = None)
         \/
         (msg = "RESTART: env is not a closure"%string /\
          ((exists addr ofs t fs,
              Machine.env s = Val_closure addr ofs /\
              heap_lookup s.(Machine.hp) addr = Some (t, fs) /\
              Nat.eqb t Closure_tag = false)
           \/
           (exists t fs,
              Machine.env s = Val_block t fs /\
              Nat.eqb t Closure_tag = false)))
         \/
         (msg = "RESTART: malformed closure"%string /\
          ((exists addr ofs t all_fields,
              Machine.env s = Val_closure addr ofs /\
              heap_lookup s.(Machine.hp) addr = Some (t, all_fields) /\
              Nat.eqb t Closure_tag = true /\
              nth_error (skipn ofs all_fields) 2 = None)
           \/
           (exists t fs,
              Machine.env s = Val_block t fs /\
              Nat.eqb t Closure_tag = true /\
              nth_error fs 2 = None))))
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETFIELD0 :
    handler_verified
      (handle_SETFIELD 0) f_instr_SETFIELD0
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
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETFIELD1 :
    handler_verified
      (handle_SETFIELD 1) f_instr_SETFIELD1
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
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETFIELD2 :
    handler_verified
      (handle_SETFIELD 2) f_instr_SETFIELD2
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
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETFIELD3 :
    handler_verified
      (handle_SETFIELD 3) f_instr_SETFIELD3
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
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETFIELD :
    forall n, handler_verified
      (handle_SETFIELD n) f_instr_SETFIELD
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
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETFLOATFIELD :
    forall n, handler_verified
      (handle_SETFLOATFIELD n) f_instr_SETFLOATFIELD
      (fun _ s => match s.(Machine.stack) with
                  | _ :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) =>
                          set_nth fields n (hd (Val_int 0) s.(Machine.stack)) = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETGLOBAL :
    forall n, handler_verified
      (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (fun _ _ => False)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_SETVECTITEM :
    handler_verified
      handle_SETVECTITEM f_instr_SETVECTITEM
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
                  | _ => True end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_STOP :
    handler_verified
      (fun _ => handle_STOP) f_instr_STOP
      (fun _ _ => False)
      (fun _ => True)
      (fun _ _ _ => False).

  Parameter verified_SUBINT :
    handler_verified
      handle_SUBINT f_instr_SUBINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_UGEINT :
    handler_verified
      handle_UGEINT f_instr_UGEINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_ULTINT :
    handler_verified
      handle_ULTINT f_instr_ULTINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_VECTLENGTH :
    handler_verified
      handle_VECTLENGTH f_instr_VECTLENGTH
      (fun _ s => size_or_heap s s.(Machine.accu) = None)
      (fun _ => False)
      (fun _ _ _ => False).

  Parameter verified_XORINT :
    handler_verified
      handle_XORINT f_instr_XORINT
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | Val_int _, Val_int _ :: _ => False
                  | _, _ => True
                  end)
      (fun _ => False)
      (fun _ _ _ => False).

End InstructVerificationSpec.

*)
