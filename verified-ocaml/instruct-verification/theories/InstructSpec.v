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
From RecordUpdate Require Import RecordUpdate.
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

(* ================================================================== *)
(* Compositional precondition building blocks                          *)
(*                                                                      *)
(* All have type  Clight.env -> mem -> state -> abs_rel_data -> Prop   *)
(* so they plug directly into handler_correct's step_pre parameter.    *)
(* They are Definitions (not Opaque), so inline lambdas in proof files *)
(* are convertible with the named versions.                            *)
(* ================================================================== *)

(* No precondition — handler works under abs_rel alone. *)
Definition no_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ _ _ => True.

(* Stack pointer has at least n bytes of room below the current sp. *)
Definition sp_at_least (n : Z) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m _ ard =>
    exists sp_b sp_ofs,
      Mem.load Mint64 m (ar_sptr_block ard)
        (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) /\
      Ptrofs.unsigned sp_ofs >= n.

(* Code buffer at current PC contains an expected int32 value. *)
Definition code_at (expected : int) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m s ard =>
    Mem.load Mint32 m (ar_code_base_block ard)
      (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
         (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint expected).

(* Conjunction of two preconditions. *)
Definition pre_and (P Q : Clight.env -> mem -> state -> abs_rel_data -> Prop)
    : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun e m s ard => P e m s ard /\ Q e m s ard.

(* Weaken a handler_correct proof: if abs_rel + weak_pre implies strong_pre,
   then handler_correct with strong_pre implies handler_correct with weak_pre. *)
Lemma handler_correct_weaken handler f sp wp pe ph pc :
  handler_correct handler f sp pe ph pc ->
  (forall e le m s ard,
     abs_rel_with_ard e le m s ard -> wp e m s ard -> sp e m s ard) ->
  handler_correct handler f wp pe ph pc.
Proof.
  unfold handler_correct. intros Hstrong Himp e le m s.
  specialize (Hstrong e le m s).
  destruct (handler (Machine.pc s) s); auto.
  intros ard Hrel Hwp.
  eapply Hstrong; eauto.
Qed.

(* Stronger variant: the implication also receives evidence that
   the handler returns Step.  Useful when the weakened precondition
   can only be derived with knowledge of the handler outcome
   (e.g. stack-index bounds from nth_error success). *)
Lemma handler_correct_weaken_step handler f sp wp pe ph pc :
  handler_correct handler f sp pe ph pc ->
  (forall e le m s s' ard,
     handler s.(Machine.pc) s = Step s' ->
     abs_rel_with_ard e le m s ard -> wp e m s ard -> sp e m s ard) ->
  handler_correct handler f wp pe ph pc.
Proof.
  unfold handler_correct. intros Hstrong Himp e le m s.
  specialize (Hstrong e le m s).
  destruct (handler (Machine.pc s) s) eqn:Heq; auto.
  intros ard Hrel Hwp.
  eapply Hstrong; eauto.
Qed.

(* Global array offset arithmetic does not overflow ptrofs. *)
Definition global_offset_safe (n : nat) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ _ ard =>
    Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus.

(* Code block and struct block are different allocations. *)
Definition code_ne_struct : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ _ ard => ar_code_base_block ard <> ar_sptr_block ard.

(* Some int32 value exists at the current PC in the code buffer. *)
Definition code_loadable : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m s ard =>
    exists v, Mem.load Mint32 m (ar_code_base_block ard)
      (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
         (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint v).

(* Branch offset at pc+1 resolves to the given target address. *)
Definition branch_offset_at (target : Z) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m s ard =>
    exists ofs_int,
      Mem.load Mint32 m (ar_code_base_block ard)
        (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
           (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
      = Some (Vint ofs_int) /\
      Ptrofs.add
        (Ptrofs.add (ar_code_base_ofs ard)
           (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
        (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                    (ptrofs_of_int Signed ofs_int))
      = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t)).

(* Accumulator is Val_int in signed 62-bit range. *)
Definition accu_signed_int : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    match Machine.accu s with
    | Val_int a => -4611686018427387904 <= a <= 4611686018427387903
    | _ => False
    end.

(* Accumulator is Val_int in unsigned 62-bit range. *)
Definition accu_unsigned_int : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    match Machine.accu s with
    | Val_int a => 0 <= a < 4611686018427387904
    | _ => False
    end.

(* Stack has at least n elements. *)
Definition stack_length_ge (n : nat) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ => (n <= length (Machine.stack s))%nat.


(* ================================================================== *)
(* Heap correspondence                                                 *)
(* ================================================================== *)

(* heap_consistent: the Rocq heap (field_or_heap / heap_lookup) is
   faithfully reflected in C memory (Mem.load).  Every mapped heap
   address that stores a block has matching field values in C. *)
Definition heap_consistent : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m s ard =>
    let hm := ar_heap_map ard in
    forall addr b ofs,
      hm addr = Some (b, ofs) ->
      forall tag fields,
        heap_lookup s.(hp) addr = Some (tag, fields) ->
        forall i v,
          nth_error fields i = Some v ->
          exists cv,
            Mem.load Mint64 m b
              (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat i * 8))))
            = Some cv /\
            val_repr hm v cv.

(* ================================================================== *)
(* Named state predicates                                              *)
(*                                                                      *)
(* These capture value-representation safety conditions that arise     *)
(* because certain C operations are only defined for non-pointer       *)
(* values (Vlong, not Vptr).                                           *)
(* ================================================================== *)

(* accu's val_repr is Vlong (safe for C integer operations). *)
Definition accu_is_long : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    forall cv, val_repr (ar_heap_map ard) s.(Machine.accu) cv ->
    exists n, cv = Vlong n.

(* Both accu and stack[0] are Val_int (tagged integers). *)
Definition both_ints : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest.

(* Both Val_int, unsigned tagged representations fit Int64 range. *)
Definition int_op_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      0 <= a * 2 + 1 <= Int64.max_unsigned /\
      0 <= b * 2 + 1 <= Int64.max_unsigned.

(* Both Val_int, signed tagged representations fit Int64 signed range. *)
Definition signed_int_op_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed.

(* Both Val_int, divisor nonzero, results in Int64 range. *)
Definition divmod_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      b <> 0%Z /\
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed.

(* Both Val_int, shift amount in [0, 64), operand in signed range. *)
Definition shift_in_range : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      0 <= b < 64 /\
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed.

(* Both Val_int, non-negative, in 62-bit unsigned range. *)
Definition unsigned_ints_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      0 <= a < 4611686018427387904 /\
      0 <= b < 4611686018427387904.

(* Accu is a boolean (0 or 1). *)
Definition accu_is_bool : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    s.(Machine.accu) = Val_int 0 \/ s.(Machine.accu) = Val_int 1.

(* Accu is an immediate value (integer or atom block). *)
Definition accu_is_immediate : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    match s.(Machine.accu) with
    | Val_int _ => True
    | Val_block _ nil => True
    | _ => False
    end.

(* ================================================================== *)
(* Module Type                                                         *)
(* ================================================================== *)

Module Type InstructVerificationSpec.

  Parameter correct_ACC0 :
    handler_correct (handle_ACC 0) f_instr_ACC0
      no_pre
      (fun _ s => s.(Machine.stack) = nil) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC1 :
    handler_correct (handle_ACC 1) f_instr_ACC1
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC2 :
    handler_correct (handle_ACC 2) f_instr_ACC2
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC3 :
    handler_correct (handle_ACC 3) f_instr_ACC3
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC4 :
    handler_correct (handle_ACC 4) f_instr_ACC4
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 4 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC5 :
    handler_correct (handle_ACC 5) f_instr_ACC5
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 5 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC6 :
    handler_correct (handle_ACC 6) f_instr_ACC6
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 6 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC7 :
    handler_correct (handle_ACC 7) f_instr_ACC7
      no_pre
      (fun _ s => nth_error s.(Machine.stack) 7 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ACC :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ACC n) f_instr_ACC
      (code_at (Int.repr (Z.of_nat n)))
      (fun _ s => nth_error s.(Machine.stack) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ADDINT :
    handler_correct handle_ADDINT f_instr_ADDINT
      no_pre
      (fun _ s => forall a b rest, s.(Machine.accu) = Val_int a -> s.(Machine.stack) = Val_int b :: rest -> False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ANDINT :
    handler_correct handle_ANDINT f_instr_ANDINT
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY1 :
    handler_correct (fun pc' s => handle_APPLY1 pc' s) f_instr_APPLY1
      no_pre
      (fun msg s => (msg = "APPLY1: accu is not a closure"%string /\ get_code_ptr_s s s.(Machine.accu) = None) \/ (msg = "APPLY1: stack underflow"%string)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY2 :
    handler_correct (fun pc' s => handle_APPLY2 pc' s) f_instr_APPLY2
      no_pre
      (fun msg s => (msg = "APPLY2: accu is not a closure"%string /\ get_code_ptr_s s s.(Machine.accu) = None) \/ (msg = "APPLY2: stack underflow"%string)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY3 :
    handler_correct (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      no_pre
      (fun msg s => match s.(Machine.stack) with | _ :: _ :: _ :: _ => get_code_ptr_s s s.(Machine.accu) = None | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY :
    forall n,
    handler_correct (fun _ s => handle_APPLY n s) f_instr_APPLY
      no_pre
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM1 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM1 slotsize s) f_instr_APPTERM1
      no_pre
      (fun msg s => s.(Machine.stack) = nil \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM2 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM2 slotsize s) f_instr_APPTERM2
      no_pre
      (fun msg s => s.(Machine.stack) = nil \/ (exists a, s.(Machine.stack) = a :: nil) \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM3 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM3 slotsize s) f_instr_APPTERM3
      no_pre
      (fun msg s => match s.(Machine.stack) with | _ :: _ :: _ :: _ => False | _ => True end \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM :
    forall nargs slotsize,
    handler_correct (fun _ s => handle_APPTERM nargs slotsize s) f_instr_APPTERM
      no_pre
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ASRINT :
    handler_correct handle_ASRINT f_instr_ASRINT
      shift_in_range
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ASSIGN :
    forall n,
    handler_correct (handle_ASSIGN n) f_instr_ASSIGN
      no_pre
      (fun _ s => set_nth s.(Machine.stack) n s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ATOM0 :
    handler_correct handle_ATOM0 f_instr_ATOM0
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ATOM :
    forall t, Z.of_nat t <= 2097151 ->
    handler_correct (handle_ATOM t) f_instr_ATOM
      (code_at (Int.repr (Z.of_nat t)))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BEQ n target) f_instr_BEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BGEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGEINT n target) f_instr_BGEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BGTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGTINT n target) f_instr_BGTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BLEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BLTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLTINT n target) f_instr_BLTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun msg s => msg = "BLTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BNEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BNEQ n target) f_instr_BNEQ
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_signed_int)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BOOLNOT :
    handler_correct handle_BOOLNOT f_instr_BOOLNOT
      accu_is_bool
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BRANCHIFNOT :
    forall target,
    handler_correct (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BRANCHIF :
    forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BRANCH :
    forall target,
    handler_correct (fun _ s => handle_BRANCH target s) f_instr_BRANCH
      code_loadable
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BREAK :
    handler_correct handle_BREAK f_instr_BREAK
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BUGEINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BUGEINT n target) f_instr_BUGEINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BULTINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      (pre_and (pre_and (pre_and code_ne_struct (code_at (Int.repr n))) (branch_offset_at target)) accu_unsigned_int)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CHECK_SIGNALS :
    handler_correct handle_CHECK_SIGNALS f_instr_CHECK_SIGNALS
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CLOSUREREC :
    forall code_ofs,
    handler_correct (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC
      no_pre
      (fun msg _ => msg = "CLOSUREREC: no code offsets"%string -> False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CLOSURE :
    forall code_ofs,
    handler_correct (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CONST0 :
    handler_correct (handle_CONSTINT 0) f_instr_CONST0
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CONST1 :
    handler_correct (handle_CONSTINT 1) f_instr_CONST1
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CONST2 :
    handler_correct (handle_CONSTINT 2) f_instr_CONST2
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CONST3 :
    handler_correct (handle_CONSTINT 3) f_instr_CONST3
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CONSTINT :
    forall n, Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (code_at (Int.repr n))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_C_CALL1 :
    forall prim_idx,
    handler_correct (handle_C_CALL 1 prim_idx) f_instr_C_CALL1
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).

  Parameter correct_C_CALL2 :
    forall prim_idx,
    handler_correct (handle_C_CALL 2 prim_idx) f_instr_C_CALL2
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).

  Parameter correct_C_CALL3 :
    forall prim_idx,
    handler_correct (handle_C_CALL 3 prim_idx) f_instr_C_CALL3
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).

  Parameter correct_C_CALL4 :
    forall prim_idx,
    handler_correct (handle_C_CALL 4 prim_idx) f_instr_C_CALL4
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).

  Parameter correct_C_CALL5 :
    forall prim_idx,
    handler_correct (handle_C_CALL 5 prim_idx) f_instr_C_CALL5
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).

  Parameter correct_C_CALLN :
    forall nargs prim_idx,
    handler_correct (handle_C_CALL nargs prim_idx) f_instr_C_CALLN
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => True).

  Parameter correct_DIVINT :
    handler_correct handle_DIVINT f_instr_DIVINT
      divmod_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int b :: _ => Z.eqb b 0 = true | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC1 :
    handler_correct (handle_ENVACC 1) f_instr_ENVACC1
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC2 :
    handler_correct (handle_ENVACC 2) f_instr_ENVACC2
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC3 :
    handler_correct (handle_ENVACC 3) f_instr_ENVACC3
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC4 :
    handler_correct (handle_ENVACC 4) f_instr_ENVACC4
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC :
    forall n,
    handler_correct (handle_ENVACC n) f_instr_ENVACC
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_EQ :
    handler_correct handle_EQ f_instr_EQ
      int_op_safe
      (fun _ s => s.(Machine.stack) = nil) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_EVENT :
    handler_correct handle_EVENT f_instr_EVENT
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GEINT :
    handler_correct handle_GEINT f_instr_GEINT
      signed_int_op_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETBYTESCHAR :
    handler_correct handle_GETSTRINGCHAR f_instr_GETBYTESCHAR
      no_pre
      (fun msg s => match s.(Machine.stack) with | Val_int idx :: _ => match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with | Some (Val_int _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETDYNMET :
    handler_correct handle_GETDYNMET f_instr_GETDYNMET
      no_pre
      (fun msg s => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD0 :
    handler_correct (handle_GETFIELD 0) f_instr_GETFIELD0
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 0 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD1 :
    handler_correct (handle_GETFIELD 1) f_instr_GETFIELD1
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD2 :
    handler_correct (handle_GETFIELD 2) f_instr_GETFIELD2
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD3 :
    handler_correct (handle_GETFIELD 3) f_instr_GETFIELD3
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD :
    forall n,
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFLOATFIELD :
    forall n,
    handler_correct (handle_GETFLOATFIELD n) f_instr_GETFLOATFIELD
      no_pre
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETGLOBALFIELD :
    forall n p,
    handler_correct (handle_GETGLOBALFIELD n p) f_instr_GETGLOBALFIELD
      no_pre
      (fun msg s => (nth_error s.(Machine.global) n = None /\ msg = "GETGLOBALFIELD: index out of bounds"%string) \/ (exists glob, nth_error s.(Machine.global) n = Some glob /\ field_or_heap s glob p = None /\ msg = "GETGLOBALFIELD: field access failed"%string)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETMETHOD :
    handler_correct handle_GETMETHOD f_instr_GETMETHOD
      no_pre
      (fun msg s => match msg with | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETPUBMET :
    forall tag,
    handler_correct (handle_GETPUBMET tag) f_instr_GETPUBMET
      no_pre
      (fun msg s => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETSTRINGCHAR :
    handler_correct handle_GETSTRINGCHAR f_instr_GETSTRINGCHAR
      no_pre
      (fun msg s => match s.(Machine.stack) with | Val_int idx :: _ => match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with | Some (Val_int _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETVECTITEM :
    handler_correct handle_GETVECTITEM f_instr_GETVECTITEM
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | _, Val_int idx :: _ => field_or_heap s s.(Machine.accu) (Z.to_nat idx) = None | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GRAB :
    forall required,
    handler_correct (handle_GRAB required) f_instr_GRAB
      no_pre
      (fun msg s => msg = "GRAB: malformed return frame"%string /\ Nat.leb required (extra_args s) = false /\ match skipn (S (extra_args s)) (Machine.stack s) with | Val_int _ :: _ :: Val_int _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GTINT :
    handler_correct handle_GTINT f_instr_GTINT
      signed_int_op_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ISINT :
    handler_correct handle_ISINT f_instr_ISINT
      accu_is_immediate
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_LEINT :
    handler_correct handle_LEINT f_instr_LEINT
      signed_int_op_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_LSLINT :
    handler_correct handle_LSLINT f_instr_LSLINT
      shift_in_range
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_LSRINT :
    handler_correct handle_LSRINT f_instr_LSRINT
      shift_in_range
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_LTINT :
    handler_correct handle_LTINT f_instr_LTINT
      signed_int_op_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK1 :
    forall t,
    handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK2 :
    forall t,
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      no_pre
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK3 :
    forall t,
    handler_correct (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      no_pre
      (fun _ s => match s.(Machine.stack) with _ :: _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK :
    forall (t size : nat), (size >= 1)%nat ->
    handler_correct (handle_MAKEBLOCK t size) f_instr_MAKEBLOCK
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEFLOATBLOCK :
    forall (n : nat), (n >= 1)%nat ->
    handler_correct (handle_MAKEFLOATBLOCK n) f_instr_MAKEFLOATBLOCK
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MODINT :
    handler_correct handle_MODINT f_instr_MODINT
      divmod_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int b :: _ => Z.eqb b 0 = true | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MULINT :
    handler_correct handle_MULINT f_instr_MULINT
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_NEGINT :
    handler_correct handle_NEGINT f_instr_NEGINT
      no_pre
      (fun _ s => forall n, s.(Machine.accu) <> Val_int n) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_NEQ :
    handler_correct handle_NEQ f_instr_NEQ
      int_op_safe
      (fun _ s => s.(Machine.stack) = nil) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETCLOSURE0 :
    handler_correct (handle_OFFSETCLOSURE 0) f_instr_OFFSETCLOSURE0
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETCLOSURE2 :
    handler_correct (handle_OFFSETCLOSURE 2) f_instr_OFFSETCLOSURE2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETCLOSUREM2 :
    handler_correct (handle_OFFSETCLOSURE (-2)) f_instr_OFFSETCLOSUREM2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETCLOSURE :
    forall n,
    handler_correct (handle_OFFSETCLOSURE n) f_instr_OFFSETCLOSURE
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETINT :
    forall ofs, Int.min_signed <= ofs * 2 <= Int.max_signed ->
    handler_correct (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (code_at (Int.repr ofs))
      (fun _ s => match s.(Machine.accu) with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETREF :
    forall n,
    handler_correct (handle_OFFSETREF n) f_instr_OFFSETREF
      no_pre
      (fun _ s => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, Val_int _ :: _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ORINT :
    handler_correct handle_ORINT f_instr_ORINT
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PERFORM :
    handler_correct handle_PERFORM f_instr_PERFORM
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_POPTRAP :
    handler_correct (handle_POPTRAP) f_instr_POPTRAP
      no_pre
      (fun msg _ => msg = "POPTRAP: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_POP :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_POP n) f_instr_POP
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) code_ne_struct) (stack_length_ge n))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC1 :
    handler_correct (handle_PUSHACC 1) f_instr_PUSHACC1
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC2 :
    handler_correct (handle_PUSHACC 2) f_instr_PUSHACC2
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC3 :
    handler_correct (handle_PUSHACC 3) f_instr_PUSHACC3
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC4 :
    handler_correct (handle_PUSHACC 4) f_instr_PUSHACC4
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 4 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC5 :
    handler_correct (handle_PUSHACC 5) f_instr_PUSHACC5
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 5 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC6 :
    handler_correct (handle_PUSHACC 6) f_instr_PUSHACC6
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 6 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHACC7 :
    handler_correct (handle_PUSHACC 7) f_instr_PUSHACC7
      (sp_at_least 16)
      (fun _ s => nth_error (s.(Machine.accu) :: s.(Machine.stack)) 7 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHATOM0 :
    handler_correct handle_PUSHATOM0 f_instr_PUSHATOM0
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHATOM :
    forall t, Z.of_nat t <= 2097151 ->
    handler_correct (handle_PUSHATOM t) f_instr_PUSHATOM
      (pre_and (sp_at_least 16) (code_at (Int.repr (Z.of_nat t))))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHCONST0 :
    handler_correct (handle_PUSHCONSTINT 0) f_instr_PUSHCONST0
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHCONST1 :
    handler_correct (handle_PUSHCONSTINT 1) f_instr_PUSHCONST1
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHCONST2 :
    handler_correct (handle_PUSHCONSTINT 2) f_instr_PUSHCONST2
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHCONST3 :
    handler_correct (handle_PUSHCONSTINT 3) f_instr_PUSHCONST3
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHCONSTINT :
    forall n,
    handler_correct (handle_PUSHCONSTINT n) f_instr_PUSHCONSTINT
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC1 :
    handler_correct (handle_PUSHENVACC 1) f_instr_PUSHENVACC1
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC2 :
    handler_correct (handle_PUSHENVACC 2) f_instr_PUSHENVACC2
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC3 :
    handler_correct (handle_PUSHENVACC 3) f_instr_PUSHENVACC3
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC4 :
    handler_correct (handle_PUSHENVACC 4) f_instr_PUSHENVACC4
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC :
    forall n,
    handler_correct (handle_PUSHENVACC n) f_instr_PUSHENVACC
      no_pre
      (fun _ s => field_or_heap s s.(Machine.env) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHGETGLOBALFIELD :
    forall n p,
    handler_correct (handle_PUSHGETGLOBALFIELD n p) f_instr_PUSHGETGLOBALFIELD
      no_pre
      (fun msg s => nth_error s.(Machine.global) n = None \/ (exists glob, nth_error s.(Machine.global) n = Some glob /\ field_or_heap s glob p = None)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHGETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      (pre_and (pre_and (code_at (Int.repr (Z.of_nat n))) (global_offset_safe n)) (sp_at_least 16))
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSURE0 :
    handler_correct (handle_PUSHOFFSETCLOSURE 0) f_instr_PUSHOFFSETCLOSURE0
      (sp_at_least 16)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSURE2 :
    handler_correct (handle_PUSHOFFSETCLOSURE 2) f_instr_PUSHOFFSETCLOSURE2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSUREM2 :
    handler_correct (handle_PUSHOFFSETCLOSURE (-2)) f_instr_PUSHOFFSETCLOSUREM2
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSURE :
    forall ofs,
    handler_correct (handle_PUSHOFFSETCLOSURE ofs) f_instr_PUSHOFFSETCLOSURE
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHTRAP :
    forall handler_pc,
    handler_correct (handle_PUSHTRAP handler_pc) f_instr_PUSHTRAP
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSH_RETADDR :
    forall ret_addr,
    handler_correct (handle_PUSH_RETADDR ret_addr) f_instr_PUSH_RETADDR
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSH :
    handler_correct handle_PUSH f_instr_PUSH
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RAISE_NOTRACE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE_NOTRACE
      no_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RAISE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE
      no_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_REPERFORMTERM :
    handler_correct handle_REPERFORMTERM f_instr_REPERFORMTERM
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RERAISE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RERAISE
      no_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RESTART :
    handler_correct handle_RESTART f_instr_RESTART
      no_pre
      (fun msg s => (msg = "RESTART: env is not a block"%string /\ match Machine.env s with | Val_int _ | Val_ptr _ => True | _ => False end) \/ (msg = "RESTART: dangling pointer"%string /\ exists addr ofs, Machine.env s = Val_closure addr ofs /\ heap_lookup s.(Machine.hp) addr = None) \/ (msg = "RESTART: env is not a closure"%string /\ ((exists addr ofs t fs, Machine.env s = Val_closure addr ofs /\ heap_lookup s.(Machine.hp) addr = Some (t, fs) /\ Nat.eqb t Closure_tag = false) \/ (exists t fs, Machine.env s = Val_block t fs /\ Nat.eqb t Closure_tag = false))) \/ (msg = "RESTART: malformed closure"%string /\ ((exists addr ofs t all_fields, Machine.env s = Val_closure addr ofs /\ heap_lookup s.(Machine.hp) addr = Some (t, all_fields) /\ Nat.eqb t Closure_tag = true /\ nth_error (skipn ofs all_fields) 2 = None) \/ (exists t fs, Machine.env s = Val_block t fs /\ Nat.eqb t Closure_tag = true /\ nth_error fs 2 = None)))) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RESUMETERM :
    handler_correct handle_RESUMETERM f_instr_RESUMETERM
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RESUME :
    handler_correct handle_RESUME f_instr_RESUME
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RETURN :
    forall stacksize,
    handler_correct (fun _ => handle_RETURN stacksize) f_instr_RETURN
      no_pre
      (fun msg _ => msg = "RETURN: accu is not a closure"%string \/ msg = "RETURN: malformed return frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETBYTESCHAR :
    handler_correct handle_SETBYTESCHAR f_instr_SETBYTESCHAR
      no_pre
      (fun _ s => match s.(Machine.stack) with | Val_int idx :: Val_int newchar :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields (Z.to_nat idx) (Val_int newchar) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD0 :
    handler_correct (handle_SETFIELD 0) f_instr_SETFIELD0
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 0 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD1 :
    handler_correct (handle_SETFIELD 1) f_instr_SETFIELD1
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 1 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD2 :
    handler_correct (handle_SETFIELD 2) f_instr_SETFIELD2
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 2 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD3 :
    handler_correct (handle_SETFIELD 3) f_instr_SETFIELD3
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 3 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD :
    forall n,
    handler_correct (handle_SETFIELD n) f_instr_SETFIELD
      no_pre
      (fun _ s => match s.(Machine.stack) with | newval :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields n newval = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFLOATFIELD :
    forall n,
    handler_correct (handle_SETFLOATFIELD n) f_instr_SETFLOATFIELD
      no_pre
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields n (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETGLOBAL :
    forall n,
    handler_correct (handle_SETGLOBAL n) f_instr_SETGLOBAL
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETVECTITEM :
    handler_correct handle_SETVECTITEM f_instr_SETVECTITEM
      no_pre
      (fun _ s => match s.(Machine.stack) with | Val_int idx :: newval :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields (Z.to_nat idx) newval = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_STOP :
    handler_correct (fun _ => handle_STOP) f_instr_STOP
      no_pre
      (fun _ _ => False) (fun _ => True) (fun _ _ _ => False).

  Parameter correct_SUBINT :
    handler_correct handle_SUBINT f_instr_SUBINT
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SWITCH :
    forall (_nc _nb : nat) (const_targets block_targets : list Z),
    handler_correct (fun _ s => handle_SWITCH _nc _nb const_targets block_targets s) f_instr_SWITCH
      no_pre
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_UGEINT :
    handler_correct handle_UGEINT f_instr_UGEINT
      unsigned_ints_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ULTINT :
    handler_correct handle_ULTINT f_instr_ULTINT
      unsigned_ints_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_VECTLENGTH :
    handler_correct handle_VECTLENGTH f_instr_VECTLENGTH
      no_pre
      (fun _ s => size_or_heap s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_XORINT :
    handler_correct handle_XORINT f_instr_XORINT
      no_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

End InstructVerificationSpec.