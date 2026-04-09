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

(* val_repr: a Rocq value corresponds to a CompCert value.
   Parameters: hm = heap map, cb = code base block, co = code base offset.
   The vr_code_ptr constructor enables Val_int (bytecode PC) to be
   represented as Vptr in the code section — needed for return addresses
   and handler PCs stored on the stack. *)
Inductive val_repr (hm : nat -> option (block * ptrofs))
    (cb : block) (co : ptrofs)
    : Value.value -> val -> Prop :=
  | vr_int : forall z,
      val_repr hm cb co (Val_int z) (Vlong (Int64.repr (z * 2 + 1)))
  | vr_ptr : forall addr b ofs,
      hm addr = Some (b, ofs) ->
      val_repr hm cb co (Val_ptr addr) (Vptr b ofs)
  | vr_closure : forall addr offset b ofs delta,
      hm addr = Some (b, ofs) ->
      delta = Ptrofs.repr (Z.of_nat offset * 8) ->
      val_repr hm cb co (Val_closure addr offset) (Vptr b (Ptrofs.add ofs delta))
  | vr_block_atom : forall tag,
      val_repr hm cb co (Val_block tag nil)
        (Vlong (Int64.repr (Z.of_nat tag * 1024)))
  | vr_code_ptr : forall pc co_val,
      val_repr hm cb co (Val_int pc)
        (Vptr cb (Ptrofs.add co_val (Ptrofs.repr (pc * sizeof_code_t)))).

(* stack_repr: Rocq stack (list value) corresponds to a C stack region *)
Inductive stack_repr (hm : nat -> option (block * ptrofs))
    (cb : block) (co : ptrofs) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | sr_nil : forall b ofs,
      stack_repr hm cb co m nil b ofs
  | sr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm cb co v cv ->
      stack_repr hm cb co m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      stack_repr hm cb co m (v :: vs) b ofs.

(* global_repr: Rocq global array corresponds to C memory region *)
Inductive global_repr (hm : nat -> option (block * ptrofs))
    (cb : block) (co : ptrofs) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | gr_nil : forall b ofs,
      global_repr hm cb co m nil b ofs
  | gr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm cb co v cv ->
      global_repr hm cb co m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      global_repr hm cb co m (v :: vs) b ofs.

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
    val_repr hm cb co s.(accu) accu_v) /\

  (exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm cb co m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
    Ptrofs.unsigned sp_ofs >= 8 /\
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)) < Ptrofs.modulus /\
    Mem.range_perm m sp_b 0
      (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
      Cur Writable /\
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs)) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm cb co s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm cb co m s.(global) gb go /\
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
    val_repr hm cb co s.(accu) accu_v) /\

  (exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm cb co m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
    Ptrofs.unsigned sp_ofs >= 8 /\
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)) < Ptrofs.modulus /\
    Mem.range_perm m sp_b 0
      (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
      Cur Writable /\
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs)) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm cb co s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm cb co m s.(global) gb go /\
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

(* Code buffer at PC + k contains an expected int32 value.
   code_arg_at 0 v is definitionally equal to code_at v. *)
Definition code_arg_at (k : nat) (expected : int) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m s ard =>
    Mem.load Mint32 m (ar_code_base_block ard)
      (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
         (Ptrofs.repr ((Machine.pc s + Z.of_nat k) * sizeof_code_t))))
    = Some (Vint expected).

(* Conjunction of two preconditions. *)
Definition pre_and (P Q : Clight.env -> mem -> state -> abs_rel_data -> Prop)
    : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun e m s ard => P e m s ard /\ Q e m s ard.

Infix "/\p" := pre_and (at level 80, right associativity).

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
            val_repr hm (ar_code_base_block ard) (ar_code_base_ofs ard) v cv.

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
    forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) s.(Machine.accu) cv ->
    exists n, cv = Vlong n.

(* stack[0]'s val_repr is Vlong (safe for C integer operations on stack head). *)
Definition stack_head_is_long : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    match s.(Machine.stack) with
    | v :: _ =>
        forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) v cv ->
        exists n, cv = Vlong n
    | nil => True
    end.

(* Both accu and stack[0] are Val_int (tagged integers). *)
Definition both_ints : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest.

(* Helper: Val_int value must have Vlong C representation (not vr_code_ptr). *)
Definition int_vlong (ard : abs_rel_data) (n : Z) : Prop :=
  forall cv,
    val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard)
             (Val_int n) cv ->
    exists z, cv = Vlong z.

(* Both Val_int, unsigned tagged representations fit Int64 range.
   Also requires Vlong representation for both operands (int_vlong). *)
Definition int_op_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      0 <= a * 2 + 1 <= Int64.max_unsigned /\
      0 <= b * 2 + 1 <= Int64.max_unsigned /\
      int_vlong ard a /\
      int_vlong ard b.

(* Both Val_int, signed tagged representations fit Int64 signed range.
   Also requires Vlong representation for both operands (int_vlong). *)
Definition signed_int_op_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b.

(* Both Val_int, divisor nonzero, results in Int64 range.
   Also requires Vlong representation for both operands (int_vlong). *)
Definition divmod_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      b <> 0%Z /\
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      Int64.min_signed <= b * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b.

(* Both Val_int, shift amount in [0, 64), operand in signed range.
   Also requires Vlong representation for both operands (int_vlong). *)
Definition shift_in_range : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      0 <= b < 64 /\
      Int64.min_signed <= a * 2 + 1 <= Int64.max_signed /\
      int_vlong ard a /\
      int_vlong ard b.

(* Both Val_int, non-negative, in 62-bit unsigned range.
   Also requires Vlong representation for both operands (int_vlong). *)
Definition unsigned_ints_safe : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    exists a b rest,
      s.(Machine.accu) = Val_int a /\
      s.(Machine.stack) = Val_int b :: rest /\
      0 <= a < 4611686018427387904 /\
      0 <= b < 4611686018427387904 /\
      int_vlong ard a /\
      int_vlong ard b.

(* Accu is a boolean (0 or 1). *)
Definition accu_is_bool : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s _ =>
    s.(Machine.accu) = Val_int 0 \/ s.(Machine.accu) = Val_int 1.

(* Accu is an immediate value (integer or atom block).
   For Val_int, also requires Vlong representation (excludes vr_code_ptr,
   since CompCert's sem_and is undefined on Vptr). *)
Definition accu_is_immediate : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ _ s ard =>
    match s.(Machine.accu) with
    | Val_int n => int_vlong ard n
    | Val_block _ nil => True
    | _ => False
    end.

(* ================================================================== *)
(* Heap field loadability building blocks                              *)
(* ================================================================== *)

(* heap_field_loadable n: accu is a heap pointer and field n is loadable *)
Definition heap_field_loadable (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) n = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Env field loadability building blocks                               *)
(* ================================================================== *)

(* env_field_loadable n: env is a pointer, field n is loadable,
   and the env block is separate from the struct block. *)
Definition env_field_loadable (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall v,
    field_or_heap s s.(Machine.env) n = Some v ->
    forall env_v,
      val_repr hm cb co s.(Machine.env) env_v ->
      exists b ofs cv,
        env_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Offset closure building blocks                                      *)
(* ================================================================== *)

(* closure_offset_pre: env is a closure that can be offset.
   rocq_ofs = closure entry offset (Rocq semantic level),
   c_byte_delta = byte offset (C level, e.g. 24 for +2 entries). *)
Definition closure_offset_pre (rocq_ofs : Z) (c_byte_delta : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  match s.(Machine.env) with
  | Val_closure addr base_ofs =>
      exists env_long,
        Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long) /\
        val_repr hm cb co (Val_closure addr (Z.to_nat (Z.of_nat base_ofs + rocq_ofs)))
          (Vlong (Int64.add env_long (Int64.repr c_byte_delta)))
  | _ => True
  end.

Definition offsetclosure_pre (n : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr n)) /\
  Int.min_signed <= n <= Int.max_signed /\
  (exists env_long,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long) /\
    match s.(Machine.env) with
    | Val_closure addr base_ofs =>
        val_repr hm cb co
          (Val_closure addr (Z.to_nat (Z.of_nat base_ofs + n)))
          (Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8))))
    | Val_block t l =>
        val_repr hm cb co (Val_block t l)
          (Vlong (Int64.add env_long
            (Int64.mul (Int64.repr (Int.signed (Int.repr n))) (Int64.repr 8))))
    | _ => True
    end).

(* ================================================================== *)
(* Setfield building blocks                                            *)
(* ================================================================== *)

(* setfield_heap_pre n: accu is a heap pointer, field n is writable after SP pop. *)
Definition setfield_heap_pre (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall newval rest,
    s.(Machine.stack) = newval :: rest ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
    forall sp_b sp_ofs,
      Mem.load Mint64 m (ar_sptr_block ard)
        (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
    forall stk_top_cv,
      val_repr hm cb co newval stk_top_cv ->
    exists hb hofs,
      accu_v = Vptr hb hofs /\
      hb <> ar_sptr_block ard /\
      hb <> sp_b /\
      hb <> ar_global_block ard /\
      (forall m1,
        Mem.store Mint64 m (ar_sptr_block ard)
          (Ptrofs.unsigned (ar_sptr_ofs ard) + 16)
          (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some m1 ->
        exists m2, Mem.store Mint64 m1 hb
                     (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr (Z.of_nat n * 8))))
                     stk_top_cv = Some m2).


(* ================================================================== *)
(* Heap block header building blocks (for VECTLENGTH)                  *)
(* ================================================================== *)

Definition heap_block_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall addr b ofs tag fields,
    hm addr = Some (b, ofs) ->
    heap_lookup s.(Machine.hp) addr = Some (tag, fields) ->
    (exists hdr_word,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr_word) /\
      Int64.shru hdr_word (Int64.repr 10) =
        Int64.repr (Z.of_nat (length fields)) /\
      Mem.load Mint8unsigned m b (Ptrofs.unsigned ofs - 8) =
        Some (Vint (Int.repr (Z.of_nat tag))) /\
      Int64.shr hdr_word (Int64.repr 10) =
        Int64.repr (Z.of_nat (length fields))) /\
    Z.of_nat tag <> 254 /\
    Ptrofs.unsigned ofs >= 8 /\
    b <> sb /\
    (0 <= Z.of_nat tag <= 255)%Z.

Definition vectlength_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  (match Machine.accu s with Val_block _ _ => False | _ => True end) /\
  heap_block_pre m s ard.

(* pushenvacc_step_pre n: SP has room + env field n is loadable with block separation. *)
Definition pushenvacc_step_pre (n : nat) (_ : Clight.env) (m : mem) (s : Machine.state)
    (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  exists sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
    Ptrofs.unsigned sp_ofs >= 16 /\
    (forall v,
      field_or_heap s s.(Machine.env) n = Some v ->
      forall env_v,
        val_repr hm cb co s.(Machine.env) env_v ->
        exists b ofs cv,
          env_v = Vptr b ofs /\
          Mem.load Mint64 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
          val_repr hm cb co v cv /\
          b <> sb /\ b <> sp_b).


Definition cm_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default).

Definition cm_fundef : Ctypes.fundef function :=
  Ctypes.External cm_ef ((tptr tlong) :: tlong :: nil) tvoid cc_default.

Definition heap_alloc_ef : external_function :=
  EF_external "heap_alloc"
    (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: nil) AST.Xlong cc_default).

Definition heap_alloc_fundef : Ctypes.fundef function :=
  Ctypes.External heap_alloc_ef
    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
    tlong cc_default.

(* ================================================================== *)
(* Heap allocation building block                                      *)
(*                                                                      *)
(* Captures the common pattern shared by MAKEBLOCK1-3, MAKEBLOCK,      *)
(* MAKEFLOATBLOCK, CLOSURE, CLOSUREREC, GETFLOATFIELD:                 *)
(*  1. _heap_alloc is not a local variable in C env                    *)
(*  2. next_addr is fresh in the heap map                              *)
(*  3. global block is valid                                           *)
(*  4. heap_alloc function is findable in the Clight global env        *)
(*  5. For any memory state m', calling heap_alloc succeeds and        *)
(*     returns a fresh block with load/perm preservation               *)
(*                                                                      *)
(* Store chains are handler-specific and composed via /\p.             *)
(* ================================================================== *)

Definition heap_alloc_pre (n_fields : Z) (tag : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let gb := ar_global_block ard in
  e ! _heap_alloc = None /\
  (ar_heap_map ard) (next_addr s) = None /\
  Mem.valid_block m gb /\
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  (forall m',
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr n_fields) :: Vlong (Int64.repr tag) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v,
          Mem.load chunk m' b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p)).

(* Store chain building blocks: after heap_alloc, the returned block
   supports N sequential Mint64 stores.  Each level guarantees store
   success, read-back, load preservation on other blocks, and
   (at the deepest level) permission preservation from m_alloc. *)

(* 1-field store chain: one Mint64 slot at new_ofs. *)
Definition alloc_store_1
    (new_b : block) (new_ofs : ptrofs) (m_alloc : mem) : Prop :=
  forall cv, exists m_store,
    Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
    Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
      Some (Val.load_result Mint64 cv) /\
    (forall b ofs chunk v, b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v ->
       Mem.load chunk m_store b ofs = Some v).

(* 2-field store chain: two Mint64 slots at new_ofs and new_ofs+8.
   Perm clause preserves from m_alloc through both stores.
   Field0-load-pres and valid_block variants can be derived via
   Mem.perm_store_2 / Mem.load_store_other in bridge proofs. *)
Definition alloc_store_2
    (new_b : block) (new_ofs : ptrofs) (m_alloc : mem) : Prop :=
  forall cv, exists m_store,
    Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
    Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
      Some (Val.load_result Mint64 cv) /\
    (forall b ofs chunk v, b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v ->
       Mem.load chunk m_store b ofs = Some v) /\
    (forall cv1, exists m_store1,
       Mem.store Mint64 m_store new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_store1 /\
       Mem.load Mint64 m_store1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
         Some (Val.load_result Mint64 cv1) /\
       (forall v0, Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) = Some v0 ->
          Mem.load Mint64 m_store1 new_b (Ptrofs.unsigned new_ofs) = Some v0) /\
       (forall b ofs chunk v, b <> new_b ->
          Mem.load chunk m_store b ofs = Some v ->
          Mem.load chunk m_store1 b ofs = Some v) /\
       (forall b ofs k p,
          Mem.perm m_alloc b ofs k p ->
          Mem.perm m_store1 b ofs k p)).

(* 3-field store chain: three Mint64 slots at new_ofs, +8, +16. *)
Definition alloc_store_3
    (new_b : block) (new_ofs : ptrofs) (m_alloc : mem) : Prop :=
  forall cv, exists m_store,
    Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
    Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
      Some (Val.load_result Mint64 cv) /\
    (forall b ofs chunk v, b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v ->
       Mem.load chunk m_store b ofs = Some v) /\
    (forall cv1, exists m_store1,
       Mem.store Mint64 m_store new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_store1 /\
       Mem.load Mint64 m_store1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
         Some (Val.load_result Mint64 cv1) /\
       (forall b ofs chunk v, b <> new_b ->
          Mem.load chunk m_store b ofs = Some v ->
          Mem.load chunk m_store1 b ofs = Some v) /\
       (forall cv2, exists m_store2,
          Mem.store Mint64 m_store1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 16))) cv2 = Some m_store2 /\
          Mem.load Mint64 m_store2 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 16))) =
            Some (Val.load_result Mint64 cv2) /\
          (forall b ofs chunk v, b <> new_b ->
             Mem.load chunk m_store1 b ofs = Some v ->
             Mem.load chunk m_store2 b ofs = Some v) /\
          (forall b ofs k p,
             Mem.perm m_alloc b ofs k p ->
             Mem.perm m_store2 b ofs k p))).

(* 1-field store + perm: like alloc_store_1 but also preserves perms. *)
Definition alloc_store_1_perm
    (new_b : block) (new_ofs : ptrofs) (m_alloc : mem) : Prop :=
  forall cv, exists m_store,
    Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
    Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
      Some (Val.load_result Mint64 cv) /\
    (forall b ofs chunk v, b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v ->
       Mem.load chunk m_store b ofs = Some v) /\
    (forall b ofs k p,
       Mem.perm m_alloc b ofs k p ->
       Mem.perm m_store b ofs k p).

(* heap_alloc_pre with store chain: combines allocation + storability.
   Used by MAKEBLOCK1-3, CLOSURE, CLOSUREREC to avoid repeating both
   the heap_alloc boilerplate AND the store chain in each entry. *)
Definition heap_alloc_with_stores (n_fields : Z) (tag : Z)
    (store_spec : block -> ptrofs -> mem -> Prop)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  heap_alloc_pre n_fields tag e m s ard /\
  (forall m' m_alloc new_b new_ofs,
     external_call heap_alloc_ef
       (Genv.to_senv (genv_genv clight_ge))
       (Vptr (ar_sptr_block ard) (ar_sptr_ofs ard)
        :: Vlong (Int64.repr n_fields) :: Vlong (Int64.repr tag) :: nil)
       m' E0 (Vptr new_b new_ofs) m_alloc ->
     (forall b, Mem.valid_block m' b -> new_b <> b) ->
     (forall b ofs chunk v,
        Mem.load chunk m' b ofs = Some v -> b <> new_b ->
        Mem.load chunk m_alloc b ofs = Some v) ->
     (forall b ofs k p,
        Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
        Mem.perm m_alloc b ofs k p) ->
     store_spec new_b new_ofs m_alloc).

Definition setvectitem_pre
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  forall idx newval rest,
    s.(Machine.stack) = Val_int idx :: newval :: rest ->
    (* Index bounds *)
    0 <= idx /\
    idx * 2 + 1 <= Int64.max_signed /\
    idx < Ptrofs.half_modulus /\
    int_vlong ard idx /\
    (* Genv requirements *)
    e ! _caml_modify = None /\
    (exists b_cm,
       Genv.find_symbol clight_ge _caml_modify = Some b_cm /\
       Genv.find_funct clight_ge (Vptr b_cm Ptrofs.zero) = Some cm_fundef) /\
    (* caml_modify call and its effects *)
    (forall accu_v newval_cv,
       val_repr hm cb co (Machine.accu s) accu_v ->
       val_repr hm cb co newval newval_cv ->
       exists hb hofs,
         accu_v = Vptr hb hofs /\
         hb <> sb /\ hb <> gb /\
         (* hb is also separate from any sp_b obtained from abs_rel *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
            hb <> sp_b) /\
         exists m_cm,
           external_call cm_ef clight_ge
             (Vptr hb (Ptrofs.add hofs (Ptrofs.repr (idx * 8)))
              :: newval_cv :: nil)
             m E0 Vundef m_cm /\
           (* Struct block loads preserved *)
           (forall ofs v,
              Mem.load Mint64 m sb ofs = Some v ->
              Mem.load Mint64 m_cm sb ofs = Some v) /\
           (* Struct block stores succeed *)
           (forall ofs v_old v_new,
              Mem.load Mint64 m sb ofs = Some v_old ->
              exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
           (* Loads on blocks other than hb are preserved *)
           (forall b ofs v,
              b <> hb ->
              Mem.load Mint64 m b ofs = Some v ->
              Mem.load Mint64 m_cm b ofs = Some v) /\
           (* Permission preservation *)
           (forall b ofs k p,
              Mem.valid_block m b -> Mem.perm m b ofs k p ->
              Mem.perm m_cm b ofs k p) /\
           (* global_repr preserved *)
           (global_repr hm cb co m_cm (Machine.global s) gb (ar_global_ofs ard))).
Definition heap_field_target (hofs : ptrofs) (n_int : int) : ptrofs :=
  Ptrofs.add hofs (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                               (ptrofs_of_int Signed n_int)).

Definition float_field_loadable_sep (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) n = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs fv,
        accu_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mfloat64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some (Vfloat fv).

Definition setfloatfield_heap_pre (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  let gb := ar_global_block ard in
  forall newval rest,
    s.(Machine.stack) = newval :: rest ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
    forall sp_b sp_ofs,
      Mem.load Mint64 m sb (Ptrofs.unsigned (ar_sptr_ofs ard) + 16)
        = Some (Vptr sp_b sp_ofs) ->
    forall stk_top_cv,
      val_repr hm cb co newval stk_top_cv ->
    exists hb hofs,
      accu_v = Vptr hb hofs /\
      hb <> sb /\ hb <> sp_b /\ hb <> gb /\ hb <> cb /\
    exists fb fofs,
      stk_top_cv = Vptr fb fofs /\
      fb <> sb /\
    exists fv : float,
      Mem.load Mfloat64 m fb (Ptrofs.unsigned fofs) = Some (Vfloat fv) /\
    (Int.min_signed <= Z.of_nat n <= Int.max_signed) /\
    (forall fv0 : float,
       exists m_post,
         Mem.store Mfloat64 m hb
           (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr (Z.of_nat n * 8))))
           (Vfloat fv0) = Some m_post /\
         (forall b ofs chunk v0,
            b <> hb ->
            Mem.load chunk m b ofs = Some v0 ->
            Mem.load chunk m_post b ofs = Some v0) /\
         (forall b ofs k p,
            Mem.perm m b ofs k p ->
            Mem.perm m_post b ofs k p)).

Definition setfloatfield_code_pre (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr (Z.of_nat n))).

Definition setfloatfield_step_pre (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  setfloatfield_heap_pre n m s ard /\ setfloatfield_code_pre n m s ard.

Definition apply3_closure_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data)
    (sp_b : block) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        accu_b <> sp_b /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

Definition apply3_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (exists pc_cv,
     val_repr hm cb co (Val_int (Machine.pc s)) pc_cv /\
     forall pc_ptr,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
       sem_cast pc_ptr (tptr tint) tlong m = Some pc_cv) /\
  (exists ea_cv,
     val_repr hm cb co (Val_int (Z.of_nat (Machine.extra_args s))) ea_cv /\
     forall ea_long,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
         Some (Vlong ea_long) ->
       Vlong (Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1)) = ea_cv) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs - 24 + 48 + 8 * Z.of_nat (length (Machine.stack s)) < Ptrofs.modulus) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b) /\
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

Definition apply2_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b) /\
  (forall pc_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
     exists ret_pc_cval,
       sem_cast pc_ptr (tptr tint) tlong m = Some ret_pc_cval /\
       val_repr hm cb co (Val_int (Machine.pc s)) ret_pc_cval /\
       Val.load_result Mint64 ret_pc_cval = ret_pc_cval) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

Definition apply_step_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

Definition getstringchar_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall idx rest c,
    s.(Machine.stack) = Val_int idx :: rest ->
    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = Some (Val_int c) ->
    0 <= idx ->
    idx * 2 + 1 <= Int64.max_signed ->
    0 <= c <= 255 ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs,
        accu_v = Vptr b ofs /\
        Mem.load Mint8unsigned m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr idx))) = Some (Vint (Int.repr c)).

Definition getvectitem_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall idx rest v,
    s.(Machine.stack) = Val_int idx :: rest ->
    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (idx * 8)))) = Some cv /\
        val_repr hm cb co v cv.

Definition getmethod_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall obj rest class_tbl n method_fn,
    s.(Machine.stack) = obj :: rest ->
    field_or_heap s obj 0 = Some class_tbl ->
    s.(Machine.accu) = Val_int n ->
    field_or_heap s class_tbl (Z.to_nat n) = Some method_fn ->
    forall sp_v,
      val_repr hm cb co obj sp_v ->
      exists obj_b obj_ofs ct_v ct_b ct_ofs meth_v,
        sp_v = Vptr obj_b obj_ofs /\
        Mem.load Mint64 m obj_b (Ptrofs.unsigned obj_ofs) = Some ct_v /\
        val_repr hm cb co class_tbl ct_v /\
        ct_v = Vptr ct_b ct_ofs /\
        Mem.load Mint64 m ct_b
          (Ptrofs.unsigned (Ptrofs.add ct_ofs (Ptrofs.repr (n * 8)))) = Some meth_v /\
        val_repr hm cb co method_fn meth_v.

Definition setbyteschar_heap_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let gb := ar_global_block ard in
  forall idx newchar rest,
    s.(Machine.stack) = Val_int idx :: Val_int newchar :: rest ->
    0 <= idx ->
    idx * 2 + 1 <= Int64.max_signed ->
    0 <= newchar <= 255 ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
    forall sp_b sp_ofs,
      Mem.load Mint64 m sb
        (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
    exists hb hofs,
      accu_v = Vptr hb hofs /\
      hb <> sb /\
      hb <> gb /\
      hb <> sp_b /\
      (* The byte store succeeds for any value stored at the right address *)
      (forall byte_v,
        exists m_byte,
          Mem.store Mint8unsigned m hb
            (Ptrofs.unsigned (Ptrofs.add hofs (Ptrofs.repr idx)))
            byte_v = Some m_byte /\
          (* sb loads preserved through byte store *)
          (forall ofs0 v0,
             Mem.load Mint64 m sb ofs0 = Some v0 ->
             Mem.load Mint64 m_byte sb ofs0 = Some v0) /\
          (* sp_b loads preserved through byte store *)
          (forall ofs0 v0,
             Mem.load Mint64 m sp_b ofs0 = Some v0 ->
             Mem.load Mint64 m_byte sp_b ofs0 = Some v0) /\
          (* Permission preservation *)
          (forall b ofs0 k p,
             Mem.perm m b ofs0 k p ->
             Mem.perm m_byte b ofs0 k p)).

Definition offsetref_heap_pre
    (n : Z) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let gb := ar_global_block ard in
  (* Code buffer contains the operand at current PC *)
  (exists (i : int),
     Mem.load Mint32 m cb
       (Ptrofs.unsigned (Ptrofs.add co
          (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
     = Some (Vint i) /\
     Int.signed i = n /\
     Int.min_signed <= Int.signed i * 2 <= Int.max_signed) /\
  (* When the Step branch is taken, the heap block is loadable, storable,
     and separate from struct/stack/global blocks *)
  (forall addr old_z rest tag,
     s.(Machine.accu) = Val_ptr addr ->
     heap_lookup s.(Machine.hp) addr = Some (tag, Val_int old_z :: rest) ->
     forall accu_v,
       val_repr hm cb co (Val_ptr addr) accu_v ->
       exists b ofs,
         accu_v = Vptr b ofs /\
         Mem.load Mint64 m b (Ptrofs.unsigned ofs) =
           Some (Vlong (Int64.repr (old_z * 2 + 1))) /\
         b <> sb /\ b <> gb /\ b <> cb /\
         (forall sp_b sp_ofs,
            stack_repr hm cb co m s.(Machine.stack) sp_b sp_ofs ->
            b <> sp_b) /\
         (forall new_cv, exists m_h,
            Mem.store Mint64 m b (Ptrofs.unsigned ofs) new_cv = Some m_h /\
            (forall b' ofs' v',
               Mem.load Mint64 m b' ofs' = Some v' ->
               b <> b' ->
               Mem.load Mint64 m_h b' ofs' = Some v') /\
            Mem.range_perm m_h sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable /\
            (forall sp_b sp_ofs,
               stack_repr hm cb co m s.(Machine.stack) sp_b sp_ofs ->
               b <> sp_b ->
               stack_repr hm cb co m_h s.(Machine.stack) sp_b sp_ofs) /\
            (forall gbl go,
               global_repr hm cb co m s.(Machine.global) gbl go ->
               b <> gbl ->
               global_repr hm cb co m_h s.(Machine.global) gbl go) /\
            (forall sp_b lo hi,
               Mem.range_perm m sp_b lo hi Cur Writable ->
               Mem.range_perm m_h sp_b lo hi Cur Writable))).

Definition pushenvacc_env_field_loadable (n : nat)
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  forall v,
    field_or_heap s s.(Machine.env) n = Some v ->
    forall env_v,
      val_repr hm cb co s.(Machine.env) env_v ->
      exists b ofs cv,
        env_v = Vptr b ofs /\
        b <> sb /\
        Mem.load Mint64 m b
          (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv /\
        val_repr hm cb co v cv /\
        forall sp_b sp_ofs,
          Mem.load Mint64 m sb (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
          b <> sp_b.

(* Generic PUSHENVACC precondition: SP has room, code encodes n, n fits, env field loadable. *)
Definition pushenvacc_generic_step_pre (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state)
    (ard : abs_rel_data) : Prop :=
  (exists sp_b sp_ofs,
    Mem.load Mint64 m (ar_sptr_block ard)
      (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) /\
    Ptrofs.unsigned sp_ofs >= 16) /\
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  Z.of_nat n < Int.half_modulus /\
  pushenvacc_env_field_loadable n m s ard.

Definition heap_field_loadable_pushgetglobalfield
    (p : nat) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall glob v cv_global,
    field_or_heap s glob p = Some v ->
    val_repr hm cb co glob cv_global ->
    exists b ofs cv,
      cv_global = Vptr b ofs /\
      b <> ar_sptr_block ard /\
      (forall sp_b sp_ofs,
         Mem.load Mint64 m (ar_sptr_block ard)
           (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
         b <> sp_b) /\
      Mem.load Mint64 m b
        (Ptrofs.unsigned (Ptrofs.add ofs
           (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
        = Some cv /\
      val_repr hm cb co v cv.

Definition getdynmet_while :=
  Swhile
    (Ebinop Olt (Etempvar _li tint) (Etempvar _hi tint) tint)
    (Ssequence
      (Sset _mi
        (Ebinop Oor
          (Ebinop Oshr
            (Ebinop Oadd (Etempvar _li tint) (Etempvar _hi tint)
              tint) (Econst_int (Int.repr 1) tint) tint)
          (Econst_int (Int.repr 1) tint) tint))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _meths tlong) (tptr tlong))
                (Etempvar _mi tint) (tptr tlong)) tlong))
          (Sifthenelse (Ebinop Olt (Etempvar _t'2 tlong)
                         (Etempvar _t'3 tlong) tint)
            (Sset _hi
              (Ebinop Osub (Etempvar _mi tint)
                (Econst_int (Int.repr 2) tint) tint))
            (Sset _li (Etempvar _mi tint)))))).

Definition getdynmet_pre
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  forall obj rest,
    s.(Machine.stack) = obj :: rest ->
    forall method_fn,
    handle_GETDYNMET (Machine.pc s) s =
      Step (mk_state (Machine.pc s) method_fn (Machine.stack s)
              (Machine.env s) (Machine.extra_args s) (Machine.global s)
              (Machine.trap_sp s) (Machine.hp s) (Machine.next_addr s)) ->
    forall obj_cv,
      val_repr hm cb co obj obj_cv ->
      exists obj_b obj_ofs meths_v meths_b meths_ofs hi_v
             final_li meth_cv,
        obj_cv = Vptr obj_b obj_ofs /\
        Mem.load Mint64 m obj_b (Ptrofs.unsigned obj_ofs) = Some meths_v /\
        meths_v = Vptr meths_b meths_ofs /\
        Mem.load Mint64 m meths_b (Ptrofs.unsigned meths_ofs) = Some (Vlong hi_v) /\
        (forall le_pre,
          le_pre ! _s = Some (Vptr sb so) ->
          le_pre ! _meths = Some (Vptr meths_b meths_ofs) ->
          le_pre ! _li = Some (Vint (Int.repr 3)) ->
          le_pre ! _hi = Some (Vint (Int.repr (Int64.unsigned hi_v))) ->
          exists le_post,
            exec e le_pre m getdynmet_while
              E0 le_post m Out_normal /\
            le_post ! _li = Some (Vint final_li) /\
            le_post ! _meths = Some (Vptr meths_b meths_ofs) /\
            le_post ! _s = Some (Vptr sb so)) /\
        Mem.load Mint64 m meths_b
          (Ptrofs.unsigned (Ptrofs.add meths_ofs
            (Ptrofs.mul (Ptrofs.repr 8)
              (ptrofs_of_int Signed (Int.sub final_li (Int.repr 1))))))
          = Some meth_cv /\
        val_repr hm cb co method_fn meth_cv.

Definition getpubmet_while :=
  Swhile
    (Ebinop Olt (Etempvar _li tint) (Etempvar _hi tint) tint)
    (Ssequence
      (Sset _mi
        (Ebinop Oor
          (Ebinop Oshr
            (Ebinop Oadd (Etempvar _li tint) (Etempvar _hi tint) tint)
            (Econst_int (Int.repr 1) tint) tint)
          (Econst_int (Int.repr 1) tint) tint))
      (Ssequence
        (Sset _t'4
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
        (Ssequence
          (Sset _t'5
            (Ederef (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
              (Etempvar _mi tint) (tptr tlong)) tlong))
          (Sifthenelse (Ebinop Olt (Etempvar _t'4 tlong) (Etempvar _t'5 tlong) tint)
            (Sset _hi (Ebinop Osub (Etempvar _mi tint) (Econst_int (Int.repr 2) tint) tint))
            (Sset _li (Etempvar _mi tint)))))).

Definition getpubmet_pre
    (tag : Z) (e : Clight.env) (m : mem)
    (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr tag)) /\
  Int.min_signed <= tag <= Int.max_signed /\
  (exists sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
    Ptrofs.unsigned sp_ofs >= 16) /\
  (forall method_fn,
    handle_GETPUBMET tag (Machine.pc s) s =
      Step (mk_state (Machine.pc s) method_fn
              (s.(Machine.accu) :: s.(Machine.stack))
              (Machine.env s) (Machine.extra_args s) (Machine.global s)
              (Machine.trap_sp s) (Machine.hp s) (Machine.next_addr s)) ->
    forall accu_cv,
      val_repr hm cb co s.(Machine.accu) accu_cv ->
      exists accu_b accu_ofs meths_b meths_ofs hi_v
             final_li meth_cv,
        accu_cv = Vptr accu_b accu_ofs /\
        Mem.load Mint64 m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr meths_b meths_ofs) /\
        Mem.load Mint64 m meths_b (Ptrofs.unsigned meths_ofs) = Some (Vlong hi_v) /\
        meths_b <> sb /\
        (forall sp_b0 sp_ofs0,
          Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b0 sp_ofs0) ->
          meths_b <> sp_b0) /\
        (forall le_pre m_loop,
          le_pre ! _s = Some (Vptr sb so) ->
          le_pre ! _meths = Some (Vptr meths_b meths_ofs) ->
          le_pre ! _li = Some (Vint (Int.repr 3)) ->
          le_pre ! _hi = Some (Vint (Int.repr (Int64.unsigned hi_v))) ->
          Mem.load Mint64 m_loop sb (Ptrofs.unsigned so + 8) =
            Some (Vlong (Int64.repr (tag * 2 + 1))) ->
          (forall idx_ofs v, Mem.load Mint64 m meths_b idx_ofs = Some v ->
            Mem.load Mint64 m_loop meths_b idx_ofs = Some v) ->
          exists le_post,
            exec e le_pre m_loop getpubmet_while
              E0 le_post m_loop Out_normal /\
            le_post ! _li = Some (Vint final_li) /\
            le_post ! _meths = Some (Vptr meths_b meths_ofs) /\
            le_post ! _s = Some (Vptr sb so)) /\
        Mem.load Mint64 m meths_b
          (Ptrofs.unsigned (Ptrofs.add meths_ofs
            (Ptrofs.mul (Ptrofs.repr 8)
              (ptrofs_of_int Signed (Int.sub final_li (Int.repr 1))))))
          = Some meth_cv /\
        val_repr hm cb co method_fn meth_cv).

Definition makeblock_loop_body : statement :=
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                   (Etempvar _wosize tulong) tint)
      Sskip
      Sbreak)
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong))))
      (Ssequence
        (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Ecast (Etempvar _block tlong) (tptr tlong))
              (Etempvar _i tulong) (tptr tlong)) tlong)
          (Etempvar _t'5 tlong))))).

Definition makeblock_loop_incr : statement :=
  (Sset _i
    (Ebinop Oadd (Etempvar _i tulong)
      (Econst_int (Int.repr 1) tint) tulong)).

Definition makeblock_loop : statement :=
  Sloop makeblock_loop_body makeblock_loop_incr.

Definition makefloatblock_loop_body : statement :=
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                   (Etempvar _size tulong) tint)
      Sskip
      Sbreak)
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tlong)) tlong))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ecast (Etempvar _t'5 tlong) (tptr tdouble))
                tdouble))
            (Sassign
              (Ederef
                (Ecast
                  (Ebinop Oadd
                    (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Ebinop Omul (Etempvar _i tulong)
                      (Ebinop Odiv (Esizeof tdouble tulong)
                        (Esizeof tlong tulong) tulong) tulong)
                    (tptr tlong)) (tptr tdouble)) tdouble)
              (Etempvar _t'6 tdouble)))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)))))).

Definition makefloatblock_loop_incr : statement :=
  (Sset _i
    (Ebinop Oadd (Etempvar _i tulong)
      (Econst_int (Int.repr 1) tint) tulong)).

Definition makefloatblock_loop : statement :=
  Sloop makefloatblock_loop_body makefloatblock_loop_incr.

Definition makefloatblock_body_after_setblock : statement :=
  Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'8
          (Ederef (Ecast (Etempvar _t'7 tlong) (tptr tdouble)) tdouble))
        (Sassign
          (Ederef
            (Ecast
              (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                (Ebinop Omul (Econst_int (Int.repr 0) tint)
                  (Ebinop Odiv (Esizeof tdouble tulong)
                    (Esizeof tlong tulong) tulong) tulong) (tptr tlong))
              (tptr tdouble)) tdouble) (Etempvar _t'8 tdouble))))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong))
        (Sloop
          makefloatblock_loop_body
          makefloatblock_loop_incr))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _block tlong))).

Definition return_tailcall_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) (sp_b : block) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        accu_b <> sp_b /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

Definition return_frame_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) (sp_b : block) (sp_ofs : ptrofs)
    (ret_pc : Z) (saved_env : value) (saved_ea : Z) (rest : list value) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  (exists pc_b pc_ofs,
    Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs) = Some (Vptr pc_b pc_ofs) /\
    pc_rel (Vptr pc_b pc_ofs) cb co ret_pc) /\
  (exists env_cv,
    Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 8) = Some env_cv /\
    val_repr hm cb co saved_env env_cv) /\
  Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 16) =
    Some (Vlong (Int64.repr (saved_ea * 2 + 1))) /\
  0 <= saved_ea /\
  saved_ea <= Int64.max_signed /\
  Int64.shr (Int64.repr (saved_ea * 2 + 1)) (Int64.repr 1) = Int64.repr saved_ea /\
  Ptrofs.unsigned sp_ofs + 24 < Ptrofs.modulus /\
  Ptrofs.unsigned sp_ofs + 24 + 8 * Z.of_nat (length rest) < Ptrofs.modulus.

Definition raise_frame_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) (sp_b : block) (sp_ofs : ptrofs)
    (handler_pc : Z) (prev_tsp : Z) (saved_env : value) (saved_ea : Z) (rest : list value) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  (* sp[0]: a code pointer encoding handler_pc *)
  (exists pc_b pc_ofs,
    Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs) = Some (Vptr pc_b pc_ofs) /\
    pc_rel (Vptr pc_b pc_ofs) cb co handler_pc) /\
  (* sp[1]: tagged integer for prev_tsp *)
  Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 8) =
    Some (Vlong (Int64.repr (prev_tsp * 2 + 1))) /\
  (* sp[2]: val_repr for saved_env *)
  (exists env_cv,
    Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 16) = Some env_cv /\
    val_repr hm cb co saved_env env_cv) /\
  (* sp[3]: tagged integer for saved_ea *)
  Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs + 24) =
    Some (Vlong (Int64.repr (saved_ea * 2 + 1))) /\
  (* prev_tsp is non-negative and shr recovers it *)
  0 <= prev_tsp /\
  prev_tsp <= Int64.max_signed /\
  Int64.shr (Int64.repr (prev_tsp * 2 + 1)) (Int64.repr 1) = Int64.repr prev_tsp /\
  (* saved_ea is non-negative and fits in Int64 shift *)
  0 <= saved_ea /\
  saved_ea <= Int64.max_signed /\
  (* shr correctly recovers saved_ea *)
  Int64.shr (Int64.repr (saved_ea * 2 + 1)) (Int64.repr 1) = Int64.repr saved_ea /\
  (* sp + 32 fits in ptrofs (for sp + 4 adjustment) *)
  Ptrofs.unsigned sp_ofs + 32 < Ptrofs.modulus /\
  (* The rest of the stack at sp + 32 is representable *)
  Ptrofs.unsigned sp_ofs + 32 + 8 * Z.of_nat (length rest) < Ptrofs.modulus.

(* raise_step_pre: precondition for RAISE/RAISE_NOTRACE/RERAISE.
   When trap_sp > 0, the trap_sp pointer (from trap_sp_rel) points to the
   trap frame.  The C code sets sp := trap_sp, then reads sp[0..3].  So the
   loads must be at the trap_sp address, which is (ar_stack_block, sub base tsp*8).
   The precondition provides raise_frame_pre AT THAT ADDRESS, plus
   stack_repr for the rest of the stack after the frame, and the
   new post-state trap_sp_rel for prev_tsp. *)
Definition raise_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let k := Nat.sub (length (Machine.stack s)) (trap_sp s) in
  let stk_b := ar_stack_block ard in
  let stk_base := ar_stack_base_ofs ard in
  forall handler_pc prev_tsp saved_env saved_ea rest,
    skipn k (Machine.stack s) =
      Val_int handler_pc :: Val_int prev_tsp :: saved_env :: Val_int saved_ea :: rest ->
    (* Frame loads are at the trap_sp address (stk_b, trap_ofs) *)
    let trap_ofs := Ptrofs.sub stk_base (Ptrofs.repr (Z.of_nat (trap_sp s) * 8)) in
    raise_frame_pre m s ard stk_b trap_ofs
      handler_pc prev_tsp saved_env saved_ea rest /\
    (* stack_repr for rest at trap_ofs + 32 *)
    stack_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard)
      m rest stk_b (Ptrofs.add trap_ofs (Ptrofs.repr 32)) /\
    (* block separation: stk_b != sb *)
    stk_b <> ar_sptr_block ard /\
    stk_b <> ar_global_block ard /\
    ar_code_base_block ard <> stk_b /\
    (* the rest of the stack is writable *)
    Mem.range_perm m stk_b 0
      (Ptrofs.unsigned (Ptrofs.add trap_ofs (Ptrofs.repr 32)) +
       8 * Z.of_nat (length rest))
      Cur Writable /\
    (align_chunk Mint64 | Ptrofs.unsigned (Ptrofs.add trap_ofs (Ptrofs.repr 32))) /\
    (* new trap_sp_rel for Z.to_nat prev_tsp *)
    trap_sp_rel
      (Vptr stk_b (Ptrofs.add trap_ofs
         (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64
            (Int64.shr (Int64.repr (prev_tsp * 2 + 1)) (Int64.repr 1))))))
      stk_b stk_base (Z.to_nat prev_tsp) /\
    (* new sp offset is large enough *)
    Ptrofs.unsigned (Ptrofs.add trap_ofs (Ptrofs.repr 32)) >= 8.

(* restart_step_pre: precondition for RESTART.
   RESTART reads the closure environment's infix header, copies fields
   3..length-1 to the stack (loop), reads field 2 (saved_env), and
   updates sp/env/extra_args.  The precondition requires:
   1. Infix header at env[-1] encodes the correct field count
   2. Closure fields 2..length-1 are loadable with val_repr
   3. SP has room for the args (num_args * 8 bytes)
   4. Arithmetic bounds (num_args fits tint, extra_args+num_args fits tlong)
   5. Env block is separate from struct block *)
Definition restart_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  forall addr offset env_b env_ofs,
    Machine.env s = Val_closure addr offset ->
    hm addr = Some (env_b, env_ofs) ->
    forall ht all_fields,
    heap_lookup s.(Machine.hp) addr = Some (ht, all_fields) ->
    Nat.eqb ht Closure_tag = true ->
    let fields := skipn offset all_fields in
    nth_error fields 2 <> None ->
    let num_args := Nat.sub (length fields) 3 in
    (* 1. Infix header encoding: word at env_ptr - 8 encodes length fields *)
    (exists hdr_word,
      Mem.load Mint64 m env_b
        (Ptrofs.unsigned env_ofs + Z.of_nat offset * 8 - 8)
        = Some (Vlong hdr_word) /\
      Int64.shr hdr_word (Int64.repr 10)
        = Int64.repr (Z.of_nat (length fields))) /\
    (* 2. Closure fields from index 2 onward loadable with val_repr *)
    (forall i v, (i >= 2)%nat -> nth_error fields i = Some v ->
      exists cv, Mem.load Mint64 m env_b
        (Ptrofs.unsigned env_ofs + (Z.of_nat offset + Z.of_nat i) * 8)
        = Some cv /\
        val_repr hm cb co v cv) /\
    (* 3. SP has room for num_args entries and the range is writable *)
    (forall sp_b sp_ofs,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 16)
        = Some (Vptr sp_b sp_ofs) ->
      Ptrofs.unsigned sp_ofs >= Z.of_nat num_args * 8 /\
      Mem.range_perm m sp_b
        (Ptrofs.unsigned sp_ofs - Z.of_nat num_args * 8)
        (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(Machine.stack)))
        Cur Writable /\
      (align_chunk Mint64 | (Ptrofs.unsigned sp_ofs - Z.of_nat num_args * 8)) /\
      env_b <> sp_b /\
      Ptrofs.unsigned sp_ofs - Z.of_nat num_args * 8 >= 8 /\
      Ptrofs.unsigned sp_ofs - Z.of_nat num_args * 8 +
        8 * Z.of_nat (num_args + length s.(Machine.stack)) < Ptrofs.modulus) /\
    (* 4. Arithmetic bounds: num_args+3 fits signed int for C array indexing _i+3 *)
    (0 <= Z.of_nat num_args + 3 <= Int.max_signed)%Z /\
    (Z.of_nat (extra_args s) + Z.of_nat num_args < Int64.modulus)%Z /\
    (* 5. Block separation *)
    env_b <> sb /\
    (* 6. Env pointer offset representability *)
    Ptrofs.unsigned env_ofs + Z.of_nat offset * 8 >= 8 /\
    Ptrofs.unsigned env_ofs + (Z.of_nat offset + Z.of_nat (length fields)) * 8 < Ptrofs.modulus.

Definition apply1_closure_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) (sp_b : block) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        accu_b <> sp_b /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

Definition apply1_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply1_closure_pre m s ard sp_b) /\
  (forall pc_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
     val_repr hm cb co (Val_int (Machine.pc s)) pc_ptr) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

Definition pushtrap_step_pre (handler_pc : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let stk_b := ar_stack_block ard in
  let stk_base := ar_stack_base_ofs ard in
  (* branch offset at *pc is readable from code buffer *)
  (exists ofs_int,
     Mem.load Mint32 m cb
       (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
     = Some (Vint ofs_int)) /\
  (* sp has room for 4 pushes (32 bytes) plus alignment headroom *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 40) /\
  (* extra_args fits for tagged (<<1|1) encoding *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus /\
  (* trap_sp fits for tagged (<<1|1) encoding *)
  Z.of_nat (Machine.trap_sp s) < Int64.half_modulus /\
  (* trap link: ptr subtraction gives Z.of_nat trap_sp as Vlong *)
  (forall sp_b sp_ofs ts_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr ->
     sem_binary_operation (genv_cenv clight_ge) Osub ts_ptr (tptr tlong)
       (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 32))) (tptr tlong) m
     = Some (Vlong (Int64.repr (Z.of_nat (Machine.trap_sp s))))) /\
  (* new trap_sp_rel for the post-state sp pointer *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     trap_sp_rel (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 32)))
       stk_b stk_base
       (S (S (S (S (length (Machine.stack s))))))).

Definition push_retaddr_step_pre (ret_addr : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  (* There exists a branch offset at the current PC position *)
  (exists ofs_int,
     Mem.load Mint32 m cb
       (Ptrofs.unsigned (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
     = Some (Vint ofs_int) /\
     Ptrofs.add
       (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t)))
       (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                   (ptrofs_of_int Signed ofs_int))
     = Ptrofs.add co (Ptrofs.repr (ret_addr * sizeof_code_t))) /\
  (* sp >= 32 to accommodate 3 pushes (24 bytes) below current sp *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (* extra_args fits for shl encoding *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

Definition apply_n_step_pre (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  Int.min_signed <= Z.of_nat n <= Int.max_signed /\
  (1 <= n)%nat /\
  apply_step_pre m s ard.

Definition appterm1_step_pre (slotsize : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat slotsize))) /\
  Z.of_nat slotsize < Int.half_modulus /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + Z.of_nat slotsize * 8 < Ptrofs.modulus) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 1) * 8 >= 8) /\
  (1 <= slotsize)%nat /\
  (slotsize <= Datatypes.length (Machine.stack s))%nat /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b).

Definition appterm2_step_pre (slotsize : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat slotsize))) /\
  Z.of_nat slotsize < Int.half_modulus /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + Z.of_nat slotsize * 8 < Ptrofs.modulus) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 2) * 8 >= 8) /\
  (2 <= slotsize)%nat /\
  (slotsize <= Datatypes.length (Machine.stack s))%nat /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b) /\
  Z.of_nat (Machine.extra_args s) + 1 < Int64.modulus.

Definition appterm3_step_pre (slotsize : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat slotsize))) /\
  Z.of_nat slotsize < Int.half_modulus /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + Z.of_nat slotsize * 8 < Ptrofs.modulus) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + (Z.of_nat slotsize - 3) * 8 >= 8) /\
  (3 <= slotsize)%nat /\
  (slotsize <= Datatypes.length (Machine.stack s))%nat /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b) /\
  Z.of_nat (extra_args s) <= Int64.max_unsigned /\
  Z.of_nat (extra_args s) <= Int64.max_signed.

Definition appterm_step_pre (nargs slotsize : nat)
    (e0 : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  get_code_ptr_s s s.(Machine.accu) <> None /\
  let s' := match get_code_ptr_s s s.(Machine.accu) with
            | Some target_pc =>
              s <|pc := target_pc|>
                <|stack := firstn nargs s.(Machine.stack) ++ skipn slotsize s.(Machine.stack)|>
                <|env := s.(Machine.accu)|>
                <|extra_args := Nat.add s.(extra_args) (Nat.sub nargs 1)|>
            | None => s
            end in
  forall le,
    abs_rel_with_ard e0 le m s ard ->
    exists le' m' out,
      exec_stmt function_entry1 clight_ge e0 le m
        (fn_body f_instr_APPTERM) E0 le' m' out /\
      abs_rel e0 le' m' s'.

Definition assign_step_pre (n : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  ar_code_base_block ard <> ar_sptr_block ard /\
  (0 <= Z.of_nat n <= Int.max_signed)%Z /\
  (forall m1 sp_b sp_ofs accu_v,
    stack_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) m1 (Machine.stack s) sp_b sp_ofs ->
    val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) accu_v ->
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n < Ptrofs.modulus ->
    exists m_sw,
      Mem.store Mint64 m1 sp_b
        (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat n) accu_v = Some m_sw).

Definition branchifnot_step_pre (target : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
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
  end /\
  (forall n, Machine.accu s = Val_int n ->
     forall cv,
     val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
     exists z, cv = Vlong z).

Definition branchif_step_pre (target : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  ar_code_base_block ard <> ar_sptr_block ard /\
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr (target - Machine.pc s))) /\
  (Machine.accu s <> Val_int 0 ->
     forall cv,
     val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
     sem_binary_operation (genv_cenv clight_ge) Cop.One
       cv tlong (Vlong (Int64.repr 1)) tlong m
       = Some (Vint Int.one)) /\
  (Machine.accu s = Val_int 0 ->
     forall cv,
     val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Machine.accu s) cv ->
     exists z, cv = Vlong z).

Definition closurerec_step_pre (code_ofs : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  e ! _heap_alloc = None /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr 1)) /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
  = Some (Vint (Int.repr 0)) /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr ((Machine.pc s + 2) * sizeof_code_t))))
  = Some (Vint (Int.repr code_ofs)) /\
  (Int.min_signed <= code_ofs <= Int.max_signed) /\
  (ar_heap_map ard) (next_addr s) = None /\
  Mem.valid_block m gb /\
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  (forall m',
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr 2) :: Vlong (Int64.repr 247) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v,
          Mem.load chunk m' b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p) /\
       (forall cv, exists m_s0,
          Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_s0 /\
          Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) =
            Some (Val.load_result Mint64 cv) /\
          (forall b ofs chunk v, b <> new_b ->
             Mem.load chunk m_alloc b ofs = Some v ->
             Mem.load chunk m_s0 b ofs = Some v) /\
          (forall cv1, exists m_s1,
             Mem.store Mint64 m_s0 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_s1 /\
             Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
               Some (Val.load_result Mint64 cv1) /\
             (forall v0, Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) = Some v0 ->
                Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned new_ofs) = Some v0) /\
             (forall b ofs chunk v, b <> new_b ->
                Mem.load chunk m_s0 b ofs = Some v ->
                Mem.load chunk m_s1 b ofs = Some v) /\
             (forall b ofs k p,
                Mem.valid_block m_s0 b -> Mem.perm m_s0 b ofs k p ->
                Mem.perm m_s1 b ofs k p)))) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 16 /\
     (align_chunk Mint64 | Ptrofs.unsigned sp_ofs - 8) /\
     Ptrofs.unsigned sp_ofs - 8 + 8 < Ptrofs.modulus).

Definition getfloatfield_step_pre (n : nat)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let hm := ar_heap_map ard in
  e ! _heap_alloc = None /\
  float_field_loadable_sep n m s ard /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  Int.min_signed <= Z.of_nat n <= Int.max_signed /\
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  Mem.valid_block m gb /\
  (forall m' fv,
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr 1) :: Vlong (Int64.repr 253) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v0,
          Mem.load chunk m' b ofs = Some v0 -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v0) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p) /\
       (exists m_fstore,
          Mem.store Mfloat64 m_alloc new_b (Ptrofs.unsigned new_ofs) (Vfloat fv) = Some m_fstore /\
          (forall b ofs chunk v0, b <> new_b ->
             Mem.load chunk m_alloc b ofs = Some v0 ->
             Mem.load chunk m_fstore b ofs = Some v0) /\
          (forall b ofs k p,
             Mem.perm m_alloc b ofs k p ->
             Mem.perm m_fstore b ofs k p))) /\
  (forall v new_b new_ofs,
     field_or_heap s s.(Machine.accu) n = Some v ->
     exists hm',
       val_repr hm' cb co v (Vptr new_b new_ofs) /\
       (forall v0 cv, val_repr hm cb co v0 cv -> val_repr hm' cb co v0 cv) /\
       (forall stk m0 sp_b0 sp_ofs0,
          stack_repr hm cb co m0 stk sp_b0 sp_ofs0 ->
          stack_repr hm' cb co m0 stk sp_b0 sp_ofs0) /\
       (forall gs m0 gb0 gofs0,
          global_repr hm cb co m0 gs gb0 gofs0 ->
          global_repr hm' cb co m0 gs gb0 gofs0)).

Definition getglobalfield_step_pre (n p : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))) (Ptrofs.repr 4)))
  = Some (Vint (Int.repr (Z.of_nat p))) /\
  0 <= Z.of_nat n <= Int.max_signed /\
  0 <= Z.of_nat p <= Int.max_signed /\
  Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
  (forall glob v cv_global,
     nth_error s.(Machine.global) n = Some glob ->
     field_or_heap s glob p = Some v ->
     val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) glob cv_global ->
     exists b ofs cv,
       cv_global = Vptr b ofs /\
       b <> ar_sptr_block ard /\
       Mem.load Mint64 m b
         (Ptrofs.unsigned (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat p))))))
         = Some cv /\
       val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) v cv).

Definition getmethod_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  getmethod_heap_pre m s ard /\
  match s.(Machine.accu) with
  | Val_int n => 0 <= n /\
                 n * 2 + 1 <= Int64.max_signed /\
                 n < Ptrofs.half_modulus /\
                 (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int n) cv -> exists z, cv = Vlong z)
  | _ => True
  end.

Definition getstringchar_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  getstringchar_heap_pre m s ard /\
  match s.(Machine.stack) with
  | Val_int idx :: _ =>
      0 <= idx /\ idx * 2 + 1 <= Int64.max_signed /\
      match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with
      | Some (Val_int c) => 0 <= c <= 255
      | _ => True
      end /\
      (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv ->
       exists z, cv = Vlong z)
  | _ => True
  end.

Definition getvectitem_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  getvectitem_heap_pre m s ard /\
  match s.(Machine.stack) with
  | Val_int idx :: _ =>
      0 <= idx /\
      idx * 2 + 1 <= Int64.max_signed /\
      idx < Ptrofs.half_modulus /\
      (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv ->
       exists z, cv = Vlong z)
  | _ => True
  end.

Definition grab_step_pre (required : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat required))) /\
  0 <= Z.of_nat required <= Int.max_signed /\
  Z.of_nat (extra_args s) <= Int64.max_signed /\
  Z.of_nat (extra_args s) <= Int64.max_unsigned /\
  Nat.leb required (extra_args s) = true.

Definition makeblock_step_pre (t size : nat)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let sp_b := ar_stack_block ard in
  let hm := ar_heap_map ard in
  e ! _heap_alloc = None /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat size))) /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t)))
       (Ptrofs.repr 4)))
  = Some (Vint (Int.repr (Z.of_nat t))) /\
  (0 <= Z.of_nat t <= 255) /\
  (0 < Z.of_nat size <= Int.max_signed) /\
  hm (next_addr s) = None /\
  Mem.valid_block m gb /\
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  (forall m',
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr (Z.of_nat size)) :: Vlong (Int64.repr (Z.of_nat t)) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v,
          Mem.load chunk m' b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p) /\
       (forall cv, exists m_store,
          Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_store /\
          Mem.load Mint64 m_store new_b (Ptrofs.unsigned new_ofs) =
            Some (Val.load_result Mint64 cv) /\
          (forall b ofs chunk v, b <> new_b ->
             Mem.load chunk m_alloc b ofs = Some v ->
             Mem.load chunk m_store b ofs = Some v) /\
          (forall b ofs k p,
             Mem.perm m_alloc b ofs k p ->
             Mem.perm m_store b ofs k p))) /\
  (forall le_pre m_field0 new_b new_ofs sp_b sp_ofs,
     le_pre ! _s = Some (Vptr sb so) ->
     le_pre ! _block = Some (Vptr new_b new_ofs) ->
     le_pre ! _wosize = Some (Vlong (Int64.repr (Z.of_nat size))) ->
     new_b <> sb -> new_b <> sp_b -> new_b <> gb -> new_b <> cb ->
     Mem.load Mint64 m_field0 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     stack_repr hm cb co m_field0 (Machine.stack s) sp_b sp_ofs ->
     Mem.range_perm m_field0 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56)
       Cur Writable ->
     exists le_loop m_loop sp_ofs_loop,
       exec_stmt function_entry1 clight_ge e le_pre m_field0
         (Ssequence
           (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong))
           makeblock_loop)
         E0 le_loop m_loop Out_normal /\
       le_loop ! _s = Some (Vptr sb so) /\
       le_loop ! _block = Some (Vptr new_b new_ofs) /\
       (forall ofs v,
          Mem.load Mint64 m_field0 sb ofs = Some v ->
          ofs <> Ptrofs.unsigned so + 16 ->
          Mem.load Mint64 m_loop sb ofs = Some v) /\
       Mem.load Mint64 m_loop sb (Ptrofs.unsigned so + 16) =
         Some (Vptr sp_b sp_ofs_loop) /\
       stack_repr hm cb co m_loop (skipn (Nat.sub size 1) (Machine.stack s))
         sp_b sp_ofs_loop /\
       Ptrofs.unsigned sp_ofs_loop >= 8 /\
       (align_chunk Mint64 | Ptrofs.unsigned sp_ofs_loop) /\
       Ptrofs.unsigned sp_ofs_loop + 8 * Z.of_nat (length (skipn (Nat.sub size 1) (Machine.stack s))) < Ptrofs.modulus /\
       Ptrofs.unsigned sp_ofs_loop + 8 * Z.of_nat (length (skipn (Nat.sub size 1) (Machine.stack s))) <=
         Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)) /\
       (forall b ofs k p,
          Mem.perm m_field0 b ofs k p ->
          Mem.perm m_loop b ofs k p) /\
       (forall b ofs chunk v,
          b <> sb -> b <> sp_b -> b <> new_b ->
          Mem.load chunk m_field0 b ofs = Some v ->
          Mem.load chunk m_loop b ofs = Some v)).

Definition makefloatblock_step_pre (n : nat)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let sp_b := ar_stack_block ard in
  let hm := ar_heap_map ard in
  e ! _heap_alloc = None /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  (0 < Z.of_nat n <= Int.max_signed) /\
  hm (next_addr s) = None /\
  Mem.valid_block m gb /\
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  (forall m',
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr (Z.of_nat n)) :: Vlong (Int64.repr 254) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v,
          Mem.load chunk m' b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p)) /\
  (forall le_pre m_alloc0 new_b new_ofs sp_b sp_ofs,
     le_pre ! _s = Some (Vptr sb so) ->
     le_pre ! _block = Some (Vptr new_b new_ofs) ->
     le_pre ! _size = Some (Vlong (Int64.repr (Z.of_nat n))) ->
     new_b <> sb -> new_b <> sp_b -> new_b <> gb -> new_b <> cb ->
     Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 8) = Some (Vptr sp_b sp_ofs) ->
     val_repr hm cb co (Machine.accu s) (Vptr sp_b sp_ofs) ->
     False) /\
  (forall le_pre m_alloc0 new_b new_ofs sp_b sp_ofs accu_v0,
     le_pre ! _s = Some (Vptr sb so) ->
     le_pre ! _block = Some (Vptr new_b new_ofs) ->
     le_pre ! _size = Some (Vlong (Int64.repr (Z.of_nat n))) ->
     new_b <> sb -> new_b <> sp_b -> new_b <> gb -> new_b <> cb ->
     Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 8) = Some accu_v0 ->
     val_repr hm cb co (Machine.accu s) accu_v0 ->
     Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     stack_repr hm cb co m_alloc0 (Machine.stack s) sp_b sp_ofs ->
     Mem.range_perm m_alloc0 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56)
       Cur Writable ->
     (forall b ofs chunk v,
          Mem.load chunk m_alloc0 b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc0 b ofs = Some v) ->
     exists le_out m_out sp_ofs_out,
       exec_stmt function_entry1 clight_ge e le_pre m_alloc0
         makefloatblock_body_after_setblock
         E0 le_out m_out Out_normal /\
       le_out ! _s = Some (Vptr sb so) /\
       le_out ! _block = Some (Vptr new_b new_ofs) /\
       (forall v,
          Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 0) = Some v ->
          Mem.load Mint64 m_out sb (Ptrofs.unsigned so + 0) = Some v) /\
       Mem.load Mint64 m_out sb (Ptrofs.unsigned so + 8) =
         Some (Vptr new_b new_ofs) /\
       Mem.load Mint64 m_out sb (Ptrofs.unsigned so + 16) =
         Some (Vptr sp_b sp_ofs_out) /\
       stack_repr hm cb co m_out (skipn (Nat.sub n 1) (Machine.stack s))
         sp_b sp_ofs_out /\
       Ptrofs.unsigned sp_ofs_out >= 8 /\
       (align_chunk Mint64 | Ptrofs.unsigned sp_ofs_out) /\
       Ptrofs.unsigned sp_ofs_out + 8 * Z.of_nat (length (skipn (Nat.sub n 1) (Machine.stack s))) < Ptrofs.modulus /\
       Ptrofs.unsigned sp_ofs_out + 8 * Z.of_nat (length (skipn (Nat.sub n 1) (Machine.stack s))) <=
         Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)) /\
       (forall fo v, fo >= 24 ->
          Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + fo) = Some v ->
          Mem.load Mint64 m_out sb (Ptrofs.unsigned so + fo) = Some v) /\
       (forall b ofs k p,
          Mem.perm m_alloc0 b ofs k p ->
          Mem.perm m_out b ofs k p) /\
       (forall ofs v,
          Mem.load Mint64 m_alloc0 gb ofs = Some v ->
          Mem.load Mint64 m_out gb ofs = Some v)).

Definition poptrap_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  exists v0 prev_tsp v2 v3 rest,
    Machine.stack s = v0 :: Val_int prev_tsp :: v2 :: v3 :: rest /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Mem.load Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)))
       = Some (Vlong (Int64.repr (prev_tsp * 2 + 1)))) /\
  Int64.shr (Int64.repr (prev_tsp * 2 + 1)) (Int64.repr 1) =
    Int64.repr prev_tsp /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + 32 + 8 * Z.of_nat (length rest) < Ptrofs.modulus) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     trap_sp_rel
       (Vptr sp_b (Ptrofs.add sp_ofs
          (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr prev_tsp)))))
       (ar_stack_block ard) (ar_stack_base_ofs ard)
       (Z.to_nat prev_tsp)).

Definition pushconstint_step_pre (n : Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  ar_code_base_block ard <> ar_sptr_block ard /\
  (forall sp_b sp_ofs sp_ptr,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some sp_ptr ->
     sp_ptr = Vptr sp_b sp_ofs ->
     ar_code_base_block ard <> sp_b) /\
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr n)) /\
  Int64.add (Int64.shl (Int64.repr (Int.signed (Int.repr n)))
                       (Int64.repr 1))
            (Int64.repr 1) = Int64.repr (n * 2 + 1) /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 16).

Definition pushgetglobalfield_step_pre (n p : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr (Z.of_nat n))) /\
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
    = Some (Vint (Int.repr (Z.of_nat p))) /\
  0 <= Z.of_nat n <= Int.max_signed /\
  0 <= Z.of_nat p <= Int.max_signed /\
  Ptrofs.unsigned (ar_global_ofs ard) + Z.of_nat n * 8 < Ptrofs.modulus /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 16) /\
  heap_field_loadable_pushgetglobalfield p m s ard.

Definition pushoffsetclosure_step_pre (ofs : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let hm := ar_heap_map ard in
  (exists sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
     Ptrofs.unsigned sp_ofs >= 16) /\
  (forall sp_b sp_ofs sp_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr ->
     sp_ptr = Vptr sp_b sp_ofs ->
     cb <> sp_b) /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
    = Some (Vint (Int.repr ofs)) /\
  match s.(Machine.env) with
  | Val_closure addr base_ofs =>
      exists env_long,
        Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long) /\
        val_repr hm cb co (Val_closure addr (Z.to_nat (Z.of_nat base_ofs + ofs)))
          (Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8))))
  | Val_block t _ =>
      exists env_long,
        Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long) /\
        Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)) = env_long
  | _ => True
  end.

Definition return_step_pre (stacksize : nat)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  Mem.load Mint32 m (ar_code_base_block ard)
    (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat stacksize))) /\
  Z.of_nat stacksize < Int.half_modulus /\
  Z.of_nat (extra_args s) <= Int64.max_signed /\
  (forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 < Ptrofs.modulus) /\
  (stacksize <= Datatypes.length (Machine.stack s))%nat /\
  (Nat.ltb 0 (extra_args s) = true ->
   forall sp_b sp_ofs,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     return_tailcall_pre m s ard sp_b) /\
  (Nat.ltb 0 (extra_args s) = false ->
   forall sp_b sp_ofs ret_pc saved_env saved_ea rest,
     Mem.load Mint64 m (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
     skipn stacksize (Machine.stack s) =
       Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest ->
     return_frame_pre m s ard sp_b
       (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8)))
       ret_pc saved_env saved_ea rest).

Definition setbyteschar_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  setbyteschar_heap_pre m s ard /\
  match s.(Machine.stack) with
  | Val_int idx :: Val_int newchar :: _ =>
      0 <= idx /\ idx * 2 + 1 <= Int64.max_signed /\
      0 <= newchar <= 255 /\
      (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv -> exists z, cv = Vlong z) /\
      (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int newchar) cv -> exists z, cv = Vlong z)
  | _ => True
  end.

Definition setfield_step_pre (n : nat)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  e ! _caml_modify = None /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  Int.min_signed <= Z.of_nat n <= Int.max_signed /\
  (exists b_cm,
     Genv.find_symbol clight_ge _caml_modify = Some b_cm /\
     Genv.find_funct clight_ge (Vptr b_cm Ptrofs.zero) = Some cm_fundef) /\
  (forall newval rest,
     Machine.stack s = newval :: rest ->
     forall accu_v,
       val_repr hm cb co (Machine.accu s) accu_v ->
     forall sp_b sp_ofs,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     forall stk_top_cv,
       val_repr hm cb co newval stk_top_cv ->
     exists hb hofs,
       accu_v = Vptr hb hofs /\
       hb <> sb /\
       hb <> sp_b /\
       hb <> ar_global_block ard /\
       hb <> cb /\
       (exists m_sp,
         Mem.store Mint64 m sb (Ptrofs.unsigned so + 16)
           (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some m_sp /\
         Mem.load Mint64 m_sp sp_b (Ptrofs.unsigned sp_ofs) = Some stk_top_cv /\
         Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs) /\
         Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 0) =
           Some (Vptr cb (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t)))) /\
         (exists m_cm,
           external_call cm_ef clight_ge
             (Vptr hb (heap_field_target hofs (Int.repr (Z.of_nat n)))
              :: stk_top_cv :: nil)
             m_sp E0 Vundef m_cm /\
           (forall ofs v,
              Mem.load Mint64 m_sp sb ofs = Some v ->
              Mem.load Mint64 m_cm sb ofs = Some v) /\
           (forall ofs v_old v_new,
              Mem.load Mint64 m_sp sb ofs = Some v_old ->
              exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
           (forall ofs v,
              Mem.load Mint64 m_sp sp_b ofs = Some v ->
              Mem.load Mint64 m_cm sp_b ofs = Some v) /\
           (forall ofs v,
              Mem.load Mint32 m_sp cb ofs = Some v ->
              Mem.load Mint32 m_cm cb ofs = Some v) /\
           (global_repr hm cb co m_cm
              (Machine.global s) (ar_global_block ard) (ar_global_ofs ard)) /\
           (forall b ofs k p,
              Mem.valid_block m_sp b -> Mem.perm m_sp b ofs k p ->
              Mem.perm m_cm b ofs k p)))).

Definition setglobal_step_pre (n : nat)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let go := ar_global_ofs ard in
  let sb := ar_sptr_block ard in
  let hm := ar_heap_map ard in
  e ! _caml_modify = None /\
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat n))) /\
  Int.min_signed <= Z.of_nat n <= Int.max_signed /\
  (exists b_cm,
     Genv.find_symbol clight_ge _caml_modify = Some b_cm /\
     Genv.find_funct clight_ge (Vptr b_cm Ptrofs.zero) = Some cm_fundef) /\
  (forall accu_v,
     val_repr hm cb co (Machine.accu s) accu_v ->
     exists m_cm,
       external_call cm_ef clight_ge
         (Vptr gb (heap_field_target go (Int.repr (Z.of_nat n)))
          :: accu_v :: nil)
         m E0 Vundef m_cm /\
       (forall ofs v,
          Mem.load Mint64 m sb ofs = Some v ->
          Mem.load Mint64 m_cm sb ofs = Some v) /\
       (forall ofs v_old v_new,
          Mem.load Mint64 m sb ofs = Some v_old ->
          exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
       (forall sp_b, sp_b <> gb ->
          forall ofs v,
          Mem.load Mint64 m sp_b ofs = Some v ->
          Mem.load Mint64 m_cm sp_b ofs = Some v) /\
       (forall new_gs,
          set_nth (Machine.global s) n (Machine.accu s) = Some new_gs ->
          global_repr hm cb co m_cm new_gs gb go) /\
       (set_nth (Machine.global s) n (Machine.accu s) = None ->
          global_repr hm cb co m_cm (Machine.global s) gb go) /\
       (forall b ofs k p,
          Mem.valid_block m b -> Mem.perm m b ofs k p ->
          Mem.perm m_cm b ofs k p)).

Definition switch_step_pre (_nc _nb : nat) (const_targets block_targets : list Z)
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  match Machine.accu s with
  | Val_int n =>
      0 <= n /\
      -4611686018427387904 <= n <= 4611686018427387903 /\
      int_vlong ard n /\
      (exists sizes_v,
        Mem.load Mint32 m (ar_code_base_block ard)
          (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
             (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
        = Some (Vint sizes_v)) /\
      (exists ofs_int,
        Mem.load Mint32 m (ar_code_base_block ard)
          (Ptrofs.unsigned
            (Ptrofs.add
              (Ptrofs.add (ar_code_base_ofs ard)
                (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
              (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
                (Ptrofs.of_int64 (Int64.repr n)))))
        = Some (Vint ofs_int) /\
        forall target,
          nth_error const_targets (Z.to_nat n) = Some target ->
          Ptrofs.add
            (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t)))
            (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tint))
              (ptrofs_of_int Signed ofs_int))
          = Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr (target * sizeof_code_t)))
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
      (accu_is_long /\p stack_head_is_long)
      (fun _ s => forall a b rest, s.(Machine.accu) = Val_int a -> s.(Machine.stack) = Val_int b :: rest -> False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ANDINT :
    handler_correct handle_ANDINT f_instr_ANDINT
      (accu_is_long /\p stack_head_is_long)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY1 :
    handler_correct (fun pc' s => handle_APPLY1 pc' s) f_instr_APPLY1
      apply1_step_pre
      (fun msg s => (msg = "APPLY1: accu is not a closure"%string /\ get_code_ptr_s s s.(Machine.accu) = None) \/ (msg = "APPLY1: stack underflow"%string)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY2 :
    handler_correct (fun pc' s => handle_APPLY2 pc' s) f_instr_APPLY2
      apply2_step_pre
      (fun msg s => (msg = "APPLY2: accu is not a closure"%string /\ get_code_ptr_s s s.(Machine.accu) = None) \/ (msg = "APPLY2: stack underflow"%string)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY3 :
    handler_correct (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      apply3_step_pre
      (fun msg s => match s.(Machine.stack) with | _ :: _ :: _ :: _ => get_code_ptr_s s s.(Machine.accu) = None | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPLY :
    forall n,
    handler_correct (fun _ s => handle_APPLY n s) f_instr_APPLY
      (apply_n_step_pre n)
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM1 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM1 slotsize s) f_instr_APPTERM1
      (appterm1_step_pre slotsize)
      (fun msg s => s.(Machine.stack) = nil \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM2 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM2 slotsize s) f_instr_APPTERM2
      (appterm2_step_pre slotsize)
      (fun msg s => s.(Machine.stack) = nil \/ (exists a, s.(Machine.stack) = a :: nil) \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM3 :
    forall slotsize,
    handler_correct (fun _ s => handle_APPTERM3 slotsize s) f_instr_APPTERM3
      (appterm3_step_pre slotsize)
      (fun msg s => match s.(Machine.stack) with | _ :: _ :: _ :: _ => False | _ => True end \/ get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_APPTERM :
    forall nargs slotsize,
    handler_correct (fun _ s => handle_APPTERM nargs slotsize s) f_instr_APPTERM
      (appterm_step_pre nargs slotsize)
      (fun msg s => get_code_ptr_s s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ASRINT :
    handler_correct handle_ASRINT f_instr_ASRINT
      shift_in_range
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ASSIGN :
    forall n,
    handler_correct (handle_ASSIGN n) f_instr_ASSIGN
      (assign_step_pre n)
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
      (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_signed_int /\p accu_is_long))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BGEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGEINT n target) f_instr_BGEINT
      (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_signed_int /\p accu_is_long))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BGTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BGTINT n target) f_instr_BGTINT
      (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_signed_int /\p accu_is_long))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BLEINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLEINT n target) f_instr_BLEINT
      (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_signed_int /\p accu_is_long))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BLTINT :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BLTINT n target) f_instr_BLTINT
      (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_signed_int /\p accu_is_long))
      (fun msg s => msg = "BLTINT: not an integer"%string /\ match Machine.accu s with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BNEQ :
    forall n target,
    Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BNEQ n target) f_instr_BNEQ
      (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_signed_int /\p accu_is_long))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BOOLNOT :
    handler_correct handle_BOOLNOT f_instr_BOOLNOT
      (accu_is_bool /\p accu_is_long)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BRANCHIFNOT :
    forall target,
    handler_correct (handle_BRANCHIFNOT target) f_instr_BRANCHIFNOT
      (branchifnot_step_pre target)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BRANCHIF :
    forall target,
    handler_correct (handle_BRANCHIF target) f_instr_BRANCHIF
      (branchif_step_pre target)
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
      ((((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p accu_unsigned_int) /\p accu_is_long)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_BULTINT :
    forall n target,
    0 <= n -> Int.min_signed <= n <= Int.max_signed ->
    handler_correct (handle_BULTINT n target) f_instr_BULTINT
      ((((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p accu_unsigned_int) /\p accu_is_long)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CHECK_SIGNALS :
    handler_correct handle_CHECK_SIGNALS f_instr_CHECK_SIGNALS
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CLOSUREREC :
    forall code_ofs, Int.min_signed <= code_ofs <= Int.max_signed ->
    handler_correct (handle_CLOSUREREC 1 0 [code_ofs]) f_instr_CLOSUREREC
      (heap_alloc_with_stores 2 247 alloc_store_2
       /\p code_at (Int.repr 1)
       /\p code_arg_at 1 (Int.repr 0)
       /\p code_arg_at 2 (Int.repr code_ofs)
       /\p sp_at_least 16)
      (fun msg _ => msg = "CLOSUREREC: no code offsets"%string -> False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_CLOSURE :
    forall code_ofs, Int.min_signed <= code_ofs <= Int.max_signed ->
    handler_correct (handle_CLOSURE 0 code_ofs) f_instr_CLOSURE
      (heap_alloc_with_stores 2 247 alloc_store_2
       /\p code_at (Int.repr 0)
       /\p code_arg_at 1 (Int.repr code_ofs))
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
      (env_field_loadable 1)
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC2 :
    handler_correct (handle_ENVACC 2) f_instr_ENVACC2
      (env_field_loadable 2)
      (fun _ s => field_or_heap s s.(Machine.env) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC3 :
    handler_correct (handle_ENVACC 3) f_instr_ENVACC3
      (env_field_loadable 3)
      (fun _ s => field_or_heap s s.(Machine.env) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC4 :
    handler_correct (handle_ENVACC 4) f_instr_ENVACC4
      (env_field_loadable 4)
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ENVACC :
    forall n, Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_ENVACC n) f_instr_ENVACC
      (code_at (Int.repr (Z.of_nat n)) /\p env_field_loadable n)
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
      getstringchar_step_pre
      (fun msg s => match s.(Machine.stack) with | Val_int idx :: _ => match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with | Some (Val_int _) => False | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETDYNMET :
    handler_correct handle_GETDYNMET f_instr_GETDYNMET
      getdynmet_pre
      (fun msg s => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD0 :
    handler_correct (handle_GETFIELD 0) f_instr_GETFIELD0
      (heap_field_loadable 0)
      (fun _ s => field_or_heap s s.(Machine.accu) 0 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD1 :
    handler_correct (handle_GETFIELD 1) f_instr_GETFIELD1
      (heap_field_loadable 1)
      (fun _ s => field_or_heap s s.(Machine.accu) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD2 :
    handler_correct (handle_GETFIELD 2) f_instr_GETFIELD2
      (heap_field_loadable 2)
      (fun _ s => field_or_heap s s.(Machine.accu) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD3 :
    handler_correct (handle_GETFIELD 3) f_instr_GETFIELD3
      (heap_field_loadable 3)
      (fun _ s => field_or_heap s s.(Machine.accu) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFIELD :
    forall n, Int.min_signed <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETFIELD n) f_instr_GETFIELD
      (heap_field_loadable n /\p code_at (Int.repr (Z.of_nat n)))
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETFLOATFIELD :
    forall n,
    handler_correct (handle_GETFLOATFIELD n) f_instr_GETFLOATFIELD
      (getfloatfield_step_pre n)
      (fun _ s => field_or_heap s s.(Machine.accu) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETGLOBALFIELD :
    forall n p,
    handler_correct (handle_GETGLOBALFIELD n p) f_instr_GETGLOBALFIELD
      (getglobalfield_step_pre n p)
      (fun msg s => (nth_error s.(Machine.global) n = None /\ msg = "GETGLOBALFIELD: index out of bounds"%string) \/ (exists glob, nth_error s.(Machine.global) n = Some glob /\ field_or_heap s glob p = None /\ msg = "GETGLOBALFIELD: field access failed"%string)) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_GETGLOBAL n) f_instr_GETGLOBAL
      (code_at (Int.repr (Z.of_nat n)) /\p global_offset_safe n)
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETMETHOD :
    handler_correct handle_GETMETHOD f_instr_GETMETHOD
      getmethod_step_pre
      (fun msg s =>
         match msg with
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETPUBMET :
    forall tag,
    handler_correct (handle_GETPUBMET tag) f_instr_GETPUBMET
      (getpubmet_pre tag)
      (fun msg s => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETSTRINGCHAR :
    handler_correct handle_GETSTRINGCHAR f_instr_GETSTRINGCHAR
      getstringchar_step_pre
      (fun msg s =>
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with
             | Some (Val_int _) => False
             | _ => True
             end
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GETVECTITEM :
    handler_correct handle_GETVECTITEM f_instr_GETVECTITEM
      getvectitem_step_pre
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with
                  | _, Val_int idx :: _ =>
                    field_or_heap s s.(Machine.accu) (Z.to_nat idx) = None
                  | _, _ => True end)
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_GRAB :
    forall required,
    handler_correct (handle_GRAB required) f_instr_GRAB
      (grab_step_pre required)
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
    forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK1 t) f_instr_MAKEBLOCK1
      (heap_alloc_with_stores 1 (Z.of_nat t) alloc_store_1
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK2 :
    forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK2 t) f_instr_MAKEBLOCK2
      (heap_alloc_with_stores 2 (Z.of_nat t) alloc_store_2
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ s => match s.(Machine.stack) with _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK3 :
    forall t, 0 <= Z.of_nat t <= 255 ->
    handler_correct (handle_MAKEBLOCK3 t) f_instr_MAKEBLOCK3
      (heap_alloc_with_stores 3 (Z.of_nat t) alloc_store_3
       /\p code_at (Int.repr (Z.of_nat t)))
      (fun _ s => match s.(Machine.stack) with _ :: _ :: _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEBLOCK :
    forall (t size : nat), (size >= 1)%nat ->
    handler_correct (handle_MAKEBLOCK t size) f_instr_MAKEBLOCK
      (makeblock_step_pre t size)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MAKEFLOATBLOCK :
    forall (n : nat), (n >= 1)%nat ->
    handler_correct (handle_MAKEFLOATBLOCK n) f_instr_MAKEFLOATBLOCK
      (makefloatblock_step_pre n)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MODINT :
    handler_correct handle_MODINT f_instr_MODINT
      divmod_safe
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int b :: _ => Z.eqb b 0 = true | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_MULINT :
    handler_correct handle_MULINT f_instr_MULINT
      (accu_is_long /\p stack_head_is_long)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_NEGINT :
    handler_correct handle_NEGINT f_instr_NEGINT
      accu_is_long
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
      (closure_offset_pre 2 24)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETCLOSUREM2 :
    handler_correct (handle_OFFSETCLOSURE (-2)) f_instr_OFFSETCLOSUREM2
      (closure_offset_pre (-2) (-24))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETCLOSURE :
    forall n,
    handler_correct (handle_OFFSETCLOSURE n) f_instr_OFFSETCLOSURE
      (offsetclosure_pre n)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETINT :
    forall ofs, Int.min_signed <= ofs * 2 <= Int.max_signed ->
    handler_correct (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (code_at (Int.repr ofs) /\p accu_is_long)
      (fun _ s => match s.(Machine.accu) with Val_int _ => False | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_OFFSETREF :
    forall n,
    handler_correct (handle_OFFSETREF n) f_instr_OFFSETREF
      (fun _ => offsetref_heap_pre n)
      (fun _ s => match s.(Machine.accu) with
                  | Val_ptr addr =>
                    match heap_lookup s.(Machine.hp) addr with
                    | Some (_, Val_int _ :: _) => False
                    | _ => True
                    end
                  | _ => True
                  end)
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_ORINT :
    handler_correct handle_ORINT f_instr_ORINT
      (accu_is_long /\p stack_head_is_long)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PERFORM :
    handler_correct handle_PERFORM f_instr_PERFORM
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_POPTRAP :
    handler_correct (handle_POPTRAP) f_instr_POPTRAP
      poptrap_step_pre
      (fun msg _ => msg = "POPTRAP: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_POP :
    forall n,
    Z.of_nat n < Int.half_modulus ->
    handler_correct (handle_POP n) f_instr_POP
      ((code_at (Int.repr (Z.of_nat n)) /\p code_ne_struct) /\p stack_length_ge n)
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
      (sp_at_least 16 /\p code_at (Int.repr (Z.of_nat t)))
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
      (pushconstint_step_pre n)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC1 :
    handler_correct (handle_PUSHENVACC 1) f_instr_PUSHENVACC1
      (pushenvacc_step_pre 1)
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC2 :
    handler_correct (handle_PUSHENVACC 2) f_instr_PUSHENVACC2
      (pushenvacc_step_pre 2)
      (fun _ s => field_or_heap s s.(Machine.env) 2 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC3 :
    handler_correct (handle_PUSHENVACC 3) f_instr_PUSHENVACC3
      (pushenvacc_step_pre 3)
      (fun _ s => field_or_heap s s.(Machine.env) 3 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC4 :
    handler_correct (handle_PUSHENVACC 4) f_instr_PUSHENVACC4
      (pushenvacc_step_pre 4)
      (fun _ s => field_or_heap s s.(Machine.env) 4 = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHENVACC :
    forall n,
    handler_correct (handle_PUSHENVACC n) f_instr_PUSHENVACC
      (pushenvacc_generic_step_pre n)
      (fun _ s => field_or_heap s s.(Machine.env) n = None)
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHGETGLOBALFIELD :
    forall n p,
    handler_correct (handle_PUSHGETGLOBALFIELD n p) f_instr_PUSHGETGLOBALFIELD
      (pushgetglobalfield_step_pre n p)
      (fun msg s =>
         nth_error s.(Machine.global) n = None \/
         (exists glob, nth_error s.(Machine.global) n = Some glob /\
                       field_or_heap s glob p = None))
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHGETGLOBAL :
    forall n,
    0 <= Z.of_nat n <= Int.max_signed ->
    handler_correct (handle_PUSHGETGLOBAL n) f_instr_PUSHGETGLOBAL
      ((code_at (Int.repr (Z.of_nat n)) /\p global_offset_safe n) /\p sp_at_least 16)
      (fun _ s => nth_error s.(Machine.global) n = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSURE0 :
    handler_correct (handle_PUSHOFFSETCLOSURE 0) f_instr_PUSHOFFSETCLOSURE0
      (sp_at_least 16)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSURE2 :
    handler_correct (handle_PUSHOFFSETCLOSURE 2) f_instr_PUSHOFFSETCLOSURE2
      (sp_at_least 16 /\p closure_offset_pre 2 24)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSUREM2 :
    handler_correct (handle_PUSHOFFSETCLOSURE (-2)) f_instr_PUSHOFFSETCLOSUREM2
      (sp_at_least 16 /\p closure_offset_pre (-2) (-24))
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHOFFSETCLOSURE :
    forall ofs,
    handler_correct (handle_PUSHOFFSETCLOSURE ofs) f_instr_PUSHOFFSETCLOSURE
      (pushoffsetclosure_step_pre ofs)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSHTRAP :
    forall handler_pc,
    handler_correct (handle_PUSHTRAP handler_pc) f_instr_PUSHTRAP
      (pushtrap_step_pre handler_pc)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSH_RETADDR :
    forall ret_addr,
    handler_correct (handle_PUSH_RETADDR ret_addr) f_instr_PUSH_RETADDR
      (push_retaddr_step_pre ret_addr)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_PUSH :
    handler_correct handle_PUSH f_instr_PUSH
      (sp_at_least 16)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RAISE_NOTRACE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE_NOTRACE
      raise_step_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RAISE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RAISE
      raise_step_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_REPERFORMTERM :
    handler_correct handle_REPERFORMTERM f_instr_REPERFORMTERM
      no_pre
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RERAISE :
    handler_correct (fun _pc s => do_raise s.(accu) s) f_instr_RERAISE
      raise_step_pre
      (fun msg _ => msg = "unhandled exception"%string \/ msg = "RAISE: malformed trap frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_RESTART :
    handler_correct handle_RESTART f_instr_RESTART
      restart_step_pre
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
      (return_step_pre stacksize)
      (fun msg _ => msg = "RETURN: accu is not a closure"%string \/ msg = "RETURN: malformed return frame"%string) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETBYTESCHAR :
    handler_correct handle_SETBYTESCHAR f_instr_SETBYTESCHAR
      setbyteschar_step_pre
      (fun _ s =>
         match s.(Machine.stack) with
         | Val_int idx :: Val_int newchar :: _ =>
             match s.(Machine.accu) with
             | Val_ptr addr =>
               match heap_lookup s.(Machine.hp) addr with
               | Some (_, fields) =>
                   set_nth fields (Z.to_nat idx) (Val_int newchar) = None
               | None => True
               end
             | _ => True
             end
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD0 :
    handler_correct (handle_SETFIELD 0) f_instr_SETFIELD0
      (setfield_heap_pre 0)
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 0 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD1 :
    handler_correct (handle_SETFIELD 1) f_instr_SETFIELD1
      (setfield_heap_pre 1)
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 1 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD2 :
    handler_correct (handle_SETFIELD 2) f_instr_SETFIELD2
      (setfield_heap_pre 2)
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 2 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD3 :
    handler_correct (handle_SETFIELD 3) f_instr_SETFIELD3
      (setfield_heap_pre 3)
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields 3 (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFIELD :
    forall n,
    handler_correct (handle_SETFIELD n) f_instr_SETFIELD
      (setfield_step_pre n)
      (fun _ s => match s.(Machine.stack) with | newval :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields n newval = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETFLOATFIELD :
    forall n,
    handler_correct (handle_SETFLOATFIELD n) f_instr_SETFLOATFIELD
      (setfloatfield_step_pre n)
      (fun _ s => match s.(Machine.stack) with | _ :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields n (hd (Val_int 0) s.(Machine.stack)) = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETGLOBAL :
    forall n,
    handler_correct (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (setglobal_step_pre n)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SETVECTITEM :
    handler_correct handle_SETVECTITEM f_instr_SETVECTITEM
      setvectitem_pre
      (fun _ s => match s.(Machine.stack) with | Val_int idx :: newval :: _ => match s.(Machine.accu) with | Val_ptr addr => match heap_lookup s.(Machine.hp) addr with | Some (_, fields) => set_nth fields (Z.to_nat idx) newval = None | None => True end | _ => True end | _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_STOP :
    handler_correct (fun _ => handle_STOP) f_instr_STOP
      no_pre
      (fun _ _ => False) (fun _ => True) (fun _ _ _ => False).

  Parameter correct_SUBINT :
    handler_correct handle_SUBINT f_instr_SUBINT
      (accu_is_long /\p stack_head_is_long)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_SWITCH :
    forall (_nc _nb : nat) (const_targets block_targets : list Z),
    handler_correct (fun _ s => handle_SWITCH _nc _nb const_targets block_targets s) f_instr_SWITCH
      (switch_step_pre _nc _nb const_targets block_targets)
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
      (fun _ => vectlength_pre)
      (fun _ s => size_or_heap s s.(Machine.accu) = None) (fun _ => False) (fun _ _ _ => False).

  Parameter correct_XORINT :
    handler_correct handle_XORINT f_instr_XORINT
      (accu_is_long /\p stack_head_is_long)
      (fun _ s => match s.(Machine.accu), s.(Machine.stack) with | Val_int _, Val_int _ :: _ => False | _, _ => True end) (fun _ => False) (fun _ _ _ => False).

End InstructVerificationSpec.