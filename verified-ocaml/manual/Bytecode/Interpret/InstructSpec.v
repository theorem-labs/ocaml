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
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Helpers Handlers Dispatch HandleInstrSpec.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.

(* External function ident not produced by clightgen (caml_modify is a
   runtime helper referenced by SETFIELD / SETVECTITEM specs but not
   directly called from the extracted handler C code). *)
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Definition _caml_modify : ident := $"caml_modify".
Local Close Scope clight_scope.

(* ================================================================== *)
(* Clight environment                                                  *)
(* ================================================================== *)

Definition clight_ge : Clight.genv :=
  {| genv_genv := Globalenvs.Genv.globalenv prog;
     genv_cenv := prog_comp_env prog |}.

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
(* Loop AST fragments used by step_pre definitions below and by        *)
(* MAKEBLOCK_correct.v / MAKEFLOATBLOCK_correct.v.  Kept here (not in  *)
(* instruct_handlers.v) because instruct_handlers.v is auto-generated  *)
(* by clightgen and overwritten on regeneration.                       *)
(* ================================================================== *)

(* MAKEBLOCK field copy loop *)
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

(* MAKEFLOATBLOCK field copy loop *)
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

(* Parameterized accumulator check — auditor reads one definition for all 5 variants. *)
Inductive accu_kind := ak_long | ak_signed_range | ak_unsigned_range | ak_bool | ak_immediate.

Definition accu_check (k : accu_kind) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  match k with
  | ak_long => accu_is_long
  | ak_signed_range => accu_signed_int
  | ak_unsigned_range => accu_unsigned_int
  | ak_bool => accu_is_bool
  | ak_immediate => accu_is_immediate
  end.

(* Parameterized arithmetic safety — auditor reads one definition for all 5 variants. *)
Inductive arith_kind := arith_unsigned | arith_signed | arith_divmod | arith_shift | arith_ucompare.

Definition arith_safe (k : arith_kind) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  match k with
  | arith_unsigned => int_op_safe
  | arith_signed => signed_int_op_safe
  | arith_divmod => divmod_safe
  | arith_shift => shift_in_range
  | arith_ucompare => unsigned_ints_safe
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


Definition caml_modify_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default).

Definition caml_modify_fundef : Ctypes.fundef function :=
  Ctypes.External caml_modify_ef ((tptr tlong) :: tlong :: nil) tvoid cc_default.

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
       Genv.find_funct clight_ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
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
           external_call caml_modify_ef clight_ge
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

(* Binary search midpoint computation: mi = ((li + hi) >> 1) | 1 *)
Definition search_midpoint (li hi : int) : int :=
  Int.or (Int.shr (Int.add li hi) (Int.repr 1)) (Int.repr 1).

(* Binary search trace for method table lookup.
   Records the sequence of comparisons the C binary search loop performs.
   - m: memory state (unchanged by the read-only loop)
   - accu_v: the value being searched for (loaded from s->accu)
   - meths_b, meths_ofs: method table location
   - li, hi: current search bounds (int)
   - final: the li value when the loop terminates *)
Inductive method_search_trace (m : mem) (accu_v : val)
    (meths_b : block) (meths_ofs : ptrofs) : int -> int -> int -> Prop :=
| mst_done : forall li hi,
    Int.lt li hi = false ->
    method_search_trace m accu_v meths_b meths_ofs li hi li
| mst_lt : forall li hi tag_v final,
    let mi := search_midpoint li hi in
    Int.lt li hi = true ->
    Mem.load Mint64 m meths_b
      (Ptrofs.unsigned (Ptrofs.add meths_ofs
         (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed mi)))) = Some tag_v ->
    Val.cmpl Clt accu_v tag_v = Some (Val.of_bool true) ->
    method_search_trace m accu_v meths_b meths_ofs
      li (Int.sub mi (Int.repr 2)) final ->
    method_search_trace m accu_v meths_b meths_ofs li hi final
| mst_ge : forall li hi tag_v final,
    let mi := search_midpoint li hi in
    Int.lt li hi = true ->
    Mem.load Mint64 m meths_b
      (Ptrofs.unsigned (Ptrofs.add meths_ofs
         (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed mi)))) = Some tag_v ->
    Val.cmpl Clt accu_v tag_v = Some (Val.of_bool false) ->
    method_search_trace m accu_v meths_b meths_ofs
      mi hi final ->
    method_search_trace m accu_v meths_b meths_ofs li hi final.

(* Extract all fields from a value, using the machine heap for pointers. *)
Definition value_all_fields (s : Machine.state) (v : value) : list value :=
  match v with
  | Val_block _ fs => fs
  | Val_ptr addr =>
    match heap_lookup s.(Machine.hp) addr with
    | Some (_, fs) => fs
    | None => nil
    end
  | _ => nil
  end.

(* Linear scan of method table pairs: fields are laid out as
     [method0, tag0, method1, tag1, ...]
   Scan returns the first method_fn whose paired tag matches. *)
Fixpoint method_scan (fields : list value) (tag : value) : option value :=
  match fields with
  | nil => None
  | _ :: nil => None
  | method_fn :: tag_val :: rest =>
    if value_eqb tag_val tag then Some method_fn
    else method_scan rest tag
  end.

Definition getdynmet_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  forall obj rest,
    s.(Machine.stack) = obj :: rest ->
    forall class_tbl,
      field_or_heap s obj 0 = Some class_tbl ->
      forall method_fn,
        method_scan (skipn 2 (value_all_fields s class_tbl)) s.(Machine.accu) = Some method_fn ->
    forall obj_cv,
      val_repr hm cb co obj obj_cv ->
      exists obj_b obj_ofs meths_v meths_b meths_ofs hi_v
             final_li meth_cv,
        obj_cv = Vptr obj_b obj_ofs /\
        Mem.load Mint64 m obj_b (Ptrofs.unsigned obj_ofs) = Some meths_v /\
        meths_v = Vptr meths_b meths_ofs /\
        Mem.load Mint64 m meths_b (Ptrofs.unsigned meths_ofs) = Some (Vlong hi_v) /\
        Mem.load Mint64 m meths_b
          (Ptrofs.unsigned (Ptrofs.add meths_ofs
            (Ptrofs.mul (Ptrofs.repr 8)
              (ptrofs_of_int Signed (Int.sub final_li (Int.repr 1))))))
          = Some meth_cv /\
        val_repr hm cb co method_fn meth_cv /\
        (forall accu_cv,
           Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_cv ->
           method_search_trace m accu_cv meths_b meths_ofs
             (Int.repr 3)
             (Int.repr (Int64.unsigned hi_v))
             final_li).


Definition getpubmet_pre
    (tag : Z) (_ : Clight.env) (m : mem)
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
  (forall class_tbl,
    field_or_heap s s.(Machine.accu) 0 = Some class_tbl ->
    forall method_fn,
      method_scan (skipn 2 (value_all_fields s class_tbl)) (Val_int tag) = Some method_fn ->
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
        Mem.load Mint64 m meths_b
          (Ptrofs.unsigned (Ptrofs.add meths_ofs
            (Ptrofs.mul (Ptrofs.repr 8)
              (ptrofs_of_int Signed (Int.sub final_li (Int.repr 1))))))
          = Some meth_cv /\
        val_repr hm cb co method_fn meth_cv /\
        method_search_trace m (Vlong (Int64.repr (tag * 2 + 1)))
          meths_b meths_ofs
          (Int.repr 3)
          (Int.repr (Int64.unsigned hi_v))
          final_li).




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
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  get_code_ptr_s s s.(Machine.accu) <> None /\
  (3 <= slotsize)%nat /\
  (slotsize <= Datatypes.length (Machine.stack s))%nat /\
  Z.of_nat (extra_args s) <= Int64.max_unsigned /\
  Z.of_nat (extra_args s) <= Int64.max_signed.

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

Definition closurerec_general_step_pre (nfuncs nvars : nat) (code_offsets : list Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let sp_b := ar_stack_block ard in
  let hm := ar_heap_map ard in
  let blksize := (3 * nfuncs - 1 + nvars)%nat in
  (* e does not bind heap_alloc *)
  e ! _heap_alloc = None /\
  (* Code buffer: nfuncs at current PC *)
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat nfuncs))) /\
  (* Code buffer: nvars at PC+1 *)
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat nvars))) /\
  (* Code offsets match nfuncs in length *)
  length code_offsets = nfuncs /\
  (* Code buffer: code_offsets[i] at PC+2+i, each in signed int range *)
  (forall i ofs, nth_error code_offsets i = Some ofs ->
     Mem.load Mint32 m cb
       (Ptrofs.unsigned (Ptrofs.add co
          (Ptrofs.repr ((Machine.pc s + 2 + Z.of_nat i) * sizeof_code_t))))
     = Some (Vint (Int.repr ofs)) /\
     Int.min_signed <= ofs <= Int.max_signed) /\
  (* nfuncs >= 1 *)
  (nfuncs >= 1)%nat /\
  (* blksize and nfuncs in int range *)
  (0 <= Z.of_nat blksize <= Int.max_signed) /\
  (0 <= Z.of_nat nfuncs <= Int.max_signed) /\
  (0 <= Z.of_nat nvars <= Int.max_signed) /\
  (* nvars bounded by stack length *)
  (nvars <= S (length (Machine.stack s)))%nat /\
  (* Heap map freshness *)
  hm (next_addr s) = None /\
  (* Global block valid *)
  Mem.valid_block m gb /\
  (* Genv lookup for heap_alloc *)
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  (* heap_alloc spec: allocate blksize fields with tag 247 *)
  (forall m',
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr (Z.of_nat blksize)) :: Vlong (Int64.repr 247) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v,
          Mem.load chunk m' b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p) /\
       (* Field 0 storable (code ptr) *)
       (forall cv, exists m_s0,
          Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_s0 /\
          Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) =
            Some (Val.load_result Mint64 cv) /\
          (forall b ofs chunk v, b <> new_b ->
             Mem.load chunk m_alloc b ofs = Some v ->
             Mem.load chunk m_s0 b ofs = Some v) /\
          (* Field 1 storable after field 0 (closinfo) *)
          (forall cv1, exists m_s1,
             Mem.store Mint64 m_s0 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_s1 /\
             Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
               Some (Val.load_result Mint64 cv1) /\
             (* Load at field 0 preserved *)
             (forall v0, Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) = Some v0 ->
                Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned new_ofs) = Some v0) /\
             (forall b ofs chunk v, b <> new_b ->
                Mem.load chunk m_s0 b ofs = Some v ->
                Mem.load chunk m_s1 b ofs = Some v) /\
             (forall b ofs k p,
                Mem.valid_block m_s0 b -> Mem.perm m_s0 b ofs k p ->
                Mem.perm m_s1 b ofs k p)))) /\
  (* sp writable below current sp for pushes *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 8 * Z.of_nat (nfuncs + 1) /\
     (align_chunk Mint64 | Ptrofs.unsigned sp_ofs - 8) /\
     Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)) < Ptrofs.modulus).

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
  (forall le_pre m_field0 new_b new_ofs sp_b0 sp_ofs,
     le_pre ! _s = Some (Vptr sb so) ->
     le_pre ! _block = Some (Vptr new_b new_ofs) ->
     le_pre ! _wosize = Some (Vlong (Int64.repr (Z.of_nat size))) ->
     new_b <> sb -> new_b <> sp_b0 -> new_b <> gb -> new_b <> cb ->
     Mem.load Mint64 m_field0 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b0 sp_ofs) ->
     stack_repr hm cb co m_field0 (Machine.stack s) sp_b0 sp_ofs ->
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
         Some (Vptr sp_b0 sp_ofs_loop) /\
       stack_repr hm cb co m_loop (skipn (Nat.sub size 1) (Machine.stack s))
         sp_b0 sp_ofs_loop /\
       Ptrofs.unsigned sp_ofs_loop >= 8 /\
       (align_chunk Mint64 | Ptrofs.unsigned sp_ofs_loop) /\
       Ptrofs.unsigned sp_ofs_loop + 8 * Z.of_nat (length (skipn (Nat.sub size 1) (Machine.stack s))) < Ptrofs.modulus /\
       Ptrofs.unsigned sp_ofs_loop + 8 * Z.of_nat (length (skipn (Nat.sub size 1) (Machine.stack s))) <=
         Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)) /\
       (forall b ofs k p,
          Mem.perm m_field0 b ofs k p ->
          Mem.perm m_loop b ofs k p) /\
       (forall b ofs chunk v,
          b <> sb -> b <> sp_b0 -> b <> new_b ->
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
  (forall le_pre m_alloc0 new_b new_ofs sp_b0 sp_ofs,
     le_pre ! _s = Some (Vptr sb so) ->
     le_pre ! _block = Some (Vptr new_b new_ofs) ->
     le_pre ! _size = Some (Vlong (Int64.repr (Z.of_nat n))) ->
     new_b <> sb -> new_b <> sp_b0 -> new_b <> gb -> new_b <> cb ->
     Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 8) = Some (Vptr sp_b0 sp_ofs) ->
     val_repr hm cb co (Machine.accu s) (Vptr sp_b0 sp_ofs) ->
     False) /\
  (forall le_pre m_alloc0 new_b new_ofs sp_b0 sp_ofs accu_v0,
     le_pre ! _s = Some (Vptr sb so) ->
     le_pre ! _block = Some (Vptr new_b new_ofs) ->
     le_pre ! _size = Some (Vlong (Int64.repr (Z.of_nat n))) ->
     new_b <> sb -> new_b <> sp_b0 -> new_b <> gb -> new_b <> cb ->
     Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 8) = Some accu_v0 ->
     val_repr hm cb co (Machine.accu s) accu_v0 ->
     Mem.load Mint64 m_alloc0 sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b0 sp_ofs) ->
     stack_repr hm cb co m_alloc0 (Machine.stack s) sp_b0 sp_ofs ->
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
         Some (Vptr sp_b0 sp_ofs_out) /\
       stack_repr hm cb co m_out (skipn (Nat.sub n 1) (Machine.stack s))
         sp_b0 sp_ofs_out /\
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

(* CLOSURE general step_pre: for handle_CLOSURE nvars code_ofs with arbitrary nvars. *)
Definition closure_general_step_pre (nvars : nat) (code_ofs : Z)
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let hm := ar_heap_map ard in
  (* e does not bind heap_alloc *)
  e ! _heap_alloc = None /\
  (* Code buffer: nvars at current PC *)
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
  = Some (Vint (Int.repr (Z.of_nat nvars))) /\
  (* Code buffer: code_ofs at PC+1 *)
  Mem.load Mint32 m cb
    (Ptrofs.unsigned (Ptrofs.add co
       (Ptrofs.repr ((Machine.pc s + 1) * sizeof_code_t))))
  = Some (Vint (Int.repr code_ofs)) /\
  (* code_ofs fits in signed int range *)
  (Int.min_signed <= code_ofs <= Int.max_signed) /\
  (* 2+nvars fits in signed int range (needed for (long)(2+nvars) cast) *)
  (0 <= Z.of_nat (2 + nvars) <= Int.max_signed) /\
  (* nvars bounded by stack length: needed for skipn nvars (accu :: stack) to be valid *)
  (nvars <= S (length (Machine.stack s)))%nat /\
  (* Heap map freshness *)
  hm (next_addr s) = None /\
  (* Global block valid *)
  Mem.valid_block m gb /\
  (* Genv lookup for heap_alloc *)
  (exists b_ha,
     Genv.find_symbol (genv_genv clight_ge) _heap_alloc = Some b_ha /\
     Genv.find_funct (genv_genv clight_ge) (Vptr b_ha Ptrofs.zero) =
       Some heap_alloc_fundef) /\
  (* heap_alloc spec: allocate (2+nvars) fields with tag 247 *)
  (forall m',
     exists m_alloc new_b new_ofs,
       external_call heap_alloc_ef
         (Genv.to_senv (genv_genv clight_ge))
         (Vptr sb so :: Vlong (Int64.repr (Z.of_nat (2 + nvars))) :: Vlong (Int64.repr 247) :: nil)
         m' E0 (Vptr new_b new_ofs) m_alloc /\
       (forall b, Mem.valid_block m' b -> new_b <> b) /\
       (forall b ofs chunk v,
          Mem.load chunk m' b ofs = Some v -> b <> new_b ->
          Mem.load chunk m_alloc b ofs = Some v) /\
       (forall b ofs k p,
          Mem.valid_block m' b -> Mem.perm m' b ofs k p ->
          Mem.perm m_alloc b ofs k p) /\
       (* Field 0 storable (code ptr) *)
       (forall cv, exists m_s0,
          Mem.store Mint64 m_alloc new_b (Ptrofs.unsigned new_ofs) cv = Some m_s0 /\
          Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) =
            Some (Val.load_result Mint64 cv) /\
          (forall b ofs chunk v, b <> new_b ->
             Mem.load chunk m_alloc b ofs = Some v ->
             Mem.load chunk m_s0 b ofs = Some v) /\
          (* Field 1 storable after field 0 (closinfo) *)
          (forall cv1, exists m_s1,
             Mem.store Mint64 m_s0 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) cv1 = Some m_s1 /\
             Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned (Ptrofs.add new_ofs (Ptrofs.repr 8))) =
               Some (Val.load_result Mint64 cv1) /\
             (* Load at field 0 preserved *)
             (forall v0, Mem.load Mint64 m_s0 new_b (Ptrofs.unsigned new_ofs) = Some v0 ->
                Mem.load Mint64 m_s1 new_b (Ptrofs.unsigned new_ofs) = Some v0) /\
             (forall b ofs chunk v, b <> new_b ->
                Mem.load chunk m_s0 b ofs = Some v ->
                Mem.load chunk m_s1 b ofs = Some v) /\
             (forall b ofs k p,
                Mem.valid_block m_s0 b -> Mem.perm m_s0 b ofs k p ->
                Mem.perm m_s1 b ofs k p))) /\
       Mem.range_perm m_alloc new_b (Ptrofs.unsigned new_ofs)
         (Ptrofs.unsigned new_ofs + 8 * Z.of_nat (2 + nvars)) Cur Writable /\
       (align_chunk Mint64 | Ptrofs.unsigned new_ofs) /\
       Ptrofs.unsigned new_ofs + 8 * Z.of_nat (2 + nvars) < Ptrofs.modulus).

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
     Genv.find_funct clight_ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
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
           external_call caml_modify_ef clight_ge
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
     Genv.find_funct clight_ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
  (forall accu_v,
     val_repr hm cb co (Machine.accu s) accu_v ->
     exists m_cm,
       external_call caml_modify_ef clight_ge
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
(* Per-instruction spec dispatch functions                              *)
(*                                                                      *)
(* Six definitions mapping each instruction to the corresponding        *)
(* argument of [handler_correct]:                                       *)
(*   instr_wfb   — bool well-formedness guard on operands               *)
(*   clight_of   — Clight function                                      *)
(*   pre_of      — step precondition (inner, without WF conjunction)    *)
(*   P_error_of  — tautological: handler s.(pc) s = Error msg           *)
(*   P_halt_of   — wfb /\ (STOP -> True | _ -> False)                   *)
(*   P_ccall_of  — wfb /\ (C_CALL -> True | _ -> False)                 *)
(*                                                                      *)
(* The bridge lemma [handler_correct_of_parameters] proves:             *)
(*   forall i, handler_correct (handle_instr i) (clight_of i)          *)
(*     (pre_of i) (P_error_of i) (P_halt_of i) (P_ccall_of i)          *)
(* ================================================================== *)

(* handler_correct_absorb_wfb removed — no longer needed after uniformizing
   InstructVerificationFineGrainedSpec parameters to use dispatch functions directly. *)

Definition instr_wfb (i : instruction) : bool :=
  match i with
  | ACC n => (Z.of_nat n <? Int.half_modulus)%Z
  | PUSH => true
  | PUSHACC n => match n with 1%nat|2%nat|3%nat|4%nat|5%nat|6%nat|7%nat => true | _ => false end
  | POP n => (Z.of_nat n <? Int.half_modulus)%Z
  | ASSIGN _ => true
  | ENVACC n => (Z.of_nat n <? Int.half_modulus)%Z
  | PUSHENVACC _ => true
  | PUSH_RETADDR _ => true
  | APPLY _ => true
  | APPLY1 => true | APPLY2 => true | APPLY3 => true
  | APPTERM _ _ => true
  | APPTERM1 _ => true | APPTERM2 _ => true | APPTERM3 _ => true
  | RETURN _ => true
  | RESTART => true
  | GRAB _ => true
  | CLOSURE nvars code_ofs =>
      ((0 <=? Z.of_nat (2 + nvars)) && (Z.of_nat (2 + nvars) <=? Int.max_signed) &&
       (Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z
  | CLOSUREREC nf nv co =>
      match nf, nv, co with
      | 1%nat, 0%nat, (code_ofs :: nil)%list =>
          ((Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z
      | _, _, _ => false
      end
  | OFFSETCLOSURE _ => true | PUSHOFFSETCLOSURE _ => true
  | GETGLOBAL n => ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z
  | PUSHGETGLOBAL n => ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z
  | GETGLOBALFIELD _ _ => true | PUSHGETGLOBALFIELD _ _ => true
  | SETGLOBAL _ => true
  | ATOM t => (Z.of_nat t <=? 2097151)%Z
  | PUSHATOM t => (Z.of_nat t <=? 2097151)%Z
  | MAKEBLOCK _ size => (1 <=? size)%nat
  | MAKEBLOCK1 t => ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z
  | MAKEBLOCK2 t => ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z
  | MAKEBLOCK3 t => ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z
  | MAKEFLOATBLOCK n => (1 <=? n)%nat
  | GETFIELD n => ((Int.min_signed <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z
  | GETFLOATFIELD _ => true
  | SETFIELD _ => true | SETFLOATFIELD _ => true
  | VECTLENGTH => true | GETVECTITEM => true | SETVECTITEM => true
  | GETBYTESCHAR => true | SETBYTESCHAR => true | GETSTRINGCHAR => true
  | BRANCH _ => true | BRANCHIF _ => true | BRANCHIFNOT _ => true
  | SWITCH _ _ _ _ => true
  | BOOLNOT => true
  | PUSHTRAP _ => true | POPTRAP => true
  | RAISE => true | RERAISE => true | RAISE_NOTRACE => true
  | CHECK_SIGNALS => true
  | C_CALL _ _ => true
  | CONSTINT n => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | PUSHCONSTINT _ => true
  | NEGINT => true | ADDINT => true | SUBINT => true
  | MULINT => true | DIVINT => true | MODINT => true
  | ANDINT => true | ORINT => true | XORINT => true
  | LSLINT => true | LSRINT => true | ASRINT => true
  | EQ => true | NEQ => true
  | LTINT => true | LEINT => true | GTINT => true | GEINT => true
  | OFFSETINT ofs => ((Int.min_signed <=? ofs * 2) && (ofs * 2 <=? Int.max_signed))%Z
  | OFFSETREF _ => true
  | ISINT => true
  | GETMETHOD => true | GETPUBMET _ => true | GETDYNMET => true
  | BEQ n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BNEQ n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BLTINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BLEINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BGTINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BGEINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | ULTINT => true | UGEINT => true
  | BULTINT n _ => ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BUGEINT n _ => ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | STOP => true
  end.

Definition clight_of (i : instruction) : function :=
  match i with
  | ACC _ => f_instr_ACC
  | PUSH => f_instr_PUSH
  | PUSHACC n =>
      match n with
      | 1%nat => f_instr_PUSHACC1 | 2%nat => f_instr_PUSHACC2
      | 3%nat => f_instr_PUSHACC3 | 4%nat => f_instr_PUSHACC4
      | 5%nat => f_instr_PUSHACC5 | 6%nat => f_instr_PUSHACC6
      | 7%nat => f_instr_PUSHACC7 | _ => f_instr_PUSHACC1
      end
  | POP _ => f_instr_POP
  | ASSIGN _ => f_instr_ASSIGN
  | ENVACC _ => f_instr_ENVACC
  | PUSHENVACC _ => f_instr_PUSHENVACC
  | PUSH_RETADDR _ => f_instr_PUSH_RETADDR
  | APPLY _ => f_instr_APPLY
  | APPLY1 => f_instr_APPLY1
  | APPLY2 => f_instr_APPLY2
  | APPLY3 => f_instr_APPLY3
  | APPTERM _ _ => f_instr_APPTERM
  | APPTERM1 _ => f_instr_APPTERM1
  | APPTERM2 _ => f_instr_APPTERM2
  | APPTERM3 _ => f_instr_APPTERM3
  | RETURN _ => f_instr_RETURN
  | RESTART => f_instr_RESTART
  | GRAB _ => f_instr_GRAB
  | CLOSURE _ _ => f_instr_CLOSURE
  | CLOSUREREC _ _ _ => f_instr_CLOSUREREC
  | OFFSETCLOSURE _ => f_instr_OFFSETCLOSURE
  | PUSHOFFSETCLOSURE _ => f_instr_PUSHOFFSETCLOSURE
  | GETGLOBAL _ => f_instr_GETGLOBAL
  | PUSHGETGLOBAL _ => f_instr_PUSHGETGLOBAL
  | GETGLOBALFIELD _ _ => f_instr_GETGLOBALFIELD
  | PUSHGETGLOBALFIELD _ _ => f_instr_PUSHGETGLOBALFIELD
  | SETGLOBAL _ => f_instr_SETGLOBAL
  | ATOM _ => f_instr_ATOM
  | PUSHATOM _ => f_instr_PUSHATOM
  | MAKEBLOCK _ _ => f_instr_MAKEBLOCK
  | MAKEBLOCK1 _ => f_instr_MAKEBLOCK1
  | MAKEBLOCK2 _ => f_instr_MAKEBLOCK2
  | MAKEBLOCK3 _ => f_instr_MAKEBLOCK3
  | MAKEFLOATBLOCK _ => f_instr_MAKEFLOATBLOCK
  | GETFIELD _ => f_instr_GETFIELD
  | GETFLOATFIELD _ => f_instr_GETFLOATFIELD
  | SETFIELD _ => f_instr_SETFIELD
  | SETFLOATFIELD _ => f_instr_SETFLOATFIELD
  | VECTLENGTH => f_instr_VECTLENGTH
  | GETVECTITEM => f_instr_GETVECTITEM
  | SETVECTITEM => f_instr_SETVECTITEM
  | GETBYTESCHAR => f_instr_GETBYTESCHAR
  | SETBYTESCHAR => f_instr_SETBYTESCHAR
  | GETSTRINGCHAR => f_instr_GETSTRINGCHAR
  | BRANCH _ => f_instr_BRANCH
  | BRANCHIF _ => f_instr_BRANCHIF
  | BRANCHIFNOT _ => f_instr_BRANCHIFNOT
  | SWITCH _ _ _ _ => f_instr_SWITCH
  | BOOLNOT => f_instr_BOOLNOT
  | PUSHTRAP _ => f_instr_PUSHTRAP
  | POPTRAP => f_instr_POPTRAP
  | RAISE => f_instr_RAISE
  | RERAISE => f_instr_RERAISE
  | RAISE_NOTRACE => f_instr_RAISE_NOTRACE
  | CHECK_SIGNALS => f_instr_CHECK_SIGNALS
  | C_CALL _ _ => f_instr_C_CALLN
  | CONSTINT _ => f_instr_CONSTINT
  | PUSHCONSTINT _ => f_instr_PUSHCONSTINT
  | NEGINT => f_instr_NEGINT
  | ADDINT => f_instr_ADDINT
  | SUBINT => f_instr_SUBINT
  | MULINT => f_instr_MULINT
  | DIVINT => f_instr_DIVINT
  | MODINT => f_instr_MODINT
  | ANDINT => f_instr_ANDINT
  | ORINT => f_instr_ORINT
  | XORINT => f_instr_XORINT
  | LSLINT => f_instr_LSLINT
  | LSRINT => f_instr_LSRINT
  | ASRINT => f_instr_ASRINT
  | EQ => f_instr_EQ
  | NEQ => f_instr_NEQ
  | LTINT => f_instr_LTINT
  | LEINT => f_instr_LEINT
  | GTINT => f_instr_GTINT
  | GEINT => f_instr_GEINT
  | OFFSETINT _ => f_instr_OFFSETINT
  | OFFSETREF _ => f_instr_OFFSETREF
  | ISINT => f_instr_ISINT
  | GETMETHOD => f_instr_GETMETHOD
  | GETPUBMET _ => f_instr_GETPUBMET
  | GETDYNMET => f_instr_GETDYNMET
  | BEQ _ _ => f_instr_BEQ
  | BNEQ _ _ => f_instr_BNEQ
  | BLTINT _ _ => f_instr_BLTINT
  | BLEINT _ _ => f_instr_BLEINT
  | BGTINT _ _ => f_instr_BGTINT
  | BGEINT _ _ => f_instr_BGEINT
  | ULTINT => f_instr_ULTINT
  | UGEINT => f_instr_UGEINT
  | BULTINT _ _ => f_instr_BULTINT
  | BUGEINT _ _ => f_instr_BUGEINT
  | STOP => f_instr_STOP
  end.

Definition P_halt_of (i : instruction) (v : value) : Prop :=
  instr_wfb i = true /\ match i with STOP => True | _ => False end.

Definition P_ccall_of (i : instruction) (n : nat) (args : list value) (s : state) : Prop :=
  instr_wfb i = true /\ match i with C_CALL _ _ => True | _ => False end.

Definition P_error_of (i : instruction) (msg : string) (s : state) : Prop :=
  match i with
  (* ACC: stack underflow *)
  | ACC n => nth_error s.(stack) n = None /\ msg = "ACC: stack underflow"
  (* PUSH: never errors *)
  | PUSH => False
  (* PUSHACC: stack underflow *)
  | PUSHACC n =>
    nth_error (s.(accu) :: s.(stack)) n = None /\ msg = "PUSHACC: stack underflow"
  (* POP: never errors *)
  | POP _ => False
  (* ASSIGN: stack underflow *)
  | ASSIGN n => set_nth s.(stack) n s.(accu) = None /\ msg = "ASSIGN: stack underflow"
  (* ENVACC: env access out of bounds *)
  | ENVACC n => field_or_heap s s.(env) n = None /\ msg = "ENVACC: env access out of bounds"
  (* PUSHENVACC: env access out of bounds *)
  | PUSHENVACC n => field_or_heap s s.(env) n = None /\ msg = "PUSHENVACC: env access out of bounds"
  (* PUSH_RETADDR: never errors *)
  | PUSH_RETADDR _ => False
  (* APPLY: accu is not a closure *)
  | APPLY n => get_code_ptr_s s s.(accu) = None /\ msg = "APPLY: accu is not a closure"
  (* APPLY1: stack underflow or accu not a closure *)
  | APPLY1 =>
    match s.(stack) with
    | _ :: _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPLY1: accu is not a closure"
    | _ => msg = "APPLY1: stack underflow"
    end
  (* APPLY2: stack underflow or accu not a closure *)
  | APPLY2 =>
    match s.(stack) with
    | _ :: _ :: _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPLY2: accu is not a closure"
    | _ => msg = "APPLY2: stack underflow"
    end
  (* APPLY3: stack underflow or accu not a closure *)
  | APPLY3 =>
    match s.(stack) with
    | _ :: _ :: _ :: _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPLY3: accu is not a closure"
    | _ => msg = "APPLY3: stack underflow"
    end
  (* APPTERM: accu not a closure *)
  | APPTERM _ _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPTERM: accu is not a closure"
  (* APPTERM1: stack underflow or accu not a closure *)
  | APPTERM1 slotsize =>
    match s.(stack) with
    | _ :: _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPTERM1: accu is not a closure"
    | _ => msg = "APPTERM1: stack underflow"
    end
  (* APPTERM2: stack underflow or accu not a closure *)
  | APPTERM2 slotsize =>
    match s.(stack) with
    | _ :: _ :: _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPTERM2: accu is not a closure"
    | _ => msg = "APPTERM2: stack underflow"
    end
  (* APPTERM3: stack underflow or accu not a closure *)
  | APPTERM3 slotsize =>
    match s.(stack) with
    | _ :: _ :: _ :: _ => get_code_ptr_s s s.(accu) = None /\ msg = "APPTERM3: accu is not a closure"
    | _ => msg = "APPTERM3: stack underflow"
    end
  (* RETURN: various error conditions *)
  | RETURN stacksize =>
    let stk := skipn stacksize s.(stack) in
    if Nat.ltb 0 s.(extra_args) then
      get_code_ptr_s s s.(accu) = None /\ msg = "RETURN: accu is not a closure"
    else
      match stk with
      | Val_int _ :: _ :: Val_int _ :: _ => False
      | _ => msg = "RETURN: malformed return frame"
      end
  (* RESTART: various error conditions *)
  | RESTART =>
    match s.(env) with
    | Val_closure addr ofs =>
      match heap_lookup s.(hp) addr with
      | Some (t, all_fields) =>
        if Nat.eqb t Closure_tag then
          let fields := skipn ofs all_fields in
          match nth_error fields 2 with
          | Some _ => False
          | None => msg = "RESTART: malformed closure"
          end
        else msg = "RESTART: env is not a closure"
      | None => msg = "RESTART: dangling pointer"
      end
    | Val_block t fields =>
      if Nat.eqb t Closure_tag then
        match nth_error fields 2 with
        | Some _ => False
        | None => msg = "RESTART: malformed closure"
        end
      else msg = "RESTART: env is not a closure"
    | _ => msg = "RESTART: env is not a block"
    end
  (* GRAB: malformed return frame *)
  | GRAB required =>
    if Nat.leb required s.(extra_args) then False
    else
      let num_args := S s.(extra_args) in
      let rest_stack := skipn num_args s.(stack) in
      match rest_stack with
      | Val_int _ :: _ :: Val_int _ :: _ => False
      | _ => msg = "GRAB: malformed return frame"
      end
  (* CLOSURE: never errors *)
  | CLOSURE _ _ => False
  (* CLOSUREREC: no code offsets *)
  | CLOSUREREC _ _ code_offsets =>
    match code_offsets with
    | [] => msg = "CLOSUREREC: no code offsets"
    | _ => False
    end
  (* OFFSETCLOSURE: errors when env is invalid *)
  | OFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure _ _ => False
    | Val_block _ _ =>
      if Z.eqb ofs 0 then False
      else msg = "OFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => msg = "OFFSETCLOSURE: invalid env"
    end
  (* PUSHOFFSETCLOSURE: errors when env is invalid *)
  | PUSHOFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure _ _ => False
    | Val_block _ _ =>
      if Z.eqb ofs 0 then False
      else msg = "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => msg = "PUSHOFFSETCLOSURE: invalid env"
    end
  (* GETGLOBAL: index out of bounds *)
  | GETGLOBAL n => nth_error s.(global) n = None /\ msg = "GETGLOBAL: index out of bounds"
  (* PUSHGETGLOBAL: index out of bounds *)
  | PUSHGETGLOBAL n => nth_error s.(global) n = None /\ msg = "PUSHGETGLOBAL: index out of bounds"
  (* GETGLOBALFIELD: index out of bounds or field access failed *)
  | GETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob => field_or_heap s glob p = None /\ msg = "GETGLOBALFIELD: field access failed"
    | None => msg = "GETGLOBALFIELD: index out of bounds"
    end
  (* PUSHGETGLOBALFIELD: index out of bounds or field access failed *)
  | PUSHGETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob => field_or_heap s glob p = None /\ msg = "PUSHGETGLOBALFIELD: field access failed"
    | None => msg = "PUSHGETGLOBALFIELD: index out of bounds"
    end
  (* SETGLOBAL: never errors *)
  | SETGLOBAL _ => False
  (* ATOM: never errors *)
  | ATOM _ => False
  (* PUSHATOM: never errors *)
  | PUSHATOM _ => False
  (* MAKEBLOCK: never errors *)
  | MAKEBLOCK _ _ => False
  (* MAKEBLOCK1: never errors *)
  | MAKEBLOCK1 _ => False
  (* MAKEBLOCK2: stack underflow *)
  | MAKEBLOCK2 _ =>
    match s.(stack) with
    | _ :: _ => False
    | _ => msg = "MAKEBLOCK2: stack underflow"
    end
  (* MAKEBLOCK3: stack underflow *)
  | MAKEBLOCK3 _ =>
    match s.(stack) with
    | _ :: _ :: _ => False
    | _ => msg = "MAKEBLOCK3: stack underflow"
    end
  (* MAKEFLOATBLOCK: never errors *)
  | MAKEFLOATBLOCK _ => False
  (* GETFIELD: access failed *)
  | GETFIELD n => field_or_heap s s.(accu) n = None /\ msg = "GETFIELD: access failed"
  (* GETFLOATFIELD: access failed *)
  | GETFLOATFIELD n => field_or_heap s s.(accu) n = None /\ msg = "GETFLOATFIELD: access failed"
  (* SETFIELD: various error cases *)
  | SETFIELD n =>
    match s.(stack) with
    | newval :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          set_nth fields n newval = None /\ msg = "SETFIELD: index out of bounds"
        | None => msg = "SETFIELD: dangling pointer"
        end
      | _ => msg = "SETFIELD: not a mutable block"
      end
    | _ => msg = "SETFIELD: stack underflow"
    end
  (* SETFLOATFIELD: various error cases *)
  | SETFLOATFIELD n =>
    match s.(stack) with
    | newval :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          set_nth fields n newval = None /\ msg = "SETFLOATFIELD: index out of bounds"
        | None => msg = "SETFLOATFIELD: dangling pointer"
        end
      | _ => msg = "SETFLOATFIELD: not a heap float array"
      end
    | _ => msg = "SETFLOATFIELD: stack underflow"
    end
  (* VECTLENGTH: not a block *)
  | VECTLENGTH => size_or_heap s s.(accu) = None /\ msg = "VECTLENGTH: not a block"
  (* GETVECTITEM: index out of bounds or stack underflow *)
  | GETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: _ =>
      field_or_heap s s.(accu) (Z.to_nat idx) = None /\ msg = "GETVECTITEM: index out of bounds"
    | _ => msg = "GETVECTITEM: bad index or stack underflow"
    end
  (* SETVECTITEM: various error cases *)
  | SETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: newval :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          set_nth fields (Z.to_nat idx) newval = None /\ msg = "SETVECTITEM: index out of bounds"
        | None => msg = "SETVECTITEM: dangling pointer"
        end
      | _ => msg = "SETVECTITEM: not a heap block"
      end
    | _ => msg = "SETVECTITEM: stack underflow"
    end
  (* GETBYTESCHAR/GETSTRINGCHAR: index/stack issues *)
  | GETBYTESCHAR | GETSTRINGCHAR =>
    match s.(stack) with
    | Val_int idx :: _ =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some (Val_int _) => False
      | _ => msg = "GETSTRINGCHAR: index out of bounds or not a char"
      end
    | _ => msg = "GETSTRINGCHAR: stack underflow"
    end
  (* SETBYTESCHAR: various error cases *)
  | SETBYTESCHAR =>
    match s.(stack) with
    | Val_int idx :: Val_int newchar :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields (Z.to_nat idx) (Val_int newchar) with
          | Some _ => False
          | None => msg = "SETBYTESCHAR: index out of bounds"
          end
        | None => msg = "SETBYTESCHAR: dangling pointer"
        end
      | _ => msg = "SETBYTESCHAR: not a heap bytes"
      end
    | _ => msg = "SETBYTESCHAR: stack underflow"
    end
  (* BRANCH: never errors *)
  | BRANCH _ => False
  (* BRANCHIF: never errors *)
  | BRANCHIF _ => False
  (* BRANCHIFNOT: never errors *)
  | BRANCHIFNOT _ => False
  (* SWITCH: various error cases *)
  | SWITCH _nc _nb const_targets block_targets =>
    match s.(accu) with
    | Val_int n =>
      nth_error const_targets (Z.to_nat n) = None /\ msg = "SWITCH: constant index out of range"
    | Val_block t _ =>
      nth_error block_targets t = None /\ msg = "SWITCH: block tag out of range"
    | Val_ptr _ | Val_closure _ _ =>
      match tag_or_heap s s.(accu) with
      | Some t =>
        nth_error block_targets t = None /\ msg = "SWITCH: block tag out of range"
      | None => msg = "SWITCH: dangling pointer"
      end
    end
  (* BOOLNOT: never errors *)
  | BOOLNOT => False
  (* PUSHTRAP: never errors *)
  | PUSHTRAP _ => False
  (* POPTRAP: malformed trap frame *)
  | POPTRAP =>
    match s.(stack) with
    | _ :: Val_int _ :: _ :: _ :: _ => False
    | _ => msg = "POPTRAP: malformed trap frame"
    end
  (* RAISE/RERAISE/RAISE_NOTRACE: delegates to do_raise *)
  | RAISE | RERAISE | RAISE_NOTRACE =>
    do_raise s.(accu) s = Error msg
  (* CHECK_SIGNALS: never errors *)
  | CHECK_SIGNALS => False
  (* C_CALL: never errors (returns CCall_request) *)
  | C_CALL _ _ => False
  (* CONSTINT: never errors *)
  | CONSTINT _ => False
  (* PUSHCONSTINT: never errors *)
  | PUSHCONSTINT _ => False
  (* NEGINT: not an integer *)
  | NEGINT =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "NEGINT: not an integer"
    end
  (* ADDINT: type error or stack underflow *)
  | ADDINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "ADDINT: type error or stack underflow"
    end
  (* SUBINT: type error or stack underflow *)
  | SUBINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "SUBINT: type error or stack underflow"
    end
  (* MULINT: type error or stack underflow *)
  | MULINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "MULINT: type error or stack underflow"
    end
  (* DIVINT: type error, stack underflow, or division-by-zero raise *)
  | DIVINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int b :: _ =>
      Z.eqb b 0 = true /\ do_raise div_by_zero_exn s = Error msg
    | _, _ => msg = "DIVINT: type error or stack underflow"
    end
  (* MODINT: type error, stack underflow, or division-by-zero raise *)
  | MODINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int b :: _ =>
      Z.eqb b 0 = true /\ do_raise div_by_zero_exn s = Error msg
    | _, _ => msg = "MODINT: type error or stack underflow"
    end
  (* ANDINT: type error or stack underflow *)
  | ANDINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "ANDINT: type error or stack underflow"
    end
  (* ORINT: type error or stack underflow *)
  | ORINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "ORINT: type error or stack underflow"
    end
  (* XORINT: type error or stack underflow *)
  | XORINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "XORINT: type error or stack underflow"
    end
  (* LSLINT: type error or stack underflow *)
  | LSLINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "LSLINT: type error or stack underflow"
    end
  (* LSRINT: type error or stack underflow *)
  | LSRINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "LSRINT: type error or stack underflow"
    end
  (* ASRINT: type error or stack underflow *)
  | ASRINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "ASRINT: type error or stack underflow"
    end
  (* EQ: stack underflow *)
  | EQ =>
    match s.(stack) with
    | _ :: _ => False
    | _ => msg = "EQ: stack underflow"
    end
  (* NEQ: stack underflow *)
  | NEQ =>
    match s.(stack) with
    | _ :: _ => False
    | _ => msg = "NEQ: stack underflow"
    end
  (* LTINT: type error or stack underflow *)
  | LTINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "LTINT: type error or stack underflow"
    end
  (* LEINT: type error or stack underflow *)
  | LEINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "LEINT: type error or stack underflow"
    end
  (* GTINT: type error or stack underflow *)
  | GTINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "GTINT: type error or stack underflow"
    end
  (* GEINT: type error or stack underflow *)
  | GEINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "GEINT: type error or stack underflow"
    end
  (* OFFSETINT: not an integer *)
  | OFFSETINT _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "OFFSETINT: not an integer"
    end
  (* OFFSETREF: not a ref *)
  | OFFSETREF _ =>
    match s.(accu) with
    | Val_ptr addr =>
      match heap_lookup s.(hp) addr with
      | Some (_, Val_int _ :: _) => False
      | _ => msg = "OFFSETREF: not a ref"
      end
    | _ => msg = "OFFSETREF: not a ref"
    end
  (* ISINT: never errors *)
  | ISINT => False
  (* GETMETHOD: various error cases *)
  | GETMETHOD =>
    match s.(stack) with
    | obj :: _ =>
      match field_or_heap s obj 0 with
      | Some class_tbl =>
        match s.(accu) with
        | Val_int n =>
          field_or_heap s class_tbl (Z.to_nat n) = None /\ msg = "GETMETHOD: method not found"
        | _ => msg = "GETMETHOD: not an integer index"
        end
      | None => msg = "GETMETHOD: no class table"
      end
    | _ => msg = "GETMETHOD: stack underflow"
    end
  (* GETPUBMET: errors when method not found or no class table *)
  | GETPUBMET tag =>
    match field_or_heap s s.(accu) 0 with
    | Some class_tbl =>
      let fields :=
        match class_tbl with
        | Val_block _ fs => fs
        | Val_ptr addr => match heap_lookup s.(hp) addr with Some (_, fs) => fs | None => [] end
        | _ => []
        end
      in
      let fix scan (remaining : list value) : Prop :=
        match remaining with
        | [] => msg = "GETPUBMET: method not found"
        | _ :: [] => msg = "GETPUBMET: method not found"
        | _ :: tag_val :: rest =>
          if value_eqb tag_val (Val_int tag) then False
          else scan rest
        end
      in scan (skipn 2 fields)
    | None => msg = "GETPUBMET: no class table"
    end
  (* GETDYNMET: errors when method not found, no class table, or stack underflow *)
  | GETDYNMET =>
    match s.(stack) with
    | obj :: _ =>
      let tag := s.(accu) in
      match field_or_heap s obj 0 with
      | Some class_tbl =>
        let fields :=
          match class_tbl with
          | Val_block _ fs => fs
          | Val_ptr addr => match heap_lookup s.(hp) addr with Some (_, fs) => fs | None => [] end
          | _ => []
          end
        in
        let fix scan (remaining : list value) : Prop :=
          match remaining with
          | [] => msg = "GETDYNMET: method not found"
          | _ :: [] => msg = "GETDYNMET: method not found"
          | _ :: tag_val :: rest =>
            if value_eqb tag_val tag then False
            else scan rest
          end
        in scan (skipn 2 fields)
      | None => msg = "GETDYNMET: no class table"
      end
    | _ => msg = "GETDYNMET: stack underflow"
    end
  (* BEQ: never errors *)
  | BEQ _ _ => False
  (* BNEQ: never errors *)
  | BNEQ _ _ => False
  (* BLTINT: not an integer *)
  | BLTINT _ _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "BLTINT: not an integer"
    end
  (* BLEINT: not an integer *)
  | BLEINT _ _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "BLEINT: not an integer"
    end
  (* BGTINT: not an integer *)
  | BGTINT _ _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "BGTINT: not an integer"
    end
  (* BGEINT: not an integer *)
  | BGEINT _ _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "BGEINT: not an integer"
    end
  (* ULTINT: type error or stack underflow *)
  | ULTINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "ULTINT: type error or stack underflow"
    end
  (* UGEINT: type error or stack underflow *)
  | UGEINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => False
    | _, _ => msg = "UGEINT: type error or stack underflow"
    end
  (* BULTINT: not an integer *)
  | BULTINT _ _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "BULTINT: not an integer"
    end
  (* BUGEINT: not an integer *)
  | BUGEINT _ _ =>
    match s.(accu) with
    | Val_int _ => False
    | _ => msg = "BUGEINT: not an integer"
    end
  (* STOP: never errors (returns Halt) *)
  | STOP => False
  end.

Definition pre_of (i : instruction) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  match i with
  | ACC n => code_at (Int.repr (Z.of_nat n))
  | PUSH => sp_at_least 16
  | PUSHACC n =>
      match n with
      | 1%nat|2%nat|3%nat|4%nat|5%nat|6%nat|7%nat => sp_at_least 16
      | _ => fun _ _ _ _ => True
      end
  | POP n => (code_at (Int.repr (Z.of_nat n)) /\p code_ne_struct) /\p stack_length_ge n
  | ASSIGN n => assign_step_pre n
  | ENVACC n => code_at (Int.repr (Z.of_nat n)) /\p env_field_loadable n
  | PUSHENVACC n => pushenvacc_generic_step_pre n
  | PUSH_RETADDR ret_addr => push_retaddr_step_pre ret_addr
  | APPLY n => apply_n_step_pre n
  | APPLY1 => apply1_step_pre
  | APPLY2 => apply2_step_pre
  | APPLY3 => apply3_step_pre
  | APPTERM nargs slotsize =>
      fun e0 m s ard =>
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
            abs_rel e0 le' m' s'
  | APPTERM1 slotsize => appterm1_step_pre slotsize
  | APPTERM2 slotsize => appterm2_step_pre slotsize
  | APPTERM3 slotsize => appterm3_step_pre slotsize
  | RETURN stacksize => return_step_pre stacksize
  | RESTART => restart_step_pre
  | GRAB required => grab_step_pre required
  | CLOSURE nvars code_ofs => closure_general_step_pre nvars code_ofs
  | CLOSUREREC nf nv co =>
      match nf, nv, co with
      | 1%nat, 0%nat, (code_ofs :: nil)%list =>
          heap_alloc_with_stores 2 247 alloc_store_2
          /\p code_at (Int.repr 1)
          /\p code_arg_at 1 (Int.repr 0)
          /\p code_arg_at 2 (Int.repr code_ofs)
          /\p sp_at_least 16
      | _, _, _ => fun _ _ _ _ => True
      end
  | OFFSETCLOSURE ofs => offsetclosure_pre ofs
  | PUSHOFFSETCLOSURE ofs => pushoffsetclosure_step_pre ofs
  | GETGLOBAL n => code_at (Int.repr (Z.of_nat n)) /\p global_offset_safe n
  | PUSHGETGLOBAL n => (code_at (Int.repr (Z.of_nat n)) /\p global_offset_safe n) /\p sp_at_least 16
  | GETGLOBALFIELD n p => getglobalfield_step_pre n p
  | PUSHGETGLOBALFIELD n p => pushgetglobalfield_step_pre n p
  | SETGLOBAL n => setglobal_step_pre n
  | ATOM t => code_at (Int.repr (Z.of_nat t))
  | PUSHATOM t => sp_at_least 16 /\p code_at (Int.repr (Z.of_nat t))
  | MAKEBLOCK t size => makeblock_step_pre t size
  | MAKEBLOCK1 t => heap_alloc_with_stores 1 (Z.of_nat t) alloc_store_1 /\p code_at (Int.repr (Z.of_nat t))
  | MAKEBLOCK2 t => heap_alloc_with_stores 2 (Z.of_nat t) alloc_store_2 /\p code_at (Int.repr (Z.of_nat t))
  | MAKEBLOCK3 t => heap_alloc_with_stores 3 (Z.of_nat t) alloc_store_3 /\p code_at (Int.repr (Z.of_nat t))
  | MAKEFLOATBLOCK n => makefloatblock_step_pre n
  | GETFIELD n => heap_field_loadable n /\p code_at (Int.repr (Z.of_nat n))
  | GETFLOATFIELD n => getfloatfield_step_pre n
  | SETFIELD n => setfield_step_pre n
  | SETFLOATFIELD n => setfloatfield_step_pre n
  | VECTLENGTH => fun _ => vectlength_pre
  | GETVECTITEM => getvectitem_step_pre
  | SETVECTITEM => setvectitem_pre
  | GETBYTESCHAR => getstringchar_step_pre
  | SETBYTESCHAR => setbyteschar_step_pre
  | GETSTRINGCHAR => getstringchar_step_pre
  | BRANCH _ => code_loadable
  | BRANCHIF target => branchif_step_pre target
  | BRANCHIFNOT target => branchifnot_step_pre target
  | SWITCH nc nb ct bt => switch_step_pre nc nb ct bt
  | BOOLNOT => accu_check ak_bool /\p accu_check ak_long
  | PUSHTRAP handler_pc => pushtrap_step_pre handler_pc
  | POPTRAP => poptrap_step_pre
  | RAISE => raise_step_pre
  | RERAISE => raise_step_pre
  | RAISE_NOTRACE => raise_step_pre
  | CHECK_SIGNALS => no_pre
  | C_CALL _ _ => no_pre
  | CONSTINT n => code_at (Int.repr n)
  | PUSHCONSTINT n => pushconstint_step_pre n
  | NEGINT => accu_check ak_long
  | ADDINT => accu_check ak_long /\p stack_head_is_long
  | SUBINT => accu_check ak_long /\p stack_head_is_long
  | MULINT => accu_check ak_long /\p stack_head_is_long
  | DIVINT => arith_safe arith_divmod
  | MODINT => arith_safe arith_divmod
  | ANDINT => accu_check ak_long /\p stack_head_is_long
  | ORINT => accu_check ak_long /\p stack_head_is_long
  | XORINT => accu_check ak_long /\p stack_head_is_long
  | LSLINT => arith_safe arith_shift
  | LSRINT => arith_safe arith_shift
  | ASRINT => arith_safe arith_shift
  | EQ => arith_safe arith_unsigned
  | NEQ => arith_safe arith_unsigned
  | LTINT => arith_safe arith_signed
  | LEINT => arith_safe arith_signed
  | GTINT => arith_safe arith_signed
  | GEINT => arith_safe arith_signed
  | OFFSETINT ofs => code_at (Int.repr ofs) /\p accu_check ak_long
  | OFFSETREF n => fun _ => offsetref_heap_pre n
  | ISINT => accu_check ak_immediate
  | GETMETHOD => getmethod_step_pre
  | GETPUBMET tag => getpubmet_pre tag
  | GETDYNMET => getdynmet_pre
  | BEQ n target => ((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_check ak_signed_range /\p accu_check ak_long)
  | BNEQ n target => ((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_check ak_signed_range /\p accu_check ak_long)
  | BLTINT n target => ((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_check ak_signed_range /\p accu_check ak_long)
  | BLEINT n target => ((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_check ak_signed_range /\p accu_check ak_long)
  | BGTINT n target => ((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_check ak_signed_range /\p accu_check ak_long)
  | BGEINT n target => ((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p (accu_check ak_signed_range /\p accu_check ak_long)
  | ULTINT => arith_safe arith_ucompare
  | UGEINT => arith_safe arith_ucompare
  | BULTINT n target => (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p accu_check ak_unsigned_range) /\p accu_check ak_long
  | BUGEINT n target => (((code_ne_struct /\p code_at (Int.repr n)) /\p branch_offset_at target) /\p accu_check ak_unsigned_range) /\p accu_check ak_long
  | STOP => no_pre
  end.

(* ================================================================== *)
(* Module Type                                                         *)
(*                                                                      *)
(* Building block vocabulary (18 shared blocks):                        *)
(*   no_pre             — no precondition (trivially True)              *)
(*   accu_check k       — accumulator satisfies kind k:                *)
(*     ak_long            val_repr maps to Vlong                        *)
(*     ak_signed_range    Val_int in signed 62-bit range                *)
(*     ak_unsigned_range  Val_int in unsigned 62-bit range              *)
(*     ak_bool            Val_int 0 or Val_int 1                        *)
(*     ak_immediate       Val_int with Vlong repr, or atom block        *)
(*   arith_safe k       — accu and stack[0] are safe for arithmetic k: *)
(*     arith_unsigned     both unsigned-tagged fit Int64                 *)
(*     arith_signed       both signed-tagged fit Int64                  *)
(*     arith_divmod       signed + divisor nonzero                      *)
(*     arith_shift        shift in [0,64), operand signed               *)
(*     arith_ucompare     both in unsigned 62-bit range                 *)
(*   stack_head_is_long — stack[0]'s val_repr is Vlong                 *)
(*   code_at v          — code buffer at PC contains int32 v            *)
(*   code_arg_at k v    — code buffer at PC+k contains int32 v         *)
(*   code_ne_struct     — code block distinct from struct block         *)
(*   code_loadable      — code at PC is loadable                        *)
(*   branch_offset_at t — branch target offset is representable         *)
(*   sp_at_least n      — stack pointer has room for n bytes            *)
(*   global_offset_safe n — global[n] offset is valid                   *)
(*   env_field_loadable n — env field n is loadable from heap           *)
(*   heap_field_loadable n — accu's heap field n is loadable            *)
(*   setfield_heap_pre n — field n is writable via store                *)
(*   heap_alloc_with_stores n tag alloc — allocation + n field stores   *)
(*   closure_offset_pre n k — closure code pointer at offset n          *)
(*   raise_step_pre     — raise infrastructure is set up                *)
(*   /\p                — right-assoc conjunction of preconditions      *)
(*                                                                      *)
(* Each entry: handler_correct handler c_func pre err stuck external    *)
(* 94 uniform parameters (one per AST constructor).                     *)
(* ================================================================== *)

Module Type InstructVerificationFineGrainedSpec (Import HI : HandleInstrSpec).

  Parameter correct_ACC : forall n,
    handler_correct (handle_instr (ACC n)) (clight_of (ACC n))
      (pre_of (ACC n))
      (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).

  Parameter correct_PUSH :
    handler_correct (handle_instr PUSH) (clight_of PUSH)
      (pre_of PUSH)
      (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).

  Parameter correct_PUSHACC : forall n,
    handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
      (pre_of (PUSHACC n))
      (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).

  Parameter correct_POP : forall n,
    handler_correct (handle_instr (POP n)) (clight_of (POP n))
      (pre_of (POP n))
      (P_error_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)).

  Parameter correct_ASSIGN : forall n,
    handler_correct (handle_instr (ASSIGN n)) (clight_of (ASSIGN n))
      (pre_of (ASSIGN n))
      (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)).

  Parameter correct_ENVACC : forall n,
    handler_correct (handle_instr (ENVACC n)) (clight_of (ENVACC n))
      (pre_of (ENVACC n))
      (P_error_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)).

  Parameter correct_PUSHENVACC : forall n,
    handler_correct (handle_instr (PUSHENVACC n)) (clight_of (PUSHENVACC n))
      (pre_of (PUSHENVACC n))
      (P_error_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)).

  Parameter correct_PUSH_RETADDR : forall z,
    handler_correct (handle_instr (PUSH_RETADDR z)) (clight_of (PUSH_RETADDR z))
      (pre_of (PUSH_RETADDR z))
      (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)).

  Parameter correct_APPLY : forall n,
    handler_correct (handle_instr (APPLY n)) (clight_of (APPLY n))
      (pre_of (APPLY n))
      (P_error_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)).

  Parameter correct_APPLY1 :
    handler_correct (handle_instr APPLY1) (clight_of APPLY1)
      (pre_of APPLY1)
      (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1).

  Parameter correct_APPLY2 :
    handler_correct (handle_instr APPLY2) (clight_of APPLY2)
      (pre_of APPLY2)
      (P_error_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2).

  Parameter correct_APPLY3 :
    handler_correct (handle_instr APPLY3) (clight_of APPLY3)
      (pre_of APPLY3)
      (P_error_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3).

  Parameter correct_APPTERM : forall nargs slotsize,
    handler_correct (handle_instr (APPTERM nargs slotsize)) (clight_of (APPTERM nargs slotsize))
      (pre_of (APPTERM nargs slotsize))
      (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)).

  Parameter correct_APPTERM1 : forall n,
    handler_correct (handle_instr (APPTERM1 n)) (clight_of (APPTERM1 n))
      (pre_of (APPTERM1 n))
      (P_error_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)).

  Parameter correct_APPTERM2 : forall n,
    handler_correct (handle_instr (APPTERM2 n)) (clight_of (APPTERM2 n))
      (pre_of (APPTERM2 n))
      (P_error_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)).

  Parameter correct_APPTERM3 : forall n,
    handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
      (pre_of (APPTERM3 n))
      (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).

  Parameter correct_RETURN : forall n,
    handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
      (pre_of (RETURN n))
      (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).

  Parameter correct_RESTART :
    handler_correct (handle_instr RESTART) (clight_of RESTART)
      (pre_of RESTART)
      (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).

  Parameter correct_GRAB : forall n,
    handler_correct (handle_instr (GRAB n)) (clight_of (GRAB n))
      (pre_of (GRAB n))
      (P_error_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)).

  Parameter correct_CLOSURE : forall n z,
    handler_correct (handle_instr (CLOSURE n z)) (clight_of (CLOSURE n z))
      (pre_of (CLOSURE n z))
      (P_error_of (CLOSURE n z)) (P_halt_of (CLOSURE n z)) (P_ccall_of (CLOSURE n z)).

  Parameter correct_CLOSUREREC : forall n1 n2 l,
    handler_correct (handle_instr (CLOSUREREC n1 n2 l)) (clight_of (CLOSUREREC n1 n2 l))
      (pre_of (CLOSUREREC n1 n2 l))
      (P_error_of (CLOSUREREC n1 n2 l)) (P_halt_of (CLOSUREREC n1 n2 l)) (P_ccall_of (CLOSUREREC n1 n2 l)).

  Parameter correct_OFFSETCLOSURE : forall z,
    handler_correct (handle_instr (OFFSETCLOSURE z)) (clight_of (OFFSETCLOSURE z))
      (pre_of (OFFSETCLOSURE z))
      (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)).

  Parameter correct_PUSHOFFSETCLOSURE : forall z,
    handler_correct (handle_instr (PUSHOFFSETCLOSURE z)) (clight_of (PUSHOFFSETCLOSURE z))
      (pre_of (PUSHOFFSETCLOSURE z))
      (P_error_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)).

  Parameter correct_GETGLOBAL : forall n,
    handler_correct (handle_instr (GETGLOBAL n)) (clight_of (GETGLOBAL n))
      (pre_of (GETGLOBAL n))
      (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)).

  Parameter correct_PUSHGETGLOBAL : forall n,
    handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n))
      (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).

  Parameter correct_GETGLOBALFIELD : forall n1 n2,
    handler_correct (handle_instr (GETGLOBALFIELD n1 n2)) (clight_of (GETGLOBALFIELD n1 n2))
      (pre_of (GETGLOBALFIELD n1 n2))
      (P_error_of (GETGLOBALFIELD n1 n2)) (P_halt_of (GETGLOBALFIELD n1 n2)) (P_ccall_of (GETGLOBALFIELD n1 n2)).

  Parameter correct_PUSHGETGLOBALFIELD : forall n1 n2,
    handler_correct (handle_instr (PUSHGETGLOBALFIELD n1 n2)) (clight_of (PUSHGETGLOBALFIELD n1 n2))
      (pre_of (PUSHGETGLOBALFIELD n1 n2))
      (P_error_of (PUSHGETGLOBALFIELD n1 n2)) (P_halt_of (PUSHGETGLOBALFIELD n1 n2)) (P_ccall_of (PUSHGETGLOBALFIELD n1 n2)).

  Parameter correct_SETGLOBAL : forall n,
    handler_correct (handle_instr (SETGLOBAL n)) (clight_of (SETGLOBAL n))
      (pre_of (SETGLOBAL n))
      (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)).

  Parameter correct_ATOM : forall n,
    handler_correct (handle_instr (ATOM n)) (clight_of (ATOM n))
      (pre_of (ATOM n))
      (P_error_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)).

  Parameter correct_PUSHATOM : forall n,
    handler_correct (handle_instr (PUSHATOM n)) (clight_of (PUSHATOM n))
      (pre_of (PUSHATOM n))
      (P_error_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)).

  Parameter correct_MAKEBLOCK : forall n1 n2,
    handler_correct (handle_instr (MAKEBLOCK n1 n2)) (clight_of (MAKEBLOCK n1 n2))
      (pre_of (MAKEBLOCK n1 n2))
      (P_error_of (MAKEBLOCK n1 n2)) (P_halt_of (MAKEBLOCK n1 n2)) (P_ccall_of (MAKEBLOCK n1 n2)).

  Parameter correct_MAKEBLOCK1 : forall n,
    handler_correct (handle_instr (MAKEBLOCK1 n)) (clight_of (MAKEBLOCK1 n))
      (pre_of (MAKEBLOCK1 n))
      (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)).

  Parameter correct_MAKEBLOCK2 : forall n,
    handler_correct (handle_instr (MAKEBLOCK2 n)) (clight_of (MAKEBLOCK2 n))
      (pre_of (MAKEBLOCK2 n))
      (P_error_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)).

  Parameter correct_MAKEBLOCK3 : forall n,
    handler_correct (handle_instr (MAKEBLOCK3 n)) (clight_of (MAKEBLOCK3 n))
      (pre_of (MAKEBLOCK3 n))
      (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)).

  Parameter correct_MAKEFLOATBLOCK : forall n,
    handler_correct (handle_instr (MAKEFLOATBLOCK n)) (clight_of (MAKEFLOATBLOCK n))
      (pre_of (MAKEFLOATBLOCK n))
      (P_error_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)).

  Parameter correct_GETFIELD : forall n,
    handler_correct (handle_instr (GETFIELD n)) (clight_of (GETFIELD n))
      (pre_of (GETFIELD n))
      (P_error_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)).

  Parameter correct_GETFLOATFIELD : forall n,
    handler_correct (handle_instr (GETFLOATFIELD n)) (clight_of (GETFLOATFIELD n))
      (pre_of (GETFLOATFIELD n))
      (P_error_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)).

  Parameter correct_SETFIELD : forall n,
    handler_correct (handle_instr (SETFIELD n)) (clight_of (SETFIELD n))
      (pre_of (SETFIELD n))
      (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)).

  Parameter correct_SETFLOATFIELD : forall n,
    handler_correct (handle_instr (SETFLOATFIELD n)) (clight_of (SETFLOATFIELD n))
      (pre_of (SETFLOATFIELD n))
      (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)).

  Parameter correct_VECTLENGTH :
    handler_correct (handle_instr VECTLENGTH) (clight_of VECTLENGTH)
      (pre_of VECTLENGTH)
      (P_error_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH).

  Parameter correct_GETVECTITEM :
    handler_correct (handle_instr GETVECTITEM) (clight_of GETVECTITEM)
      (pre_of GETVECTITEM)
      (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM).

  Parameter correct_SETVECTITEM :
    handler_correct (handle_instr SETVECTITEM) (clight_of SETVECTITEM)
      (pre_of SETVECTITEM)
      (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM).

  Parameter correct_GETBYTESCHAR :
    handler_correct (handle_instr GETBYTESCHAR) (clight_of GETBYTESCHAR)
      (pre_of GETBYTESCHAR)
      (P_error_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR).

  Parameter correct_SETBYTESCHAR :
    handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
      (pre_of SETBYTESCHAR)
      (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).

  Parameter correct_GETSTRINGCHAR :
    handler_correct (handle_instr GETSTRINGCHAR) (clight_of GETSTRINGCHAR)
      (pre_of GETSTRINGCHAR)
      (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR).

  Parameter correct_BRANCH : forall z,
    handler_correct (handle_instr (BRANCH z)) (clight_of (BRANCH z))
      (pre_of (BRANCH z))
      (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)).

  Parameter correct_BRANCHIF : forall z,
    handler_correct (handle_instr (BRANCHIF z)) (clight_of (BRANCHIF z))
      (pre_of (BRANCHIF z))
      (P_error_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)).

  Parameter correct_BRANCHIFNOT : forall z,
    handler_correct (handle_instr (BRANCHIFNOT z)) (clight_of (BRANCHIFNOT z))
      (pre_of (BRANCHIFNOT z))
      (P_error_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)).

  Parameter correct_SWITCH : forall n1 n2 l1 l2,
    handler_correct (handle_instr (SWITCH n1 n2 l1 l2)) (clight_of (SWITCH n1 n2 l1 l2))
      (pre_of (SWITCH n1 n2 l1 l2))
      (P_error_of (SWITCH n1 n2 l1 l2)) (P_halt_of (SWITCH n1 n2 l1 l2)) (P_ccall_of (SWITCH n1 n2 l1 l2)).

  Parameter correct_BOOLNOT :
    handler_correct (handle_instr BOOLNOT) (clight_of BOOLNOT)
      (pre_of BOOLNOT)
      (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT).

  Parameter correct_PUSHTRAP : forall z,
    handler_correct (handle_instr (PUSHTRAP z)) (clight_of (PUSHTRAP z))
      (pre_of (PUSHTRAP z))
      (P_error_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)).

  Parameter correct_POPTRAP :
    handler_correct (handle_instr POPTRAP) (clight_of POPTRAP)
      (pre_of POPTRAP)
      (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP).

  Parameter correct_RAISE :
    handler_correct (handle_instr RAISE) (clight_of RAISE)
      (pre_of RAISE)
      (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE).

  Parameter correct_RERAISE :
    handler_correct (handle_instr RERAISE) (clight_of RERAISE)
      (pre_of RERAISE)
      (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE).

  Parameter correct_RAISE_NOTRACE :
    handler_correct (handle_instr RAISE_NOTRACE) (clight_of RAISE_NOTRACE)
      (pre_of RAISE_NOTRACE)
      (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE).

  Parameter correct_CHECK_SIGNALS :
    handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
      (pre_of CHECK_SIGNALS)
      (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS).

  Parameter correct_C_CALL : forall n1 n2,
    handler_correct (handle_instr (C_CALL n1 n2)) (clight_of (C_CALL n1 n2))
      (pre_of (C_CALL n1 n2))
      (P_error_of (C_CALL n1 n2)) (P_halt_of (C_CALL n1 n2)) (P_ccall_of (C_CALL n1 n2)).

  Parameter correct_CONSTINT : forall z,
    handler_correct (handle_instr (CONSTINT z)) (clight_of (CONSTINT z))
      (pre_of (CONSTINT z))
      (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)).

  Parameter correct_PUSHCONSTINT : forall z,
    handler_correct (handle_instr (PUSHCONSTINT z)) (clight_of (PUSHCONSTINT z))
      (pre_of (PUSHCONSTINT z))
      (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)).

  Parameter correct_NEGINT :
    handler_correct (handle_instr NEGINT) (clight_of NEGINT)
      (pre_of NEGINT)
      (P_error_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).

  Parameter correct_ADDINT :
    handler_correct (handle_instr ADDINT) (clight_of ADDINT)
      (pre_of ADDINT)
      (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).

  Parameter correct_SUBINT :
    handler_correct (handle_instr SUBINT) (clight_of SUBINT)
      (pre_of SUBINT)
      (P_error_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT).

  Parameter correct_MULINT :
    handler_correct (handle_instr MULINT) (clight_of MULINT)
      (pre_of MULINT)
      (P_error_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT).

  Parameter correct_DIVINT :
    handler_correct (handle_instr DIVINT) (clight_of DIVINT)
      (pre_of DIVINT)
      (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT).

  Parameter correct_MODINT :
    handler_correct (handle_instr MODINT) (clight_of MODINT)
      (pre_of MODINT)
      (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT).

  Parameter correct_ANDINT :
    handler_correct (handle_instr ANDINT) (clight_of ANDINT)
      (pre_of ANDINT)
      (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).

  Parameter correct_ORINT :
    handler_correct (handle_instr ORINT) (clight_of ORINT)
      (pre_of ORINT)
      (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT).

  Parameter correct_XORINT :
    handler_correct (handle_instr XORINT) (clight_of XORINT)
      (pre_of XORINT)
      (P_error_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT).

  Parameter correct_LSLINT :
    handler_correct (handle_instr LSLINT) (clight_of LSLINT)
      (pre_of LSLINT)
      (P_error_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT).

  Parameter correct_LSRINT :
    handler_correct (handle_instr LSRINT) (clight_of LSRINT)
      (pre_of LSRINT)
      (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).

  Parameter correct_ASRINT :
    handler_correct (handle_instr ASRINT) (clight_of ASRINT)
      (pre_of ASRINT)
      (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT).

  Parameter correct_EQ :
    handler_correct (handle_instr EQ) (clight_of EQ)
      (pre_of EQ)
      (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ).

  Parameter correct_NEQ :
    handler_correct (handle_instr NEQ) (clight_of NEQ)
      (pre_of NEQ)
      (P_error_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ).

  Parameter correct_LTINT :
    handler_correct (handle_instr LTINT) (clight_of LTINT)
      (pre_of LTINT)
      (P_error_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT).

  Parameter correct_LEINT :
    handler_correct (handle_instr LEINT) (clight_of LEINT)
      (pre_of LEINT)
      (P_error_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT).

  Parameter correct_GTINT :
    handler_correct (handle_instr GTINT) (clight_of GTINT)
      (pre_of GTINT)
      (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT).

  Parameter correct_GEINT :
    handler_correct (handle_instr GEINT) (clight_of GEINT)
      (pre_of GEINT)
      (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT).

  Parameter correct_OFFSETINT : forall z,
    handler_correct (handle_instr (OFFSETINT z)) (clight_of (OFFSETINT z))
      (pre_of (OFFSETINT z))
      (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)).

  Parameter correct_OFFSETREF : forall z,
    handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
      (pre_of (OFFSETREF z))
      (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).

  Parameter correct_ISINT :
    handler_correct (handle_instr ISINT) (clight_of ISINT)
      (pre_of ISINT)
      (P_error_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT).

  Parameter correct_GETMETHOD :
    handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
      (pre_of GETMETHOD)
      (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).

  Parameter correct_GETPUBMET : forall z,
    handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
      (pre_of (GETPUBMET z))
      (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).

  Parameter correct_GETDYNMET :
    handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
      (pre_of GETDYNMET)
      (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).

  Parameter correct_BEQ : forall z1 z2,
    handler_correct (handle_instr (BEQ z1 z2)) (clight_of (BEQ z1 z2))
      (pre_of (BEQ z1 z2))
      (P_error_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)).

  Parameter correct_BNEQ : forall z1 z2,
    handler_correct (handle_instr (BNEQ z1 z2)) (clight_of (BNEQ z1 z2))
      (pre_of (BNEQ z1 z2))
      (P_error_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)).

  Parameter correct_BLTINT : forall z1 z2,
    handler_correct (handle_instr (BLTINT z1 z2)) (clight_of (BLTINT z1 z2))
      (pre_of (BLTINT z1 z2))
      (P_error_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)).

  Parameter correct_BLEINT : forall z1 z2,
    handler_correct (handle_instr (BLEINT z1 z2)) (clight_of (BLEINT z1 z2))
      (pre_of (BLEINT z1 z2))
      (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)).

  Parameter correct_BGTINT : forall z1 z2,
    handler_correct (handle_instr (BGTINT z1 z2)) (clight_of (BGTINT z1 z2))
      (pre_of (BGTINT z1 z2))
      (P_error_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)).

  Parameter correct_BGEINT : forall z1 z2,
    handler_correct (handle_instr (BGEINT z1 z2)) (clight_of (BGEINT z1 z2))
      (pre_of (BGEINT z1 z2))
      (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)).

  Parameter correct_ULTINT :
    handler_correct (handle_instr ULTINT) (clight_of ULTINT)
      (pre_of ULTINT)
      (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT).

  Parameter correct_UGEINT :
    handler_correct (handle_instr UGEINT) (clight_of UGEINT)
      (pre_of UGEINT)
      (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT).

  Parameter correct_BULTINT : forall z1 z2,
    handler_correct (handle_instr (BULTINT z1 z2)) (clight_of (BULTINT z1 z2))
      (pre_of (BULTINT z1 z2))
      (P_error_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)).

  Parameter correct_BUGEINT : forall z1 z2,
    handler_correct (handle_instr (BUGEINT z1 z2)) (clight_of (BUGEINT z1 z2))
      (pre_of (BUGEINT z1 z2))
      (P_error_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)).

  Parameter correct_STOP :
    handler_correct (handle_instr STOP) (clight_of STOP)
      (pre_of STOP)
      (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP).

End InstructVerificationFineGrainedSpec.

Module Type InstructVerificationSpec (Import HI : HandleInstrSpec).
  Parameter handler_correct_all :
    forall i, handler_correct (handle_instr i) (clight_of i)
                (pre_of i)
                (P_error_of i) (P_halt_of i) (P_ccall_of i).
End InstructVerificationSpec.

Module InstructVerificationFromFineGrained
       (Import HI : HandleInstrSpec)
       (Import FG : InstructVerificationFineGrainedSpec HI) <: InstructVerificationSpec HI.

    Lemma handler_correct_all :
      forall i, handler_correct (handle_instr i) (clight_of i)
                  (pre_of i)
                  (P_error_of i) (P_halt_of i) (P_ccall_of i).
    Proof.
      intro i; destruct i;
      [ apply correct_ACC | apply correct_PUSH | apply correct_PUSHACC | apply correct_POP
      | apply correct_ASSIGN | apply correct_ENVACC | apply correct_PUSHENVACC
      | apply correct_PUSH_RETADDR | apply correct_APPLY | apply correct_APPLY1
      | apply correct_APPLY2 | apply correct_APPLY3 | apply correct_APPTERM
      | apply correct_APPTERM1 | apply correct_APPTERM2 | apply correct_APPTERM3
      | apply correct_RETURN | apply correct_RESTART | apply correct_GRAB
      | apply correct_CLOSURE | apply correct_CLOSUREREC | apply correct_OFFSETCLOSURE
      | apply correct_PUSHOFFSETCLOSURE | apply correct_GETGLOBAL | apply correct_PUSHGETGLOBAL
      | apply correct_GETGLOBALFIELD | apply correct_PUSHGETGLOBALFIELD | apply correct_SETGLOBAL
      | apply correct_ATOM | apply correct_PUSHATOM | apply correct_MAKEBLOCK
      | apply correct_MAKEBLOCK1 | apply correct_MAKEBLOCK2 | apply correct_MAKEBLOCK3
      | apply correct_MAKEFLOATBLOCK | apply correct_GETFIELD | apply correct_GETFLOATFIELD
      | apply correct_SETFIELD | apply correct_SETFLOATFIELD | apply correct_VECTLENGTH
      | apply correct_GETVECTITEM | apply correct_SETVECTITEM | apply correct_GETBYTESCHAR
      | apply correct_SETBYTESCHAR | apply correct_GETSTRINGCHAR | apply correct_BRANCH
      | apply correct_BRANCHIF | apply correct_BRANCHIFNOT | apply correct_SWITCH
      | apply correct_BOOLNOT | apply correct_PUSHTRAP | apply correct_POPTRAP
      | apply correct_RAISE | apply correct_RERAISE | apply correct_RAISE_NOTRACE
      | apply correct_CHECK_SIGNALS | apply correct_C_CALL | apply correct_CONSTINT
      | apply correct_PUSHCONSTINT | apply correct_NEGINT | apply correct_ADDINT
      | apply correct_SUBINT | apply correct_MULINT | apply correct_DIVINT
      | apply correct_MODINT | apply correct_ANDINT | apply correct_ORINT
      | apply correct_XORINT | apply correct_LSLINT | apply correct_LSRINT
      | apply correct_ASRINT | apply correct_EQ | apply correct_NEQ
      | apply correct_LTINT | apply correct_LEINT | apply correct_GTINT
      | apply correct_GEINT | apply correct_OFFSETINT | apply correct_OFFSETREF
      | apply correct_ISINT | apply correct_GETMETHOD | apply correct_GETPUBMET
      | apply correct_GETDYNMET | apply correct_BEQ | apply correct_BNEQ
      | apply correct_BLTINT | apply correct_BLEINT | apply correct_BGTINT
      | apply correct_BGEINT | apply correct_ULTINT | apply correct_UGEINT
      | apply correct_BULTINT | apply correct_BUGEINT | apply correct_STOP ].
    Qed.
End InstructVerificationFromFineGrained.

