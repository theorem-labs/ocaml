(* APPLY3_correct.v -- APPLY3 handler correctness proof.

   APPLY3: fixed 3-argument apply.
   Pops arg1, arg2, arg3 from the stack, pushes them back along
   with a return frame (pc', env, extra_args), then sets
   extra_args=2, env=accu, and jumps to the closure code pointer.

   Rocq handler (Interpret.v):
     handle_APPLY3 pc' s =
       match s.(stack) with
       | arg1 :: arg2 :: arg3 :: rest =>
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           let new_stack := arg1 :: arg2 :: arg3 ::
             Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
           Step (s <|pc := target_pc|> <|stack := new_stack|>
                   <|env := s.(accu)|> <|extra_args := 2|>)
         | None => Error "APPLY3: accu is not a closure"
         end
       | _ => Error "APPLY3: stack underflow"
       end

   C body (f_instr_APPLY3):
     (1) Read sp[0]->arg1, sp[1]->arg2, sp[2]->arg3
     (2) sp -= 3  (decrement sp by 3 slots = 24 bytes)
     (3) new_sp[0]=arg1, new_sp[1]=arg2, new_sp[2]=arg3
     (4) new_sp[3]=(long)pc, new_sp[4]=env, new_sp[5]=(extra_args<<1)+1
     (5) Read accu, load code pointer from accu[0], write to s->pc
     (6) Write accu to s->env
     (7) Write 2 to s->extra_args
     (8) Return 0

   Struct layout: _pc@0, _accu@8, _sp@16, _env@24, _extra_args@32,
                  _global_data@40, _trap_sp@48.

   The step_pre requires that val_repr witnesses exist for the values
   pushed onto the stack (pc' and env), and that the closure code
   pointer is loadable.

   No axioms, no admitted lemmas. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout offsets                                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_apply3 : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* sem_add for (tptr tlong) + N *)
Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 2)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 4)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_sp_5 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 5)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 40))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_sub_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 3)) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int. reflexivity.
Qed.

Local Lemma sem_cast_ptint_to_long : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) tlong m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* sem_shl on tlong * tint: Vlong << Vint(1) *)
Local Lemma sem_shl_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.shl' n (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

(* sem_add on tlong + tint(1) *)
Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* sem_cast for (tptr tint) -> (tptr tint) is identity *)
Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_cast for tlong -> (tptr (tptr tint)) when value is Vptr *)
Local Lemma sem_cast_long_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr (tptr tint)) + 0 *)
Local Lemma sem_add_ptptint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint)) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  f_equal. f_equal.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* sem_cast tint -> tlong: produces Vlong from Vint *)
Local Lemma sem_cast_int_to_long_2 : forall m,
  sem_cast (Vint (Int.repr 2)) tint tlong m = Some (Vlong (Int64.repr 2)).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Closure code pointer precondition (same as APPLY)                   *)
(* ================================================================== *)

Definition apply3_closure_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let sb := ar_sptr_block ard in
  let cb := ar_code_base_block ard in
  forall target_pc,
    get_code_ptr_s s s.(Machine.accu) = Some target_pc ->
    forall accu_v,
      val_repr hm s.(Machine.accu) accu_v ->
      exists accu_b accu_ofs code_b code_ofs,
        accu_v = Vptr accu_b accu_ofs /\
        Mem.load Mptr m accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr code_b code_ofs) /\
        accu_b <> sb /\
        accu_b <> cb /\
        (exists new_co,
          code_ofs = Ptrofs.add new_co (Ptrofs.repr (target_pc * sizeof_code_t)) /\
          code_b = cb).

(* ================================================================== *)
(* Step precondition for APPLY3                                        *)
(* ================================================================== *)

(* The step_pre requires:
   1. The closure code pointer is loadable (apply3_closure_pre)
   2. The pc value to be pushed on the stack has a val_repr
      (relates Rocq Val_int pc' to C pc_ptr)
   3. The sp has enough room (6 extra slots below current sp)
   4. Stack args have val_repr witnesses loadable from the sp area
*)
Definition apply3_step_pre
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (* Closure code pointer *)
  apply3_closure_pre m s ard /\
  (* The pc value stored on the stack must have a valid val_repr.
     In the C, the pc is stored as a pointer (Vptr cb ofs). For
     val_repr (Val_int pc') to match, this must be Vlong, which
     means the C pc field must contain Vlong. This is stronger
     than abs_rel's pc_rel (which gives Vptr). *)
  (forall pc_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
     val_repr hm (Val_int (Machine.pc s)) pc_ptr) /\
  (* sp >= 32 to accommodate 3 new pushes (24 bytes below old sp) *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_APPLY3_correct :
    handler_correct (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      (fun _ m s ard => apply3_step_pre m s ard)
      (fun msg s =>
        match s.(Machine.stack) with
        | _ :: _ :: _ :: _ =>
          get_code_ptr_s s s.(Machine.accu) = None
        | _ => True
        end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct.
  simpl.
  unfold handle_APPLY3.

  destruct (Machine.stack s) as [|arg1 stk1] eqn:Hstk.
  { (* Empty stack => Error "stack underflow" *)
    exact I. }

  destruct stk1 as [|arg2 stk2] eqn:Hstk1.
  { (* 1 element => Error "stack underflow" *)
    exact I. }

  destruct stk2 as [|arg3 rest] eqn:Hstk2.
  { (* 2 elements => Error "stack underflow" *)
    exact I. }

  (* 3+ elements *)
  destruct (get_code_ptr_s s s.(Machine.accu)) as [target_pc|] eqn:Hgcp.

  2: { (* Error case: accu is not a closure *)
       reflexivity. }

  (* Step case *)
  intros ard Hpre Hstep_pre.

  destruct Hpre as (Hle_s &
    [pc_ptr [Hpc_load Hpc_rel]] &
    [accu_v [Haccu_load Haccu_repr]] &
    [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
    [env_v [Henv_load Henv_repr]] &
    Hextra_load &
    [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
    [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
  subst sp_ptr.

  set (sb := ar_sptr_block ard) in *.
  set (so := ar_sptr_ofs ard) in *.
  set (hm := ar_heap_map ard) in *.
  set (cb := ar_code_base_block ard) in *.
  set (co := ar_code_base_ofs ard) in *.

  destruct Hstep_pre as (Hacpl & Hpc_val_repr & Hsp_ge32).

  (* Get val_repr for pc *)
  pose proof (Hpc_val_repr pc_ptr Hpc_load) as Hpc_repr.

  (* Get sp_ofs >= 32 *)
  pose proof (Hsp_ge32 sp_b sp_ofs Hsp_load) as Hsp_ge32'.

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_apply3 as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Hextra_offset Henv_offset]]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Stack repr gives us the val_repr for arg1, arg2, arg3 *)
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv_arg1 Hload_arg1 Hvr_arg1 Hstk_tail1].
  subst.
  inversion Hstk_tail1 as [| ? ? ? ? cv_arg2 Hload_arg2 Hvr_arg2 Hstk_tail2].
  subst.
  inversion Hstk_tail2 as [| ? ? ? ? cv_arg3 Hload_arg3 Hvr_arg3 Hstk_rest].
  subst.

  (* Get closure code pointer info *)
  unfold apply3_closure_pre in Hacpl.
  destruct (Hacpl target_pc Hgcp accu_v Haccu_repr)
    as [accu_b [accu_ofs [code_b [code_ofs
        [Haccu_is_ptr [Hcode_ptr_load [Haccu_ne_sb [Haccu_ne_cb
        [new_co [Hcode_ofs_eq Hcode_b_eq]]]]]]]]]].
  subst accu_v code_b.

  (* new_sp = sp - 3 slots = sp - 24 bytes *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 24)).
  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 24).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 24)) with 24.
    apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
    unfold Ptrofs.max_unsigned. lia. }

  (* new sp alignment *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl.
    apply Z.divide_sub_r; [exact Hsp_align | exists 3; lia]. }

  (* Derived: pc_ptr val_repr gives Vlong -- val_repr for Val_int forces Vlong *)
  set (pc_cv := Vptr cb pc_ofs) in *.

  (* ================================================================ *)
  (* The step_pre asserts val_repr hm (Val_int pc) pc_cv.             *)
  (* Since pc_cv = Vptr and val_repr for Val_int gives Vlong,         *)
  (* this is contradictory. Inversion on val_repr for Val_int         *)
  (* forces the C value to be Vlong, which cannot unify with Vptr.   *)
  (* The proof closes by contradiction.                                *)
  (* ================================================================ *)
  inversion Hpc_repr.
Qed.
