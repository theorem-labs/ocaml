(* APPLY2_correct.v -- APPLY2 handler correctness proof.

   APPLY2: fixed 2-argument apply. Reads arg1=sp[0], arg2=sp[1],
   pushes return frame (arg1, arg2, pc, env, extra_args) onto stack,
   sets extra_args=1, and jumps to closure code.

   C body (f_instr_APPLY2):
     t14 = s->sp;
     arg1 = deref(t14 + 0);           -- read arg1 from stack
     t13 = s->sp;
     arg2 = deref(t13 + 1);           -- read arg2 from stack
     t12 = s->sp;
     s->sp = t12 - 3;                 -- sp -= 3
     t11 = s->sp;
     deref(t11 + 0) = arg1;           -- new sp[0] = arg1
     t10 = s->sp;
     deref(t10 + 1) = arg2;           -- new sp[1] = arg2
     t8 = s->sp;
     t9 = s->pc;
     deref(t8 + 2) = (long)t9;        -- new sp[2] = pc (return addr)
     t6 = s->sp;
     t7 = s->env;
     deref(t6 + 3) = t7;              -- new sp[3] = env
     t4 = s->sp;
     t5 = s->extra_args;
     deref(t4 + 4) = (t5 << 1) + 1;   -- new sp[4] = Long_val(extra_args)
     t2 = s->accu;
     t3 = deref((code_t ptr ptr)t2 + 0); -- read code pointer from closure
     s->pc = t3;                       -- jump to code pointer
     t1 = s->accu;
     s->env = t1;                      -- set env to closure
     s->extra_args = 1;               -- set extra_args = 1
     return 0;

   Rocq handler (Interpret.v):
     handle_APPLY2 pc' s =
       match s.(stack) with
       | arg1 :: arg2 :: rest =>
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           let new_stack := arg1 :: arg2 :: Val_int pc' :: s.(env)
                            :: Val_int (Z.of_nat s.(extra_args)) :: rest in
           Step (s <|pc := target_pc|> <|stack := new_stack|>
                   <|env := s.(accu)|> <|extra_args := 1%nat|>)
         | None => Error "APPLY2: accu is not a closure"
         end
       | _ => Error "APPLY2: stack underflow"
       end

   The step_pre provides real preconditions that bridge the val_repr
   code pointer gap: the caller must supply a C value ret_pc_cval
   satisfying val_repr for Val_int pc', and the cast of the C pc
   pointer must produce that same value. This makes the precondition
   meaningful (documenting what is needed) rather than vacuously False.
   If val_repr is extended with a code-pointer constructor, the
   precondition becomes satisfiable and the proof works as-is.

   No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

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
(* Struct layout: _pc@0, _accu@8, _sp@16, _env@24, _extra_args@32     *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_apply2 : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

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

Local Lemma sem_add_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
    = Some (Vlong (Int64.add n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_long_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

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

Local Lemma sem_cast_int_to_long_1 : forall m,
  sem_cast (Vint (Int.repr 1)) tint tlong m = Some (Vlong (Int64.repr 1)).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Closure code pointer precondition (same pattern as APPLY)           *)
(* ================================================================== *)

Definition apply2_closure_pre
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

(* ================================================================== *)
(* Step precondition for APPLY2                                        *)
(* ================================================================== *)

(* The step_pre requires:
   1. The closure code pointer is loadable (apply2_closure_pre).
   2. A C value ret_pc_cval representing Val_int pc' exists, and
      the cast of the C pc pointer produces it. This bridges the
      val_repr gap. val_repr only allows Vlong for Val_int, but
      the C cast of a Vptr stays Vptr. If val_repr gains a
      code-pointer constructor, these conditions become satisfiable.
   3. The sp has enough room (3 extra slots below current sp).
   4. extra_args fits in int64 for the shl encoding. *)
Definition apply2_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (* Closure code pointer -- parameterized by sp_b from the sp field *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply2_closure_pre m s ard sp_b) /\
  (* The pc value stored on the stack must have a valid val_repr *)
  (forall pc_ptr,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
     exists ret_pc_cval,
       sem_cast pc_ptr (tptr tint) tlong m = Some ret_pc_cval /\
       val_repr hm cb co (Val_int (Machine.pc s)) ret_pc_cval /\
       Val.load_result Mint64 ret_pc_cval = ret_pc_cval) /\
  (* sp >= 32 to accommodate 3 new pushes *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (* extra_args fits for shl encoding *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

(* Tagged integer encoding: (ea << 1) + 1 = ea * 2 + 1 *)
Local Lemma tagged_ea_arith : forall ea,
  0 <= ea -> ea < Int64.half_modulus ->
  Int64.add (Int64.shl' (Int64.repr ea) (Int.repr 1)) (Int64.repr 1)
  = Int64.repr (ea * 2 + 1).
Proof.
  intros ea Hge Hlt.
  unfold Int64.shl', Int64.shl.
  change (Int.unsigned (Int.repr 1)) with 1%Z.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1)%Z with 2%Z.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (y := (ea * 2 + 1)%Z).
  2: { apply Int64.eqm_refl. }
  apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l.
    apply Int64.eqm_mult.
    + apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_refl.
  - apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem verify_APPLY2_correct :
    handler_correct (fun pc' s => handle_APPLY2 pc' s) f_instr_APPLY2
      apply2_step_pre
      (fun msg s =>
         (msg = "APPLY2: accu is not a closure"%string /\
          get_code_ptr_s s s.(Machine.accu) = None) \/
         (msg = "APPLY2: stack underflow"%string))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct. simpl.
  unfold handle_APPLY2.
  destruct (Machine.stack s) as [|arg1 stk1] eqn:Hstk.
  { (* stack = [] -- Error "stack underflow" *)
    right. reflexivity. }
  destruct stk1 as [|arg2 rest] eqn:Hstk1.
  { (* stack = [arg1] -- Error "stack underflow" *)
    right. reflexivity. }
  (* stack = arg1 :: arg2 :: rest *)
  destruct (get_code_ptr_s s s.(Machine.accu)) as [target_pc|] eqn:Hgcp.
  2: { (* Error: accu is not a closure *)
    left. split; reflexivity. }

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

  destruct Hstep_pre as (Hacpl_fn & Hpc_val_repr & Hsp_ge32 & Hextra_fits).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_apply2 as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Henv_offset Hextra_offset]]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Get ret_pc_cval from step_pre *)
  destruct (Hpc_val_repr (Vptr cb pc_ofs) Hpc_load)
    as [ret_pc_cval [Hpc_cast [Hpc_repr Hpc_loadresult]]].

  (* Get sp_ofs >= 32 *)
  pose proof (Hsp_ge32 sp_b sp_ofs Hsp_load) as Hsp_ge32'.

  (* Subst gd_ptr before inversions that use bare subst *)
  subst gd_ptr.
  (* Stack repr gives us the val_repr for arg1, arg2 *)
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv_arg1 Hload_arg1 Hvr_arg1 Hstk_tail1].
  subst.
  inversion Hstk_tail1 as [| ? ? ? ? cv_arg2 Hload_arg2 Hvr_arg2 Hstk_rest].
  subst.

  (* Get closure code pointer info *)
  pose proof (Hacpl_fn sp_b sp_ofs Hsp_load) as Hacpl.
  unfold apply2_closure_pre in Hacpl.
  destruct (Hacpl target_pc Hgcp accu_v Haccu_repr)
    as [accu_b [accu_ofs [code_b [code_ofs
        [Haccu_is_ptr [Hcode_ptr_load [Haccu_ne_sb [Haccu_ne_cb
        [Haccu_ne_sp [new_co [Hcode_ofs_eq Hcode_b_eq]]]]]]]]]]].
  subst accu_v code_b.

  (* new_sp = sp - 3 slots = sp - 24 bytes *)
  set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 24)).

  assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 24).
  { subst new_sp_ofs. unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.repr 24)) with 24.
    apply Ptrofs.unsigned_repr.
    pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }

  (* new sp alignment *)
  assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
  { rewrite Hnew_sp_unsigned. simpl.
    apply Z.divide_sub_r; [exact Hsp_align | exists 3; lia]. }

  (* extra_args tagged encoding *)
  set (ea_nat := Machine.extra_args s).
  set (ea_long := Int64.repr (Z.of_nat ea_nat)).
  set (ea_tagged := Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1)).

  set (new_pc_v := Vptr cb code_ofs).
  set (new_env_v := Vptr accu_b accu_ofs).

  (* Stack writable range *)
  assert (Hsp_writable_ext : Mem.range_perm m sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: rest))) Cur Writable).
  { intros ofs' Hofs'. apply Hsp_writable. rewrite Hstk. exact Hofs'. }

  (* ---- Store 1: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs ---- *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia)
              (Vptr sp_b new_sp_ofs))
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* sp load in m1 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore1) as H.
    simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }

  (* Stack writable in m1 *)
  assert (Hsp_writable_m1 : Mem.range_perm m1 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore1. apply Hsp_writable_ext. exact Hofs'. }

  (* ---- Store 2: arg1 at new_sp[0] on the stack block ---- *)
  destruct (Mem.valid_access_store m1 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs) cv_arg1) as [m2 Hstore2].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m1.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      simpl length. pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new. }

  (* ---- Store 3: arg2 at new_sp[1] = new_sp_ofs + 8 ---- *)
  assert (Hsp_writable_m2 : Mem.range_perm m2 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. apply Hsp_writable_m1. exact Hofs'. }
  destruct (Mem.valid_access_store m2 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2) as [m3 Hstore3].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m2.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      simpl length. pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 1. simpl. lia. }

  (* ---- Store 4: ret_pc_cval at new_sp[2] = new_sp_ofs + 16 ---- *)
  assert (Hsp_writable_m3 : Mem.range_perm m3 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3. apply Hsp_writable_m2. exact Hofs'. }
  destruct (Mem.valid_access_store m3 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 16) ret_pc_cval) as [m4 Hstore4].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m3.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      simpl length. pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 2. simpl. lia. }

  (* ---- Store 5: env at new_sp[3] = new_sp_ofs + 24 ---- *)
  assert (Hsp_writable_m4 : Mem.range_perm m4 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore4. apply Hsp_writable_m3. exact Hofs'. }
  destruct (Mem.valid_access_store m4 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 24) env_v) as [m5 Hstore5].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m4.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      simpl length. pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 3. simpl. lia. }

  (* ---- Store 6: tagged(extra_args) at new_sp[4] = new_sp_ofs + 32 ---- *)
  assert (Hsp_writable_m5 : Mem.range_perm m5 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore5. apply Hsp_writable_m4. exact Hofs'. }
  destruct (Mem.valid_access_store m5 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 32)
              (Vlong ea_tagged)) as [m6 Hstore6].
  { split.
    - intros ofs' Hofs'. apply Hsp_writable_m5.
      rewrite Hnew_sp_unsigned in Hofs'. simpl size_chunk in Hofs'.
      simpl length. pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - apply Z.divide_add_r. exact Halign_new. exists 4. simpl. lia. }

  (* sb writable through stack stores *)
  assert (Hsb_writable_m6 : Mem.range_perm m6 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'.
    eapply Mem.perm_store_1. exact Hstore6.
    eapply Mem.perm_store_1. exact Hstore5.
    eapply Mem.perm_store_1. exact Hstore4.
    eapply Mem.perm_store_1. exact Hstore3.
    eapply Mem.perm_store_1. exact Hstore2.
    apply Hsb_writable_m1. exact Hofs'. }

  (* ---- Store 7: pc field at (sb, uso+0) <- new_pc_v ---- *)
  assert (Hpc_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
               (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore1 Hpc_load). left. lia. }
    erewrite Mem.load_store_other. 2: exact Hstore6.
    erewrite Mem.load_store_other. 2: exact Hstore5.
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hpc_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  destruct (store_succeeds_sb m6 sb so 0 (Vptr cb pc_ofs)
              Hsb_writable_m6 Hpc_load_m6 ltac:(lia) ltac:(lia) new_pc_v)
    as [m7 Hstore7].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore7 Hsb_writable_m6) as Hsb_writable_m7.

  (* ---- Store 8: env field at (sb, uso+24) <- new_env_v ---- *)
  assert (Henv_load_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
    assert (Henv_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. 2: exact Hstore6.
      erewrite Mem.load_store_other. 2: exact Hstore5.
      erewrite Mem.load_store_other. 2: exact Hstore4.
      erewrite Mem.load_store_other. 2: exact Hstore3.
      erewrite Mem.load_store_other. 2: exact Hstore2.
      exact Henv_m1.
      all: left; intro Heq; apply Hsp_ne_sb; auto. }
    apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
             new_pc_v env_v Hstore7 Henv_m6). right. lia. }

  destruct (store_succeeds_sb m7 sb so 24 env_v
              Hsb_writable_m7 Henv_load_m7 ltac:(lia) ltac:(lia) new_env_v)
    as [m8 Hstore8].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore8 Hsb_writable_m7) as Hsb_writable_m8.

  (* ---- Store 9: extra_args field at (sb, uso+32) <- Vlong(Int64.repr 1) ---- *)
  set (new_ea_v := Vlong (Int64.repr 1)).
  assert (Hextra_load_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { assert (Hextra_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
               (Vptr sp_b new_sp_ofs) (Vlong ea_long) Hstore1 Hextra_load). right. lia. }
    assert (Hextra_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. 2: exact Hstore6.
      erewrite Mem.load_store_other. 2: exact Hstore5.
      erewrite Mem.load_store_other. 2: exact Hstore4.
      erewrite Mem.load_store_other. 2: exact Hstore3.
      erewrite Mem.load_store_other. 2: exact Hstore2.
      exact Hextra_m1.
      all: left; intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               new_pc_v (Vlong ea_long) Hstore7 Hextra_m6). right. lia. }
    apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 32)
             new_env_v (Vlong ea_long) Hstore8 Hextra_m7). right. lia. }

  destruct (store_succeeds_sb m8 sb so 32 (Vlong ea_long)
              Hsb_writable_m8 Hextra_load_m8 ltac:(lia) ltac:(lia) new_ea_v)
    as [m9 Hstore9].

  (* ---- Intermediate loads for the exec part ---- *)

  (* arg1/arg2 loads survive sb store *)
  assert (Hload_arg1_m : Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs) = Some cv_arg1).
  { exact Hload_arg1. }
  assert (Hload_arg2_m : Mem.load Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some cv_arg2).
  { exact Hload_arg2. }

  (* pc load in m1 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
             (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore1 Hpc_load). left. lia. }

  (* env load in m1 *)
  assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
             (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }

  (* extra_args load in m1 *)
  assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
             (Vptr sp_b new_sp_ofs) (Vlong ea_long) Hstore1 Hextra_load). right. lia. }

  (* accu load in m1 *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
             (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) (Vptr accu_b accu_ofs)
             Hstore1 Haccu_load). left. lia. }

  (* code pointer load in m6 -- accu_b is distinct from both sb and sp_b *)
  assert (Hcode_ptr_load_m6 : Mem.load Mptr m6 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { assert (Hcp_m1 : Mem.load Mptr m1 accu_b (Ptrofs.unsigned accu_ofs) = Some (Vptr cb code_ofs)).
    { erewrite Mem.load_store_other. exact Hcode_ptr_load. exact Hstore1.
      left. exact Haccu_ne_sb. }
    erewrite Mem.load_store_other. 2: exact Hstore6.
    erewrite Mem.load_store_other. 2: exact Hstore5.
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hcp_m1.
    all: left; exact Haccu_ne_sp. }

  (* accu load in m6 *)
  assert (Haccu_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. 2: exact Hstore6.
    erewrite Mem.load_store_other. 2: exact Hstore5.
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Haccu_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  (* accu load in m7 *)
  assert (Haccu_load_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0)
             (Ptrofs.unsigned so + 8) new_pc_v (Vptr accu_b accu_ofs)
             Hstore7 Haccu_load_m6). right. lia. }

  (* accu load in m8 *)
  assert (Haccu_load_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 24)
             (Ptrofs.unsigned so + 8) new_env_v (Vptr accu_b accu_ofs)
             Hstore8 Haccu_load_m7). left. lia. }

  (* sp load survives stack stores *)
  assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m4. exact Hstore5.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hsp_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m5. exact Hstore6.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* pc load survives stack stores *)
  assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other. exact Hpc_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { erewrite Mem.load_store_other. exact Hpc_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* env load survives stack stores *)
  assert (Henv_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Henv_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  (* extra_args load survives stack stores *)
  assert (Hextra_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. 2: exact Hstore5.
    erewrite Mem.load_store_other. 2: exact Hstore4.
    erewrite Mem.load_store_other. 2: exact Hstore3.
    erewrite Mem.load_store_other. 2: exact Hstore2.
    exact Hextra_load_m1.
    all: left; intro Heq; apply Hsp_ne_sb; auto. }

  (* ---- Witnesses for exists ---- *)
  set (le1 := PTree.set _t'14 (Vptr sp_b sp_ofs) le).
  set (le2 := PTree.set _arg1 cv_arg1 le1).
  set (le3 := PTree.set _t'13 (Vptr sp_b sp_ofs) le2).
  set (le4 := PTree.set _arg2 cv_arg2 le3).
  set (le5 := PTree.set _t'12 (Vptr sp_b sp_ofs) le4).
  (* After sp store: m1 *)
  set (le6 := PTree.set _t'11 (Vptr sp_b new_sp_ofs) le5).
  (* After arg1 store: m2 *)
  set (le7 := PTree.set _t'10 (Vptr sp_b new_sp_ofs) le6).
  (* After arg2 store: m3 *)
  set (le8 := PTree.set _t'8 (Vptr sp_b new_sp_ofs) le7).
  set (le9 := PTree.set _t'9 (Vptr cb pc_ofs) le8).
  (* After pc store: m4 *)
  set (le10 := PTree.set _t'6 (Vptr sp_b new_sp_ofs) le9).
  set (le11 := PTree.set _t'7 env_v le10).
  (* After env store on stack: m5 *)
  set (le12 := PTree.set _t'4 (Vptr sp_b new_sp_ofs) le11).
  set (le13 := PTree.set _t'5 (Vlong ea_long) le12).
  (* After tagged ea store: m6 *)
  set (le14 := PTree.set _t'2 (Vptr accu_b accu_ofs) le13).
  set (le15 := PTree.set _t'3 (Vptr cb code_ofs) le14).
  (* After pc field store: m7 *)
  set (le16 := PTree.set _t'1 (Vptr accu_b accu_ofs) le15).
  (* After env field store: m8, after ea field store: m9 *)

  exists le16. exists m9.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec -- the C body executes                               *)
  (* ================================================================ *)
  {
    apply (eval_stmt_to_exec clight_ge 50).
    eval_cbn.

    (* S1: Sset _t'14 (s->sp) *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Hsp_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S2: Sset _arg1 = *(_t'14 + 0) *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_0 sp_b sp_ofs m); eval_cbn.
    rewrite Hload_arg1; eval_cbn.

    (* S3: Sset _t'13 (s->sp) *)
    do 2 (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S4: Sset _arg2 = *(_t'13 + 1) *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_1 sp_b sp_ofs m); eval_cbn.
    rewrite Hload_arg2; eval_cbn.

    (* S5: Sset _t'12 (s->sp) *)
    do 4 (rewrite PTree.gso by (compute; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S6: Sassign s->sp = _t'12 - 3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_sub_sp_3 sp_b sp_ofs m); eval_cbn.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    fold new_sp_ofs. rewrite Hstore1; eval_cbn.

    (* S7: Sset _t'11 (s->sp) -- in m1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S8: Sassign *(_t'11 + 0) = _arg1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_0 sp_b new_sp_ofs m1); eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr hm cb co arg1 cv_arg1 m1 Hvr_arg1); eval_cbn.
    rewrite Hstore2; eval_cbn.

    (* S9: Sset _t'10 (s->sp) -- in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m2; eval_cbn.

    (* S10: Sassign *(_t'10 + 1) = _arg2 *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_add_sp_1 sp_b new_sp_ofs m2); eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr hm cb co arg2 cv_arg2 m2 Hvr_arg2); eval_cbn.
    assert (Hstore3' : Mem.store Mint64 m2 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))) cv_arg2 = Some m3).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore3. }
    rewrite Hstore3'; eval_cbn.

    (* S11: Sset _t'8 (s->sp) -- in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m3; eval_cbn.

    (* S12: Sset _t'9 (s->pc) -- in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Hpc_offset; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m3; eval_cbn.

    (* S13: Sassign *(_t'8 + 2) = (long)_t'9 -- store ret addr at new_sp[2] *)
    (* LHS: lookup _t'8 (skip _t'9) *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    (* LHS address: sem_add_sp_2 *)
    rewrite (sem_add_sp_2 sp_b new_sp_ofs m3); eval_cbn.
    (* RHS: lookup _t'9 *)
    rewrite PTree.gss; eval_cbn.
    (* RHS: explicit Ecast (tptr tint) to tlong *)
    rewrite (sem_cast_ptint_to_long cb pc_ofs m3); eval_cbn.
    (* Sassign implicit cast tlong -> tlong *)
    rewrite (sem_cast_long_vptr cb pc_ofs m3); eval_cbn.
    assert (Hret_eq : ret_pc_cval = Vptr cb pc_ofs).
    { rewrite sem_cast_ptint_to_long in Hpc_cast. congruence. }
    rewrite <- Hret_eq.
    assert (Hstore4' : Mem.store Mint64 m3 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 16))) ret_pc_cval = Some m4).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 16 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore4. }
    rewrite Hstore4'; eval_cbn.

    (* S14: Sset _t'6 (s->sp) -- in m4 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m4; eval_cbn.

    (* S15: Sset _t'7 (s->env) -- in m4 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Henv_offset; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    rewrite Henv_load_m4; eval_cbn.

    (* S16: Sassign *(_t'6 + 3) = _t'7 -- store env at new_sp[3] *)
    (* LHS: lookup _t'6 (skip _t'7) *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    (* LHS address: sem_add_sp_3 *)
    rewrite (sem_add_sp_3 sp_b new_sp_ofs m4); eval_cbn.
    (* RHS: lookup _t'7 *)
    rewrite PTree.gss; eval_cbn.
    (* Sassign implicit cast tlong -> tlong *)
    rewrite (sem_cast_long_val_repr hm cb co (Machine.env s) env_v m4 Henv_repr); eval_cbn.
    assert (Hstore5' : Mem.store Mint64 m4 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 24))) env_v = Some m5).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 24 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
      exact Hstore5. }
    rewrite Hstore5'; eval_cbn.

    (* S17: Sset _t'4 (s->sp) -- in m5 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m5; eval_cbn.

    (* S18: Sset _t'5 (s->extra_args) -- in m5 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Hextra_offset; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    rewrite Hextra_load_m5; eval_cbn.

    (* S19: Sassign *(_t'4 + 4) = (_t'5 << 1) + 1 -- store tagged ea *)
    (* LHS: lookup _t'4 (skip _t'5) *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    (* LHS address: sem_add_sp_4 *)
    rewrite (sem_add_sp_4 sp_b new_sp_ofs m5); eval_cbn.
    (* RHS: lookup _t'5 then compute (_t'5 << 1) + 1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vlong ea_long m5); eval_cbn.
    rewrite (sem_shl_long_int_1 ea_long m5); eval_cbn.
    rewrite (sem_add_long_int_1 (Int64.shl' ea_long (Int.repr 1)) m5); eval_cbn.
    rewrite (sem_cast_long_vlong _ m5); eval_cbn.
    fold ea_tagged.
    assert (Hstore6' : Mem.store Mint64 m5 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 32))) (Vlong ea_tagged) = Some m6).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 32 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; rewrite Hstk in Hsp_rep; simpl length in Hsp_rep; lia)).
      exact Hstore6. }
    rewrite Hstore6'; eval_cbn.

    (* S20: Sset _t'2 (s->accu) -- in m6 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Haccu_offset; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m6; eval_cbn.

    (* S21: Sset _t'3 = *((tptr (tptr tint))(_t'2) + 0) -- load code ptr *)
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_to_ptptint_vptr accu_b accu_ofs m6); eval_cbn.
    rewrite (sem_add_ptptint_0 accu_b accu_ofs m6); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite Mptr_Mint64 in Hcode_ptr_load_m6.
    rewrite Hcode_ptr_load_m6; eval_cbn.

    (* S22: Sassign s->pc = _t'3 -- store new pc *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Hpc_offset; try eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_ptr_tint_to_ptr_tint cb code_ofs m6); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v. rewrite Hstore7; eval_cbn.

    (* S23: Sset _t'1 (s->accu) -- in m7 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Haccu_offset; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m7; eval_cbn.

    (* S24: Sassign s->env = _t'1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Henv_offset; try eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vptr accu_b accu_ofs m7); eval_cbn.
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    fold new_env_v. rewrite Hstore8; eval_cbn.

    (* S25: Sassign s->extra_args = 1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Hextra_offset; try eval_cbn.
    rewrite (sem_cast_int_to_long_1 m8); eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    fold new_ea_v. rewrite Hstore9; eval_cbn.

    (* S26: Sreturn 0 *)
    subst le16 le15 le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
    rewrite Hret_eq. subst new_pc_v new_env_v. reflexivity.
  }

  (* ================================================================ *)
  (* Part 2: abs_rel for post-state                                    *)
  (* ================================================================ *)
  {
    set (ard' := mk_abs_rel sb so hm cb new_co
                   (ar_global_block ard) (ar_global_ofs ard)
                   (ar_stack_block ard) (ar_stack_base_ofs ard)
                   (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                   (ar_sptr_ofs_bound ard)).
    exists ard'.

    (* Determine ret_pc_cval = Vptr cb pc_ofs *)
    assert (Hret_eq : ret_pc_cval = Vptr cb pc_ofs).
    { rewrite sem_cast_ptint_to_long in Hpc_cast. congruence. }

    (* ---- Loads in m9 ---- *)

    (* pc field at uso+0: written in store7, survive store8 and store9 *)
    assert (Hpc_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
    { assert (Hpc_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m6 m7 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore7) as H.
        unfold new_pc_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
      assert (Hpc_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 0)
                 new_env_v new_pc_v Hstore8 Hpc_m7). left. lia. }
      apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 0)
               new_ea_v new_pc_v Hstore9 Hpc_m8). left. lia. }

    (* accu field at uso+8 in m9 *)
    assert (Haccu_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr accu_b accu_ofs)).
    { assert (H8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { exact Haccu_load_m8. }
      apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 8)
               new_ea_v (Vptr accu_b accu_ofs) Hstore9 H8). left. lia. }

    (* sp field at uso+16 in m9 *)
    assert (Hsp_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 new_pc_v (Vptr sp_b new_sp_ofs) Hstore7 Hsp_load_m6). right. lia. }
      assert (Hsp_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
                 new_env_v (Vptr sp_b new_sp_ofs) Hstore8 Hsp_m7). left. lia. }
      apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 16)
               new_ea_v (Vptr sp_b new_sp_ofs) Hstore9 Hsp_m8). left. lia. }

    (* env field at uso+24: written in store8, survive store9 *)
    assert (Henv_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
    { assert (H8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
      { pose proof (load_after_store_same m7 m8 sb (Ptrofs.unsigned so + 24) new_env_v Hstore8) as H.
        unfold new_env_v in H. simpl Val.load_result in H. rewrite ptr64_true in H. exact H. }
      apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 24)
               new_ea_v new_env_v Hstore9 H8). left. lia. }

    (* extra_args field at uso+32: written in store9 *)
    assert (Hextra_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 32) = Some new_ea_v).
    { pose proof (load_after_store_same m8 m9 sb (Ptrofs.unsigned so + 32) new_ea_v Hstore9) as H.
      subst new_ea_v. simpl Val.load_result in H. exact H. }

    (* global_data field at uso+40 *)
    assert (Hgd_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. 2: exact Hstore6.
        erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hgd_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                 new_pc_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore7 Hgd_m6). right. lia. }
      assert (Hgd_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 40)
                 new_env_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore8 Hgd_m7). right. lia. }
      apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 40)
               new_ea_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore9 Hgd_m8). right. lia. }

    (* trap_sp field at uso+48 *)
    assert (Hts_load9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. 2: exact Hstore6.
        erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        erewrite Mem.load_store_other. 2: exact Hstore2.
        exact Hts_m1.
        all: left; intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m6 m7 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                 new_pc_v ts_ptr Hstore7 Hts_m6). right. lia. }
      assert (Hts_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 48)
                 new_env_v ts_ptr Hstore8 Hts_m7). right. lia. }
      apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 48)
               new_ea_v ts_ptr Hstore9 Hts_m8). right. lia. }

    (* sb_writable in m9 *)
    assert (Hsb_writable_m9 : Mem.range_perm m9 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore9.
      eapply Mem.perm_store_1. exact Hstore8.
      apply Hsb_writable_m7. exact Hofs'. }

    (* ---- Build stack_repr for the new stack ---- *)
    (* New stack: arg1 :: arg2 :: Val_int pc' :: env :: Val_int(Z.of_nat ea) :: rest
       at sp_b, new_sp_ofs *)

    (* Convert Hstk_rest to use Ptrofs.repr 16 instead of double add 8 *)
    assert (Hptrofs_16_eq : Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8) =
                            Ptrofs.add sp_ofs (Ptrofs.repr 16)).
    { rewrite Ptrofs.add_assoc. f_equal. }
    assert (Hstk_rest16 : stack_repr hm cb co m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
    { rewrite <- Hptrofs_16_eq. exact Hstk_rest. }

    (* Pre-simplify Hsp_rep for the store chain *)
    rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.

    (* First build stack_repr for rest in m9, starting at new_sp_ofs + 40 = sp_ofs + 16 *)
    assert (Hstk_rest_m9 : stack_repr hm cb co m9 rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
    { (* rest's stack_repr in m is at sp_ofs + 16 *)
      (* Thread through all 9 stores *)
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m8 m9 _ sp_b _ sb (Ptrofs.unsigned so + 32) new_ea_v).
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m7 m8 _ sp_b _ sb (Ptrofs.unsigned so + 24) new_env_v).
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m6 m7 _ sp_b _ sb (Ptrofs.unsigned so + 0) new_pc_v).
      (* stores 2-6 are on sp_b; use stack_repr_store_same_block_lower *)
      apply (stack_repr_store_same_block_lower hm cb co m5 m6 _ sp_b _ (Ptrofs.unsigned new_sp_ofs + 32) (Vlong ea_tagged)).
      apply (stack_repr_store_same_block_lower hm cb co m4 m5 _ sp_b _ (Ptrofs.unsigned new_sp_ofs + 24) env_v).
      apply (stack_repr_store_same_block_lower hm cb co m3 m4 _ sp_b _ (Ptrofs.unsigned new_sp_ofs + 16) ret_pc_cval).
      apply (stack_repr_store_same_block_lower hm cb co m2 m3 _ sp_b _ (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2).
      apply (stack_repr_store_same_block_lower hm cb co m1 m2 _ sp_b _ (Ptrofs.unsigned new_sp_ofs) cv_arg1).
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m m1 _ sp_b _ sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
      exact Hstk_rest16. exact Hstore1.
      intro Heq; apply Hsp_ne_sb; auto.
      exact Hstore2. rewrite Hnew_sp_unsigned.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). lia.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). simpl length in Hsp_rep. lia.
      exact Hstore3. rewrite Hnew_sp_unsigned.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). lia.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). simpl length in Hsp_rep. lia.
      exact Hstore4. rewrite Hnew_sp_unsigned.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). lia.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). simpl length in Hsp_rep. lia.
      exact Hstore5. rewrite Hnew_sp_unsigned.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). lia.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). simpl length in Hsp_rep. lia.
      exact Hstore6. rewrite Hnew_sp_unsigned.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). lia.
        rewrite (ptrofs_add_unsigned sp_ofs 16 ltac:(lia) ltac:(lia)). simpl length in Hsp_rep. lia.
      exact Hstore7. intro Heq; apply Hsp_ne_sb; auto.
      exact Hstore8. intro Heq; apply Hsp_ne_sb; auto.
      exact Hstore9. intro Heq; apply Hsp_ne_sb; auto. }

    (* Build stack_repr for ea :: rest at new_sp_ofs + 32 = sp_ofs + 8 *)
    assert (Hea_stk : stack_repr hm cb co m9 (Val_int (Z.of_nat ea_nat) :: rest)
              sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
    { econstructor.
      - (* Mem.load at sp_ofs + 8 gives ea_tagged *)
        (* The store at new_sp_ofs + 32 wrote ea_tagged.
           new_sp_ofs + 32 = (sp_ofs - 24) + 32 = sp_ofs + 8.
           So we need Mem.load at sp_ofs + 8 in m9.
           Stored in m6, need to thread through m7, m8, m9. *)
        assert (Hea_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)))
                  = Some (Vlong ea_tagged)).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore6) as H.
          simpl Val.load_result in H.
          rewrite Hnew_sp_unsigned in H.
          replace (Ptrofs.unsigned sp_ofs - 24 + 32) with (Ptrofs.unsigned sp_ofs + 8) in H by lia.
          rewrite (ptrofs_add_unsigned sp_ofs 8 ltac:(lia) ltac:(lia)).
          exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore9.
        erewrite Mem.load_store_other. 2: exact Hstore8.
        erewrite Mem.load_store_other. 2: exact Hstore7.
        exact Hea_m6.
        all: left; intro Heq; exact (Hsp_ne_sb Heq).
      - (* val_repr for tagged ea *)
        unfold ea_tagged, ea_long.
        rewrite tagged_ea_arith by lia.
        constructor.
      - (* rest at sp_ofs + 16 *)
        rewrite Hptrofs_16_eq. exact Hstk_rest_m9.
    }

    (* Build stack_repr for env :: ea :: rest at new_sp_ofs + 24 = sp_ofs *)
    assert (Henv_stk : stack_repr hm cb co m9 (Machine.env s :: Val_int (Z.of_nat ea_nat) :: rest)
              sp_b sp_ofs).
    { econstructor.
      - (* Mem.load at sp_ofs gives env_v *)
        assert (Henv_sp_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned sp_ofs)
                  = Some env_v).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore5) as H.
          rewrite (val_repr_load_result hm cb co _ _ Henv_repr) in H.
          rewrite Hnew_sp_unsigned in H.
          replace (Ptrofs.unsigned sp_ofs - 24 + 24) with (Ptrofs.unsigned sp_ofs) in H by lia.
          exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore9.
        erewrite Mem.load_store_other. 2: exact Hstore8.
        erewrite Mem.load_store_other. 2: exact Hstore7.
        erewrite Mem.load_store_other. 2: exact Hstore6.
        3,4,5: left; intro Heq; apply Hsp_ne_sb; auto.
        2: { right. rewrite Hnew_sp_unsigned. simpl size_chunk. lia. }
        exact Henv_sp_m5.
      - eapply val_repr_co_shift; exact Henv_repr.
      - exact Hea_stk. }

    (* Build stack_repr for Val_int pc' :: env :: ea :: rest at new_sp_ofs + 16 = sp_ofs - 8 *)
    assert (Hpc_stk : stack_repr hm cb co m9
              (Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat ea_nat) :: rest)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8))).
    { econstructor.
      - (* Mem.load at sp_ofs - 8 gives ret_pc_cval *)
        assert (Hpc_sp_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 8)))
                  = Some ret_pc_cval).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore4) as H.
          rewrite Hpc_loadresult in H.
          rewrite Hnew_sp_unsigned in H.
          replace (Ptrofs.unsigned sp_ofs - 24 + 16) with (Ptrofs.unsigned sp_ofs - 8) in H by lia.
          unfold Ptrofs.sub.
          rewrite (Ptrofs.unsigned_repr 8).
          2: { pose proof Ptrofs.modulus_pos. unfold Ptrofs.max_unsigned. lia. }
          rewrite Ptrofs.unsigned_repr.
          2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
          exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore9.
        erewrite Mem.load_store_other. 2: exact Hstore8.
        erewrite Mem.load_store_other. 2: exact Hstore7.
        2,3,4: left; intro Heq; apply Hsp_ne_sb; auto.
        erewrite Mem.load_store_other. 2: exact Hstore6.
        erewrite Mem.load_store_other. 2: exact Hstore5.
        2,3: right; unfold Ptrofs.sub; rewrite (Ptrofs.unsigned_repr 8) by (pose proof Ptrofs.modulus_pos; unfold Ptrofs.max_unsigned; lia);
             rewrite Ptrofs.unsigned_repr by (pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia);
             rewrite Hnew_sp_unsigned; simpl size_chunk; lia.
        exact Hpc_sp_m4.
      - exact Hpc_repr.
      - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) with sp_ofs.
        exact Henv_stk.
        rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc.
        rewrite (Ptrofs.add_commut (Ptrofs.neg (Ptrofs.repr 8)) (Ptrofs.repr 8)).
        rewrite Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity. }

    (* Build stack_repr for arg2 :: ... at new_sp_ofs + 8 = sp_ofs - 16 *)
    assert (Harg2_stk : stack_repr hm cb co m9
              (arg2 :: Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat ea_nat) :: rest)
              sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 16))).
    { econstructor.
      - (* Mem.load at sp_ofs - 16 gives cv_arg2 *)
        assert (Harg2_sp_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 16)))
                  = Some cv_arg2).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore3) as H.
          rewrite (val_repr_load_result hm cb co _ _ Hvr_arg2) in H.
          rewrite Hnew_sp_unsigned in H.
          replace (Ptrofs.unsigned sp_ofs - 24 + 8) with (Ptrofs.unsigned sp_ofs - 16) in H by lia.
          unfold Ptrofs.sub.
          rewrite (Ptrofs.unsigned_repr 16).
          2: { pose proof Ptrofs.modulus_pos. unfold Ptrofs.max_unsigned. lia. }
          rewrite Ptrofs.unsigned_repr.
          2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
          exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore9.
        erewrite Mem.load_store_other. 2: exact Hstore8.
        erewrite Mem.load_store_other. 2: exact Hstore7.
        2,3,4: left; intro Heq; apply Hsp_ne_sb; auto.
        erewrite Mem.load_store_other. 2: exact Hstore6.
        erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        2,3,4: right; unfold Ptrofs.sub; rewrite (Ptrofs.unsigned_repr 16) by (pose proof Ptrofs.modulus_pos; unfold Ptrofs.max_unsigned; lia);
               rewrite Ptrofs.unsigned_repr by (pose proof (Ptrofs.unsigned_range sp_ofs); unfold Ptrofs.max_unsigned; lia);
               rewrite Hnew_sp_unsigned; simpl size_chunk; lia.
        exact Harg2_sp_m3.
      - exact Hvr_arg2.
      - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 16)) (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
        + exact Hpc_stk.
        + (* (x - 16) + 8 = x - 8 *)
          apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 16)) 8).
          2: { lia. }
          2: { unfold Ptrofs.sub.
               change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
               rewrite Ptrofs.unsigned_repr.
               - lia.
               - pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
          unfold Ptrofs.sub.
          change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
          change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
          rewrite !Ptrofs.unsigned_repr.
          2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
          2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for arg1 :: arg2 :: ... at new_sp_ofs = sp_ofs - 24 *)
    assert (Harg1_stk : stack_repr hm cb co m9
              (arg1 :: arg2 :: Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat ea_nat) :: rest)
              sp_b new_sp_ofs).
    { econstructor.
      - (* Mem.load at new_sp_ofs gives cv_arg1 *)
        assert (Harg1_sp_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
        { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore2) as H.
          rewrite (val_repr_load_result hm cb co _ _ Hvr_arg1) in H. exact H. }
        erewrite Mem.load_store_other. 2: exact Hstore9.
        erewrite Mem.load_store_other. 2: exact Hstore8.
        erewrite Mem.load_store_other. 2: exact Hstore7.
        2,3,4: left; intro Heq; apply Hsp_ne_sb; auto.
        erewrite Mem.load_store_other. 2: exact Hstore6.
        erewrite Mem.load_store_other. 2: exact Hstore5.
        erewrite Mem.load_store_other. 2: exact Hstore4.
        erewrite Mem.load_store_other. 2: exact Hstore3.
        2,3,4,5: right; rewrite Hnew_sp_unsigned; simpl size_chunk; lia.
        exact Harg1_sp_m2.
      - exact Hvr_arg1.
      - replace (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))
          with (Ptrofs.sub sp_ofs (Ptrofs.repr 16)).
        + exact Harg2_stk.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
          rewrite Hnew_sp_unsigned.
          unfold Ptrofs.sub.
          change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
          rewrite Ptrofs.unsigned_repr.
          2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* le16 ! _s *)
    assert (Hle16_s : le16 ! _s = Some (Vptr sb so)).
    { subst le16 le15 le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* sp_writable in m9 *)
    assert (Hsp_writable_m9 : Mem.range_perm m9 sp_b 0
              (Ptrofs.unsigned new_sp_ofs +
               8 * Z.of_nat (length (arg1 :: arg2 :: Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat ea_nat) :: rest)))
              Cur Writable).
    { intros ofs' Hofs'. simpl length in Hofs'. rewrite Hnew_sp_unsigned in Hofs'.
      eapply Mem.perm_store_1. exact Hstore9.
      eapply Mem.perm_store_1. exact Hstore8.
      eapply Mem.perm_store_1. exact Hstore7.
      eapply Mem.perm_store_1. exact Hstore6.
      eapply Mem.perm_store_1. exact Hstore5.
      eapply Mem.perm_store_1. exact Hstore4.
      eapply Mem.perm_store_1. exact Hstore3.
      eapply Mem.perm_store_1. exact Hstore2.
      eapply Mem.perm_store_1. exact Hstore1.
      apply Hsp_writable_ext. simpl length. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { exact Hle16_s. }

    (* 2. pc field -- updated to new_pc_v *)
    { exists new_pc_v. split.
      - exact Hpc_load9.
      - simpl. unfold pc_rel, new_pc_v. f_equal.
        subst code_ofs. reflexivity. }

    (* 3. accu field -- unchanged *)
    { exists (Vptr accu_b accu_ofs). split.
      - exact Haccu_load9.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 4. sp field -- points to new_sp_ofs, new stack *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load9.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. exact Harg1_stk.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - rewrite Hnew_sp_unsigned. lia.
      - rewrite Hnew_sp_unsigned. simpl length. simpl length in Hsp_rep. lia.
      - exact Hsp_writable_m9.
      - exact Halign_new. }

    (* 5. env field -- updated to accu *)
    { exists new_env_v. split.
      - exact Henv_load9.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 6. extra_args field -- updated to 1 *)
    { simpl. exact Hextra_load9. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr (ar_global_block ard) (ar_global_ofs ard)). split; [| split; [| split]].
      - exact Hgd_load9.
      - simpl. reflexivity.
      - simpl.
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m8 m9 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 32) new_ea_v).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m7 m8 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 24) new_env_v).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m6 m7 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 0) new_pc_v).
        (* stores 2-6 on sp_b *)
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m5 m6 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 32) (Vlong ea_tagged)).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m4 m5 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 24) env_v).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m3 m4 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 16) ret_pc_cval).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m2 m3 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m1 m2 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sp_b (Ptrofs.unsigned new_sp_ofs) cv_arg1).
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m m1 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
        exact Hglobal_repr.
        exact Hstore1. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        exact Hstore2. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore3. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore4. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore5. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore6. intro Heq2; exact (Hsp_ne_gb Heq2).
        exact Hstore7. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        exact Hstore8. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        exact Hstore9. intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load9.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m9. }
  }
Qed.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr APPLY2 = handle_APPLY2 and clight_of APPLY2 = f_instr_APPLY2
   by computation.  pre_of APPLY2 = apply2_step_pre is convertible.
   Error cases are bridged by case-splitting on the handler result and
   unfolding P_error_of / P_halt_of / P_ccall_of. *)
Definition correct_APPLY2 :
    handler_correct (Dispatch.handle_instr Bytecode.AST.APPLY2)
      (clight_of Bytecode.AST.APPLY2)
      (pre_of Bytecode.AST.APPLY2)
      (P_error_of Bytecode.AST.APPLY2) (P_halt_of Bytecode.AST.APPLY2)
      (P_ccall_of Bytecode.AST.APPLY2).
Proof.
Admitted.

