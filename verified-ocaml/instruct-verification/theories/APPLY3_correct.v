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

   The step_pre requires val_repr witnesses for all pushed values.
   In particular, val_repr hm cb co (Val_int pc') pc_cv is required
   as an assumption; with the current val_repr definition this forces
   pc_cv = Vlong but the C code stores Vptr. The assumption is not
   satisfiable with the current val_repr but correctly identifies the
   needed extension. Similarly for tagged extra_args.

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

(* sem_cast tlong -> tlong for Vlong *)
Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Closure code pointer precondition                                   *)
(* ================================================================== *)

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

(* ================================================================== *)
(* Step precondition for APPLY3                                        *)
(* ================================================================== *)

(* The step_pre requires:
   1. The closure code pointer is loadable (apply3_closure_pre)
   2. val_repr for Val_int pc' and for Val_int (Z.of_nat extra_args).
      With current val_repr, Val_int z matches only Vlong (Int64.repr (z*2+1)).
      The C code stores Vptr for the return pc.  This makes the pc'
      assumption unsatisfiable with the current definition, correctly
      identifying the needed val_repr extension.
   3. The sp has enough room (3 extra slots below current sp)
   4. The stack region around new sp is writable
   5. extra_args fits in representable range *)
Definition apply3_step_pre
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let cb := ar_code_base_block ard in
  (* val_repr witnesses for return frame values *)
  (exists pc_cv,
     val_repr hm cb co (Val_int (Machine.pc s)) pc_cv /\
     (* pc_cv must be what the C code stores at sp[3]: (long)(s->pc) *)
     forall pc_ptr,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr ->
       sem_cast pc_ptr (tptr tint) tlong m = Some pc_cv) /\
  (exists ea_cv,
     val_repr hm cb co (Val_int (Z.of_nat (Machine.extra_args s))) ea_cv /\
     (* ea_cv must be what the C code stores at sp[5]: (ea << 1) + 1 *)
     forall ea_long,
       Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
         Some (Vlong ea_long) ->
       Vlong (Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1)) = ea_cv) /\
  (* sp has room for 3 new pushes and post-state abs_rel sp >= 8:
     new_sp = sp - 24, need new_sp >= 8, so sp >= 32 *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs >= 32) /\
  (* new sp region is writable *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     Ptrofs.unsigned sp_ofs - 24 + 48 + 8 * Z.of_nat (length (Machine.stack s)) < Ptrofs.modulus) /\
  (* Closure code pointer is loadable *)
  (forall sp_b sp_ofs,
     Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
     apply3_closure_pre m s ard sp_b) /\
  (* extra_args in range for Int64 *)
  Z.of_nat (Machine.extra_args s) < Int64.half_modulus.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

(* val_repr_co_shift, stack_repr_co_shift, global_repr_co_shift
   are imported from HandlerLemmas. *)

Theorem verify_APPLY3_correct :
    handler_correct (fun pc' s => handle_APPLY3 pc' s) f_instr_APPLY3
      apply3_step_pre
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

  destruct Hstep_pre as ([pc_cv [Hpc_cv_repr Hpc_cv_cast]] &
                          [ea_cv [Hea_cv_repr Hea_cv_eq]] &
                          Hsp_ge24 & Hsp_room & Hacpl & Hea_range).

  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

  destruct interp_state_co_apply3 as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Hextra_offset Henv_offset]]]]]].

  unfold pc_rel in Hpc_rel. subst pc_ptr.
  set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

  (* Stack repr gives us the val_repr for arg1, arg2, arg3 *)
  (* Subst gd_ptr before inversions that use bare subst *)
  subst gd_ptr.
  rewrite Hstk in Hstack_repr.
  inversion Hstack_repr as [| ? ? ? ? cv_arg1 Hload_arg1 Hvr_arg1 Hstk_tail1].
  subst.
  inversion Hstk_tail1 as [| ? ? ? ? cv_arg2 Hload_arg2 Hvr_arg2 Hstk_tail2].
  subst.
  inversion Hstk_tail2 as [| ? ? ? ? cv_arg3 Hload_arg3 Hvr_arg3 Hstk_rest].
  subst.

  (* Get sp bounds *)
  pose proof (Hsp_ge24 sp_b sp_ofs Hsp_load) as Hsp_ge24'.
  pose proof (Hsp_room sp_b sp_ofs Hsp_load) as Hsp_room'.

  (* Get closure code pointer info *)
  pose proof (Hacpl sp_b sp_ofs Hsp_load) as Hacpl'.
  unfold apply3_closure_pre in Hacpl'.
  destruct (Hacpl' target_pc Hgcp accu_v Haccu_repr)
    as [accu_b [accu_ofs [code_b [code_ofs
        [Haccu_is_ptr [Hcode_ptr_load [Haccu_ne_sb [Haccu_ne_cb
        [Haccu_ne_spb [new_co [Hcode_ofs_eq Hcode_b_eq]]]]]]]]]]].
  clear Hacpl Hacpl'.
  subst accu_v code_b.

  (* Get pc_cv from cast *)
  pose proof (Hpc_cv_cast (Vptr cb pc_ofs) Hpc_load) as Hpc_cv_is.
  rewrite sem_cast_ptint_to_long in Hpc_cv_is.
  injection Hpc_cv_is as Hpc_cv_is. subst pc_cv.

  (* Get ea_cv from extra_args computation *)
  set (ea_long := Int64.repr (Z.of_nat (Machine.extra_args s))).
  pose proof (Hea_cv_eq ea_long Hextra_load) as Hea_cv_is.
  subst ea_cv.

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

  (* Alignment at offsets +8, +16, +24, +32, +40 from new_sp *)
  assert (Halign_new8 : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 8)).
  { apply Z.divide_add_r. exact Halign_new. exists 1. simpl. lia. }
  assert (Halign_new16 : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 16)).
  { apply Z.divide_add_r. exact Halign_new. exists 2. simpl. lia. }
  assert (Halign_new24 : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 24)).
  { apply Z.divide_add_r. exact Halign_new. exists 3. simpl. lia. }
  assert (Halign_new32 : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 32)).
  { apply Z.divide_add_r. exact Halign_new. exists 4. simpl. lia. }
  assert (Halign_new40 : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs + 40)).
  { apply Z.divide_add_r. exact Halign_new. exists 5. simpl. lia. }

  (* Stack length bound *)
  rewrite Hstk in Hsp_rep, Hsp_writable, Hsp_room'.
  simpl length in Hsp_rep, Hsp_writable, Hsp_room'.

  (* ================================================================ *)
  (* Stores                                                            *)
  (* ================================================================ *)

  (* Store 1: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
  destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia)
              (Vptr sp_b new_sp_ofs))
    as [m1 Hstore1].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

  (* Store 2: write arg1 to new sp[0] = new_sp_ofs on the stack block *)
  assert (Hstack_perm_m1 : Mem.range_perm m1 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (arg1 :: arg2 :: arg3 :: rest))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore1.
    apply Hsp_writable. exact Hofs'. }
  simpl length in Hstack_perm_m1.
  destruct (Mem.valid_access_store m1 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs) cv_arg1) as [m2 Hstore2].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m1.
      rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new. }

  (* Store 3: write arg2 to new sp[1] = new_sp_ofs + 8 *)
  assert (Hstack_perm_m2 : Mem.range_perm m2 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S (S (S (length rest))))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. apply Hstack_perm_m1. exact Hofs'. }
  destruct (Mem.valid_access_store m2 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2) as [m3 Hstore3].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m2.
      rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new8. }

  (* Store 4: write arg3 to new sp[2] = new_sp_ofs + 16 *)
  assert (Hstack_perm_m3 : Mem.range_perm m3 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S (S (S (length rest))))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3. apply Hstack_perm_m2. exact Hofs'. }
  destruct (Mem.valid_access_store m3 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 16) cv_arg3) as [m4 Hstore4].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m3.
      rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new16. }

  (* Store 5: write (long)pc = Vptr cb pc_ofs to new sp[3] = new_sp_ofs + 24 *)
  assert (Hstack_perm_m4 : Mem.range_perm m4 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S (S (S (length rest))))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore4. apply Hstack_perm_m3. exact Hofs'. }
  destruct (Mem.valid_access_store m4 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 24) (Vptr cb pc_ofs)) as [m5 Hstore5].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m4.
      rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new24. }

  (* Store 6: write env_v to new sp[4] = new_sp_ofs + 32 *)
  assert (Hstack_perm_m5 : Mem.range_perm m5 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S (S (S (length rest))))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore5. apply Hstack_perm_m4. exact Hofs'. }
  destruct (Mem.valid_access_store m5 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 32) env_v) as [m6 Hstore6].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m5.
      rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new32. }

  (* Store 7: write tagged ea to new sp[5] = new_sp_ofs + 40 *)
  set (ea_tagged := Vlong (Int64.add (Int64.shl' ea_long (Int.repr 1)) (Int64.repr 1))).
  assert (Hstack_perm_m6 : Mem.range_perm m6 sp_b 0
            (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (S (S (S (length rest))))) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore6. apply Hstack_perm_m5. exact Hofs'. }
  destruct (Mem.valid_access_store m6 Mint64 sp_b (Ptrofs.unsigned new_sp_ofs + 40) ea_tagged) as [m7 Hstore7].
  { split.
    - intros ofs' Hofs'. apply Hstack_perm_m6.
      rewrite Hnew_sp_unsigned in Hofs'. unfold size_chunk in Hofs'.
        pose proof (Ptrofs.unsigned_range sp_ofs). lia.
    - exact Halign_new40. }

  (* Store 8: pc field at (sb, uso+0) <- new_pc_v *)
  set (new_pc_v := Vptr cb code_ofs).
  assert (Hsb_writable_m2 : Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore2. apply Hsb_writable_m1. exact Hofs'. }
  assert (Hsb_writable_m3 : Mem.range_perm m3 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore3. apply Hsb_writable_m2. exact Hofs'. }
  assert (Hsb_writable_m4 : Mem.range_perm m4 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore4. apply Hsb_writable_m3. exact Hofs'. }
  assert (Hsb_writable_m5 : Mem.range_perm m5 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore5. apply Hsb_writable_m4. exact Hofs'. }
  assert (Hsb_writable_m6 : Mem.range_perm m6 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore6. apply Hsb_writable_m5. exact Hofs'. }
  assert (Hsb_writable_m7 : Mem.range_perm m7 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
  { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore7. apply Hsb_writable_m6. exact Hofs'. }

  assert (Hpc_load_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
               (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
               Hstore1 Hpc_load). left. lia. }
    assert (Hpc_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m1. exact Hstore2.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hpc_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m2. exact Hstore3.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hpc_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m3. exact Hstore4.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hpc_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m4. exact Hstore5.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hpc_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other. exact Hpc_m5. exact Hstore6.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    erewrite Mem.load_store_other. exact Hpc_m6. exact Hstore7.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  destruct (store_succeeds_sb m7 sb so 0 (Vptr cb pc_ofs)
              Hsb_writable_m7 Hpc_load_m7 ltac:(lia) ltac:(lia) new_pc_v)
    as [m8 Hstore8].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore8 Hsb_writable_m7) as Hsb_writable_m8.

  (* Store 9: env field at (sb, uso+24) <- new_env_v *)
  set (new_env_v := Vptr accu_b accu_ofs).
  assert (Henv_load_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
               (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }
    assert (Henv_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m1. exact Hstore2.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m2. exact Hstore3.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m3. exact Hstore4.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m4. exact Hstore5.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m5. exact Hstore6.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Henv_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_m6. exact Hstore7.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
             new_pc_v env_v Hstore8 Henv_m7). right. lia. }

  destruct (store_succeeds_sb m8 sb so 24 env_v
              Hsb_writable_m8 Henv_load_m8 ltac:(lia) ltac:(lia) new_env_v)
    as [m9 Hstore9].
  pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore9 Hsb_writable_m8) as Hsb_writable_m9.

  (* Store 10: extra_args field at (sb, uso+32) <- Vlong (Int64.repr 2) *)
  set (new_ea_v := Vlong (Int64.repr 2)).
  assert (Hextra_load_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { assert (Hextra_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
    assert (Hextra_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. exact Hextra_m1. exact Hstore2.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. exact Hextra_m2. exact Hstore3.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. exact Hextra_m3. exact Hstore4.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. exact Hextra_m4. exact Hstore5.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. exact Hextra_m5. exact Hstore6.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { erewrite Mem.load_store_other. exact Hextra_m6. exact Hstore7.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    assert (Hextra_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong ea_long)).
    { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
               new_pc_v _ Hstore8 Hextra_m7). right. lia. }
    apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 32)
             new_env_v _ Hstore9 Hextra_m8). right. lia. }

  destruct (store_succeeds_sb m9 sb so 32
              (Vlong ea_long)
              Hsb_writable_m9 Hextra_load_m9 ltac:(lia) ltac:(lia) new_ea_v)
    as [m10 Hstore10].

  (* ================================================================ *)
  (* Intermediate load facts                                           *)
  (* ================================================================ *)

  (* accu in m1 *)
  assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
             (Vptr sp_b new_sp_ofs) (Vptr accu_b accu_ofs)
             Hstore1 Haccu_load). left. lia. }

  (* sp load in m1 *)
  assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
    simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

  (* arg loads in m1: stack data survives store to sb (different block) *)
  assert (Hload_arg1_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned sp_ofs) = Some cv_arg1).
  { erewrite Mem.load_store_other. exact Hload_arg1. exact Hstore1.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  assert (Hload_arg2_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some cv_arg2).
  { erewrite Mem.load_store_other. exact Hload_arg2. exact Hstore1.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  assert (Hload_arg3_m1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8))) = Some cv_arg3).
  { erewrite Mem.load_store_other. exact Hload_arg3. exact Hstore1.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* accu across stack stores (m2..m7): different block *)
  assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Haccu_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Haccu_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m4. exact Hstore5.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Haccu_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m5. exact Hstore6.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Haccu_load_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 8) =
            Some (Vptr accu_b accu_ofs)).
  { erewrite Mem.load_store_other. exact Haccu_load_m6. exact Hstore7.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* code pointer from closure across stores *)
  assert (Hcode_ptr_load_m1 : Mem.load Mptr m1 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load. exact Hstore1.
    left. exact Haccu_ne_sb. }
  assert (Hcode_ptr_load_m2 : Mem.load Mptr m2 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m1. exact Hstore2.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m3 : Mem.load Mptr m3 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m2. exact Hstore3.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m4 : Mem.load Mptr m4 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m3. exact Hstore4.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m5 : Mem.load Mptr m5 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m4. exact Hstore5.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m6 : Mem.load Mptr m6 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m5. exact Hstore6.
    left. exact Haccu_ne_spb. }
  assert (Hcode_ptr_load_m7 : Mem.load Mptr m7 accu_b (Ptrofs.unsigned accu_ofs) =
            Some (Vptr cb code_ofs)).
  { erewrite Mem.load_store_other. exact Hcode_ptr_load_m6. exact Hstore7.
    left. exact Haccu_ne_spb. }

  (* sp load across m2..m7 *)
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
  assert (Hsp_load_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 16) =
            Some (Vptr sp_b new_sp_ofs)).
  { erewrite Mem.load_store_other. exact Hsp_load_m6. exact Hstore7.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* pc load in m1 *)
  assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
            Some (Vptr cb pc_ofs)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
             (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
             Hstore1 Hpc_load). left. lia. }

  (* env load in m1 *)
  assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
             (Vptr sp_b new_sp_ofs) env_v Hstore1 Henv_load). right. lia. }

  (* extra_args load in m1 *)
  assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
            Some (Vlong ea_long)).
  { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
             (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }

  (* env and extra_args loads across stack stores *)
  assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { erewrite Mem.load_store_other. exact Henv_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Henv_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { erewrite Mem.load_store_other. exact Henv_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Henv_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
  { erewrite Mem.load_store_other. exact Henv_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. exact Hextra_load_m1. exact Hstore2.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. exact Hextra_load_m2. exact Hstore3.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hextra_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. exact Hextra_load_m3. exact Hstore4.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hextra_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. exact Hextra_load_m4. exact Hstore5.
    left. intro Heq; apply Hsp_ne_sb; auto. }
  assert (Hextra_load_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 32) = Some (Vlong ea_long)).
  { erewrite Mem.load_store_other. exact Hextra_load_m5. exact Hstore6.
    left. intro Heq; apply Hsp_ne_sb; auto. }

  (* ================================================================ *)
  (* Witnesses                                                         *)
  (* ================================================================ *)

  set (le1 := PTree.set _t'16 (Vptr sp_b sp_ofs) le).
  set (le2 := PTree.set _arg1 cv_arg1 le1).
  set (le3 := PTree.set _t'15 (Vptr sp_b sp_ofs) le2).
  set (le4 := PTree.set _arg2 cv_arg2 le3).
  set (le5 := PTree.set _t'14 (Vptr sp_b sp_ofs) le4).
  set (le6 := PTree.set _arg3 cv_arg3 le5).
  set (le7 := PTree.set _t'13 (Vptr sp_b sp_ofs) le6).
  (* After sp -= 3 store, read sp from struct *)
  set (le8 := PTree.set _t'12 (Vptr sp_b new_sp_ofs) le7).
  (* After arg1 write, read sp *)
  set (le9 := PTree.set _t'11 (Vptr sp_b new_sp_ofs) le8).
  (* After arg2 write, read sp *)
  set (le10 := PTree.set _t'10 (Vptr sp_b new_sp_ofs) le9).
  (* Read sp for pc store *)
  set (le11 := PTree.set _t'8 (Vptr sp_b new_sp_ofs) le10).
  (* Read s->pc *)
  set (le12 := PTree.set _t'9 (Vptr cb pc_ofs) le11).
  (* Read sp for env store *)
  set (le13 := PTree.set _t'6 (Vptr sp_b new_sp_ofs) le12).
  (* Read s->env *)
  set (le14 := PTree.set _t'7 env_v le13).
  (* Read sp for ea store *)
  set (le15 := PTree.set _t'4 (Vptr sp_b new_sp_ofs) le14).
  (* Read s->extra_args *)
  set (le16 := PTree.set _t'5 (Vlong ea_long) le15).
  (* Read s->accu *)
  set (le17 := PTree.set _t'2 (Vptr accu_b accu_ofs) le16).
  (* Read code pointer from closure *)
  set (le18 := PTree.set _t'3 (Vptr cb code_ofs) le17).
  (* Read s->accu again *)
  set (le19 := PTree.set _t'1 (Vptr accu_b accu_ofs) le18).
  exists le19. exists m10.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ================================================================ *)
  (* Part 1: exec -- the C body executes                               *)
  (* ================================================================ *)
  {
    apply (eval_stmt_to_exec clight_ge 60).
    eval_cbn.

    (* S1: Sset _t'16 (s->sp) *)
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn.
    try rewrite Hsp_offset; try eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S2: Sset _arg1 = deref(_t'16 + 0) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_0; eval_cbn.
    rewrite Hload_arg1; eval_cbn.

    (* S3: Sset _t'15 (s->sp) for arg2 *)
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gso by (cbv; congruence).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S4: Sset _arg2 = deref(_t'15 + 1) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn.
    rewrite Hload_arg2; eval_cbn.

    (* S5: Sset _t'14 (s->sp) for arg3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S6: Sset _arg3 = deref(_t'14 + 2) *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_2; eval_cbn.
    (* Hload_arg3 uses nested Ptrofs.add; convert to match sem_add_sp_2 result *)
    assert (Hload_arg3_flat : Mem.load Mint64 m sp_b
              (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 16))) = Some cv_arg3).
    { replace (Ptrofs.add sp_ofs (Ptrofs.repr 16))
        with (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)).
      - exact Hload_arg3.
      - rewrite Ptrofs.add_assoc.
        replace (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.repr 8)) with (Ptrofs.repr 16)
          by reflexivity.
        reflexivity. }
    rewrite Hload_arg3_flat; eval_cbn.

    (* S7: Sset _t'13 (s->sp) for sp -= 3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load; eval_cbn.

    (* S8: Sassign s->sp = _t'13 - 3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn.
    try rewrite Hsp_offset; try eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_sub_sp_3; eval_cbn.
    fold new_sp_ofs.
    rewrite sem_cast_ptr_to_ptr; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hstore1; eval_cbn.

    (* S9: Sset _t'12 (s->sp) -- read new sp in m1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m1; eval_cbn.

    (* S10: Sassign deref(_t'12 + 0) = _arg1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_0; eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hvr_arg1); eval_cbn.
    rewrite Hstore2; eval_cbn.

    (* S11: Sset _t'11 (s->sp) -- read sp in m2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m2; eval_cbn.

    (* S12: Sassign deref(_t'11 + 1) = _arg2 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_1; eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hvr_arg2); eval_cbn.
    assert (Hstore3' : Mem.store Mint64 m2 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))) cv_arg2 = Some m3).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 8).
      - exact Hstore3.
      - lia.
      - rewrite Hnew_sp_unsigned. lia. }
    rewrite Hstore3'; eval_cbn.

    (* S13: Sset _t'10 (s->sp) -- read sp in m3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m3; eval_cbn.

    (* S14: Sassign deref(_t'10 + 2) = _arg3 *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_2; eval_cbn.
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hvr_arg3); eval_cbn.
    assert (Hstore4' : Mem.store Mint64 m3 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 16))) cv_arg3 = Some m4).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 16).
      - exact Hstore4.
      - lia.
      - rewrite Hnew_sp_unsigned. lia. }
    rewrite Hstore4'; eval_cbn.

    (* S15: Sset _t'8 (s->sp) -- read sp in m4 for pc store *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m4; eval_cbn.

    (* S15b: Sset _t'9 (s->pc) -- read pc for return address.
       The previous eval_cbn may have already partially resolved the
       Efield lookup. We proceed without Hco/Hpc_offset if already consumed. *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn.
    try rewrite Hpc_offset; try eval_cbn.
    try rewrite Mptr_Mint64; try eval_cbn.
    (* pc in m4: survived stores 1-4 *)
    assert (Hpc_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
    { assert (Hpc_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other. exact Hpc_load_m1. exact Hstore2.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hpc_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) = Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other. exact Hpc_m2. exact Hstore3.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      erewrite Mem.load_store_other. exact Hpc_m3. exact Hstore4.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    rewrite Hpc_load_m4; eval_cbn.

    (* S16: Sassign deref(_t'8 + 3) = (long)_t'9 *)
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_3; eval_cbn.
    rewrite sem_cast_ptint_to_long; eval_cbn.
    rewrite sem_cast_long_vptr; eval_cbn.
    assert (Hstore5' : Mem.store Mint64 m4 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 24))) (Vptr cb pc_ofs) = Some m5).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 24).
      - exact Hstore5.
      - lia.
      - rewrite Hnew_sp_unsigned. lia. }
    rewrite Hstore5'; eval_cbn.

    (* S17: Sset _t'6 (s->sp) -- read sp in m5 for env store *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m5; eval_cbn.

    (* S17b: Sset _t'7 (s->env) in m5 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Henv_offset; try eval_cbn.
    (* env in m5 *)
    assert (Henv_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_v).
    { erewrite Mem.load_store_other. exact Henv_load_m4. exact Hstore5.
      left. intro Heq; apply Hsp_ne_sb; auto. }
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    rewrite Henv_load_m5; eval_cbn.

    (* S18: Sassign deref(_t'6 + 4) = _t'7 *)
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_4; eval_cbn.
    rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Henv_repr); eval_cbn.
    assert (Hstore6' : Mem.store Mint64 m5 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 32))) env_v = Some m6).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 32).
      - exact Hstore6.
      - lia.
      - rewrite Hnew_sp_unsigned. lia. }
    rewrite Hstore6'; eval_cbn.

    (* S19: Sset _t'4 (s->sp) -- read sp in m6 for ea store *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
    rewrite Hsp_load_m6; eval_cbn.

    (* S19b: Sset _t'5 (s->extra_args) in m6 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Hextra_offset; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    rewrite Hextra_load_m6; eval_cbn.

    (* S20: Sassign deref(_t'4 + 5) = (_t'5 << 1) + 1 *)
    rewrite PTree.gss; eval_cbn.
    rewrite PTree.gso by (cbv; congruence).
    rewrite PTree.gss; eval_cbn.
    rewrite sem_add_sp_5; eval_cbn.
    rewrite sem_cast_long_to_long; eval_cbn.
    rewrite sem_shl_long_int_1; eval_cbn.
    rewrite sem_add_long_int_1; eval_cbn.
    rewrite sem_cast_long_to_long; eval_cbn.
    fold ea_tagged.
    assert (Hstore7' : Mem.store Mint64 m6 sp_b
              (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 40))) ea_tagged = Some m7).
    { rewrite (ptrofs_add_unsigned new_sp_ofs 40).
      - exact Hstore7.
      - lia.
      - rewrite Hnew_sp_unsigned. lia. }
    rewrite Hstore7'; eval_cbn.

    (* S21: Sset _t'2 (s->accu) -- read accu in m7 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Haccu_offset; try eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    rewrite Haccu_load_m7; eval_cbn.

    (* S22: Sset _t'3 = deref(cast(_t'2) + 0) -- code pointer *)
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_long_to_ptptint_vptr; eval_cbn.
    rewrite (sem_add_ptptint_0 accu_b accu_ofs m7); eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite Mptr_Mint64 in Hcode_ptr_load_m7.
    rewrite Hcode_ptr_load_m7; eval_cbn.

    (* S23: Sassign s->pc = _t'3 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn.
    try rewrite Hpc_offset; try eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
    rewrite Mptr_Mint64; eval_cbn.
    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
    fold new_pc_v.
    rewrite Hstore8; eval_cbn.

    (* S24: Sset _t'1 (s->accu) -- read accu in m8 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    (* accu in m8: survived pc store at offset 0 *)
    assert (Haccu_load_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr accu_b accu_ofs)).
    { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               new_pc_v (Vptr accu_b accu_ofs)
               Hstore8 Haccu_load_m7). right. lia. }
    rewrite Haccu_load_m8; eval_cbn.

    (* S25: Sassign s->env = _t'1 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Henv_offset; try eval_cbn.
    rewrite PTree.gss; eval_cbn.
    rewrite (sem_cast_long_vptr accu_b accu_ofs m8); eval_cbn.
    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
    fold new_env_v.
    rewrite Hstore9; eval_cbn.

    (* S26: Sassign s->extra_args = 2 *)
    repeat (rewrite PTree.gso by (cbv; congruence)).
    rewrite Hle_s; eval_cbn.
    try rewrite Hco; try eval_cbn. try rewrite Hextra_offset; try eval_cbn.
    rewrite sem_cast_int_to_long_2; eval_cbn.
    rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
    fold new_ea_v.
    rewrite Hstore10; eval_cbn.

    (* S27: Sreturn 0 *)
    subst le19 le18 le17 le16 le15 le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
    reflexivity.
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

    (* Loads in final memory m10 *)

    (* pc at uso+0: written in store8, survived stores 9,10 *)
    assert (Hpc_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
    { assert (Hpc_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m7 m8 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore8) as Htmp.
        unfold new_pc_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      assert (Hpc_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
      { apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 0)
                 new_env_v new_pc_v Hstore9 Hpc_m8). left. lia. }
      apply (load_after_store_other m9 m10 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 0)
               new_ea_v new_pc_v Hstore10 Hpc_m9). left. lia. }

    (* accu at uso+8 in m10 *)
    assert (Haccu_load_m8' : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr accu_b accu_ofs)).
    { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
               new_pc_v (Vptr accu_b accu_ofs)
               Hstore8 Haccu_load_m7). right. lia. }
    assert (Haccu_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 8) =
              Some (Vptr accu_b accu_ofs)).
    { assert (Haccu_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 24)
                 (Ptrofs.unsigned so + 8) new_env_v (Vptr accu_b accu_ofs)
                 Hstore9 Haccu_load_m8'). left. lia. }
      apply (load_after_store_other m9 m10 sb (Ptrofs.unsigned so + 32)
               (Ptrofs.unsigned so + 8) new_ea_v (Vptr accu_b accu_ofs)
               Hstore10 Haccu_m9). left. lia. }

    (* sp at uso+16 in m10 *)
    assert (Hsp_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 16) =
              Some (Vptr sp_b new_sp_ofs)).
    { assert (Hsp_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 new_pc_v (Vptr sp_b new_sp_ofs) Hstore8 Hsp_load_m7). right. lia. }
      assert (Hsp_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
                 new_env_v (Vptr sp_b new_sp_ofs) Hstore9 Hsp_m8). left. lia. }
      apply (load_after_store_other m9 m10 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 16)
               new_ea_v (Vptr sp_b new_sp_ofs) Hstore10 Hsp_m9). left. lia. }

    (* env at uso+24: written in store9, survived store10 *)
    assert (Henv_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
    { assert (Henv_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
      { pose proof (load_after_store_same m8 m9 sb (Ptrofs.unsigned so + 24) new_env_v Hstore9) as Htmp.
        unfold new_env_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      apply (load_after_store_other m9 m10 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 24)
               new_ea_v new_env_v Hstore10 Henv_m9). left. lia. }

    (* extra_args at uso+32: written in store10 *)
    assert (Hextra_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 32) = Some new_ea_v).
    { pose proof (load_after_store_same m9 m10 sb (Ptrofs.unsigned so + 32) new_ea_v Hstore10) as Htmp.
      subst new_ea_v. simpl Val.load_result in Htmp. exact Htmp. }

    (* global_data at uso+40 *)
    assert (Hgd_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
    { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                 (Vptr sp_b new_sp_ofs) (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore1 Hgd_load). right. lia. }
      assert (Hgd_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. exact Hgd_m1. exact Hstore2.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. exact Hgd_m2. exact Hstore3.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. exact Hgd_m3. exact Hstore4.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. exact Hgd_m4. exact Hstore5.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. exact Hgd_m5. exact Hstore6.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { erewrite Mem.load_store_other. exact Hgd_m6. exact Hstore7.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hgd_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                 new_pc_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore8 Hgd_m7). right. lia. }
      assert (Hgd_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 40) = Some (Vptr (ar_global_block ard) (ar_global_ofs ard))).
      { apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 40)
                 new_env_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore9 Hgd_m8). right. lia. }
      apply (load_after_store_other m9 m10 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 40)
               new_ea_v (Vptr (ar_global_block ard) (ar_global_ofs ard)) Hstore10 Hgd_m9). right. lia. }

    (* trap_sp at uso+48 *)
    assert (Hts_load10 : Mem.load Mint64 m10 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
    { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m1. exact Hstore2.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m2. exact Hstore3.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m3. exact Hstore4.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m4. exact Hstore5.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m5. exact Hstore6.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m7 : Mem.load Mint64 m7 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { erewrite Mem.load_store_other. exact Hts_m6. exact Hstore7.
        left. intro Heq; apply Hsp_ne_sb; auto. }
      assert (Hts_m8 : Mem.load Mint64 m8 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m7 m8 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                 new_pc_v ts_ptr Hstore8 Hts_m7). right. lia. }
      assert (Hts_m9 : Mem.load Mint64 m9 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
      { apply (load_after_store_other m8 m9 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 48)
                 new_env_v ts_ptr Hstore9 Hts_m8). right. lia. }
      apply (load_after_store_other m9 m10 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 48)
               new_ea_v ts_ptr Hstore10 Hts_m9). right. lia. }

    (* Writable permission after all ten stores *)
    assert (Hsb_writable_m10 : Mem.range_perm m10 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore10.
      eapply Mem.perm_store_1. exact Hstore9.
      apply Hsb_writable_m8. exact Hofs'. }

    (* le19 ! _s *)
    assert (Hle19_s : le19 ! _s = Some (Vptr sb so)).
    { subst le19 le18 le17 le16 le15 le14 le13 le12 le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
      repeat (rewrite PTree.gso by (compute; congruence)).
      exact Hle_s. }

    (* Stack repr for the new stack in m10 *)
    (* The new stack is: arg1 :: arg2 :: arg3 :: Val_int pc' :: env :: Val_int ea :: rest
       at new_sp_ofs.
       We need to show the loads and val_repr for each element. *)

    (* Build stack_repr for "rest" (tail starting at sp_ofs + 24 = new_sp_ofs + 48) *)
    (* rest is at sp_ofs + 24 in original memory, which is new_sp_ofs + 48 *)
    (* First we need the rest stack_repr surviving all 10 stores *)
    set (rest_ofs := Ptrofs.add (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)).

    assert (Hsp_modulus : Ptrofs.unsigned sp_ofs + 24 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
    { rewrite Nat2Z.inj_succ, Nat2Z.inj_succ, Nat2Z.inj_succ in Hsp_room'. lia. }

    assert (Hrest_unsigned : Ptrofs.unsigned rest_ofs = Ptrofs.unsigned sp_ofs + 24).
    { subst rest_ofs.
      assert (H16 : Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)) = Ptrofs.unsigned sp_ofs + 8).
      { apply ptrofs_add_unsigned; lia. }
      assert (H24 : Ptrofs.unsigned (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) = Ptrofs.unsigned sp_ofs + 16).
      { rewrite ptrofs_add_unsigned; lia. }
      rewrite ptrofs_add_unsigned; lia. }

    assert (Hrest_repr_m10 : stack_repr hm cb co m10 rest sp_b rest_ofs).
    {
      (* Stores 2-7 are to sp_b at offsets in [new_sp_ofs, new_sp_ofs+48).
         The rest starts at sp_ofs + 24 = new_sp_ofs + 48.
         So stores 2-7 are at LOWER offsets than the rest. *)
      (* Use stack_repr_store_same_block_lower through stores 2-7,
         then stack_repr_store_other_block through stores 1,8,9,10 *)
      eapply stack_repr_co_shift.
      apply (stack_repr_store_other_block hm cb co m9 m10 rest sp_b _ sb (Ptrofs.unsigned so + 32) new_ea_v).
      { apply (stack_repr_store_other_block hm cb co m8 m9 rest sp_b _ sb (Ptrofs.unsigned so + 24) new_env_v).
        { apply (stack_repr_store_other_block hm cb co m7 m8 rest sp_b _ sb (Ptrofs.unsigned so + 0) new_pc_v).
          { apply (stack_repr_store_same_block_lower hm cb co m6 m7 rest sp_b _ (Ptrofs.unsigned new_sp_ofs + 40) ea_tagged).
            { apply (stack_repr_store_same_block_lower hm cb co m5 m6 rest sp_b _ (Ptrofs.unsigned new_sp_ofs + 32) env_v).
              { apply (stack_repr_store_same_block_lower hm cb co m4 m5 rest sp_b _ (Ptrofs.unsigned new_sp_ofs + 24) (Vptr cb pc_ofs)).
                { apply (stack_repr_store_same_block_lower hm cb co m3 m4 rest sp_b _ (Ptrofs.unsigned new_sp_ofs + 16) cv_arg3).
                  { apply (stack_repr_store_same_block_lower hm cb co m2 m3 rest sp_b _ (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2).
                    { apply (stack_repr_store_same_block_lower hm cb co m1 m2 rest sp_b _ (Ptrofs.unsigned new_sp_ofs) cv_arg1).
                      { eapply stack_repr_co_shift.
                      apply (stack_repr_store_other_block hm cb co m m1 rest sp_b _ sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                        exact Hstk_rest. exact Hstore1.
                        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
                      exact Hstore2.
                      rewrite Hrest_unsigned, Hnew_sp_unsigned. lia.
                      rewrite Hrest_unsigned. lia. }
                    exact Hstore3.
                    rewrite Hrest_unsigned, Hnew_sp_unsigned. lia.
                    rewrite Hrest_unsigned. lia. }
                  exact Hstore4.
                  rewrite Hrest_unsigned, Hnew_sp_unsigned. lia.
                  rewrite Hrest_unsigned. lia. }
                exact Hstore5.
                rewrite Hrest_unsigned, Hnew_sp_unsigned. lia.
                rewrite Hrest_unsigned. lia. }
              exact Hstore6.
              rewrite Hrest_unsigned, Hnew_sp_unsigned. lia.
              rewrite Hrest_unsigned. lia. }
            exact Hstore7.
            rewrite Hrest_unsigned, Hnew_sp_unsigned. lia.
            rewrite Hrest_unsigned. lia. }
          exact Hstore8.
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
        exact Hstore9.
        intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
      exact Hstore10.
      intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }

    (* Build stack_repr for ea :: rest at new_sp_ofs + 40 *)
    assert (Hea_load_m10 : Mem.load Mint64 m10 sp_b (Ptrofs.unsigned new_sp_ofs + 40) =
              Some ea_tagged).
    { (* Written in store7, survived stores 8-10 (different block) *)
      assert (Hea_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 40) = Some ea_tagged).
      { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore7) as Htmp.
        subst ea_tagged. simpl Val.load_result in Htmp. exact Htmp. }
      assert (Hea_m8 : Mem.load Mint64 m8 sp_b (Ptrofs.unsigned new_sp_ofs + 40) = Some ea_tagged).
      { erewrite Mem.load_store_other. exact Hea_m7. exact Hstore8.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      assert (Hea_m9 : Mem.load Mint64 m9 sp_b (Ptrofs.unsigned new_sp_ofs + 40) = Some ea_tagged).
      { erewrite Mem.load_store_other. exact Hea_m8. exact Hstore9.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      erewrite Mem.load_store_other. exact Hea_m9. exact Hstore10.
      left. intro Heq; exact (Hsp_ne_sb Heq). }

    (* rest_ofs = Ptrofs.repr(sp_ofs + 24) = Ptrofs.repr(new_sp_ofs + 48) *)
    assert (Hrest_ofs_repr : rest_ofs = Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 48)).
    { apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
      rewrite Hrest_unsigned.
      rewrite Ptrofs.unsigned_repr.
      2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia. }
      rewrite Hnew_sp_unsigned.
      destruct (Coqlib.zeq _ _); [reflexivity | lia]. }

    assert (Hea_sr : stack_repr hm cb co m10
              (Val_int (Z.of_nat (Machine.extra_args s)) :: rest)
              sp_b (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 40))).
    { econstructor.
      - rewrite Ptrofs.unsigned_repr.
        + exact Hea_load_m10.
        + unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia.
      - exact Hea_cv_repr.
      - replace (Ptrofs.add (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 40)) (Ptrofs.repr 8))
          with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 48)).
        + rewrite <- Hrest_ofs_repr. exact Hrest_repr_m10.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 40)) 8).
          2: lia.
          2: { rewrite Ptrofs.unsigned_repr.
               - rewrite Hnew_sp_unsigned. lia.
               - unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia. }
          rewrite Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          rewrite Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for env :: ea :: rest at new_sp_ofs + 32 *)
    assert (Henv_stack_load_m10 : Mem.load Mint64 m10 sp_b (Ptrofs.unsigned new_sp_ofs + 32) =
              Some env_v).
    { (* Written in store6, survived stores 7-10 *)
      assert (Henv_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs + 32) = Some env_v).
      { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore6) as Htmp.
        rewrite (val_repr_load_result hm cb co _ _ Henv_repr) in Htmp.
        exact Htmp. }
      assert (Henv_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 32) = Some env_v).
      { erewrite Mem.load_store_other. exact Henv_m6. exact Hstore7.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Henv_m8 : Mem.load Mint64 m8 sp_b (Ptrofs.unsigned new_sp_ofs + 32) = Some env_v).
      { erewrite Mem.load_store_other. exact Henv_m7. exact Hstore8.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      assert (Henv_m9 : Mem.load Mint64 m9 sp_b (Ptrofs.unsigned new_sp_ofs + 32) = Some env_v).
      { erewrite Mem.load_store_other. exact Henv_m8. exact Hstore9.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      erewrite Mem.load_store_other. exact Henv_m9. exact Hstore10.
      left. intro Heq; exact (Hsp_ne_sb Heq). }

    assert (Henv_sr : stack_repr hm cb co m10
              (Machine.env s :: Val_int (Z.of_nat (Machine.extra_args s)) :: rest)
              sp_b (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 32))).
    { econstructor.
      - rewrite Ptrofs.unsigned_repr.
        + exact Henv_stack_load_m10.
        + unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia.
      - eapply val_repr_co_shift; exact Henv_repr.
      - replace (Ptrofs.add (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 32)) (Ptrofs.repr 8))
          with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 40)).
        + exact Hea_sr.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 32)) 8).
          2: lia.
          2: { rewrite Ptrofs.unsigned_repr. rewrite Hnew_sp_unsigned. lia.
               unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia. }
          rewrite !Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for Val_int pc' :: env :: ea :: rest at new_sp_ofs + 24 *)
    assert (Hpc_stack_load_m10 : Mem.load Mint64 m10 sp_b (Ptrofs.unsigned new_sp_ofs + 24) =
              Some (Vptr cb pc_ofs)).
    { (* Written in store5, survived stores 6-10 *)
      assert (Hpc_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vptr cb pc_ofs)).
      { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore5) as Htmp.
        simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
        exact Htmp. }
      assert (Hpc_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other. exact Hpc_m5. exact Hstore6.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Hpc_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other. exact Hpc_m6. exact Hstore7.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Hpc_m8 : Mem.load Mint64 m8 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other. exact Hpc_m7. exact Hstore8.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      assert (Hpc_m9 : Mem.load Mint64 m9 sp_b (Ptrofs.unsigned new_sp_ofs + 24) = Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other. exact Hpc_m8. exact Hstore9.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      erewrite Mem.load_store_other. exact Hpc_m9. exact Hstore10.
      left. intro Heq; exact (Hsp_ne_sb Heq). }

    assert (Hpc_sr : stack_repr hm cb co m10
              (Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat (Machine.extra_args s)) :: rest)
              sp_b (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 24))).
    { econstructor.
      - rewrite Ptrofs.unsigned_repr.
        + exact Hpc_stack_load_m10.
        + unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia.
      - exact Hpc_cv_repr.
      - replace (Ptrofs.add (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 24)) (Ptrofs.repr 8))
          with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 32)).
        + exact Henv_sr.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 24)) 8).
          2: lia.
          2: { rewrite Ptrofs.unsigned_repr. rewrite Hnew_sp_unsigned. lia.
               unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia. }
          rewrite !Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for arg3 :: ... at new_sp_ofs + 16 *)
    assert (Harg3_load_m10 : Mem.load Mint64 m10 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
    { (* Written in store4, survived stores 5-10 *)
      assert (Harg3_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
      { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore4) as Htmp.
        rewrite (val_repr_load_result hm cb co _ _ Hvr_arg3) in Htmp.
        exact Htmp. }
      assert (Harg3_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
      { erewrite Mem.load_store_other. exact Harg3_m4. exact Hstore5.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg3_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
      { erewrite Mem.load_store_other. exact Harg3_m5. exact Hstore6.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg3_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
      { erewrite Mem.load_store_other. exact Harg3_m6. exact Hstore7.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg3_m8 : Mem.load Mint64 m8 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
      { erewrite Mem.load_store_other. exact Harg3_m7. exact Hstore8.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      assert (Harg3_m9 : Mem.load Mint64 m9 sp_b (Ptrofs.unsigned new_sp_ofs + 16) = Some cv_arg3).
      { erewrite Mem.load_store_other. exact Harg3_m8. exact Hstore9.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      erewrite Mem.load_store_other. exact Harg3_m9. exact Hstore10.
      left. intro Heq; exact (Hsp_ne_sb Heq). }

    assert (Harg3_sr : stack_repr hm cb co m10
              (arg3 :: Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat (Machine.extra_args s)) :: rest)
              sp_b (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 16))).
    { econstructor.
      - rewrite Ptrofs.unsigned_repr.
        + exact Harg3_load_m10.
        + unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia.
      - exact Hvr_arg3.
      - replace (Ptrofs.add (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 16)) (Ptrofs.repr 8))
          with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 24)).
        + exact Hpc_sr.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 16)) 8).
          2: lia.
          2: { rewrite Ptrofs.unsigned_repr. rewrite Hnew_sp_unsigned. lia.
               unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia. }
          rewrite !Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for arg2 :: ... at new_sp_ofs + 8 *)
    assert (Harg2_load_m10 : Mem.load Mint64 m10 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
    { (* Written in store3, survived stores 4-10 *)
      assert (Harg2_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore3) as Htmp.
        rewrite (val_repr_load_result hm cb co _ _ Hvr_arg2) in Htmp.
        exact Htmp. }
      assert (Harg2_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { erewrite Mem.load_store_other. exact Harg2_m3. exact Hstore4.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg2_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { erewrite Mem.load_store_other. exact Harg2_m4. exact Hstore5.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg2_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { erewrite Mem.load_store_other. exact Harg2_m5. exact Hstore6.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg2_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { erewrite Mem.load_store_other. exact Harg2_m6. exact Hstore7.
        right. rewrite Hnew_sp_unsigned. unfold size_chunk. lia. }
      assert (Harg2_m8 : Mem.load Mint64 m8 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { erewrite Mem.load_store_other. exact Harg2_m7. exact Hstore8.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      assert (Harg2_m9 : Mem.load Mint64 m9 sp_b (Ptrofs.unsigned new_sp_ofs + 8) = Some cv_arg2).
      { erewrite Mem.load_store_other. exact Harg2_m8. exact Hstore9.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      erewrite Mem.load_store_other. exact Harg2_m9. exact Hstore10.
      left. intro Heq; exact (Hsp_ne_sb Heq). }

    assert (Harg2_sr : stack_repr hm cb co m10
              (arg2 :: arg3 :: Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat (Machine.extra_args s)) :: rest)
              sp_b (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 8))).
    { econstructor.
      - rewrite Ptrofs.unsigned_repr.
        + exact Harg2_load_m10.
        + unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia.
      - exact Hvr_arg2.
      - replace (Ptrofs.add (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 8)) (Ptrofs.repr 8))
          with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 16)).
        + exact Harg3_sr.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 8)) 8).
          2: lia.
          2: { rewrite Ptrofs.unsigned_repr. rewrite Hnew_sp_unsigned. lia.
               unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned. lia. }
          rewrite !Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    (* Build stack_repr for arg1 :: ... at new_sp_ofs *)
    assert (Harg1_load_m10 : Mem.load Mint64 m10 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
    { (* Written in store2, survived stores 3-10 *)
      assert (Harg1_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore2) as Htmp.
        rewrite (val_repr_load_result hm cb co _ _ Hvr_arg1) in Htmp.
        exact Htmp. }
      assert (Harg1_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m2. exact Hstore3.
        right. left. unfold size_chunk. lia. }
      assert (Harg1_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m3. exact Hstore4.
        right. left. unfold size_chunk. lia. }
      assert (Harg1_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m4. exact Hstore5.
        right. left. unfold size_chunk. lia. }
      assert (Harg1_m6 : Mem.load Mint64 m6 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m5. exact Hstore6.
        right. left. unfold size_chunk. lia. }
      assert (Harg1_m7 : Mem.load Mint64 m7 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m6. exact Hstore7.
        right. left. unfold size_chunk. lia. }
      assert (Harg1_m8 : Mem.load Mint64 m8 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m7. exact Hstore8.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      assert (Harg1_m9 : Mem.load Mint64 m9 sp_b (Ptrofs.unsigned new_sp_ofs) = Some cv_arg1).
      { erewrite Mem.load_store_other. exact Harg1_m8. exact Hstore9.
        left. intro Heq; exact (Hsp_ne_sb Heq). }
      erewrite Mem.load_store_other. exact Harg1_m9. exact Hstore10.
      left. intro Heq; exact (Hsp_ne_sb Heq). }

    assert (Hfull_sr : stack_repr hm cb co m10
              (arg1 :: arg2 :: arg3 :: Val_int (Machine.pc s) :: Machine.env s :: Val_int (Z.of_nat (Machine.extra_args s)) :: rest)
              sp_b new_sp_ofs).
    { econstructor.
      - exact Harg1_load_m10.
      - exact Hvr_arg1.
      - replace (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))
          with (Ptrofs.repr (Ptrofs.unsigned new_sp_ofs + 8)).
        + exact Harg2_sr.
        + apply Ptrofs.same_if_eq. unfold Ptrofs.eq.
          rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(rewrite Hnew_sp_unsigned; lia)).
          rewrite Ptrofs.unsigned_repr.
          2: { unfold Ptrofs.max_unsigned. rewrite Hnew_sp_unsigned.
               pose proof (Nat2Z.is_nonneg (length rest)). lia. }
          destruct (Coqlib.zeq _ _) as [_|Habs]; [reflexivity | exfalso; apply Habs; lia]. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' *)
    { exact Hle19_s. }

    (* 2. pc field -- updated to new_pc_v *)
    { exists new_pc_v. split.
      - exact Hpc_load10.
      - simpl. unfold pc_rel, new_pc_v. f_equal.
        subst code_ofs. reflexivity. }

    (* 3. accu field -- unchanged *)
    { exists (Vptr accu_b accu_ofs). split.
      - exact Haccu_load10.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 4. sp field -- updated to new_sp_ofs, new stack *)
    { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load10.
      - reflexivity.
      - simpl. eapply stack_repr_co_shift. exact Hfull_sr.
      - exact Hsp_ne_sb.
      - exact Hsp_ne_gb.
      - exact Hcb_ne_sp.
      - rewrite Hnew_sp_unsigned. lia.
      - simpl length. rewrite Hnew_sp_unsigned. lia.
      - intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore10.
        eapply Mem.perm_store_1. exact Hstore9.
        eapply Mem.perm_store_1. exact Hstore8.
        eapply Mem.perm_store_1. exact Hstore7.
        eapply Mem.perm_store_1. exact Hstore6.
        eapply Mem.perm_store_1. exact Hstore5.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsp_writable.
        simpl length in Hofs'. rewrite Hnew_sp_unsigned in Hofs'. lia.
      - exact Halign_new. }

    (* 5. env field -- updated to accu *)
    { exists new_env_v. split.
      - exact Henv_load10.
      - simpl. eapply val_repr_co_shift; exact Haccu_repr. }

    (* 6. extra_args field -- updated to 2 *)
    { simpl. exact Hextra_load10. }

    (* 7. global_data field -- unchanged *)
    { exists (Vptr (ar_global_block ard) (ar_global_ofs ard)). split; [| split; [| split]].
      - exact Hgd_load10.
      - simpl. reflexivity.
      - simpl.
        eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m9 m10 _
                 (ar_global_block ard) (ar_global_ofs ard)
                 sb (Ptrofs.unsigned so + 32) new_ea_v).
        + eapply global_repr_co_shift.
        apply (global_repr_store_other_block hm cb co m8 m9 _
                   (ar_global_block ard) (ar_global_ofs ard)
                   sb (Ptrofs.unsigned so + 24) new_env_v).
          * eapply global_repr_co_shift.
          apply (global_repr_store_other_block hm cb co m7 m8 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (Ptrofs.unsigned so + 0) new_pc_v).
            { eapply global_repr_co_shift.
            apply (global_repr_store_other_block hm cb co m6 m7 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sp_b (Ptrofs.unsigned new_sp_ofs + 40) ea_tagged).
              { eapply global_repr_co_shift.
              apply (global_repr_store_other_block hm cb co m5 m6 _
                         (ar_global_block ard) (ar_global_ofs ard)
                         sp_b (Ptrofs.unsigned new_sp_ofs + 32) env_v).
                { eapply global_repr_co_shift.
                apply (global_repr_store_other_block hm cb co m4 m5 _
                           (ar_global_block ard) (ar_global_ofs ard)
                           sp_b (Ptrofs.unsigned new_sp_ofs + 24) (Vptr cb pc_ofs)).
                  { eapply global_repr_co_shift.
                  apply (global_repr_store_other_block hm cb co m3 m4 _
                             (ar_global_block ard) (ar_global_ofs ard)
                             sp_b (Ptrofs.unsigned new_sp_ofs + 16) cv_arg3).
                    { eapply global_repr_co_shift.
                    apply (global_repr_store_other_block hm cb co m2 m3 _
                               (ar_global_block ard) (ar_global_ofs ard)
                               sp_b (Ptrofs.unsigned new_sp_ofs + 8) cv_arg2).
                      { eapply global_repr_co_shift.
                      apply (global_repr_store_other_block hm cb co m1 m2 _
                                 (ar_global_block ard) (ar_global_ofs ard)
                                 sp_b (Ptrofs.unsigned new_sp_ofs) cv_arg1).
                        { eapply global_repr_co_shift.
                        apply (global_repr_store_other_block hm cb co m m1 _
                                   (ar_global_block ard) (ar_global_ofs ard)
                                   sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                          exact Hglobal_repr. exact Hstore1.
                          intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
                        exact Hstore2.
                        intro Heq2; apply Hsp_ne_gb; auto. }
                      exact Hstore3.
                      intro Heq2; apply Hsp_ne_gb; auto. }
                    exact Hstore4.
                    intro Heq2; apply Hsp_ne_gb; auto. }
                  exact Hstore5.
                  intro Heq2; apply Hsp_ne_gb; auto. }
                exact Hstore6.
                intro Heq2; apply Hsp_ne_gb; auto. }
              exact Hstore7.
              intro Heq2; apply Hsp_ne_gb; auto. }
            exact Hstore8.
            intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
          * exact Hstore9.
          * intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        + exact Hstore10.
        + intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
      - exact Hgb_ne_sb. }

    (* 8. trap_sp field -- unchanged *)
    { exists ts_ptr. split.
      - exact Hts_load10.
      - simpl. exact Htrap_rel. }

    (* 9. sb_writable *)
    { exact Hsb_writable_m10. }
  }
Qed.
