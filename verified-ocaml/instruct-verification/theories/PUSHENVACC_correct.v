(* PUSHENVACC_correct.v -- PUSHENVACC (parameterized) handler completeness proof.

   PUSHENVACC n: pushes accu to stack, reads index n from the code buffer,
   reads env[n] from the closure environment, stores to accu, and advances
   pc past the argument.

   C handler (f_instr_PUSHENVACC):
     _t'7 = s->sp;               // read sp
     _t'1 = (long ptr)(_t'7-1);  // new_sp = sp - 1
     s->sp = _t'1;               // store 1: update sp field
     _t'6 = s->accu;             // read accu
     *_t'1 = _t'6;               // store 2: push accu onto stack
     _t'2 = s->pc;               // read pc pointer
     s->pc = _t'2 + 1;           // store 3: advance pc past argument
     _t'3 = s->env;              // read env
     _t'4 = *_t'2;               // read n from code buffer (Mint32)
     _t'5 = *(cast(_t'3, tptr tlong) + _t'4);  // env[n]
     s->accu = _t'5;             // store 4: set accu to env field
     return 0;

   Rocq (handle_PUSHENVACC n):
     let new_stack := accu :: stack in
     match field_or_heap s s.(env) n with
     | Some v => Step (s <|pc:=pc'|> <|accu:=v|> <|stack:=new_stack|>)
     | None => Error "PUSHENVACC: env access out of bounds"
     end

   Four stores:
     Store 1: sp field  (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp   (sp_b, new_sp_ofs) <- accu_v
     Store 3: pc field  (sb, uso+0)  <- new_pc_v
     Store 4: accu field (sb, uso+8) <- cv (env field value)

   No Axioms, no Admitted. *)

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
(* Struct layout lemmas                                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full).
Proof.
  eexists. split; [| split; [| split; [| split]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_all_PUSHENVACC : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr_PEA : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Lemma sem_add_env_n : forall env_b env_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr env_b env_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr env_b (Ptrofs.add env_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Lemma pc_rel_shift : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Lemma ptrofs_mul_8_of_ints_eq : forall n,
  0 <= n ->
  n < Int.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr n))
  = Ptrofs.repr (n * 8).
Proof.
  intros n Hnn Hn_bound.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  change Int.half_modulus with 2147483648 in Hn_bound.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite (Ptrofs.unsigned_repr n).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_PUSHENVACC_correct : forall n,
    handler_correct (handle_PUSHENVACC n) f_instr_PUSHENVACC
      (pushenvacc_generic_step_pre n)
      (fun _ s => field_or_heap s s.(Machine.env) n = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro n.
  intros e le m s.
  unfold handler_correct, handle_PUSHENVACC.

  destruct (field_or_heap s s.(Machine.env) n) as [v|] eqn:Hfoh.

  2: { reflexivity. }

  {
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
    set (uso := Ptrofs.unsigned so) in *.

    unfold pushenvacc_generic_step_pre in Hstep_pre.
    destruct Hstep_pre as [[sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]] [Hcode_load [Hn_bound Hefl]]].
    assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
      by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    destruct interp_state_co_all_PUSHENVACC as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset Henv_offset]]]]].

    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    unfold pushenvacc_env_field_loadable in Hefl.
    destruct (Hefl v Hfoh env_v Henv_repr)
      as [env_b [env_ofs [cv [Henv_is_ptr [Henv_ne_sb [Hfield_load [Hfield_repr Henv_ne_spb_fn]]]]]]].
    subst env_v.

    assert (Henv_ne_spb : env_b <> sp_b).
    { exact (Henv_ne_spb_fn sp_b sp_ofs Hsp_load). }

    assert (Henv_n_eq :
      Ptrofs.add env_ofs (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr (Z.of_nat n))))
      = Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat n * 8))).
    { f_equal. apply ptrofs_mul_8_of_ints_eq; lia. }

    set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
    assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
    { subst new_sp_ofs. unfold Ptrofs.sub.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
      apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
      unfold Ptrofs.max_unsigned. lia. }

    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore_sp].

    (* Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v *)
    assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
    { rewrite Hnew_sp_unsigned. simpl align_chunk.
      apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
    destruct (store_to_sp_after_sb_store m m1 sb (uso + 16) (Vptr sp_b new_sp_ofs)
                sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
                (Ptrofs.unsigned new_sp_ofs)
                Hstore_sp Hsp_writable
                ltac:(rewrite Hnew_sp_unsigned; lia)
                ltac:(rewrite Hnew_sp_unsigned; lia)
                Halign_new accu_v) as [m2 Hstore_push].

    (* Helper: sb load in m1 -> sb load in m2 (store2 is on sp_b <> sb) *)
    assert (Hload_sb_m1_m2 : forall ofs v0,
      Mem.load Mint64 m1 sb ofs = Some v0 ->
      Mem.load Mint64 m2 sb ofs = Some v0).
    { intros ofs v0 Hload1.
      erewrite Mem.load_store_other; [exact Hload1 | exact Hstore_push |].
      left. exact (not_eq_sym Hsp_ne_sb). }

    (* Loads surviving stores 1 and 2 on sb *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 0)
               (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs) Hstore_sp Hpc_load). left. lia. }
    assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (uso + 0) = Some (Vptr cb pc_ofs)).
    { exact (Hload_sb_m1_m2 _ _ Hpc_load_m1). }

    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 8)
               (Vptr sp_b new_sp_ofs) accu_v Hstore_sp Haccu_load). left. lia. }
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (uso + 8) = Some accu_v).
    { exact (Hload_sb_m1_m2 _ _ Haccu_load_m1). }

    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some (Vptr env_b env_ofs)).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 24)
               (Vptr sp_b new_sp_ofs) (Vptr env_b env_ofs) Hstore_sp Henv_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (uso + 24) = Some (Vptr env_b env_ofs)).
    { exact (Hload_sb_m1_m2 _ _ Henv_load_m1). }

    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
               (Vptr sp_b new_sp_ofs) _ Hstore_sp Hextra_load). right. lia. }
    assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { exact (Hload_sb_m1_m2 _ _ Hextra_load_m1). }

    assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
               (Vptr sp_b new_sp_ofs) gd_ptr Hstore_sp Hgd_load). right. lia. }
    assert (Hgd_load_m2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
    { exact (Hload_sb_m1_m2 _ _ Hgd_load_m1). }

    assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
               (Vptr sp_b new_sp_ofs) ts_ptr Hstore_sp Hts_load). right. lia. }
    assert (Hts_load_m2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
    { exact (Hload_sb_m1_m2 _ _ Hts_load_m1). }

    (* Store 3: pc field (sb, uso+0) <- new_pc_v *)
    assert (Hsb_writable_m2 : Mem.range_perm m2 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_push.
      eapply Mem.perm_store_1. exact Hstore_sp. apply Hsb_writable. exact Hofs'. }
    destruct (store_succeeds_sb m2 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m2 Hpc_load_m2 ltac:(lia) ltac:(lia) new_pc_v)
      as [m3 Hstore_pc].

    (* Loads surviving store 3 *)
    assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (uso + 8) = Some accu_v).
    { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 8)
               new_pc_v accu_v Hstore_pc Haccu_load_m2). right. lia. }
    assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { pose proof (load_after_store_same m m1 sb (uso + 16)
                    (Vptr sp_b new_sp_ofs) Hstore_sp) as Htmp.
      simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
    assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { exact (Hload_sb_m1_m2 _ _ Hsp_load_m1). }
    assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 16)
               new_pc_v (Vptr sp_b new_sp_ofs) Hstore_pc Hsp_load_m2). right. lia. }
    assert (Henv_load_m3 : Mem.load Mint64 m3 sb (uso + 24) = Some (Vptr env_b env_ofs)).
    { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 24)
               new_pc_v (Vptr env_b env_ofs) Hstore_pc Henv_load_m2). right. lia. }
    assert (Hextra_load_m3 : Mem.load Mint64 m3 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 32)
               new_pc_v _ Hstore_pc Hextra_load_m2). right. lia. }
    assert (Hgd_load_m3 : Mem.load Mint64 m3 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 40)
               new_pc_v gd_ptr Hstore_pc Hgd_load_m2). right. lia. }
    assert (Hts_load_m3 : Mem.load Mint64 m3 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 48)
               new_pc_v ts_ptr Hstore_pc Hts_load_m2). right. lia. }

    (* Code buffer load survives all 3 stores *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { apply (code_buffer_load_at Mint32 Mint64 m m1 cb sb
               (Ptrofs.unsigned pc_ofs) (uso + 16)
               (Vint (Int.repr (Z.of_nat n))) (Vptr sp_b new_sp_ofs)
               Hcode_load Hstore_sp Hcb_ne). }
    assert (Hcode_load_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { erewrite Mem.load_store_other. exact Hcode_load_m1. exact Hstore_push.
      left. exact Hcb_ne_sp. }
    assert (Hcode_load_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat n)))).
    { apply (code_buffer_load_at Mint32 Mint64 m2 m3 cb sb
               (Ptrofs.unsigned pc_ofs) (uso + 0)
               (Vint (Int.repr (Z.of_nat n))) new_pc_v
               Hcode_load_m2 Hstore_pc Hcb_ne). }

    (* Env field load survives stores 1-3 *)
    assert (Hfield_load_m1 : Mem.load Mint64 m1 env_b (Ptrofs.unsigned (Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv).
    { erewrite Mem.load_store_other. exact Hfield_load. exact Hstore_sp.
      left. exact Henv_ne_sb. }
    assert (Hfield_load_m2 : Mem.load Mint64 m2 env_b (Ptrofs.unsigned (Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv).
    { erewrite Mem.load_store_other. exact Hfield_load_m1. exact Hstore_push.
      left. exact Henv_ne_spb. }
    assert (Hfield_load_m3 : Mem.load Mint64 m3 env_b (Ptrofs.unsigned (Ptrofs.add env_ofs (Ptrofs.repr (Z.of_nat n * 8)))) = Some cv).
    { erewrite Mem.load_store_other. exact Hfield_load_m2. exact Hstore_pc.
      left. exact Henv_ne_sb. }

    (* Store 4: accu field (sb, uso+8) <- cv *)
    assert (Hsb_writable_m3 : Mem.range_perm m3 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
    { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore_pc.
      apply Hsb_writable_m2. exact Hofs'. }
    destruct (store_succeeds_sb m3 sb so 8 accu_v Hsb_writable_m3 Haccu_load_m3 ltac:(lia) ltac:(lia) cv)
      as [m4 Hstore_accu_field].

    (* Final field values in m4 *)
    assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (uso + 0) = Some new_pc_v).
    { pose proof (load_after_store_same m2 m3 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
      unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
    assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 0)
               cv new_pc_v Hstore_accu_field Hpc_load_m3). left. lia. }

    assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some cv).
    { pose proof (load_after_store_same m3 m4 sb (uso + 8) cv Hstore_accu_field) as Htmp.
      rewrite (val_repr_load_result hm cb co v cv Hfield_repr) in Htmp.
      exact Htmp. }

    assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 16)
               cv (Vptr sp_b new_sp_ofs) Hstore_accu_field Hsp_load_m3). right. lia. }

    assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some (Vptr env_b env_ofs)).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 24)
               cv (Vptr env_b env_ofs) Hstore_accu_field Henv_load_m3). right. lia. }

    assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 32)
               cv _ Hstore_accu_field Hextra_load_m3). right. lia. }

    assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 40)
               cv gd_ptr Hstore_accu_field Hgd_load_m3). right. lia. }

    assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 48)
               cv ts_ptr Hstore_accu_field Hts_load_m3). right. lia. }

    (* Witnesses *)
    set (le' := PTree.set _t'5 cv
                (PTree.set _t'4 (Vint (Int.repr (Z.of_nat n)))
                (PTree.set _t'3 (Vptr env_b env_ofs)
                (PTree.set _t'2 (Vptr cb pc_ofs)
                (PTree.set _t'6 accu_v
                (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                (PTree.set _t'7 (Vptr sp_b sp_ofs) le))))))).
    exists le'. exists m4.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 25).
      eval_cbn.

      (* S1: Sset _t'7 (s->sp) *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      fold uso. rewrite Hsp_load; eval_cbn.

      (* S2: Sset _t'1 (cast (sub _t'7 1) (tptr tlong)) *)
      rewrite PTree.gss; eval_cbn.
      rewrite sem_sub_sp_1; eval_cbn.
      rewrite sem_cast_ptr_to_ptr; eval_cbn.

      (* S3: Sassign (s->sp) _t'1 -- store 1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite sem_cast_ptr_to_ptr; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      fold new_sp_ofs.
      rewrite Hstore_sp; eval_cbn.

      (* S4: Sset _t'6 (s->accu) *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Hco; eval_cbn.
      try rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold uso.
      rewrite Haccu_load_m1; eval_cbn.

      (* S5: Sassign (deref _t'1) _t'6 -- store 2 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
      fold new_sp_ofs.
      rewrite Hstore_push; eval_cbn.

      (* S6: Sset _t'2 (s->pc) *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Hco; eval_cbn.
      try rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold uso. rewrite Hpc_load_m2; eval_cbn.

      (* S7: Sassign (s->pc) (_t'2 + 1) -- store 3 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs m2); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_ofs.
      fold new_pc_v.
      rewrite Hstore_pc; eval_cbn.

      (* S8: Sset _t'3 (s->env) *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Hco; eval_cbn.
      try rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
      fold uso. rewrite Henv_load_m3; eval_cbn.

      (* S9: Sset _t'4 (deref _t'2) -- read n from code buffer *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite Hcode_load_m3; eval_cbn.

      (* S10: Sset _t'5 (deref (cast(_t'3, tptr tlong) + _t'4)) -- env[n] *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_to_ptr_vptr_PEA env_b env_ofs m3); eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_env_n env_b env_ofs (Int.repr (Z.of_nat n)) m3); eval_cbn.
      rewrite Henv_n_eq.
      rewrite Hfield_load_m3; eval_cbn.

      (* S11: Sassign (s->accu) _t'5 -- store 4 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      try rewrite Hco; eval_cbn.
      try rewrite Haccu_offset; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Hstore_accu_field; eval_cbn.

      (* S12: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel sb so hm cb new_co
                     (ar_global_block ard) (ar_global_ofs ard)
                     (ar_stack_block ard) (ar_stack_base_ofs ard)
                     (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                     (ar_sptr_ofs_bound ard)).
      exists ard'.

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field *)
      { exists new_pc_v. split.
        - exact Hpc_load4.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift. }

      (* 3. accu field *)
      { exists cv. split.
        - exact Haccu_load4.
        - simpl. eapply val_repr_co_shift. exact Hfield_repr. }

      (* 4. sp field + stack *)
      { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load4.
        - reflexivity.
        - simpl.
          eapply stack_repr_store_other_block; [| exact Hstore_accu_field | auto].
          eapply stack_repr_store_other_block; [| exact Hstore_pc | auto].
          eapply stack_repr_co_shift.
          eapply stack_repr_cons_after_store; [| | exact Hstore_push | | ].
          + eapply stack_repr_store_other_block; [| exact Hstore_sp | auto].
            exact Hstack_repr.
          + exact Haccu_repr.
          + lia.
          + lia.
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - rewrite Hnew_sp_unsigned. lia.
        - simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned. lia.
        - simpl length. rewrite Nat2Z.inj_succ. rewrite Hnew_sp_unsigned.
          replace (Ptrofs.unsigned sp_ofs - 8 + 8 * Z.succ (Z.of_nat (length (Machine.stack s))))
            with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))) by lia.
          intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore_accu_field.
          eapply Mem.perm_store_1. exact Hstore_pc.
          eapply Mem.perm_store_1. exact Hstore_push.
          eapply Mem.perm_store_1. exact Hstore_sp.
          apply Hsp_writable. exact Hofs'.
        - exact Halign_new. }

      (* 5. env field *)
      { exists (Vptr env_b env_ofs). split.
        - exact Henv_load4.
        - simpl. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field *)
      { simpl. exact Hextra_load4. }

      (* 7. global_data field *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load4.
        - simpl. exact Hgd_eq.
        - simpl. eapply global_repr_co_shift.
          eapply global_repr_store_other_block; [| exact Hstore_accu_field | auto].
          eapply global_repr_store_other_block; [| exact Hstore_pc | auto].
          eapply global_repr_store_other_block; [| exact Hstore_push | auto].
          eapply global_repr_store_other_block; [| exact Hstore_sp | auto].
          exact Hglobal_repr.
        - simpl. exact Hgb_ne_sb. }

      (* 8. trap_sp field *)
      { exists ts_ptr. split.
        - exact Hts_load4.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore_accu_field.
        eapply Mem.perm_store_1. exact Hstore_pc.
        eapply Mem.perm_store_1. exact Hstore_push.
        eapply Mem.perm_store_1. exact Hstore_sp.
        apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
