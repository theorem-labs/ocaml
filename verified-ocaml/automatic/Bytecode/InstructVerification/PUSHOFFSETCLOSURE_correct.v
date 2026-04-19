(* PUSHOFFSETCLOSURE_correct.v -- PUSHOFFSETCLOSURE (parameterized) completeness proof.

   C handler (f_instr_PUSHOFFSETCLOSURE):
     _t'6 = s->sp;                    // load sp
     _t'1 = (tptr tlong)(_t'6 - 1);   // new_sp = sp - 1
     s->sp = _t'1;                     // store 1: update sp field
     _t'5 = s->accu;                   // load accu
     *_t'1 = _t'5;                     // store 2: push accu onto stack
     _t'2 = s->pc;                     // load pc
     s->pc = _t'2 + 1;                // store 3: advance pc
     _t'3 = s->env;                    // load env from m3
     _t'4 = *_t'2;                     // read N from code buffer
     s->accu = _t'3 + _t'4 * sizeof(long);  // store 4: accu = env + N*8
     return 0;

   Rocq (handle_PUSHOFFSETCLOSURE ofs):
     let new_stack := accu :: stack in
     match env with
     | Val_closure addr base_ofs =>
         Step (accu := Val_closure addr (Z.to_nat (Z.of_nat base_ofs + ofs)),
               stack := new_stack)
     | Val_block t _ => if Z.eqb ofs 0 then Step ... else Error
     | _ => Error
     end

   Four stores on struct block + one on stack block:
     Store 1: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs
     Store 2: *new_sp (sp_b, new_sp_ofs) <- accu_v
     Store 3: pc field (sb, uso+0) <- Vptr cb new_pc_ofs
     Store 4: accu field (sb, uso+8) <- result_v  (= env_long + ofs*8)

   step_pre: sp_ofs >= 16 + code buffer read + closure offset precondition.
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
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: all four field offsets                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_all : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                     *)
(* ================================================================== *)

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_cast_tulong_tlong : forall n m,
  sem_cast (Vlong n) tulong tlong m = Some (Vlong n).
Proof. intros. reflexivity. Qed.

(* Omul: Vint(N) * Vptrofs(8) -> Vlong(Int.signed N * 8) *)
Local Lemma sem_mul_int_sizeof : forall n m,
  sem_binary_operation (genv_cenv ge) Omul
    (Vint n) tint
    (Vptrofs (Ptrofs.repr 8)) tulong m
  = Some (Vlong (Int64.mul (Int64.repr (Int.signed n)) (Int64.repr 8))).
Proof. intros. reflexivity. Qed.

(* Oadd: Vlong + Vlong -> Vlong *)
Local Lemma sem_add_long_long : forall a b m,
  sem_binary_operation (genv_cenv ge) Oadd
    (Vlong a) tlong (Vlong b) tulong m
  = Some (Vlong (Int64.add a b)).
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* pc_rel with shifted code base *)
Local Lemma pc_rel_shift : forall cb co rocq_pc,
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

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_PUSHOFFSETCLOSURE_correct : forall ofs,
    handler_correct (handle_PUSHOFFSETCLOSURE ofs) f_instr_PUSHOFFSETCLOSURE
      (fun e m s ard =>
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let hm := ar_heap_map ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         (* sp has room for push *)
         (exists sp_b sp_ofs,
            Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) /\
            Ptrofs.unsigned sp_ofs >= 16) /\
         (* code block separate from stack block *)
         (forall sp_b sp_ofs sp_ptr,
            Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr ->
            sp_ptr = Vptr sp_b sp_ofs ->
            cb <> sp_b) /\
         (* code memory at pc contains ofs *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
           = Some (Vint (Int.repr ofs)) /\
         (* env representability for result *)
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
         end)
      (fun msg s =>
        (msg = "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"%string /\
         match Machine.env s with Val_block _ _ => True | _ => False end) \/
        (msg = "PUSHOFFSETCLOSURE: invalid env"%string /\
         match Machine.env s with Val_closure _ _ | Val_block _ _ => False | _ => True end))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intro ofs.
  intros e le m s.
  unfold handler_correct, handle_PUSHOFFSETCLOSURE.

  (* Case split on s.(env) *)
  destruct (Machine.env s) eqn:Henv_eq.

  (* ================================================================ *)
  (* Case 1: env = Val_int z => Error "invalid env"                    *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 2: env = Val_block n l                                       *)
  (* ================================================================ *)
  - destruct (Z.eqb ofs 0) eqn:Hofs_eqb.
    (* Case 2a: ofs = 0 => Step (accu := env) -- need to prove *)
    + simpl.
      intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.

      (* Extract preconditions *)
      destruct Hstep_pre as [[sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]] [Hcb_ne_spb [Hcode_load [env_long [Henv_long_load Hresult_eq]]]]].
      simpl in Hsp_load'. fold sb so in Hsp_load'.
      assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
        by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

      (* Code block separate from stack block *)
      assert (Hcb_ne_sp_b : cb <> sp_b).
      { exact (Hcb_ne_spb sp_b sp_ofs (Vptr sp_b sp_ofs) Hsp_load eq_refl). }

      (* env_v = Vlong env_long *)
      assert (Henv_v_long : env_v = Vlong env_long).
      { rewrite Henv_long_load in Henv_load. congruence. }
      subst env_v.

      (* Rewrite env_repr for Val_block case *)
      rewrite Henv_eq in Henv_repr.

      (* Structural invariants *)
      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
      pose proof (code_block_ne_sptr ard) as Hcb_ne_sb. fold sb cb in Hcb_ne_sb.

      (* Composite environment facts *)
      destruct interp_state_co_all as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].
      destruct interp_state_co_env as [co_env [Hco_env [Henv_offset _]]].
      assert (co_env = co_is) as -> by congruence.

      (* pc_ptr is a concrete Vptr *)
      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      (* New sp after push *)
      set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
      assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
      { subst new_sp_ofs. unfold Ptrofs.sub.
        change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
        apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
        unfold Ptrofs.max_unsigned. lia. }

      (* New pc after advancement *)
      set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
      set (new_pc_v := Vptr cb new_pc_ofs).

      (* Store 1: sp field <- new_sp *)
      destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

      (* Store 2: *new_sp <- accu_v *)
      assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
      { rewrite Hnew_sp_unsigned. simpl align_chunk.
        apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
      destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
                  sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
                  (Ptrofs.unsigned new_sp_ofs)
                  Hstore1 Hsp_writable
                  ltac:(rewrite Hnew_sp_unsigned; lia)
                  ltac:(rewrite Hnew_sp_unsigned; lia)
                  Halign_new accu_v) as [m2 Hstore2].

      (* Store 3: pc field <- new_pc_v *)
      assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
                Some (Vptr cb pc_ofs)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
                 (Ptrofs.unsigned so + 0) (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
                 Hstore1 Hpc_load). left. lia. }
      assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
                Some (Vptr cb pc_ofs)).
      { erewrite Mem.load_store_other; [exact Hpc_load_m1 | exact Hstore2 |].
        left. exact (not_eq_sym Hsp_ne_sb). }
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.
      destruct (store_succeeds_sb m2 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m2 Hpc_load_m2 ltac:(lia) ltac:(lia) new_pc_v) as [m3 Hstore3].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

      (* Vlong env_long survives stores 1, 2, 3 *)
      assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
                 (Ptrofs.unsigned so + 24) (Vptr sp_b new_sp_ofs) (Vlong env_long)
                 Hstore1 Henv_long_load). right. lia. }
      assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
      { erewrite Mem.load_store_other; [exact Henv_load_m1 | exact Hstore2 |].
        left. exact (not_eq_sym Hsp_ne_sb). }
      assert (Henv_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0)
                 (Ptrofs.unsigned so + 24) new_pc_v (Vlong env_long)
                 Hstore3 Henv_load_m2). right. lia. }

      (* Code load survives stores 1, 2, 3 (cb distinct from sb and sp_b) *)
      assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr ofs))).
      { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore1 |].
        left. exact Hcb_ne_sb. }
      assert (Hcode_load_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr ofs))).
      { erewrite Mem.load_store_other; [exact Hcode_load_m1 | exact Hstore2 |].
        left. exact Hcb_ne_sp_b. }
      assert (Hcode_load_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr ofs))).
      { erewrite Mem.load_store_other; [exact Hcode_load_m2 | exact Hstore3 |].
        left. exact Hcb_ne_sb. }

      (* Store 4: accu field <- env_v *)
      assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
                 (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
                 Hstore1 Haccu_load). left. lia. }
      assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore2 |].
        left. exact (not_eq_sym Hsp_ne_sb). }
      assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some accu_v).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0)
                 (Ptrofs.unsigned so + 8) new_pc_v accu_v
                 Hstore3 Haccu_load_m2). right. lia. }
      (* Compute result value: env + ofs * sizeof(long) *)
      set (result_v := Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)))).
      destruct (store_succeeds_sb m3 sb so 8 accu_v Hsb_writable_m3 Haccu_load_m3 ltac:(lia) ltac:(lia) result_v) as [m4 Hstore4].

      (* Witnesses *)
      set (le' := PTree.set _t'4 (Vint (Int.repr ofs))
                  (PTree.set _t'3 (Vlong env_long)
                  (PTree.set _t'2 (Vptr cb pc_ofs)
                  (PTree.set _t'5 accu_v
                  (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                  (PTree.set _t'6 (Vptr sp_b sp_ofs) le)))))).
      exists le'. exists m4.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* ============================================================== *)
      (* Part 1: exec via computational evaluator                        *)
      (* ============================================================== *)
      {
        unfold so, sb in *.

        apply (eval_stmt_to_exec clight_ge 20).
        eval_cbn.

        (* S1: Sset _t'6 (s->sp) *)
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hsp_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
        rewrite Hsp_load; eval_cbn.

        (* S2: Sset _t'1 (cast (_t'6 - 1) (tptr tlong)) *)
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
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
        fold new_sp_ofs.
        rewrite Hstore1; eval_cbn.

        (* S4: Sset _t'5 (s->accu) from m1 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Haccu_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
        rewrite Haccu_load_m1; eval_cbn.

        (* S5: Sassign (deref _t'1) _t'5 -- store 2 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
        fold new_sp_ofs.
        rewrite Hstore2; eval_cbn.

        (* S6: Sset _t'2 (s->pc) from m2 *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load_m2; eval_cbn.

        (* S7: Sassign (s->pc) (_t'2 + 1) -- store 3: advance pc *)
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m2); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
        fold new_pc_v.
        rewrite Hstore3; eval_cbn.

        (* S8: Sset _t'3 (s->env) from m3 *)
        (* After Sassign (store3), temp env is still: _t'2 -> _t'5 -> _t'1 -> _t'6 -> le *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'2 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'5 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'1 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'6 *)
        rewrite Hle_s; eval_cbn.
        rewrite Henv_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 24 ltac:(lia) ltac:(lia)).
        rewrite Henv_load_m3; eval_cbn.

        (* S9: Sset _t'4 (deref _t'2) -- read N from code *)
        (* After Sset _t'3, env is: _t'3 -> _t'2 -> _t'5 -> _t'1 -> _t'6 -> le *)
        (* Need to read _t'2: skip _t'3 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'3 *)
        rewrite PTree.gss; eval_cbn. (* _t'2 *)
        rewrite Hcode_load_m3; eval_cbn.

        (* S10: Sassign (s->accu) (_t'3 + _t'4 * sizeof(long)) -- store 4 *)
        (* After Sset _t'4, env is: _t'4 -> _t'3 -> _t'2 -> _t'5 -> _t'1 -> _t'6 -> le *)
        (* Lvalue: s->accu -- need _s: skip _t'4, _t'3, _t'2, _t'5, _t'1, _t'6 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'4 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'3 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'2 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'5 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'1 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'6 *)
        rewrite Hle_s; eval_cbn.

        (* Rvalue: _t'3 + _t'4 * sizeof(long) *)
        (* _t'3: skip _t'4 *)
        rewrite PTree.gso by (compute; congruence). (* skip _t'4 *)
        rewrite PTree.gss; eval_cbn. (* _t'3 *)

        (* _t'4 *)
        rewrite PTree.gss; eval_cbn. (* _t'4 *)

        (* Inner mul: _t'4 * sizeof(long) *)
        rewrite sem_mul_int_sizeof; eval_cbn.

        (* Outer add: env_long + N*8 *)
        rewrite sem_add_long_long; eval_cbn.

        (* Cast: tulong -> tlong *)
        rewrite sem_cast_tulong_tlong; eval_cbn.

        (* Store to accu field *)
        rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
        fold result_v.
        rewrite Hstore4; eval_cbn.

        (* S11: Sreturn 0 *)
        subst le'. reflexivity.
      }

      (* ============================================================== *)
      (* Part 2: abs_rel for post-state                                  *)
      (* ============================================================== *)
      {
        set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
        set (ard' := mk_abs_rel
          (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
          (ar_code_base_block ard) new_co
          (ar_global_block ard) (ar_global_ofs ard)
          (ar_stack_block ard) (ar_stack_base_ofs ard)
          (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
          (ar_sptr_ofs_bound ard)).
        exists ard'.
        set (uso := Ptrofs.unsigned so) in *.

        (* Helper: loads on sb survive store 2 (different block) *)
        assert (Hload_sb_m2 : forall ofs' v,
          Mem.load Mint64 m1 sb ofs' = Some v ->
          Mem.load Mint64 m2 sb ofs' = Some v).
        { intros ofs' v Hload1.
          erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
          left. exact (not_eq_sym Hsp_ne_sb). }

        (* result_v = Vlong env_long in the Val_block ofs=0 case *)
        assert (Hresult_is_env : result_v = Vlong env_long).
        { unfold result_v. f_equal. exact Hresult_eq. }

        (* pc field at uso+0: survived stores 1,2; written by store 3; survives store 4 *)
        assert (Hpc_load_m3' : Mem.load Mint64 m3 sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m2 m3 sb (uso + 0) new_pc_v Hstore3) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
        assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
        { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 0)
                   result_v new_pc_v Hstore4 Hpc_load_m3'). left. lia. }

        (* accu field at uso+8: survived stores 1,2,3; written by store 4 *)
        assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some result_v).
        { pose proof (load_after_store_same m3 m4 sb (uso + 8) result_v Hstore4) as Htmp.
          unfold result_v in Htmp |- *.
          change (Val.load_result Mint64 (Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)))))
            with (Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)))) in Htmp.
          exact Htmp. }

        (* sp field at uso+16: written by store 1, survives stores 2,3,4 *)
        assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
        { pose proof (load_after_store_same m m1 sb (uso + 16)
                        (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
          simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
        assert (Hsp_load_m2' : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
        { exact (Hload_sb_m2 _ _ Hsp_load_m1). }
        assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
        { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 16)
                   new_pc_v (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2'). right. lia. }
        assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
        { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 16)
                   result_v (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3). right. lia. }

        (* env field at uso+24: unaffected by all 4 stores *)
        assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some (Vlong env_long)).
        { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 24)
                   result_v (Vlong env_long) Hstore4 Henv_load_m3). right. lia. }

        (* extra_args field at uso+32: unaffected *)
        assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                   (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
        assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 32)
                   result_v _ Hstore4).
          - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 32)
                     new_pc_v _ Hstore3).
            + exact (Hload_sb_m2 _ _ Hextra_load_m1).
            + right. lia.
          - right. lia. }

        (* global_data field at uso+40: unaffected *)
        assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                   (Vptr sp_b new_sp_ofs) gd_ptr Hstore1 Hgd_load). right. lia. }
        assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 40)
                   result_v gd_ptr Hstore4).
          - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 40)
                     new_pc_v gd_ptr Hstore3).
            + exact (Hload_sb_m2 _ _ Hgd_load_m1).
            + right. lia.
          - right. lia. }

        (* trap_sp field at uso+48: unaffected *)
        assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                   (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
        assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 48)
                   result_v ts_ptr Hstore4).
          - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 48)
                     new_pc_v ts_ptr Hstore3).
            + exact (Hload_sb_m2 _ _ Hts_load_m1).
            + right. lia.
          - right. lia. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s is in le' *)
        { subst le'.
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          rewrite PTree.gso by (compute; congruence).
          exact Hle_s. }

        (* 2. pc field -- updated, shifted code_base *)
        { exists new_pc_v. split.
          - exact Hpc_load4.
          - simpl. subst new_pc_v new_pc_ofs.
            apply pc_rel_shift. }

        (* 3. accu field -- updated to result_v = Vlong env_long *)
        { exists result_v. split.
          - exact Haccu_load4.
          - simpl. rewrite Hresult_is_env.
            eapply val_repr_co_shift. exact Henv_repr. }

        (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
        { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load4.
          - reflexivity.
          - simpl.
            eapply stack_repr_store_other_block; [| exact Hstore4 | auto].
            eapply stack_repr_store_other_block; [| exact Hstore3 | auto].
            eapply stack_repr_co_shift.
            eapply stack_repr_cons_after_store; [| | exact Hstore2 | | ].
            + eapply stack_repr_store_other_block; [| exact Hstore1 | auto].
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
            intros ofs' Hofs'.
            eapply Mem.perm_store_1. exact Hstore4.
            eapply Mem.perm_store_1. exact Hstore3.
            eapply Mem.perm_store_1. exact Hstore2.
            eapply Mem.perm_store_1. exact Hstore1.
            apply Hsp_writable. lia.
          - exact Halign_new. }

        (* 5. env field -- unchanged *)
        { exists (Vlong env_long). split.
          - exact Henv_load4.
          - simpl. rewrite Henv_eq. eapply val_repr_co_shift. exact Henv_repr. }

        (* 6. extra_args field -- unchanged *)
        { simpl. exact Hextra_load4. }

        (* 7. global_data field -- unchanged *)
        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load4.
          - simpl. exact Hgd_eq.
          - simpl. eapply global_repr_co_shift.
            eapply global_repr_store_other_block; [| exact Hstore4 | auto].
            eapply global_repr_store_other_block; [| exact Hstore3 | auto].
            eapply global_repr_store_other_block; [| exact Hstore2 | auto].
            eapply global_repr_store_other_block; [| exact Hstore1 | auto].
            exact Hglobal_repr.
          - simpl. exact Hgb_ne_sb. }

        (* 8. trap_sp field -- unchanged *)
        { exists ts_ptr. split.
          - exact Hts_load4.
          - simpl. exact Htrap_rel. }

        (* 9. sb_writable *)
        { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore4.
          eapply Mem.perm_store_1. exact Hstore3.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsb_writable. exact Hofs'. }
      }

    (* Case 2b: ofs <> 0 => Error "non-zero offset" *)
    + left; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 3: env = Val_ptr n => Error "invalid env"                    *)
  (* ================================================================ *)
  - right; exact (conj eq_refl I).

  (* ================================================================ *)
  (* Case 4: env = Val_closure n n0 => Step                            *)
  (* ================================================================ *)
  - simpl.
    intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    (* Extract preconditions *)
    destruct Hstep_pre as [[sp_b' [sp_ofs' [Hsp_load' Hsp_ge16]]] [Hcb_ne_spb [Hcode_load [env_long [Henv_long_load Hresult_repr]]]]].
    simpl in Hsp_load'. fold sb so in Hsp_load'.
    assert (sp_b' = sp_b /\ sp_ofs' = sp_ofs) as [-> ->]
      by (rewrite Hsp_load in Hsp_load'; injection Hsp_load'; auto).

    (* Code block separate from stack block *)
    assert (Hcb_ne_sp_b : cb <> sp_b).
    { exact (Hcb_ne_spb sp_b sp_ofs (Vptr sp_b sp_ofs) Hsp_load eq_refl). }

    (* env_v = Vlong env_long *)
    assert (Henv_v_long : env_v = Vlong env_long).
    { rewrite Henv_long_load in Henv_load. congruence. }
    subst env_v.

    (* Rewrite env in Henv_repr *)
    rewrite Henv_eq in Henv_repr.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.
    pose proof (code_block_ne_sptr ard) as Hcb_ne_sb. fold sb cb in Hcb_ne_sb.

    (* Composite environment facts *)
    destruct interp_state_co_all as [co_is [Hco [Hpc_offset [Haccu_offset Hsp_offset]]]].
    destruct interp_state_co_env as [co_env [Hco_env [Henv_offset _]]].
    assert (co_env = co_is) as -> by congruence.

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* New sp after push *)
    set (new_sp_ofs := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
    assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs = Ptrofs.unsigned sp_ofs - 8).
    { subst new_sp_ofs. unfold Ptrofs.sub.
      change (Ptrofs.unsigned (Ptrofs.repr 8)) with 8.
      apply Ptrofs.unsigned_repr. pose proof (Ptrofs.unsigned_range sp_ofs).
      unfold Ptrofs.max_unsigned. lia. }

    (* New pc after advancement *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* Result value *)
    set (result_v := Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)))).

    (* Store 1: sp field <- new_sp *)
    destruct (store_succeeds_sb m sb so 16 (Vptr sp_b sp_ofs) Hsb_writable Hsp_load ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m1 Hstore1].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

    (* Store 2: *new_sp <- accu_v *)
    assert (Halign_new : (align_chunk Mint64 | Ptrofs.unsigned new_sp_ofs)).
    { rewrite Hnew_sp_unsigned. simpl align_chunk.
      apply Z.divide_sub_r. exact Hsp_align. exists 1; lia. }
    destruct (store_to_sp_after_sb_store m m1 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)
                sp_b (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
                (Ptrofs.unsigned new_sp_ofs)
                Hstore1 Hsp_writable
                ltac:(rewrite Hnew_sp_unsigned; lia)
                ltac:(rewrite Hnew_sp_unsigned; lia)
                Halign_new accu_v) as [m2 Hstore2].

    (* Store 3: pc field <- new_pc_v *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 0) (Vptr sp_b new_sp_ofs) (Vptr cb pc_ofs)
               Hstore1 Hpc_load). left. lia. }
    assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { erewrite Mem.load_store_other; [exact Hpc_load_m1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.
    destruct (store_succeeds_sb m2 sb so 0 (Vptr cb pc_ofs) Hsb_writable_m2 Hpc_load_m2 ltac:(lia) ltac:(lia) new_pc_v) as [m3 Hstore3].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

    (* env_v survives stores 1, 2, 3 *)
    assert (Henv_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 24) (Vptr sp_b new_sp_ofs) (Vlong env_long)
               Hstore1 Henv_long_load). right. lia. }
    assert (Henv_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
    { erewrite Mem.load_store_other; [exact Henv_load_m1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }
    assert (Henv_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some (Vlong env_long)).
    { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 24) new_pc_v (Vlong env_long)
               Hstore3 Henv_load_m2). right. lia. }

    (* Code load survives stores 1, 2, 3 *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr ofs))).
    { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore1 |].
      left. exact Hcb_ne_sb. }
    assert (Hcode_load_m2 : Mem.load Mint32 m2 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr ofs))).
    { erewrite Mem.load_store_other; [exact Hcode_load_m1 | exact Hstore2 |].
      left. exact Hcb_ne_sp_b. }
    assert (Hcode_load_m3 : Mem.load Mint32 m3 cb (Ptrofs.unsigned pc_ofs) = Some (Vint (Int.repr ofs))).
    { erewrite Mem.load_store_other; [exact Hcode_load_m2 | exact Hstore3 |].
      left. exact Hcb_ne_sb. }

    (* Store 4: accu field <- result_v *)
    assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 16)
               (Ptrofs.unsigned so + 8) (Vptr sp_b new_sp_ofs) accu_v
               Hstore1 Haccu_load). left. lia. }
    assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { erewrite Mem.load_store_other; [exact Haccu_load_m1 | exact Hstore2 |].
      left. exact (not_eq_sym Hsp_ne_sb). }
    assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some accu_v).
    { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 8) new_pc_v accu_v
               Hstore3 Haccu_load_m2). right. lia. }
    destruct (store_succeeds_sb m3 sb so 8 accu_v Hsb_writable_m3 Haccu_load_m3 ltac:(lia) ltac:(lia) result_v) as [m4 Hstore4].

    (* Witnesses *)
    set (le' := PTree.set _t'4 (Vint (Int.repr ofs))
                (PTree.set _t'3 (Vlong env_long)
                (PTree.set _t'2 (Vptr cb pc_ofs)
                (PTree.set _t'5 accu_v
                (PTree.set _t'1 (Vptr sp_b new_sp_ofs)
                (PTree.set _t'6 (Vptr sp_b sp_ofs) le)))))).
    exists le'. exists m4.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      unfold so, sb in *.

      apply (eval_stmt_to_exec clight_ge 20).
      eval_cbn.

      (* S1: Sset _t'6 (s->sp) *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      (* S2: Sset _t'1 (cast (_t'6 - 1) (tptr tlong)) *)
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
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 16 ltac:(lia) ltac:(lia)).
      fold new_sp_ofs.
      rewrite Hstore1; eval_cbn.

      (* S4: Sset _t'5 (s->accu) from m1 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load_m1; eval_cbn.

      (* S5: Sassign (deref _t'1) _t'5 -- store 2 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Haccu_repr); eval_cbn.
      fold new_sp_ofs.
      rewrite Hstore2; eval_cbn.

      (* S6: Sset _t'2 (s->pc) from m2 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Hpc_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_m2; eval_cbn.

      (* S7: Sassign (s->pc) (_t'2 + 1) -- store 3: advance pc *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_pc_1 cb pc_ofs m2); eval_cbn.
      rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore3; eval_cbn.

      (* S8: Sset _t'3 (s->env) from m3 *)
      (* After Sassign (store3), temp env is still: _t'2 -> _t'5 -> _t'1 -> _t'6 -> le *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'2 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'5 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'1 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'6 *)
      rewrite Hle_s; eval_cbn.
      rewrite Henv_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 24 ltac:(lia) ltac:(lia)).
      rewrite Henv_load_m3; eval_cbn.

      (* S9: Sset _t'4 (deref _t'2) -- read N from code *)
      (* After Sset _t'3, env is: _t'3 -> _t'2 -> _t'5 -> _t'1 -> _t'6 -> le *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'3 *)
      rewrite PTree.gss; eval_cbn. (* _t'2 *)
      rewrite Hcode_load_m3; eval_cbn.

      (* S10: Sassign (s->accu) (_t'3 + _t'4 * sizeof(long)) -- store 4 *)
      (* After Sset _t'4, env is: _t'4 -> _t'3 -> _t'2 -> _t'5 -> _t'1 -> _t'6 -> le *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'4 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'3 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'2 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'5 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'1 *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'6 *)
      rewrite Hle_s; eval_cbn.

      (* Rvalue: _t'3 + _t'4 * sizeof(long) *)
      rewrite PTree.gso by (compute; congruence). (* skip _t'4 *)
      rewrite PTree.gss; eval_cbn. (* _t'3 *)
      rewrite PTree.gss; eval_cbn. (* _t'4 *)

      (* Inner mul: _t'4 * sizeof(long) *)
      rewrite sem_mul_int_sizeof; eval_cbn.

      (* Outer add: env_long + N*8 *)
      rewrite sem_add_long_long; eval_cbn.

      (* Cast: tulong -> tlong *)
      rewrite sem_cast_tulong_tlong; eval_cbn.

      (* Store to accu field *)
      rewrite (ptrofs_add_unsigned (ar_sptr_ofs ard) 8 ltac:(lia) ltac:(lia)).
      fold result_v.
      rewrite Hstore4; eval_cbn.

      (* S11: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel
        (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
        (ar_code_base_block ard) new_co
        (ar_global_block ard) (ar_global_ofs ard)
        (ar_stack_block ard) (ar_stack_base_ofs ard)
        (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
        (ar_sptr_ofs_bound ard)).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      (* Helper: loads on sb survive store 2 (different block) *)
      assert (Hload_sb_m2 : forall ofs' v,
        Mem.load Mint64 m1 sb ofs' = Some v ->
        Mem.load Mint64 m2 sb ofs' = Some v).
      { intros ofs' v Hload1.
        erewrite Mem.load_store_other; [exact Hload1 | exact Hstore2 |].
        left. exact (not_eq_sym Hsp_ne_sb). }

      (* pc field at uso+0: survived stores 1,2; written by store 3; survives store 4 *)
      assert (Hpc_load_m3' : Mem.load Mint64 m3 sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m2 m3 sb (uso + 0) new_pc_v Hstore3) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
      assert (Hpc_load4 : Mem.load Mint64 m4 sb (uso + 0) = Some new_pc_v).
      { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 0)
                 result_v new_pc_v Hstore4 Hpc_load_m3'). left. lia. }

      (* accu field at uso+8: survived stores 1,2,3; written by store 4 *)
      assert (Haccu_load4 : Mem.load Mint64 m4 sb (uso + 8) = Some result_v).
      { pose proof (load_after_store_same m3 m4 sb (uso + 8) result_v Hstore4) as Htmp.
        unfold result_v in Htmp |- *.
        change (Val.load_result Mint64 (Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)))))
          with (Vlong (Int64.add env_long (Int64.mul (Int64.repr (Int.signed (Int.repr ofs))) (Int64.repr 8)))) in Htmp.
        exact Htmp. }

      (* sp field at uso+16: written by store 1, survives stores 2,3,4 *)
      assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { pose proof (load_after_store_same m m1 sb (uso + 16)
                      (Vptr sp_b new_sp_ofs) Hstore1) as Htmp.
        simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
      assert (Hsp_load_m2' : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { exact (Hload_sb_m2 _ _ Hsp_load_m1). }
      assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 16)
                 new_pc_v (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2'). right. lia. }
      assert (Hsp_load4 : Mem.load Mint64 m4 sb (uso + 16) = Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 16)
                 result_v (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3). right. lia. }

      (* env field at uso+24: unaffected by all 4 stores *)
      assert (Henv_load4 : Mem.load Mint64 m4 sb (uso + 24) = Some (Vlong env_long)).
      { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 24)
                 result_v (Vlong env_long) Hstore4 Henv_load_m3). right. lia. }

      (* extra_args field at uso+32: unaffected *)
      assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 32)
                 (Vptr sp_b new_sp_ofs) _ Hstore1 Hextra_load). right. lia. }
      assert (Hextra_load4 : Mem.load Mint64 m4 sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 32)
                 result_v _ Hstore4).
        - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 32)
                   new_pc_v _ Hstore3).
          + exact (Hload_sb_m2 _ _ Hextra_load_m1).
          + right. lia.
        - right. lia. }

      (* global_data field at uso+40: unaffected *)
      assert (Hgd_load_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 40)
                 (Vptr sp_b new_sp_ofs) gd_ptr Hstore1 Hgd_load). right. lia. }
      assert (Hgd_load4 : Mem.load Mint64 m4 sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 40)
                 result_v gd_ptr Hstore4).
        - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 40)
                   new_pc_v gd_ptr Hstore3).
          + exact (Hload_sb_m2 _ _ Hgd_load_m1).
          + right. lia.
        - right. lia. }

      (* trap_sp field at uso+48: unaffected *)
      assert (Hts_load_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m1 sb (uso + 16) (uso + 48)
                 (Vptr sp_b new_sp_ofs) ts_ptr Hstore1 Hts_load). right. lia. }
      assert (Hts_load4 : Mem.load Mint64 m4 sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m3 m4 sb (uso + 8) (uso + 48)
                 result_v ts_ptr Hstore4).
        - apply (load_after_store_other m2 m3 sb (uso + 0) (uso + 48)
                   new_pc_v ts_ptr Hstore3).
          + exact (Hload_sb_m2 _ _ Hts_load_m1).
          + right. lia.
        - right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated, shifted code_base *)
      { exists new_pc_v. split.
        - exact Hpc_load4.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift. }

      (* 3. accu field -- updated to result_v *)
      { exists result_v. split.
        - exact Haccu_load4.
        - simpl. eapply val_repr_co_shift. exact Hresult_repr. }

      (* 4. sp field -- updated to new_sp_ofs; stack gets accu prepended *)
      { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load4.
        - reflexivity.
        - simpl.
          eapply stack_repr_store_other_block; [| exact Hstore4 | auto].
          eapply stack_repr_store_other_block; [| exact Hstore3 | auto].
          eapply stack_repr_co_shift.
          eapply stack_repr_cons_after_store; [| | exact Hstore2 | | ].
          + eapply stack_repr_store_other_block; [| exact Hstore1 | auto].
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
          intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore4.
          eapply Mem.perm_store_1. exact Hstore3.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsp_writable. lia.
        - exact Halign_new. }

      (* 5. env field -- unchanged *)
      { exists (Vlong env_long). split.
        - exact Henv_load4.
        - simpl. rewrite Henv_eq. eapply val_repr_co_shift. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load4. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load4.
        - simpl. exact Hgd_eq.
        - simpl. eapply global_repr_co_shift.
          eapply global_repr_store_other_block; [| exact Hstore4 | auto].
          eapply global_repr_store_other_block; [| exact Hstore3 | auto].
          eapply global_repr_store_other_block; [| exact Hstore2 | auto].
          eapply global_repr_store_other_block; [| exact Hstore1 | auto].
          exact Hglobal_repr.
        - simpl. exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load4.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable *)
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore4.
        eapply Mem.perm_store_1. exact Hstore3.
        eapply Mem.perm_store_1. exact Hstore2.
        eapply Mem.perm_store_1. exact Hstore1.
        apply Hsb_writable. exact Hofs'. }
    }
Qed.
