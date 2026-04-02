(* ENVACC1_correct.v -- ENVACC1 correctness proof.

   ENVACC1: accu = Field(env, 1), i.e., load field 1 from the closure
   environment pointed to by env.

   Rocq handler (Interpret.v):
     handle_ENVACC 1 pc' s =
       match field_or_heap s s.(env) 1 with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "ENVACC: env access out of bounds"
       end

   C handler (instruct_handlers.v, f_instr_ENVACC1):
     t1 = s->env;
     t2 = deref((long ptr)t1 + 1);   // deref env as pointer, field 1
     s->accu = t2;
     return 0;

   Same heap model gap as GETFIELD0 -- uses a heap_field_loadable
   precondition for the env pointer.

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
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr                 *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr_EA1 : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 1 *)
Lemma sem_add_ptr_long_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 1)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 8))).
Proof. exact sem_add_sp_1. Qed.

(* ================================================================== *)
(* Heap field precondition for env field 1                             *)
(* ================================================================== *)

Definition env_field_loadable_1
    (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  forall v,
    field_or_heap s s.(Machine.env) 1 = Some v ->
    forall env_v,
      val_repr hm s.(Machine.env) env_v ->
      exists b ofs cv,
        env_v = Vptr b ofs /\
        Mem.load Mint64 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) = Some cv /\
        val_repr hm v cv.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ENVACC1_with_pre :
    handler_correct (handle_ENVACC 1) f_instr_ENVACC1
      (fun _ => env_field_loadable_1)
      (fun _ s => field_or_heap s s.(Machine.env) 1 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_ENVACC.
  destruct (field_or_heap s s.(Machine.env) 1) as [v|] eqn:Hfoh.

  (* ================================================================ *)
  (* Case 1: field_or_heap = Some v => Step                            *)
  (* ================================================================ *)
  2: { reflexivity. }
  {
    intros ard Hpre Hefl.

    (* Unpack abs_rel_with_ard *)
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

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

    (* Use heap precondition to get the field value in C memory *)
    unfold env_field_loadable_1 in Hefl.
    destruct (Hefl v Hfoh env_v Henv_repr)
      as [b [ofs [cv [Henv_is_ptr [Hfield_load Hfield_repr]]]]].
    subst env_v.

    (* Composite environment facts *)
    destruct interp_state_co_env as [co_is [Hco [Henv_offset Haccu_offset]]].

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv) as [m' Hstore].

    (* Witnesses *)
    set (le' := PTree.set _t'2 cv (PTree.set _t'1 (Vptr b ofs) le)).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 10).

      (* --- Initial reduction --- *)
      eval_cbn.

      (* === Sset _t'1 (s->env) === *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      rewrite Hco; eval_cbn.                                         (* composite lookup *)
      rewrite Henv_offset; eval_cbn.                                 (* field_offset _env *)
      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).     (* env ptrofs *)
      rewrite Henv_load; eval_cbn.                                   (* env field load *)

      (* === Sset _t'2 : deref (cast(_t'1) + 1) === *)
      rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
      (* Cast: tlong -> (tptr tlong) for Vptr *)
      rewrite sem_cast_long_to_ptr_vptr_EA1; eval_cbn.              (* sem_cast *)
      (* Add: ptr + 1 = ptr + 8 bytes *)
      rewrite (sem_add_ptr_long_1 b ofs m); eval_cbn.               (* sem_add *)
      (* Deref: load field 1 from heap block *)
      rewrite Hfield_load; eval_cbn.                                 (* field load *)

      (* === Sassign (s->accu = _t'2) === *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)

      (* === Sassign rvalue + sem_cast + store === *)
      rewrite PTree.gss; eval_cbn.                                   (* le2 ! _t'2 *)
      rewrite (sem_cast_long_val_repr _ _ _ _ Hfield_repr); eval_cbn. (* sem_cast *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* accu ptrofs *)
      rewrite Hstore; eval_cbn.                                      (* accu store *)

      (* === Sreturn 0 -- reduces automatically === *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some (Vptr b ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv (Vptr b ofs)
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv Hstore) as Htmp.
        rewrite (val_repr_load_result hm v cv Hfield_repr) in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to env field value *)
      { exists cv. split.
        - exact Haccu_load'.
        - simpl. exact Hfield_repr. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          apply (stack_repr_store_other_block hm m m' _ sp_b sp_ofs sb (uso + 8) cv
                   Hstack_repr Hstore).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists (Vptr b ofs). split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm m m' _ _ _ sb (uso + 8) cv
                   Hglobal_repr Hstore).
          intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
