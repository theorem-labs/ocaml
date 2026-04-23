(* NEGINT_bigstep_compl_computational.v -- NEGINT completeness proof using
   the computational evaluator from StepToBigstep.v.

   NEGINT handler:
   - Rocq: handle_NEGINT pc' s matches accu:
       Val_int n => Step {pc:=pc', accu:=Val_int(-n)}
       _         => Error

   - C (Clight AST): The handler body does:
       1. _t'1 = s->accu                          (read accu tagged int)
       2. s->accu = (long)(2 - (long)_t'1)        (tagged negation)
       3. return 0

   Tagged integer arithmetic correspondence:
     val_repr (Val_int n) = Vlong (Int64.repr (n*2+1))
     C computes: 2 - (n*2+1) = (-n)*2+1 = val_repr (Val_int (-n))

   Key differences from ACC0:
   - Case split on accu (Val_int vs other constructors)
   - Arithmetic computation on tagged integers, not just value shuffling
   - Only ONE store: accu field at offset +8
   - The result value is computed, not just copied

   Uses abs_rel directly (no separate _pre relation).
   All lemmas/axioms imported from HandlerLemmas. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.
Local Notation exec := (exec_stmt function_entry1 clight_ge).

(* Tactic for controlled reduction of the evaluator.
   Same as ACC0: cbn reduces evaluator control flow while leaving
   abstract operations (ge expansion, memory ops, ptrofs arith,
   semantic ops, PTree ops) unreduced. *)
Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Lemma: sem_sub on tint - tlong = Int64.sub with sign extension     *)
(*                                                                      *)
(* sem_binary_operation Osub (Vint (Int.repr 2)) tint                  *)
(*                           (Vlong n) tlong m                         *)
(*   = Some (Vlong (Int64.sub (Int64.repr 2) n))                      *)
(*                                                                      *)
(* Path through sem_sub:                                                *)
(*   classify_sub tint tlong = sub_default                              *)
(*   sem_binarith with classify_binarith tint tlong = bin_case_l Signed *)
(*   sem_cast (Vint (Int.repr 2)) tint tlong = Some (Vlong (Int64.repr 2))*)
(*     via cast_case_i2l Signed, cast_int_long Signed (Int.repr 2)     *)
(*     = Int64.repr (Int.signed (Int.repr 2)) = Int64.repr 2           *)
(*   sem_cast (Vlong n) tlong tlong = Some (Vlong n)                   *)
(*   sem_long Signed = fun _ n1 n2 => Some (Vlong (Int64.sub n1 n2))  *)
(* ================================================================== *)

Lemma sem_sub_int_long_2 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vint (Int.repr 2)) tint
    (Vlong n) tlong
    m = Some (Vlong (Int64.sub (Int64.repr 2) n)).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  (* classify_sub tint tlong = sub_default *)
  change (classify_sub tint tlong) with sub_default.
  unfold sem_binarith.
  change (classify_binarith tint tlong) with (bin_case_l Signed).
  simpl binarith_type.
  (* sem_cast (Vint (Int.repr 2)) tint tlong
     = Some (Vlong (cast_int_long Signed (Int.repr 2)))
     = Some (Vlong (Int64.repr (Int.signed (Int.repr 2))))
     = Some (Vlong (Int64.repr 2)) *)
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  change (Int.signed (Int.repr 2)) with 2%Z.
  (* sem_cast (Vlong n) tlong tlong = Some (Vlong n) *)
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  reflexivity.
Qed.

(* ================================================================== *)
(* Lemma: tagged integer negation correspondence                       *)
(*                                                                      *)
(* Int64.sub (Int64.repr 2) (Int64.repr (n*2+1))                      *)
(*   = Int64.repr ((-n)*2+1)                                           *)
(*                                                                      *)
(* Algebraically: 2 - (2n+1) = 1 - 2n = (-n)*2 + 1. Holds mod 2^64.  *)
(* ================================================================== *)

Lemma tagged_negint_arith : forall n,
  Int64.sub (Int64.repr 2) (Int64.repr (n * 2 + 1))
  = Int64.repr ((- n) * 2 + 1).
Proof.
  intros n.
  replace ((- n) * 2 + 1)%Z with (2 - (n * 2 + 1))%Z by lia.
  unfold Int64.sub.
  rewrite !Int64.unsigned_repr_eq.
  set (M := Int64.modulus).
  assert (HM : (M > 0)%Z) by (unfold M; vm_compute; reflexivity).
  assert (H2mod : (2 mod M = 2)%Z) by (unfold M; vm_compute; reflexivity).
  rewrite H2mod.
  (* Goal: repr(2 - (n*2+1) mod M) = repr(2 - (n*2+1)) *)
  apply Int64.eqm_samerepr.
  unfold Int64.eqm.
  pose proof (Z.div_mod (n * 2 + 1) M ltac:(lia)) as Hdm.
  set (q := ((n * 2 + 1) / M)%Z).
  exists q. lia.
Qed.

(* ================================================================== *)
(* Lemma: val_repr for the result of tagged negation                   *)
(*                                                                      *)
(* val_repr hm cb co (Val_int (-n))                                          *)
(*   (Vlong (Int64.sub (Int64.repr 2) (Int64.repr (n*2+1))))          *)
(* ================================================================== *)

Lemma val_repr_negint_result : forall hm cb co n,
  val_repr hm cb co (Val_int (- n))
    (Vlong (Int64.sub (Int64.repr 2) (Int64.repr (n * 2 + 1)))).
Proof.
  intros. rewrite tagged_negint_arith. constructor.
Qed.

(* ================================================================== *)
(* Lemma: load_result for Vlong is identity                            *)
(* ================================================================== *)

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_NEGINT_compl_comp :
    handler_correct_v1 handle_NEGINT f_instr_NEGINT
      accu_is_long
      (fun _ s => forall n, s.(Machine.accu) <> Val_int n)
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct_v1, handle_NEGINT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [n | | | ] eqn:Haccu_eq;
    try (intros; congruence).  (* non-Val_int accu => Error *)

  (* ================================================================ *)
  (* The Step case: accu = Val_int n                                   *)
  (* ================================================================ *)
  {
    intros ard Hpre Hstep_pre. unfold abs_rel_with_ard in Hpre.
    unfold accu_is_long in Hstep_pre.
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

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Determine accu_v from val_repr + accu = Val_int n *)
    rewrite Haccu_eq in Haccu_repr.
    (* Save the rewritten Haccu_repr for use in vr_code_ptr contradiction *)
    pose proof Haccu_repr as Haccu_repr_rw.
    inversion Haccu_repr; subst accu_v.
    2: { (* vr_code_ptr case: accu_v = Vptr cb ... but Hstep_pre says val_repr gives Vlong *)
         exfalso.
         rewrite Haccu_eq in Hstep_pre.
         destruct (Hstep_pre _ Haccu_repr_rw) as [z Hz].
         discriminate Hz. }
    set (cv_accu := Vlong (Int64.repr (n * 2 + 1))) in *.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* The result of the tagged negation *)
    set (cv_result := Vlong (Int64.sub (Int64.repr 2)
                                        (Int64.repr (n * 2 + 1)))) in *.

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 cv_accu Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv_result)
      as [m' Hstore].

    (* Witnesses *)
    set (le' := PTree.set _t'1 cv_accu le).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (*                                                                  *)
    (* The NEGINT handler body execution:                              *)
    (*   S1. _t'1 = s->accu             [Sset, field type tlong]      *)
    (*   S2. s->accu = (long)(2 - (long)_t'1) [Sassign, tagged neg]   *)
    (*   S3. return 0                                                   *)
    (*                                                                  *)
    (* Memory: m for S1, m' (after accu store) after S2.               *)
    (* Temp env: le -> le1(+_t'1)                                      *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 10).

      (* --- Initial reduction of the nested Ssequences --- *)
      eval_cbn.

      (* ============================================================ *)
      (* S1: Sset _t'1 (Efield (Ederef (Etempvar _s ...) ...)        *)
      (*                        _accu tlong)                           *)
      (*                                                                *)
      (* Path: Etempvar -> PTree.get _s le                             *)
      (*   -> Ederef struct -> comp_deref_loc By_copy -> Vptr sb so    *)
      (*   -> Efield: composite lookup, field_offset _accu = (8,Full)  *)
      (*   -> comp_deref_loc tlong By_value Mint64 -> Mem.load        *)
      (* ============================================================ *)
      rewrite Hle_s; eval_cbn.                                       (* PTree.get _s le *)
      rewrite Hco; eval_cbn.                                         (* genv_cenv ! _interp_state *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)
      (* access_mode tlong = By_value Mint64, cbn reduces directly *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* Ptrofs.unsigned (so + 8) *)
      rewrite Haccu_load; eval_cbn.                                  (* Mem.load accu field *)
      (* le1 = PTree.set _t'1 cv_accu le *)

      (* ============================================================ *)
      (* S2: Sassign (Efield ... _accu tlong)                          *)
      (*     (Ecast (Ebinop Osub (Econst_int 2 tint)                  *)
      (*                         (Ecast (Etempvar _t'1 tlong) tlong)  *)
      (*                         tlong) tlong)                         *)
      (*                                                                *)
      (* Lvalue: same struct field path, but in le1                    *)
      (* Rvalue: (long)(2 - (long)_t'1) = tagged negation             *)
      (* Inner Ecast tlong->tlong: sem_cast_long_vlong (identity)      *)
      (* Osub tint tlong: sem_sub_int_long_2                           *)
      (* Outer Ecast tlong->tlong: sem_cast_long_vlong                 *)
      (* Sassign cast tlong->tlong: sem_cast_long_vlong                *)
      (* Store via comp_assign_loc: By_value Mint64                    *)
      (* ============================================================ *)
      (* S2 lvalue + rvalue: single eval_cbn chain.
         After S1, the eval_cbn reduced the composite lookup and
         field_offset for the lvalue. Then for the rvalue, it evaluates
         subexpressions until hitting blocked terms (PTree.get, sem_cast,
         sem_binary_operation, Mem.store). *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'1 in le1 *)
      rewrite Hle_s; eval_cbn.                                       (* PTree.get _s le; lvalue fully computed *)

      (* Rvalue: resolve _t'1 *)
      rewrite PTree.gss; eval_cbn.                                   (* PTree.get _t'1 le1 = cv_accu *)
      rewrite (sem_cast_long_vlong (Int64.repr (n * 2 + 1))); eval_cbn.  (* Ecast identity *)

      (* Ebinop Osub: Vint(2) - Vlong(n*2+1) *)
      rewrite sem_sub_int_long_2; eval_cbn.                          (* Int64.sub result *)

      (* Outer Ecast tlong -> tlong *)
      rewrite sem_cast_long_vlong; eval_cbn.                         (* identity cast *)

      (* Sassign sem_cast: typeof rhs (tlong) -> typeof lhs (tlong) *)
      rewrite sem_cast_long_vlong; eval_cbn.                         (* identity cast *)

      (* comp_assign_loc: access_mode tlong = By_value Mint64 *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* Ptrofs.unsigned (so + 8) *)
      fold cv_result.                                                 (* re-fold expanded set *)
      rewrite Hstore; eval_cbn.                                      (* Mem.store accu: m -> m' *)

      (* ============================================================ *)
      (* S3: Sreturn (Some (Econst_int 0 tint))                       *)
      (* Reduces automatically after eval_cbn.                         *)
      (* ============================================================ *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv_result pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv_result env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv_result _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv_result gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv_result ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv_result Hstore) as Htmp.
        subst cv_result.
        rewrite load_result_vlong in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged by handler *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to negated value *)
      { exists cv_result. split.
        - exact Haccu_load'.
        - simpl. apply val_repr_negint_result. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv_result
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
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv_result
                   Hglobal_repr Hstore).
                    intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
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

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr NEGINT / clight_of NEGINT / pre_of NEGINT are convertible
   with handle_NEGINT / f_instr_NEGINT / accu_is_long.
   P_halt_of and P_ccall_of are vacuously satisfied (NEGINT never halts or
   issues a C call).  error_message_of requires a small computation bridge. *)
Definition correct_NEGINT :
    handler_correct (handle_instr NEGINT) (clight_of NEGINT)
      (error_message_of NEGINT)
      (pre_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).
Proof.
Admitted.
