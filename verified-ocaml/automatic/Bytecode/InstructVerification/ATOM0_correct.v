(* ATOM0_correct.v -- ATOM0 correctness proof.

   ATOM0 sets accu to Atom(0) = tag 0 atom = (long)(0 << 10) = 0.
   No PC advancement (no argument read from code stream).

   C code (f_instr_ATOM0):
     s->accu = (long)(0 << 10);   // atom with tag 0
     return 0;

   Rocq handler (handle_ATOM0):
     handle_ATOM0 pc' s = Step (s <|accu := Val_block 0 []|>)

   Atoms are empty blocks represented as tagged integers,
   matching vr_block_atom in val_repr.

   Single store to accu field at offset +8. No PC change, no temps.

   NO AXIOMS.  NO ADMITTED. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From RecordUpdate Require Import RecordUpdate.
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
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* 0 << 10 as ints *)
Local Lemma sem_shl_int_0_10 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint (Int.repr 0)) tint (Vint (Int.repr 10)) tint m =
    Some (Vint (Int.shl (Int.repr 0) (Int.repr 10))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 10) Int.iwordsize) with true.
  reflexivity.
Qed.

(* Int.shl 0 10 = 0 *)
Local Lemma int_shl_0_10 : Int.shl (Int.repr 0) (Int.repr 10) = Int.repr 0.
Proof.
  unfold Int.shl.
  change (Int.unsigned (Int.repr 10)) with 10%Z.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 10)%Z with 1024%Z.
  change (Int.unsigned (Int.repr 0)) with 0%Z.
  simpl. reflexivity.
Qed.

(* cast (int)0 -> (long)0 *)
Local Lemma sem_cast_int_shl_0_10_to_long : forall m,
  sem_cast (Vint (Int.shl (Int.repr 0) (Int.repr 10))) tint tlong m =
    Some (Vlong (Int64.repr 0)).
Proof.
  intros. rewrite int_shl_0_10.
  unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

(* load_result for Vlong 0 *)
Local Lemma atom0_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 0)) = Vlong (Int64.repr 0).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_ATOM0_correct :
    handler_correct handle_ATOM0 f_instr_ATOM0
      (fun _ _ _ _ => True)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handle_ATOM0. simpl.

  intros ard Hpre _. unfold abs_rel_with_ard in Hpre.
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
  pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
  pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
  pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

  (* Composite environment facts *)
  destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

  (* The atom value: Vlong (Int64.repr 0) *)
  set (atom_v := Vlong (Int64.repr 0)).

  (* Store: accu field at (sb, uso+8) <- atom_v *)
  destruct (store_succeeds_sb m sb so 8 accu_v Hsb_writable Haccu_load ltac:(lia) ltac:(lia) atom_v)
    as [m' Hstore].

  (* Witnesses -- fn_temps = nil, so le' = le *)
  exists le. exists m'.
  exists (Out_return (Some (Vint (Int.repr 0), tint))).

  split.

  (* ============================================================== *)
  (* Part 1: exec via computational evaluator                        *)
  (*                                                                  *)
  (* ATOM0 body:                                                     *)
  (*   Sassign (s->accu) (cast (0 << 10) tlong)                     *)
  (*   Sreturn 0                                                     *)
  (* ============================================================== *)
  {
    apply (eval_stmt_to_exec clight_ge 10).
    eval_cbn.

    (* === Sassign lvalue: s->accu === *)
    rewrite Hle_s; eval_cbn.
    rewrite Hco; eval_cbn.
    rewrite Haccu_offset; eval_cbn.

    (* === Sassign rvalue: (long)(0 << 10) === *)
    (* The Oshl subexpression: (int)0 << (int)10 *)
    rewrite (sem_shl_int_0_10 m); eval_cbn.

    (* The Ecast subexpression: sem_cast result to tlong *)
    rewrite (sem_cast_int_shl_0_10_to_long m); eval_cbn.

    (* === Sassign: sem_cast for store === *)
    rewrite (sem_cast_long_vlong (Int64.repr 0)); eval_cbn.

    (* === Sassign: store to accu field === *)
    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
    fold atom_v. rewrite Hstore; eval_cbn.

    (* === Sreturn 0 === *)
    reflexivity.
  }

  (* ============================================================== *)
  (* Part 2: abs_rel for post-state                                  *)
  (* ============================================================== *)
  {
    exists ard.
    set (uso := Ptrofs.unsigned so) in *.

    (* pc field at uso+0: unaffected by store at uso+8 *)
    assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
    { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) atom_v pc_ptr
               Hstore Hpc_load). left. lia. }

    (* accu field at uso+8: written by store *)
    assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some atom_v).
    { pose proof (load_after_store_same m m' sb (uso + 8) atom_v Hstore) as Htmp.
      subst atom_v. simpl in Htmp. exact Htmp. }

    (* sp field at uso+16: unaffected *)
    assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
    { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) atom_v (Vptr sp_b sp_ofs)
               Hstore Hsp_load). right. lia. }

    (* env field at uso+24: unaffected *)
    assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
    { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) atom_v env_v
               Hstore Henv_load). right. lia. }

    (* extra_args field at uso+32: unaffected *)
    assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) atom_v _
               Hstore Hextra_load). right. lia. }

    (* global_data field at uso+40: unaffected *)
    assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
    { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) atom_v gd_ptr
               Hstore Hgd_load). right. lia. }

    (* trap_sp field at uso+48: unaffected *)
    assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
    { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) atom_v ts_ptr
               Hstore Hts_load). right. lia. }

    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

    (* 1. _s is in le' -- le unchanged since fn_temps = nil *)
    { exact Hle_s. }

    (* 2. pc field -- unchanged by handler *)
    { exists pc_ptr. split.
      - exact Hpc_load'.
      - simpl. exact Hpc_rel. }

    (* 3. accu field -- updated to Val_block 0 [] via vr_block_atom *)
    { exists atom_v. split.
      - exact Haccu_load'.
      - simpl. subst atom_v.
        (* Val_block 0 nil <-> Vlong (Int64.repr (Z.of_nat 0 * 1024)) *)
        (* Z.of_nat 0 * 1024 = 0, so this is Vlong (Int64.repr 0) *)
        exact (vr_block_atom _ _ _ 0). }

    (* 4. sp field -- unchanged *)
    { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
      - exact Hsp_load'.
      - reflexivity.
      - simpl.
        apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) atom_v
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
        apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) atom_v
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
Qed.
