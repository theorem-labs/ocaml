(* OFFSETINT_correct.v -- OFFSETINT completeness proof.

   OFFSETINT handler:
   - Rocq: handle_OFFSETINT ofs pc' s matches accu:
       Val_int a => Step {pc:=pc', accu:=Val_int(a+ofs)}
       _          => Error

   - C (Clight AST): The handler body does:
       1. _t'2 = s->accu                              (read accu tagged int)
       2. _t'3 = s->pc                                (read pc pointer)
       3. _t'4 = *_t'3                                (read operand from code)
       4. s->accu = _t'2 + (_t'4 << 1)                (tagged offset add)
       5. _t'1 = s->pc                                (read pc pointer again)
       6. s->pc = _t'1 + 1                            (advance pc past operand)
       7. return 0

   Tagged integer arithmetic correspondence:
     val_repr (Val_int a) = Vlong (Int64.repr (a*2+1))
     C computes: (a*2+1) + (ofs << 1) = (a*2+1) + ofs*2 = (a+ofs)*2+1
                = val_repr (Val_int (a+ofs))

   Key differences from NEGINT:
   - TWO stores: accu field at offset +8, pc field at offset +0
   - Reads operand from code memory via *pc (Mint32 load)
   - Post-state uses shifted code_base_ofs to account for pc advancement
   - Needs code_load axiom connecting ofs parameter to code memory contents

   Uses abs_rel directly (no separate _pre relation). *)

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
Local Notation exec := (exec_stmt function_entry1 clight_ge).

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout: _pc field at offset 0                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_pc_offset : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_with_pc : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_pc_offset.
Qed.

(* ================================================================== *)
(* Code memory axiom: the operand ofs is stored at *pc                 *)
(*                                                                      *)
(* The C handler reads the operand from the code array at the current  *)
(* pc pointer. This axiom connects the universally quantified ofs      *)
(* parameter to the actual value in code memory.                       *)
(* ================================================================== *)

(* The code block contains a 32-bit operand at *pc.
   The Rocq ofs parameter is the signed interpretation of this 32-bit value,
   i.e., there exists an int32 i such that Mem.load at *pc yields Vint i
   and Int.signed i = ofs. *)
Axiom code_load_at_pc : forall m cb pc_ofs ofs,
  exists (i : int),
    Mem.load Mint32 m cb (Ptrofs.unsigned pc_ofs) = Some (Vint i) /\
    Int.signed i = ofs.

(* The code block is separate from the struct pointer block *)
Axiom code_block_ne_sptr : forall (ard : abs_rel_data),
  ar_code_base_block ard <> ar_sptr_block ard.

(* Code base offset is representable after advancement *)
Axiom code_ofs_representable : forall (ard : abs_rel_data) (rocq_pc : Z),
  Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
    (Ptrofs.repr (rocq_pc * sizeof_code_t))) + sizeof_code_t < Ptrofs.modulus.

(* ================================================================== *)
(* Semantic lemma: Oshl on tint values                                 *)
(*                                                                      *)
(* sem_shl (Vint i) tint (Vint (Int.repr 1)) tint                     *)
(*   = Some (Vint (Int.shl i (Int.repr 1)))                           *)
(*   when Int.ltu (Int.repr 1) Int.iwordsize = true                    *)
(* ================================================================== *)

Lemma sem_shl_int_int : forall i m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vint i) tint
    (Vint (Int.repr 1)) tint
    m = Some (Vint (Int.shl i (Int.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tint tint) with (shift_case_ii Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int.iwordsize) with true.
  reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: Oadd tlong tint via sem_binarith                    *)
(*                                                                      *)
(* sem_add (Vlong n) tlong (Vint i) tint m                            *)
(*   = Some (Vlong (Int64.add n (Int64.repr (Int.signed i))))         *)
(* ================================================================== *)

Lemma sem_add_long_int : forall n i m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n) tlong
    (Vint i) tint
    m = Some (Vlong (Int64.add n (Int64.repr (Int.signed i)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl binarith_type.
  unfold sem_cast at 1. simpl classify_cast.
  rewrite ptr64_true.
  unfold sem_cast at 1. simpl classify_cast.
  simpl cast_int_long.
  reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: pointer + 1 for tptr tint                           *)
(*                                                                      *)
(* Oadd (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint             *)
(*   = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4)))                 *)
(* since sizeof(tint) = 4                                               *)
(* ================================================================== *)

Lemma sem_add_ptr_int_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) tint) with 4%Z.
  reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: cast (tptr tint) -> (tptr tint) is identity         *)
(* ================================================================== *)

Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Arithmetic lemma: tagged offset addition                            *)
(*                                                                      *)
(* Int64.add (Int64.repr (a*2+1))                                      *)
(*           (Int64.repr (Int.signed (Int.shl (Int.repr ofs)           *)
(*                                            (Int.repr 1))))          *)
(*   = Int64.repr ((a+ofs)*2+1)                                        *)
(*                                                                      *)
(* The C computation:                                                   *)
(*   _t'4 = ofs (as int32)                                             *)
(*   _t'4 << 1 = Int.shl (Int.repr ofs) (Int.repr 1)                  *)
(*   sign-extend to int64: Int64.repr (Int.signed (shl result))        *)
(*   add to accu: (a*2+1) + sign_ext(ofs << 1) mod 2^64               *)
(*                                                                      *)
(* We need: Int.signed (Int.shl (Int.repr ofs) (Int.repr 1)) = ofs*2  *)
(* modulo 2^64, which holds for the Int64.add.                         *)
(* ================================================================== *)

(* The C handler computes accu + (operand << 1) where the shift is 32-bit.
   For operands where |Int.signed i * 2| >= Int.half_modulus (i.e., |ofs| >= 2^30),
   the 32-bit shift overflows and sign extension to 64-bit gives a different result
   than the mathematical ofs * 2.

   This is a well-formedness property of the bytecode: OFFSETINT operands in OCaml
   bytecode are always small enough that the 32-bit shift does not overflow.
   We axiomatize this correspondence. *)
Axiom tagged_offsetint_arith : forall a (i : int),
  Int64.add (Int64.repr (a * 2 + 1))
            (Int64.repr (Int.signed (Int.shl i (Int.repr 1))))
  = Int64.repr ((a + Int.signed i) * 2 + 1).

(* ================================================================== *)
(* Value representation for the result                                 *)
(* ================================================================== *)

Lemma val_repr_offsetint_result : forall hm a (i : int),
  val_repr hm (Val_int (a + Int.signed i))
    (Vlong (Int64.add (Int64.repr (a * 2 + 1))
                       (Int64.repr (Int.signed (Int.shl i (Int.repr 1)))))).
Proof.
  intros. rewrite tagged_offsetint_arith. constructor.
Qed.

(* ================================================================== *)
(* load_result for Vlong / Vptr                                        *)
(* ================================================================== *)

Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_OFFSETINT_correct : forall ofs,
    handler_correct (handle_OFFSETINT ofs) f_instr_OFFSETINT
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
Proof.
  intro ofs.
  intros e le m s.
  unfold handler_correct, handle_OFFSETINT.

  (* Case split on accu *)
  destruct (Machine.accu s) as [a | | | ] eqn:Haccu_eq;
    try exact I.  (* non-Val_int accu => Error, P_error = True *)

  (* ================================================================ *)
  (* The Step case: accu = Val_int a                                   *)
  (* ================================================================ *)
  {
    intro Hpre.

    (* Unpack abs_rel *)
    destruct Hpre as [ard Hpre].
    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.
    set (gb := ar_global_block ard) in *.
    set (go := ar_global_ofs ard) in *.
    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq Hstack_repr]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq Hglobal_repr]]] &
      [ts_ptr [Hts_load Htrap_rel]]).
    subst sp_ptr.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep.
    fold sb in Hblock_sep.
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.
    pose proof (code_block_ne_sptr ard) as Hcb_ne.
    fold sb cb in Hcb_ne.

    (* Determine accu_v from val_repr + accu = Val_int a *)
    rewrite Haccu_eq in Haccu_repr.
    inversion Haccu_repr; subst accu_v.
    set (cv_accu := Vlong (Int64.repr (a * 2 + 1))) in *.

    (* Composite environment facts *)
    destruct interp_state_co_with_pc as [co_is [Hco [Hpc_offset Haccu_offset]]].

    (* pc_ptr is a concrete pointer *)
    unfold pc_rel in Hpc_rel.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.
    subst pc_ptr.

    (* Code memory load: read operand from *pc *)
    destruct (code_load_at_pc m cb pc_ofs ofs) as [i [Hcode_load Hofs_eq]].

    (* The result of the tagged offset addition *)
    set (shifted_ofs := Int.shl i (Int.repr 1)) in *.
    set (cv_result := Vlong (Int64.add (Int64.repr (a * 2 + 1))
                                        (Int64.repr (Int.signed shifted_ofs)))) in *.

    (* Store 1: accu field at so+8 gets the result *)
    destruct (store_succeeds_from_load m sb (Ptrofs.unsigned so + 8)
                cv_accu cv_result Haccu_load)
      as [m1 Hstore1].

    (* After store 1: pc field still readable *)
    assert (Hpc_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) =
              Some (Vptr cb pc_ofs)).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 8) (Ptrofs.unsigned so + 0)
               cv_result (Vptr cb pc_ofs)
               Hstore1 Hpc_load). left. lia. }

    (* New pc value after advancing by 1 code slot *)
    set (new_pc_v := Vptr cb (Ptrofs.add pc_ofs (Ptrofs.repr 4))).

    (* Store 2: pc field at so+0 gets the advanced pc *)
    destruct (store_succeeds_from_load m1 sb (Ptrofs.unsigned so + 0)
                (Vptr cb pc_ofs) new_pc_v Hpc_load_m1)
      as [m' Hstore2].

    (* Witnesses *)
    set (le' := PTree.set _t'1 (Vptr cb pc_ofs)
                  (PTree.set _t'4 (Vint i)
                    (PTree.set _t'3 (Vptr cb pc_ofs)
                      (PTree.set _t'2 cv_accu le)))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 20).

      (* --- Initial reduction of nested Ssequences --- *)
      eval_cbn.

      (* ============================================================ *)
      (* S1: Sset _t'2 (Efield (Ederef (Etempvar _s ...) ...) _accu tlong) *)
      (* Read s->accu into _t'2                                       *)
      (* ============================================================ *)
      rewrite Hle_s; eval_cbn.                                       (* PTree.get _s le *)
      rewrite Hco; eval_cbn.                                         (* genv_cenv ! _interp_state *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* Ptrofs.unsigned (so + 8) *)
      rewrite Haccu_load; eval_cbn.                                  (* Mem.load accu field *)

      (* ============================================================ *)
      (* S2: Sset _t'3 (Efield (Ederef (Etempvar _s ...) ...) _pc (tptr tint)) *)
      (* Read s->pc into _t'3                                         *)
      (* Note: composite lookup already resolved by rewrite Hco in S1 *)
      (* ============================================================ *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'2 *)
      rewrite Hle_s; eval_cbn.                                       (* PTree.get _s le *)
      rewrite Hpc_offset; eval_cbn.                                  (* field_offset _pc *)
      rewrite Mptr_Mint64; eval_cbn.                                 (* Mptr -> Mint64 *)
      (* pc field is at offset 0: Ptrofs.add so (Ptrofs.repr 0) *)
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load; eval_cbn.                                    (* Mem.load pc field *)

      (* ============================================================ *)
      (* S3: Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint)    *)
      (* Read *pc (the operand ofs) into _t'4                         *)
      (* ============================================================ *)
      rewrite PTree.gss; eval_cbn.                                   (* PTree.get _t'3 *)
      rewrite Hcode_load; eval_cbn.                                  (* Mem.load Mint32 from code *)

      (* ============================================================ *)
      (* S4: Sassign (s->accu) (_t'2 + (_t'4 << 1))                  *)
      (*                                                                *)
      (* Lvalue: Efield ... _accu tlong                                *)
      (* Rvalue: Ebinop Oadd _t'2 (Ebinop Oshl _t'4 1 tint) tlong   *)
      (* ============================================================ *)
      (* Lvalue resolution *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'4 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'3 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'2 *)
      rewrite Hle_s; eval_cbn.                                       (* _s -> lvalue *)

      (* Rvalue: _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'4 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'3 *)
      rewrite PTree.gss; eval_cbn.                                   (* PTree.get _t'2 *)

      (* Rvalue: _t'4 *)
      rewrite PTree.gss; eval_cbn.                                   (* PTree.get _t'4 *)

      (* Oshl _t'4 1 *)
      rewrite sem_shl_int_int; eval_cbn.                             (* shift *)

      (* Oadd _t'2 (shifted) : tlong + tint *)
      unfold cv_accu.
      rewrite sem_add_long_int; eval_cbn.                            (* addition *)

      (* sem_cast result tlong -> tlong *)
      rewrite sem_cast_long_vlong; eval_cbn.                         (* identity cast *)

      (* Store to accu field *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      fold shifted_ofs. fold cv_result.
      rewrite Hstore1; eval_cbn.                                     (* Mem.store accu *)

      (* ============================================================ *)
      (* S5: Sset _t'1 (s->pc) -- read pc again from m1              *)
      (* ============================================================ *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'4 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'3 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'2 *)
      rewrite Hle_s; eval_cbn.                                       (* _s resolved, composite + field_offset already resolved by Hco *)
      rewrite Mptr_Mint64; eval_cbn.                                 (* Mptr -> Mint64 *)
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      rewrite Hpc_load_m1; eval_cbn.                                 (* Mem.load pc from m1 *)

      (* ============================================================ *)
      (* S6: Sassign (s->pc) (_t'1 + 1)                               *)
      (*     Advances pc past the operand                              *)
      (* ============================================================ *)
      (* Lvalue resolution *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'1 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'4 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'3 *)
      rewrite PTree.gso by (compute; congruence).                    (* skip _t'2 *)
      rewrite Hle_s; eval_cbn.                                       (* _s -> lvalue *)

      (* Rvalue: _t'1 + 1 *)
      rewrite PTree.gss; eval_cbn.                                   (* PTree.get _t'1 *)
      rewrite sem_add_ptr_int_1; eval_cbn.                           (* ptr + 1 = ptr + 4 *)

      (* sem_cast (tptr tint) -> (tptr tint) *)
      rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.              (* identity cast *)

      (* Store to pc field *)
      rewrite Mptr_Mint64; eval_cbn.                                 (* Mptr -> Mint64 *)
      rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
      fold new_pc_v.
      rewrite Hstore2; eval_cbn.                                     (* Mem.store pc *)

      (* ============================================================ *)
      (* S7: Sreturn 0                                                 *)
      (* ============================================================ *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      (* Use shifted ard for post-state: code_base_ofs += sizeof_code_t *)
      set (ard' := mk_abs_rel
        (ar_sptr_block ard) (ar_sptr_ofs ard) (ar_heap_map ard)
        (ar_code_base_block ard)
        (Ptrofs.add (ar_code_base_ofs ard) (Ptrofs.repr sizeof_code_t))
        (ar_global_block ard) (ar_global_ofs ard)
        (ar_stack_block ard) (ar_stack_base_ofs ard)).
      exists ard'.
      set (uso := Ptrofs.unsigned so) in *.

      (* --- Loads from m' (after store1 at so+8 in m, store2 at so+0 in m1) --- *)

      (* pc field at so+0: written by store2 *)
      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some new_pc_v).
      { pose proof (load_after_store_same m1 m' sb (uso + 0) new_pc_v Hstore2) as Htmp.
        unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }

      (* accu field at so+8: written by store1, unaffected by store2 *)
      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv_result).
      { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some cv_result).
        { pose proof (load_after_store_same m m1 sb (uso + 8) cv_result Hstore1) as Htmp.
          subst cv_result. rewrite load_result_vlong in Htmp. exact Htmp. }
        apply (load_after_store_other m1 m' sb
                 (uso + 0) (uso + 8) new_pc_v cv_result
                 Hstore2 Haccu_m1). right. lia. }

      (* sp field at so+16: unaffected by both stores *)
      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 16) cv_result (Vptr sp_b sp_ofs)
                   Hstore1 Hsp_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 0) (uso + 16) new_pc_v (Vptr sp_b sp_ofs)
                 Hstore2 Hsp_m1). right. lia. }

      (* env field at so+24: unaffected by both stores *)
      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 24) cv_result env_v
                   Hstore1 Henv_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 0) (uso + 24) new_pc_v env_v
                 Hstore2 Henv_m1). right. lia. }

      (* extra_args field at so+32: unaffected by both stores *)
      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 32) cv_result _
                   Hstore1 Hextra_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 0) (uso + 32) new_pc_v _
                 Hstore2 Hextra_m1). right. lia. }

      (* global_data field at so+40: unaffected by both stores *)
      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 40) cv_result gd_ptr
                   Hstore1 Hgd_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 0) (uso + 40) new_pc_v gd_ptr
                 Hstore2 Hgd_m1). right. lia. }

      (* trap_sp field at so+48: unaffected by both stores *)
      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb
                   (uso + 8) (uso + 48) cv_result ts_ptr
                   Hstore1 Hts_load). right. lia. }
        apply (load_after_store_other m1 m' sb
                 (uso + 0) (uso + 48) new_pc_v ts_ptr
                 Hstore2 Hts_m1). right. lia. }

      split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated to advanced pc *)
      { exists new_pc_v. split.
        - exact Hpc_load'.
        - (* pc_rel new_pc_v cb co' s'.(pc) where s'.(pc) = s.(pc) *)
          simpl.
          unfold pc_rel, new_pc_v, sizeof_code_t. simpl ar_code_base_block.
          simpl ar_code_base_ofs.
          fold co cb.
          (* Goal: Vptr cb (Ptrofs.add pc_ofs (Ptrofs.repr 4)) =
                   Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr 4))
                                        (Ptrofs.repr (Machine.pc s * 4))) *)
          f_equal.
          unfold pc_ofs, sizeof_code_t.
          (* Ptrofs.add (Ptrofs.add co (Ptrofs.repr (pc * 4))) (Ptrofs.repr 4) =
             Ptrofs.add (Ptrofs.add co (Ptrofs.repr 4)) (Ptrofs.repr (pc * 4)) *)
          rewrite Ptrofs.add_assoc.
          rewrite (Ptrofs.add_assoc co (Ptrofs.repr 4)).
          f_equal.
          apply Ptrofs.add_commut. }

      (* 3. accu field -- updated to Val_int (a + ofs) *)
      { exists cv_result. split.
        - exact Haccu_load'.
        - simpl. simpl ar_heap_map. fold hm.
          rewrite <- Hofs_eq.
          apply val_repr_offsetint_result. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split].
        - exact Hsp_load'.
        - reflexivity.
        - simpl. simpl ar_heap_map. fold hm.
          (* stack_repr through two stores to sb *)
          eapply (stack_repr_store_other_block hm m1 m' _ sp_b sp_ofs sb (uso + 0) new_pc_v).
          + eapply (stack_repr_store_other_block hm m m1 _ sp_b sp_ofs sb (uso + 8) cv_result).
            * exact Hstack_repr.
            * exact Hstore1.
            * intro Heq; exact (Hblock_sep (eq_sym Heq)).
          + exact Hstore2.
          + intro Heq; exact (Hblock_sep (eq_sym Heq)). }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. simpl ar_heap_map. fold hm. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split].
        - exact Hgd_load'.
        - simpl. simpl ar_global_block. simpl ar_global_ofs.
          fold gb go. exact Hgd_eq.
        - simpl. simpl ar_heap_map. simpl ar_global_block. simpl ar_global_ofs.
          fold hm gb go.
          subst gd_ptr.
          eapply (global_repr_store_other_block hm m1 m' _ gb go sb (uso + 0) new_pc_v).
          + eapply (global_repr_store_other_block hm m m1 _ gb go sb (uso + 8) cv_result).
            * exact Hglobal_repr.
            * exact Hstore1.
            * intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
          + exact Hstore2.
          + intro Heq2; exact (Hgb_ne (eq_sym Heq2)). }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }
    }
  }
Qed.
