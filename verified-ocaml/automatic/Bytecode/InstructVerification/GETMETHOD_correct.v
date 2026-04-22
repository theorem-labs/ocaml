(* GETMETHOD_correct.v -- GETMETHOD correctness proof.

   GETMETHOD: accu is the method index (tagged integer), stack top
   is the object.  Load the object's class table (field 0 of the
   object), then index into the class table at position (accu >> 1)
   to get the method closure.

   Rocq handler (Interpret.v):
     handle_GETMETHOD pc' s =
       match s.(stack) with
       | obj :: _ =>
         match field_or_heap s obj 0 with
         | Some class_tbl =>
           match s.(accu) with
           | Val_int n =>
             match field_or_heap s class_tbl (Z.to_nat n) with
             | Some method_fn => Step (s <|pc:=pc'|> <|accu:=method_fn|>)
             | None => Error "GETMETHOD: method not found"
             end
           | _ => Error "GETMETHOD: not an integer index"
           end
         | None => Error "GETMETHOD: no class table"
         end
       | _ => Error "GETMETHOD: stack underflow"
       end

   C handler (instruct_handlers.v, f_instr_GETMETHOD):
     t1 = s->sp
     t2 = deref(cast(t1) + 0)            sp[0] = object
     t3 = deref(cast(t2) + 0)            object[0] = class table pointer
     t4 = s->accu                         load accu (tagged method index)
     t5 = deref(cast(t3) + (t4 shr 1))   class_table[accu shr 1] = method
     s->accu = t5                         store method to accu
     return 0

   One store: accu field.
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
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        Ptrofs.of_int64
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr               *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: shr (Vlong n) (Vint 1) for tlong -> tlong         *)
(* ================================================================== *)

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Semantic lemma: cast tlong -> tlong for Vlong                      *)
(* ================================================================== *)

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic lemma: (tptr tlong) + (tlong) idx                         *)
(* ================================================================== *)

Local Lemma sem_add_ptr_tlong_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong idx) tlong m
  = Some (Vptr b (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 8)
                        (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

(* ================================================================== *)
(* Arithmetic: shr of tagged integer                                   *)
(* ================================================================== *)

Local Lemma shr_tagged_int : forall idx,
  0 <= idx ->
  idx * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx.
Proof.
  intros idx Hge Hlt.
  unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Int64.signed_repr.
  2: { split.
       - pose proof Int64.min_signed_neg. lia.
       - exact Hlt. }
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^1)%Z with 2%Z.
  rewrite Z.div_add_l by lia.
  change (1 / 2)%Z with 0%Z.
  f_equal. lia.
Qed.

Local Lemma ptrofs_mul_8_of_int64 : forall idx,
  0 <= idx ->
  idx < Ptrofs.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
  = Ptrofs.repr (idx * 8).
Proof.
  intros idx Hge Hlt.
  assert (Hhm8 : (Ptrofs.half_modulus >= 8)%Z) by (vm_compute; discriminate).
  pose proof Ptrofs.half_modulus_modulus.
  unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr.
  2: { change Int64.max_unsigned with Ptrofs.max_unsigned.
       unfold Ptrofs.max_unsigned. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { unfold Ptrofs.max_unsigned. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { unfold Ptrofs.max_unsigned. lia. }
  f_equal. lia.
Qed.

(* ================================================================== *)
(* Heap precondition for GETMETHOD                                     *)
(*                                                                      *)
(* When field_or_heap chains succeed:                                   *)
(* 1. sp[0] (the object) dereferences to Vptr obj_b obj_ofs            *)
(* 2. obj[0] (class table) loads from obj_b at obj_ofs                  *)
(* 3. class_table[n] loads the method                                   *)
(* ================================================================== *)

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

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_GETMETHOD_correct :
    handler_correct handle_GETMETHOD f_instr_GETMETHOD
      (fun _ m s ard =>
         getmethod_heap_pre m s ard /\
         match s.(Machine.accu) with
         | Val_int n => 0 <= n /\
                        n * 2 + 1 <= Int64.max_signed /\
                        n < Ptrofs.half_modulus /\
                        (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int n) cv -> exists z, cv = Vlong z)
         | _ => True
         end)
      (fun msg _ => msg = "GETMETHOD: stack underflow"%string \/
        msg = "GETMETHOD: no class table"%string \/
        msg = "GETMETHOD: not an integer index"%string \/
        msg = "GETMETHOD: method not found"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_GETMETHOD.

  (* Case split on stack *)
  destruct (Machine.stack s) as [| obj stk_tl] eqn:Hstk.
  { (* stack = nil => Error *) left; reflexivity. }

  (* stack = obj :: stk_tl *)
  destruct (field_or_heap s obj 0) as [class_tbl|] eqn:Hclass.
  2: { (* field_or_heap = None => Error *) right; left; reflexivity. }

  (* field_or_heap obj 0 = Some class_tbl *)
  destruct (Machine.accu s) as [n | | |] eqn:Haccu_eq.

  2-4: right; right; left; reflexivity.

  (* accu = Val_int n *)
  destruct (field_or_heap s class_tbl (Z.to_nat n)) as [method_fn|] eqn:Hmethod.
  2: { (* method not found => Error *) right; right; right; reflexivity. }

  (* ================================================================ *)
  (* Step case: all lookups succeeded                                  *)
  (* ================================================================ *)
  {
    intros ard Hpre [Hhfl Hidx_bounds].

    destruct Hidx_bounds as [Hidx_ge [Hidx_signed [Hidx_ptrofs Haccu_tagged]]].

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
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (global_block_ne_sptr ard) as Hgb_ne.
    fold sb in Hgb_ne.

    (* Extract stack head from stack_repr *)
    rewrite Hstk in Hstack_repr.
    inversion Hstack_repr as [| ? ? ? ? cv_obj Hload_sp0 Hval_repr_obj Hstack_repr_rest].

    (* Use heap precondition *)
    unfold getmethod_heap_pre in Hhfl.
    destruct (Hhfl obj stk_tl class_tbl n method_fn Hstk Hclass Haccu_eq Hmethod cv_obj Hval_repr_obj)
      as (obj_b & obj_ofs & ct_v & ct_b & ct_ofs & meth_v &
          Hobj_is_ptr & Hobj_load & Hct_repr & Hct_is_ptr & Hmeth_load & Hmeth_repr).
    subst cv_obj ct_v.

    (* Accu representation *)
    pose proof Haccu_repr as Haccu_repr'.
    rewrite Haccu_eq in Haccu_repr.
    inversion Haccu_repr; subst accu_v.
    2: { exfalso. rewrite Haccu_eq in Haccu_repr'.
         destruct (Haccu_tagged _ Haccu_repr') as [z Hz]. discriminate Hz. }
    rename H0 into Haccu_is_int.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* Arithmetic facts *)
    assert (Hshr_n : Int64.shr (Int64.repr (n * 2 + 1)) (Int64.repr 1) = Int64.repr n).
    { apply shr_tagged_int; assumption. }
    assert (Hptrofs_mul : Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr n))
                          = Ptrofs.repr (n * 8)).
    { apply ptrofs_mul_8_of_int64; assumption. }

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 (Vlong (Int64.repr (n * 2 + 1))) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) meth_v) as [m' Hstore].

    (* Witnesses *)
    set (le' := PTree.set _t'5 meth_v
                  (PTree.set _t'4 (Vlong (Int64.repr (n * 2 + 1)))
                    (PTree.set _t'3 (Vptr ct_b ct_ofs)
                      (PTree.set _t'2 (Vptr obj_b obj_ofs)
                        (PTree.set _t'1 (Vptr sp_b sp_ofs) le))))).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 15).
      eval_cbn.

      (* S1: Sset _t'1 (s->sp) -- load sp from struct *)
      rewrite Hle_s; eval_cbn.
      rewrite Hco; eval_cbn.
      rewrite Hsp_offset; eval_cbn.
      rewrite Mptr_Mint64; eval_cbn.
      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
      rewrite Hsp_load; eval_cbn.

      (* S2: Sset _t'2 (deref (t1 + 0)) -- load sp[0] = object *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_add_sp_0 sp_b sp_ofs m); eval_cbn.
      rewrite Hload_sp0; eval_cbn.

      (* S3: Sset _t'3 (deref (cast(t2) + 0)) -- load object[0] = class table *)
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_to_ptr_vptr obj_b obj_ofs m); eval_cbn.
      rewrite (sem_add_sp_0 obj_b obj_ofs m); eval_cbn.
      rewrite Hobj_load; eval_cbn.

      (* S4: Sset _t'4 (s->accu) -- load accu *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gso by (compute; congruence).
      rewrite Hle_s; eval_cbn.
      rewrite Haccu_offset; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite Haccu_load; eval_cbn.

      (* S5: Sset _t'5 (deref (cast(t3) + (cast(t4) >> 1))) *)
      (* Read _t'3 = class table ptr: skip _t'4, hit _t'3 *)
      rewrite PTree.gso by (compute; congruence).
      rewrite PTree.gss; eval_cbn.
      (* Cast class table tlong -> tptr tlong *)
      rewrite (sem_cast_long_to_ptr_vptr ct_b ct_ofs m); eval_cbn.
      (* Read _t'4 = tagged index: _t'4 is at top of PTree *)
      rewrite PTree.gss; eval_cbn.
      (* Cast tlong -> tlong *)
      rewrite (sem_cast_tlong_tlong_vlong (Int64.repr (n * 2 + 1)) m); eval_cbn.
      (* shr by 1: untag *)
      rewrite (sem_shr_long_int_1 (Int64.repr (n * 2 + 1)) m); eval_cbn.
      rewrite Hshr_n.
      (* ptr + shifted index *)
      rewrite (sem_add_ptr_tlong_idx ct_b ct_ofs (Int64.repr n) m); eval_cbn.
      rewrite Hptrofs_mul.
      (* Deref: load method from class table *)
      rewrite Hmeth_load; eval_cbn.

      (* S6: Sassign (s->accu = _t'5) -- store method to accu *)
      repeat (rewrite PTree.gso by (compute; congruence)).
      rewrite Hle_s; eval_cbn.
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
      rewrite PTree.gss; eval_cbn.
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hmeth_repr); eval_cbn.
      rewrite Hstore; eval_cbn.

      (* S7: Sreturn 0 *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) meth_v pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) meth_v (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) meth_v env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) meth_v _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) meth_v gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) meth_v ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some meth_v).
      { pose proof (load_after_store_same m m' sb (uso + 8) meth_v Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co method_fn meth_v Hmeth_repr) in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to method *)
      { exists meth_v. split.
        - exact Haccu_load'.
        - simpl. exact Hmeth_repr. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl. rewrite Hstk.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) meth_v
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
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) meth_v
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
   handle_instr GETMETHOD / clight_of GETMETHOD / pre_of GETMETHOD are
   convertible with handle_GETMETHOD / f_instr_GETMETHOD / getmethod_step_pre.
   P_halt_of and P_ccall_of are vacuously satisfied (GETMETHOD never halts or
   issues a C call).  P_error_of requires bridging from the disjunction in the
   old proof to `error_message_of GETMETHOD s = Some msg`. *)
Definition correct_GETMETHOD :
    handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
      (pre_of GETMETHOD)
      (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).
Proof.
  intros e le m s.
  change (handle_instr GETMETHOD (Machine.pc s) s)
    with (handle_GETMETHOD (Machine.pc s) s).
  unfold handle_GETMETHOD at 1.
  (* Case split on stack *)
  destruct (Machine.stack s) as [| obj stk_tl] eqn:Hstk.
  { (* stack = nil => Error "GETMETHOD: stack underflow" *)
    unfold P_error_of. simpl. rewrite Hstk. reflexivity. }
  (* stack = obj :: stk_tl *)
  destruct (field_or_heap s obj 0) as [class_tbl|] eqn:Hclass.
  2: { (* field_or_heap = None => Error "GETMETHOD: no class table" *)
    unfold P_error_of. simpl. rewrite Hstk. rewrite Hclass. reflexivity. }
  (* field_or_heap obj 0 = Some class_tbl *)
  destruct (Machine.accu s) as [n | | |] eqn:Haccu_eq.
  - (* Val_int n *)
    destruct (field_or_heap s class_tbl (Z.to_nat n)) as [method_fn|] eqn:Hmethod.
    + (* Step case: all lookups succeeded — delegate to verify_GETMETHOD_correct *)
      intros ard Habs Hpre.
      specialize (verify_GETMETHOD_correct e le m s) as Hold.
      unfold handler_correct, handle_GETMETHOD in Hold.
      rewrite Hstk in Hold. rewrite Hclass in Hold.
      rewrite Haccu_eq in Hold. rewrite Hmethod in Hold.
      specialize (Hold ard Habs).
      apply Hold.
      unfold pre_of, getmethod_step_pre in Hpre.
      rewrite Haccu_eq in Hpre. exact Hpre.
    + (* method not found => Error *)
      unfold P_error_of. simpl. rewrite Hstk. rewrite Hclass.
      rewrite Haccu_eq. rewrite Hmethod. reflexivity.
  - (* Val_block: Error "GETMETHOD: not an integer index" *)
    unfold P_error_of. simpl. rewrite Hstk. rewrite Hclass.
    rewrite Haccu_eq. reflexivity.
  - (* Val_ptr: Error "GETMETHOD: not an integer index" *)
    unfold P_error_of. simpl. rewrite Hstk. rewrite Hclass.
    rewrite Haccu_eq. reflexivity.
  - (* Val_closure: Error "GETMETHOD: not an integer index" *)
    unfold P_error_of. simpl. rewrite Hstk. rewrite Hclass.
    rewrite Haccu_eq. reflexivity.
Qed.
