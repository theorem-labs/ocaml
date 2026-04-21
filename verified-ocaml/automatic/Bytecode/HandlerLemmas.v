(* HandlerLemmas.v -- Proves (or keeps as Axiom) the axioms from
   ACC0_bigstep_compl_allresults.v using CompCert's memory model.

   Status summary:
   - PROVED: ptr64_true, load_after_store_same, load_after_store_other,
     stack_repr_store_other_block, global_repr_store_other_block,
     val_repr_load_result, sem_cast_long_vlong, sem_cast_long_vptr,
     sem_cast_long_val_repr, sem_add_sp_0, Mptr_Mint64,
     ptrofs_add_unsigned, interp_state_co, ptrofs_mul_8_1,
     sem_sub_sp_1, sem_cast_ptr_to_ptr
   - PROVED (from abs_rel_data record fields):
     global_block_ne_sptr, sptr_ofs_representable
   - PROVED (induction on stack_repr):
     stack_repr_store_same_block_lower, stack_repr_cons_after_store
   - PROVED (from abs_rel range_perm):
     store_succeeds_sb, sb_writable_after_store, store_to_sp_after_sb_store
   - DELETED: store_succeeds_from_load, store_to_other_block,
     store_succeeds_stack (all replaced by proved lemmas or unused)
   - DELETED (redundant with abs_rel sp_ofs >= 8 / sp_rep):
     sp_ofs_ge_8, sp_ofs_stack_representable
   - REMOVED: sem_cast_long (provably FALSE for Vundef/Vfloat/Vsingle/Vint;
     use sem_cast_long_val_repr instead) *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.

(* ================================================================== *)
(* Architecture — provable for x86-64 CompCert                         *)
(* ================================================================== *)

(* Archi.ptr64 is defined as [true] in compcert/x86_64/Archi.v and
   then declared [Global Opaque].  Despite the opacity barrier, Rocq's
   kernel can still see through to the definition body, so plain
   [reflexivity] closes the goal.  No axiom required. *)
Lemma ptr64_true : Archi.ptr64 = true.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Struct layout — derivable from the clightgen output                 *)
(* ================================================================== *)

(* The composite environment contains an entry for _interp_state with
   the expected field offsets.

   PERFORMANCE: We factor the proof through [ce], a local alias for the
   composite env built directly from [composites] (1 struct entry).
   Plain [reflexivity] uses the kernel's lazy reduction to check the
   equalities without expanding [global_definitions] (~9000 lines).
   A direct [vm_compute; reflexivity] on [genv_cenv clight_ge] forces
   expansion of the full program AST and takes 50+ minutes in dune's
   rocqworker; this factored approach takes < 1 second. *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_facts : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_facts.
Qed.

Local Lemma ce_facts_env : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Lemma interp_state_co_env : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full).
Proof.
  rewrite cenv_is_ce. exact ce_facts_env.
Qed.

(* ================================================================== *)
(* Memory separation — structural invariants (must stay axiomatic)     *)
(* ================================================================== *)

(* Block separation invariants are now carried in abs_rel_data
   (code block separation, global block separation, sptr offset bound)
   and in abs_rel conjuncts (sp/global block separation from sptr).

   global_block_ne_sptr and sptr_ofs_representable are proved lemmas
   (extracting from record fields).

   sp_block_ne_sptr and sp_block_ne_global have been DELETED
   (they were FALSE — universally quantified over all blocks).
   Handler proofs now use Hsp_ne_sb/Hsp_ne_gb from abs_rel destruct. *)

(* The global data block is separate from the struct pointer block. *)
Lemma global_block_ne_sptr : forall (ard : abs_rel_data),
  ar_global_block ard <> ar_sptr_block ard.
Proof. intros. exact (ar_global_ne_sptr ard). Qed.

(* The struct pointer offset is in representable range.
   Now proved from the ar_sptr_ofs_bound record field. *)
Lemma sptr_ofs_representable : forall (ard : abs_rel_data),
  Ptrofs.unsigned (ar_sptr_ofs ard) + 56 < Ptrofs.modulus.
Proof.
  intros. exact (ar_sptr_ofs_bound ard).
Qed.

(* ================================================================== *)
(* Code block separation — proved from abs_rel_data record fields      *)
(* ================================================================== *)

(* The code base block is separate from the struct pointer block.
   Proved from the ar_code_ne_sptr record field. *)
Lemma code_block_ne_sptr : forall (ard : abs_rel_data),
  ar_code_base_block ard <> ar_sptr_block ard.
Proof.
  intros. exact (ar_code_ne_sptr ard).
Qed.

(* The code base block is separate from the global data block.
   Proved from the ar_code_ne_global record field. *)
Lemma code_block_ne_global : forall (ard : abs_rel_data),
  ar_code_base_block ard <> ar_global_block ard.
Proof.
  intros. exact (ar_code_ne_global ard).
Qed.

(* store_to_sp_after_sb_store: After storing to the struct block sb,
   we can store to the stack block sp_b.  Uses Mem.perm_store_1 to
   thread Writable through the sb store, plus explicit alignment.
   Replaces the former axiom store_to_other_block. *)
Lemma store_to_sp_after_sb_store :
  forall m m' sb ofs_sb v sp_b sp_bound new_ofs,
  Mem.store Mint64 m sb ofs_sb v = Some m' ->
  Mem.range_perm m sp_b 0 sp_bound Cur Writable ->
  0 <= new_ofs -> new_ofs + 8 <= sp_bound ->
  (align_chunk Mint64 | new_ofs) ->
  forall cv_new, exists m'', Mem.store Mint64 m' sp_b new_ofs cv_new = Some m''.
Proof.
  intros m m' sb ofs_sb v sp_b sp_bound new_ofs
    Hstore Hsp_writable Hlo Hhi Halign cv_new.
  destruct (Mem.valid_access_store m' Mint64 sp_b new_ofs cv_new) as [m'' Hst].
  { split.
    - intros ofs' Hofs'.
      eapply Mem.perm_store_1. exact Hstore.
      apply Hsp_writable. unfold size_chunk in Hofs'. lia.
    - exact Halign. }
  exists m''. exact Hst.
Qed.

(* sp_ofs_aligned: stack offsets from stack_repr are 8-aligned,
   since Mem.load Mint64 succeeds only at aligned addresses. *)
Lemma sp_ofs_aligned : forall hm cb co m v vs sp_b sp_ofs,
  stack_repr hm cb co m (v :: vs) sp_b sp_ofs ->
  (align_chunk Mint64 | Ptrofs.unsigned sp_ofs).
Proof.
  intros hm cb co m v vs sp_b sp_ofs Hsr.
  inversion Hsr as [| ? ? ? ? cv Hload Hvr Htail].
  exact (proj2 (Mem.load_valid_access _ _ _ _ _ Hload)).
Qed.

(* ================================================================== *)
(* Memory operations — provable from CompCert                          *)
(* ================================================================== *)

Lemma load_after_store_same : forall m m' b ofs v,
  Mem.store Mint64 m b ofs v = Some m' ->
  Mem.load Mint64 m' b ofs = Some (Val.load_result Mint64 v).
Proof.
  intros. eapply Mem.load_store_same; eauto.
Qed.

Lemma load_after_store_other : forall m m' b ofs_store ofs_load v val0,
  Mem.store Mint64 m b ofs_store v = Some m' ->
  Mem.load Mint64 m b ofs_load = Some val0 ->
  (ofs_load + 8 <= ofs_store \/ ofs_store + 8 <= ofs_load) ->
  Mem.load Mint64 m' b ofs_load = Some val0.
Proof.
  intros m m' b ofs_store ofs_load v val0 Hstore Hload Hsep.
  erewrite Mem.load_store_other; eauto.
Qed.

(* store_succeeds_sb: Storing to the struct pointer block at any field
   offset succeeds, given Writable range_perm on the struct and an
   existing load (for alignment).  Replaces the former axiom
   store_succeeds_from_load. *)
Lemma store_succeeds_sb : forall m sb so ofs v,
  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable ->
  Mem.load Mint64 m sb (Ptrofs.unsigned so + ofs) = Some v ->
  0 <= ofs -> ofs + 8 <= 56 ->
  forall v_new, exists m', Mem.store Mint64 m sb (Ptrofs.unsigned so + ofs) v_new = Some m'.
Proof.
  intros m sb so ofs v Hrp Hload Hlo Hhi v_new.
  destruct (Mem.valid_access_store m Mint64 sb (Ptrofs.unsigned so + ofs) v_new) as [m' Hst].
  { pose proof (Mem.load_valid_access _ _ _ _ _ Hload) as [Hrp' Halign].
    split.
    - intros ofs' Hofs'. apply Hrp. unfold size_chunk in Hofs'. lia.
    - exact Halign. }
  exists m'. exact Hst.
Qed.

(* sb_writable_after_store: range_perm on sb is preserved through any
   Mem.store operation (via Mem.perm_store_1). *)
Lemma sb_writable_after_store : forall m m' sb so b ofs chunk v,
  Mem.store chunk m b ofs v = Some m' ->
  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable ->
  Mem.range_perm m' sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable.
Proof.
  intros m m' sb so b ofs chunk v Hstore Hrp ofs' Hofs'.
  eapply Mem.perm_store_1; eauto.
Qed.

(* ================================================================== *)
(* Representation preservation under store to other block              *)
(* ================================================================== *)

Lemma stack_repr_store_other_block : forall hm cb co m m' stk sp_b sp_ofs sb ofs v,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  Mem.store Mint64 m sb ofs v = Some m' ->
  sb <> sp_b ->
  stack_repr hm cb co m' stk sp_b sp_ofs.
Proof.
  intros hm cb co m m' stk. revert m m'.
  induction stk as [| hd tl IH]; intros m m' sp_b sp_ofs sb ofs v Hsr Hstore Hne.
  - constructor.
  - inversion Hsr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
Qed.

Lemma global_repr_store_other_block : forall hm cb co m m' gs gb gofs sb ofs v,
  global_repr hm cb co m gs gb gofs ->
  Mem.store Mint64 m sb ofs v = Some m' ->
  sb <> gb ->
  global_repr hm cb co m' gs gb gofs.
Proof.
  intros hm cb co m m' gs. revert m m'.
  induction gs as [| hd tl IH]; intros m m' gb gofs sb ofs v Hgr Hstore Hne.
  - constructor.
  - inversion Hgr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
Qed.

(* store_succeeds_stack: DELETED — 0 references across the codebase. *)

(* sp_ofs_ge_8: DELETED — redundant with abs_rel_with_ard's Hsp_ge8. *)
(* sp_ofs_stack_representable: DELETED — redundant with abs_rel_with_ard's Hsp_rep. *)

(* ================================================================== *)
(* Value representation                                                *)
(* ================================================================== *)

Lemma val_repr_load_result : forall hm cb co v cv,
  val_repr hm cb co v cv ->
  Val.load_result Mint64 cv = cv.
Proof.
  intros hm cb co v cv Hvr. inversion Hvr; subst; simpl.
  - (* vr_int: Vlong *) reflexivity.
  - (* vr_ptr: Vptr — needs ptr64 *)
    rewrite ptr64_true. reflexivity.
  - (* vr_closure: Vptr *) rewrite ptr64_true. reflexivity.
  - (* vr_block_atom: Vlong *) reflexivity.
  - (* vr_code_ptr: Vptr *) rewrite ptr64_true. reflexivity.
Qed.

(* ================================================================== *)
(* Semantic operations — depend on ptr64                               *)
(* ================================================================== *)

(* The general statement "forall v" is false — sem_cast returns None
   for Vundef, Vfloat, Vsingle, and Vint when the cast classification
   is cast_case_pointer (which is the case for tlong->tlong on x86-64).
   These specialized versions cover what's actually needed in proofs. *)
Lemma sem_cast_long_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

Lemma sem_cast_long_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong tlong m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* Restricted form covering all values produced by val_repr.
   val_repr only constructs Vlong and Vptr, both of which satisfy
   sem_cast _ tlong tlong = Some _.  This is the correct lemma to use
   in proof contexts where the cast value comes from val_repr.

   The general statement "forall v, sem_cast v tlong tlong m = Some v"
   is provably FALSE: sem_cast returns None for Vundef, Vfloat,
   Vsingle, and Vint when ptr64 = true (cast_case_pointer path).
   ACC0_bigstep_compl_allresults.v uses it at a point where the value
   satisfies val_repr, so this proved lemma is a sound replacement. *)
Lemma sem_cast_long_val_repr : forall hm cb co v cv m,
  val_repr hm cb co v cv ->
  sem_cast cv tlong tlong m = Some cv.
Proof.
  intros hm cb co v cv m Hvr. inversion Hvr; subst.
  - (* vr_int: Vlong *) apply sem_cast_long_vlong.
  - (* vr_ptr: Vptr *) apply sem_cast_long_vptr.
  - (* vr_closure: Vptr *) apply sem_cast_long_vptr.
  - (* vr_block_atom: Vlong *) apply sem_cast_long_vlong.
  - (* vr_code_ptr: Vptr *) apply sem_cast_long_vptr.
Qed.

Lemma sem_add_sp_0 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 0)) tint
    m = Some (Vptr sp_b sp_ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. f_equal. f_equal.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer subtraction                                                 *)
(* ================================================================== *)

Lemma ptrofs_mul_8_1 :
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr 1)) = Ptrofs.repr 8.
Proof.
  change (Ptrofs.of_ints (Int.repr 1)) with (Ptrofs.repr 1).
  change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_one. reflexivity.
Qed.

Lemma sem_sub_sp_1 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8))).
Proof.
  intros.
  unfold sem_binary_operation, sem_sub.
  change (classify_sub (tptr tlong) tint) with (sub_case_pi tlong Signed).
  cbv beta iota.
  change (sizeof (genv_cenv clight_ge) tlong) with 8%Z.
  unfold ptrofs_of_int.
  rewrite ptrofs_mul_8_1.
  reflexivity.
Qed.

(* ================================================================== *)
(* Cast: (tptr tlong) -> (tptr tlong) is identity for Vptr             *)
(* ================================================================== *)

Lemma sem_cast_ptr_to_ptr : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tlong) (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  reflexivity.
Qed.

(* ================================================================== *)
(* Helper lemmas                                                       *)
(* ================================================================== *)

Lemma Mptr_Mint64 : Mptr = Mint64.
Proof. unfold Mptr. rewrite ptr64_true. reflexivity. Qed.

Lemma ptrofs_add_unsigned : forall base delta,
  0 <= delta ->
  Ptrofs.unsigned base + delta < Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr delta)) =
    Ptrofs.unsigned base + delta.
Proof.
  intros. unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr delta).
  2: { pose proof (Ptrofs.unsigned_range base). unfold Ptrofs.max_unsigned. lia. }
  apply Ptrofs.unsigned_repr.
  pose proof (Ptrofs.unsigned_range base). unfold Ptrofs.max_unsigned. lia.
Qed.

(* ================================================================== *)
(* Representation preservation under store to same block               *)
(* ================================================================== *)

(* After storing to the stack block at a LOWER offset, the existing
   stack_repr (which starts at a HIGHER offset) is preserved.
   This is needed when PUSH decrements sp and stores there: the old
   stack_repr at the old sp is unaffected because the store is at
   old_sp - 8, which does not overlap old_sp, old_sp + 8, ... *)
Lemma stack_repr_store_same_block_lower : forall hm cb co m m' stk sp_b sp_ofs ofs v,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  Mem.store Mint64 m sp_b ofs v = Some m' ->
  ofs + 8 <= Ptrofs.unsigned sp_ofs ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus ->
  stack_repr hm cb co m' stk sp_b sp_ofs.
Proof.
  intros hm cb co m m' stk. revert m m'.
  induction stk as [| hd tl IH]; intros m m' sp_b sp_ofs ofs v Hsr Hstore Hle Hrep.
  - constructor.
  - inversion Hsr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
      * rewrite ptrofs_add_unsigned; [lia | lia | simpl length in Hrep; lia].
      * rewrite ptrofs_add_unsigned; [| lia | simpl length in Hrep; lia].
        simpl length in Hrep. lia.
Qed.

(* stack_repr for a newly pushed value: after storing cv at
   (sp_b, new_sp_unsigned) where val_repr hm v cv, and old stack has
   stack_repr at (sp_b, sp_ofs), the new stack v :: old_stk has
   stack_repr at (sp_b, new_sp) where new_sp = sp_ofs - 8.

   This combines load_after_store_same for the head element with
   stack_repr_store_same_block_lower for the tail. *)
Lemma stack_repr_cons_after_store : forall hm cb co m m' stk sp_b sp_ofs v cv,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  val_repr hm cb co v cv ->
  Mem.store Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 8))) cv = Some m' ->
  Ptrofs.unsigned sp_ofs >= 8 ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus ->
  stack_repr hm cb co m' (v :: stk) sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
Proof.
  intros hm cb co m m' stk sp_b sp_ofs v cv Hsr Hvr Hstore Hge8 Hrep.
  econstructor.
  - pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore) as Hload.
    rewrite (val_repr_load_result hm cb co v cv Hvr) in Hload. exact Hload.
  - exact Hvr.
  - replace (Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) with sp_ofs.
    + eapply stack_repr_store_same_block_lower; eauto.
      unfold Ptrofs.sub.
      rewrite (Ptrofs.unsigned_repr 8).
      2: { pose proof Ptrofs.modulus_pos. unfold Ptrofs.max_unsigned. lia. }
      rewrite Ptrofs.unsigned_repr.
      2: { pose proof (Ptrofs.unsigned_range sp_ofs). unfold Ptrofs.max_unsigned. lia. }
      lia.
    + rewrite Ptrofs.sub_add_opp. rewrite Ptrofs.add_assoc.
      rewrite (Ptrofs.add_commut (Ptrofs.neg (Ptrofs.repr 8)) (Ptrofs.repr 8)).
      rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero. reflexivity.
Qed.

(* ================================================================== *)
(* Pointer arithmetic: sp + 1 = sp + 8 bytes (sizeof long)            *)
(* ================================================================== *)

Lemma sem_add_sp_1 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* ================================================================== *)
(* Long + Long via sem_binarith                                        *)
(* ================================================================== *)

Lemma sem_add_long_long : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong n1) tlong (Vlong n2) tlong m
    = Some (Vlong (Int64.add n1 n2)).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Long - Int(1) subtraction                                           *)
(* ================================================================== *)

Lemma sem_sub_long_int : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vlong n) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.sub n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* Tagged integer addition: (2a+1) + (2b+1) - 1 = 2(a+b)+1           *)
(* ================================================================== *)

Local Lemma eqm64_sub : forall x x' y y',
  Int64.eqm x x' -> Int64.eqm y y' -> Int64.eqm (x - y) (x' - y').
Proof.
  intros x x' y y' [kx Hx] [ky Hy].
  exists (kx - ky)%Z. lia.
Qed.

Local Lemma int64_sub_repr : forall x y : Int64.int,
  Int64.sub x y = Int64.repr (Int64.unsigned x - Int64.unsigned y).
Proof. reflexivity. Qed.

Lemma tagged_addint_arith : forall a b,
  Int64.sub (Int64.add (Int64.repr (a * 2 + 1))
                        (Int64.repr (b * 2 + 1)))
            (Int64.repr 1)
  = Int64.repr ((a + b) * 2 + 1).
Proof.
  intros a b.
  rewrite int64_sub_repr, Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  replace ((a + b) * 2 + 1)%Z with ((a * 2 + 1) + (b * 2 + 1) - 1)%Z by lia.
  apply eqm64_sub.
  - apply Int64.eqm_unsigned_repr_l.
    apply Int64.eqm_add; apply Int64.eqm_unsigned_repr_l; apply Int64.eqm_refl.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.

(* ================================================================== *)
(* CONST0 semantic lemmas                                              *)
(* ================================================================== *)

Lemma sem_cast_int_to_long_0 : forall m,
  sem_cast (Vint (Int.repr 0)) tint tlong m =
    Some (Vlong (Int64.repr 0)).
Proof.
  intros. unfold sem_cast.
  change (classify_cast tint tlong) with (cast_case_i2l Signed).
  simpl. reflexivity.
Qed.

Lemma sem_shl_long_0_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oshl
    (Vlong (Int64.repr 0)) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.repr 0)).
Proof.
  intros. unfold sem_binary_operation, sem_shl, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Lemma sem_add_long_int_0_1 : forall m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vlong (Int64.repr 0)) tlong
    (Vint (Int.repr 1)) tint
    m = Some (Vlong (Int64.repr 1)).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add tlong tint) with add_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed).
  simpl. reflexivity.
Qed.

Lemma val_int_0_load_result :
  Val.load_result Mint64 (Vlong (Int64.repr 1)) = Vlong (Int64.repr 1).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Code buffer load preservation under store to other block            *)
(* ================================================================== *)

(* code_buffer_load_at: A Mem.load on the code buffer block cb
   is preserved after any Mem.store to a different block sb.

   This is the pattern used in every parameterized handler proof
   (CONSTINT, BRANCHIF, ATOM, POP, ASSIGN, GETGLOBAL, MAKEBLOCK1,
   PUSHCONSTINT, etc.):

     assert (Hcode_load_m1 : Mem.load Mint32 m1 cb ... = Some ...).
     { erewrite Mem.load_store_other; [exact Hcode_load | exact Hstore |].
       left. exact Hcb_ne. }

   This lemma packages that three-line proof into a single apply. *)
(* ================================================================== *)
(* pc_rel lemmas: prove pc_rel with same code base, new rocq_pc      *)
(* ================================================================== *)

Local Lemma ptrofs_add_repr_hl : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

(* PC advances by 1 instruction *)
Lemma pc_rel_next : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr sizeof_code_t)))
         cb co (rocq_pc + 1).
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr_hl. f_equal. lia.
Qed.

(* PC advances by 2 instructions *)
Lemma pc_rel_next2 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr (2 * sizeof_code_t))))
         cb co (rocq_pc + 2).
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr_hl. f_equal. lia.
Qed.

(* PC advances by 3 instructions *)
Lemma pc_rel_next3 : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr (3 * sizeof_code_t))))
         cb co (rocq_pc + 3).
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  rewrite ptrofs_add_repr_hl. f_equal. lia.
Qed.

(* PC jumps to target via branch offset *)
Lemma pc_rel_branch : forall cb co target,
  pc_rel (Vptr cb (Ptrofs.add co (Ptrofs.repr (target * sizeof_code_t))))
         cb co target.
Proof. intros. unfold pc_rel. reflexivity. Qed.

(* ================================================================== *)
(* val_repr / stack_repr / global_repr are independent of co           *)
(* (since vr_code_ptr uses its own co_val, not the parameter co).      *)
(* ================================================================== *)

Lemma val_repr_co_shift : forall hm cb co co' v cv,
  val_repr hm cb co v cv -> val_repr hm cb co' v cv.
Proof.
  intros hm0 cb0 co0 co' v0 cv0 H. inversion H; subst.
  - constructor.
  - eapply vr_ptr; eassumption.
  - eapply vr_closure; eauto.
  - constructor.
  - eapply vr_code_ptr.
Qed.

Lemma stack_repr_co_shift : forall hm cb co co' m stk b ofs,
  stack_repr hm cb co m stk b ofs -> stack_repr hm cb co' m stk b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 stk0 b0 ofs0 H. induction H.
  - constructor.
  - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.

Lemma global_repr_co_shift : forall hm cb co co' m vs b ofs,
  global_repr hm cb co m vs b ofs -> global_repr hm cb co' m vs b ofs.
Proof.
  intros hm0 cb0 co0 co' m0 vs0 b0 ofs0 H. induction H.
  - constructor.
  - econstructor; [eassumption | eapply val_repr_co_shift; eassumption | assumption].
Qed.

Lemma code_buffer_load_at : forall chunk chunk' m m' cb sb ofs_code ofs_store v_code v_store,
  Mem.load chunk m cb ofs_code = Some v_code ->
  Mem.store chunk' m sb ofs_store v_store = Some m' ->
  cb <> sb ->
  Mem.load chunk m' cb ofs_code = Some v_code.
Proof.
  intros chunk chunk' m m' cb sb ofs_code ofs_store v_code v_store
    Hload Hstore Hne.
  erewrite Mem.load_store_other; eauto.
Qed.
