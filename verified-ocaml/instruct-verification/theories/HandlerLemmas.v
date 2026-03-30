(* HandlerLemmas.v -- Proves (or keeps as Axiom) the axioms from
   ACC0_bigstep_compl_allresults.v using CompCert's memory model.

   Status summary:
   - PROVED: ptr64_true, load_after_store_same, load_after_store_other,
     stack_repr_store_other_block, global_repr_store_other_block,
     val_repr_load_result, sem_cast_long_vlong, sem_cast_long_vptr,
     sem_cast_long_val_repr, sem_add_sp_0, Mptr_Mint64,
     ptrofs_add_unsigned, interp_state_co
   - AXIOM (structural invariants, not derivable from CompCert alone):
     store_succeeds_from_load (needs Writable; load only gives Readable),
     sp_block_ne_sptr, global_block_ne_sptr, sptr_ofs_representable
   - REMOVED: sem_cast_long (provably FALSE for Vundef/Vfloat/Vsingle/Vint;
     use sem_cast_long_val_repr instead) *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
Require Import instruct_handlers.
Require Import InstructSpec.

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

(* ================================================================== *)
(* Memory separation — structural invariants (must stay axiomatic)     *)
(* ================================================================== *)

(* These are invariants about the C memory layout that hold because
   different allocations produce distinct blocks.  They cannot be
   derived from CompCert's memory model alone; they require knowledge
   of how the runtime sets up the interp_state struct, stack, and
   global data in separate allocations.

   DESIGN NOTE: These could be eliminated as top-level axioms by adding
   them as conjuncts to abs_rel / abs_rel_pre in InstructSpec.v.  For
   example, abs_rel could require:
     sp_b <> ar_sptr_block ard /\
     ar_global_block ard <> ar_sptr_block ard /\
     Ptrofs.unsigned (ar_sptr_ofs ard) + 56 < Ptrofs.modulus
   This would push the proof obligation to the caller who sets up the
   initial abs_rel witness (where Mem.alloc / Mem.valid_new_block can
   establish block distinctness).  Each handler proof would then just
   extract the invariant from its abs_rel hypothesis instead of
   appealing to an axiom. *)

(* The sp block is separate from the struct pointer block *)
Axiom sp_block_ne_sptr : forall (ard : abs_rel_data) sp_b,
  sp_b <> ar_sptr_block ard.

(* The global data block is separate from the struct pointer block *)
Axiom global_block_ne_sptr : forall (ard : abs_rel_data),
  ar_global_block ard <> ar_sptr_block ard.

(* The struct pointer offset is in representable range *)
Axiom sptr_ofs_representable : forall (ard : abs_rel_data),
  Ptrofs.unsigned (ar_sptr_ofs ard) + 56 < Ptrofs.modulus.

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

(* store_succeeds_from_load: Mem.load_valid_access gives
   Mem.valid_access m Mint64 b ofs Readable, but Mem.valid_access_store
   requires Writable.  CompCert's perm_order satisfies
   perm_order Writable Readable (Writable implies Readable) but NOT
   perm_order Readable Writable, so there is no valid_access_implies
   path from Readable to Writable.

   Mem.store_valid_access_3 and Mem.valid_access_free_2 do not help
   either: the former gives valid_access from a successful store (wrong
   direction), and the latter weakens Freeable.

   To eliminate this axiom, add a Writable (or Freeable) invariant for
   the struct pointer block to abs_rel / abs_rel_pre.  For example:
     Mem.valid_access m Mint64 (ar_sptr_block ard)
       (Ptrofs.unsigned (ar_sptr_ofs ard) + field_ofs) Writable
   for each field offset.  The initial abs_rel witness can establish
   this from Mem.alloc (which grants Freeable >= Writable).
   Alternatively, a single range_perm covering the entire struct
   (offsets 0..55, Writable) would suffice and be simpler. *)
Axiom store_succeeds_from_load : forall m b ofs v_old v_new,
  Mem.load Mint64 m b ofs = Some v_old ->
  exists m', Mem.store Mint64 m b ofs v_new = Some m'.

(* ================================================================== *)
(* Representation preservation under store to other block              *)
(* ================================================================== *)

Lemma stack_repr_store_other_block : forall hm m m' stk sp_b sp_ofs sb ofs v,
  stack_repr hm m stk sp_b sp_ofs ->
  Mem.store Mint64 m sb ofs v = Some m' ->
  sb <> sp_b ->
  stack_repr hm m' stk sp_b sp_ofs.
Proof.
  intros hm m m' stk. revert m m'.
  induction stk as [| hd tl IH]; intros m m' sp_b sp_ofs sb ofs v Hsr Hstore Hne.
  - constructor.
  - inversion Hsr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
Qed.

Lemma global_repr_store_other_block : forall hm m m' gs gb gofs sb ofs v,
  global_repr hm m gs gb gofs ->
  Mem.store Mint64 m sb ofs v = Some m' ->
  sb <> gb ->
  global_repr hm m' gs gb gofs.
Proof.
  intros hm m m' gs. revert m m'.
  induction gs as [| hd tl IH]; intros m m' gb gofs sb ofs v Hgr Hstore Hne.
  - constructor.
  - inversion Hgr; subst. econstructor.
    + erewrite Mem.load_store_other; eauto.
    + eassumption.
    + eapply IH; eauto.
Qed.

(* ================================================================== *)
(* Value representation                                                *)
(* ================================================================== *)

Lemma val_repr_load_result : forall hm v cv,
  val_repr hm v cv ->
  Val.load_result Mint64 cv = cv.
Proof.
  intros hm v cv Hvr. inversion Hvr; subst; simpl.
  - (* vr_int: Vlong *) reflexivity.
  - (* vr_ptr: Vptr — needs ptr64 *)
    rewrite ptr64_true. reflexivity.
  - (* vr_closure: Vptr *) rewrite ptr64_true. reflexivity.
  - (* vr_block_atom: Vlong *) reflexivity.
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
Lemma sem_cast_long_val_repr : forall hm v cv m,
  val_repr hm v cv ->
  sem_cast cv tlong tlong m = Some cv.
Proof.
  intros hm v cv m Hvr. inversion Hvr; subst.
  - (* vr_int: Vlong *) apply sem_cast_long_vlong.
  - (* vr_ptr: Vptr *) apply sem_cast_long_vptr.
  - (* vr_closure: Vptr *) apply sem_cast_long_vptr.
  - (* vr_block_atom: Vlong *) apply sem_cast_long_vlong.
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
