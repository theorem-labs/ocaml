(* DecodeProof.v - Correctness of the bytecode encode/decode roundtrip.

   Main theorem (modulo well-formedness):
     decode_bytecode (encode_bytecode code) 0 (length (encode_bytecode code))
     = code

   The encoder always uses general opcode forms (ACC=8, PUSHACC=18, etc.)
   and the decoder maps these back to the same instruction constructors,
   so the roundtrip is well-defined for well-formed programs.

   Proof strategy:
   1. Byte-level lemmas: read_u32_le inverts encode_word_le for values
      in the 32-bit range.
   2. Per-instruction lemma: decode_raw + resolve_one inverts encode_instr
      for each instruction form.
   3. The offset maps built by encoder and decoder are consistent.
   4. Main theorem by induction on the instruction list.

   Due to the complexity of the full proof (100+ opcode cases, branch
   target resolution, two-pass offset map consistency), we prove the
   key structural lemmas fully and state the main theorem as Admitted
   with proven sub-lemmas. *)

From Stdlib Require Import ZArith PeanoNat Bool List Lia.
Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Bytecode Require Import Encode DecodeSpec.
From OCamlInterp.Automatic.Bytecode Require Import Decode.
Open Scope Z_scope.
Open Scope nat_scope.

(* ================================================================== *)
(* Byte-level lemmas                                                   *)
(* ================================================================== *)

(* byte_at on a concrete list prefix *)
Lemma byte_at_cons_0 : forall b rest, byte_at (b :: rest) 0 = b.
Proof. reflexivity. Qed.

Lemma byte_at_cons_S : forall b rest n, byte_at (b :: rest) (S n) = byte_at rest n.
Proof. reflexivity. Qed.

(* byte_at on an appended list when the index is within the first part *)
Lemma byte_at_app_l : forall (l1 l2 : list Z) (n : nat),
  n < List.length l1 ->
  byte_at (l1 ++ l2) n = byte_at l1 n.
Proof.
  induction l1 as [| b l1' IH]; intros l2 n Hlt.
  - simpl in Hlt. lia.
  - destruct n.
    + reflexivity.
    + simpl. apply IH. simpl in Hlt. lia.
Qed.

(* The key byte-level roundtrip: reading a u32 from encoded bytes
   recovers the original value (masked to 32 bits).

   encode_word_le v = [b0; b1; b2; b3] where bi are the LE bytes.
   read_u32_le [b0; b1; b2; b3] 0 = Z.land v 0xFFFFFFFF.              *)

Lemma encode_word_le_length : forall v, List.length (encode_word_le v) = 4.
Proof. reflexivity. Qed.

Local Open Scope Z_scope.

(* Helper: masking a value in [0, 2^32) with 0xFFFFFFFF is identity. *)
Lemma land_mask_32_id : forall v,
  (0 <= v < 4294967296)%Z ->
  Z.land v 4294967295 = v.
Proof.
  intros v Hv.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  replace 4294967295 with (Z.ones 32) by reflexivity.
  destruct (Z_lt_dec i 32).
  - rewrite Z.ones_spec_low by lia. rewrite Bool.andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
    symmetry. apply Z.bits_above_log2; try lia.
    destruct (Z.eq_dec v 0).
    + subst. simpl. lia.
    + assert (Hpos : (0 < v)%Z) by lia.
      replace 4294967296 with (2 ^ 32)%Z in Hv by reflexivity.
      pose proof (proj1 (Z.log2_lt_pow2 v 32 Hpos) ltac:(lia)).
      lia.
Qed.

(* Helper: bits of a 32-bit value above index 31 are false. *)
Lemma testbit_above_32 : forall v i,
  (0 <= v < 4294967296)%Z ->
  (32 <= i)%Z ->
  Z.testbit v i = false.
Proof.
  intros v i Hv Hi.
  apply Z.bits_above_log2; try lia.
  destruct (Z.eq_dec v 0).
  - subst. simpl. lia.
  - assert (Hpos : (0 < v)%Z) by lia.
    replace 4294967296 with (2 ^ 32)%Z in Hv by reflexivity.
    pose proof (proj1 (Z.log2_lt_pow2 v 32 Hpos) ltac:(lia)).
    lia.
Qed.

(* Helper: reassembling four LE bytes via lor/shiftl recovers the original
   32-bit value.  Proof by Z.bits_inj' with case splits on byte boundaries. *)
Lemma reassemble_le_bytes : forall v,
  (0 <= v < 4294967296)%Z ->
  Z.lor (Z.land v (Z.ones 8))
    (Z.lor (Z.shiftl (Z.land (Z.shiftr v 8) (Z.ones 8)) 8)
       (Z.lor (Z.shiftl (Z.land (Z.shiftr v 16) (Z.ones 8)) 16)
              (Z.shiftl (Z.land (Z.shiftr v 24) (Z.ones 8)) 24)))
  = v.
Proof.
  intros v Hv.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.lor_spec.
  destruct (Z_lt_dec i 8) as [Hi8|Hi8].
  - (* Byte 0: 0 <= i < 8 *)
    rewrite Z.land_spec, Z.ones_spec_low by lia.
    rewrite Bool.andb_true_r.
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 16)) by lia.
    rewrite Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 24)) by lia.
    rewrite !Bool.orb_false_r. reflexivity.
  - destruct (Z_lt_dec i 16) as [Hi16|Hi16].
    + (* Byte 1: 8 <= i < 16 *)
      rewrite Z.land_spec, Z.ones_spec_high by lia.
      rewrite Bool.andb_false_r.
      rewrite Z.shiftl_spec by lia.
      rewrite Z.land_spec, Z.shiftr_spec by lia.
      rewrite Z.ones_spec_low by lia.
      rewrite Bool.andb_true_r.
      rewrite Z.shiftl_spec by lia.
      rewrite (Z.testbit_neg_r _ (i - 16)) by lia.
      rewrite Z.shiftl_spec by lia.
      rewrite (Z.testbit_neg_r _ (i - 24)) by lia.
      rewrite !Bool.orb_false_r. simpl. f_equal. lia.
    + destruct (Z_lt_dec i 24) as [Hi24|Hi24].
      * (* Byte 2: 16 <= i < 24 *)
        rewrite Z.land_spec, Z.ones_spec_high by lia.
        rewrite Bool.andb_false_r.
        rewrite Z.shiftl_spec by lia.
        rewrite Z.land_spec, Z.shiftr_spec by lia.
        rewrite Z.ones_spec_high by lia.
        rewrite Bool.andb_false_r.
        rewrite Z.shiftl_spec by lia.
        rewrite Z.land_spec, Z.shiftr_spec by lia.
        rewrite Z.ones_spec_low by lia.
        rewrite Bool.andb_true_r.
        rewrite Z.shiftl_spec by lia.
        rewrite (Z.testbit_neg_r _ (i - 24)) by lia.
        rewrite !Bool.orb_false_r. simpl. f_equal. lia.
      * destruct (Z_lt_dec i 32) as [Hi32|Hi32].
        -- (* Byte 3: 24 <= i < 32 *)
           rewrite Z.land_spec, Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           rewrite Z.shiftl_spec by lia.
           rewrite Z.land_spec, Z.shiftr_spec by lia.
           rewrite Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           rewrite Z.shiftl_spec by lia.
           rewrite Z.land_spec, Z.shiftr_spec by lia.
           rewrite Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           rewrite Z.shiftl_spec by lia.
           rewrite Z.land_spec, Z.shiftr_spec by lia.
           rewrite Z.ones_spec_low by lia.
           rewrite Bool.andb_true_r.
           simpl. f_equal. lia.
        -- (* i >= 32: all bits are false *)
           pose proof (testbit_above_32 v i Hv ltac:(lia)) as Hvi.
           rewrite Hvi.
           rewrite Z.land_spec, Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           rewrite Z.shiftl_spec by lia.
           rewrite Z.land_spec, Z.shiftr_spec by lia.
           rewrite Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           rewrite Z.shiftl_spec by lia.
           rewrite Z.land_spec, Z.shiftr_spec by lia.
           rewrite Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           rewrite Z.shiftl_spec by lia.
           rewrite Z.land_spec, Z.shiftr_spec by lia.
           rewrite Z.ones_spec_high by lia.
           rewrite Bool.andb_false_r.
           reflexivity.
Qed.

Local Close Scope Z_scope.

(* For a value that is already masked to 32 bits and is non-negative,
   reading back the encoded bytes gives the original value. *)
Lemma read_u32_le_encode_word_le : forall v,
  (0 <= v < 4294967296)%Z ->
  read_u32_le (encode_word_le v) 0 = v.
Proof.
  intros v Hv.
  unfold read_u32_le, encode_word_le, byte_at.
  rewrite land_mask_32_id by assumption.
  change 255%Z with (Z.ones 8).
  apply reassemble_le_bytes. assumption.
Qed.

(* Generalized unsigned roundtrip: for any v,
   read_u32_le (encode_word_le v) 0 = Z.land v (Z.ones 32).
   The encode masks v to 32 bits, extracts LE bytes, and read reassembles. *)
Lemma land_mask_32_idem : forall v,
  Z.land (Z.land v 4294967295) 4294967295 = Z.land v 4294967295.
Proof.
  intros v.
  apply land_mask_32_id.
  replace 4294967295%Z with (Z.ones 32) by reflexivity.
  replace 4294967296%Z with (2^32)%Z by reflexivity.
  rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma read_u32_le_encode_word_le_gen : forall v,
  read_u32_le (encode_word_le v) 0 = Z.land v (Z.ones 32).
Proof.
  intros v.
  replace (Z.land v (Z.ones 32)) with (Z.land v 4294967295)
    by reflexivity.
  set (u := Z.land v 4294967295).
  assert (Hu : (0 <= u < 4294967296)%Z).
  { subst u. replace 4294967295%Z with (Z.ones 32) by reflexivity.
    rewrite Z.land_ones by lia.
    replace 4294967296%Z with (2^32)%Z by reflexivity.
    apply Z.mod_pos_bound. lia. }
  assert (Heu : encode_word_le v = encode_word_le u).
  { unfold encode_word_le. subst u.
    rewrite land_mask_32_idem.
    reflexivity. }
  rewrite Heu.
  apply read_u32_le_encode_word_le. exact Hu.
Qed.

(* For v in [0, 2^31), bit 31 of v is false. *)
Lemma testbit_31_nonneg : forall v,
  (0 <= v <= 2147483647)%Z ->
  Z.testbit v 31 = false.
Proof.
  intros v Hv.
  apply Z.bits_above_log2; try lia.
  destruct (Z.eq_dec v 0).
  - subst. simpl. lia.
  - assert (0 < v)%Z by lia.
    replace 2147483647%Z with (2^31 - 1)%Z in Hv by reflexivity.
    assert (v < 2^31)%Z by lia.
    pose proof (proj1 (Z.log2_lt_pow2 v 31 ltac:(lia)) ltac:(lia)).
    lia.
Qed.

(* For -2^n <= v < 0: v mod 2^n = v + 2^n. *)
Lemma neg_mod_pow2 : forall v n,
  (0 <= n)%Z ->
  (-(2^n) <= v < 0)%Z ->
  (v mod 2^n = v + 2^n)%Z.
Proof.
  intros v n Hn Hv.
  assert (Hp : (0 < 2^n)%Z) by (apply Z.pow_pos_nonneg; lia).
  symmetry. apply Z.mod_unique with (-1)%Z.
  - left. lia.
  - lia.
Qed.

(* For negative v in [-2^31, 0), bit 31 of (v mod 2^32) is true. *)
Lemma testbit_31_neg_mod : forall v,
  (-2147483648 <= v < 0)%Z ->
  Z.testbit (v mod 2^32) 31 = true.
Proof.
  intros v Hv.
  rewrite neg_mod_pow2 by lia.
  replace (-2147483648)%Z with (-(2^31))%Z in Hv by reflexivity.
  assert (Hu : (2^31 <= v + 2^32 < 2^32)%Z).
  { replace (2^32)%Z with (2 * 2^31)%Z by reflexivity. lia. }
  rewrite Z.testbit_true by lia.
  assert (Hdiv : (1 = (v + 2^32) / 2^31)%Z).
  { apply Z.div_unique with (v + 2^32 - 2^31)%Z.
    - left. split; [lia | ]. replace (2^32)%Z with (2 * 2^31)%Z by reflexivity. lia.
    - lia.
  }
  rewrite <- Hdiv. reflexivity.
Qed.

(* Z.land (v mod 2^n) (Z.lnot (Z.ones n)) = 0:
   the mod keeps only low n bits, lnot ones keeps only high bits. *)
Lemma land_mod_lnot_ones : forall v n,
  (0 <= n)%Z ->
  Z.land (v mod 2^n) (Z.lnot (Z.ones n)) = 0%Z.
Proof.
  intros v n Hn.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  rewrite Z.bits_0.
  destruct (Z_lt_dec i n).
  - rewrite Z.lnot_spec by lia.
    rewrite Z.ones_spec_low by lia.
    simpl. apply Bool.andb_false_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    reflexivity.
Qed.

(* Sign extension recovers v for negative v in [-2^n, 0). *)
Lemma sign_extend_neg : forall v n,
  (0 <= n)%Z ->
  (-(2^n) <= v < 0)%Z ->
  Z.lor (v mod 2^n) (Z.lnot (Z.ones n)) = v.
Proof.
  intros v n Hn Hv.
  pose proof (Z.add_lor_land (v mod 2^n) (Z.lnot (Z.ones n))) as Hadd.
  rewrite land_mod_lnot_ones in Hadd by assumption.
  assert (Z.lor (v mod 2^n) (Z.lnot (Z.ones n)) = v mod 2^n + Z.lnot (Z.ones n))%Z by lia.
  rewrite H.
  unfold Z.lnot.
  rewrite Z.ones_equiv by assumption.
  rewrite neg_mod_pow2 by assumption.
  lia.
Qed.

(* The signed variant: read_i32_le inverts encode_word_le for values
   in the signed 32-bit range [-2^31, 2^31]. *)
Lemma read_i32_le_encode_word_le : forall v,
  z_fits_i32b v = true ->
  read_i32_le (encode_word_le v) 0 = v.
Proof.
  intros v Hwf.
  unfold z_fits_i32b in Hwf.
  apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  unfold read_i32_le.
  rewrite read_u32_le_encode_word_le_gen.
  rewrite Z.land_ones by lia.
  destruct (Z_lt_dec v 0) as [Hneg | Hnn].
  - (* Negative case: -2^31 <= v < 0 *)
    rewrite testbit_31_neg_mod by
      (replace (-2147483648)%Z with (-(2^31))%Z by reflexivity; lia).
    apply sign_extend_neg; lia.
  - (* Non-negative case: 0 <= v <= 2^31-1 *)
    assert (Hrange : (0 <= v < 2^32)%Z).
    { replace (2^32)%Z with 4294967296%Z by reflexivity.
      replace 2147483647%Z with (2^31 - 1)%Z in Hhi by reflexivity.
      lia. }
    rewrite Z.mod_small by lia.
    rewrite testbit_31_nonneg by lia.
    reflexivity.
Qed.

(* ================================================================== *)
(* Offset map consistency                                              *)
(* ================================================================== *)

(* The encoder builds an offset map (list nat) from instruction index
   to word offset.  The decoder builds an association list (list (nat * nat))
   from word offset to instruction index.  These are inverses for
   well-formed programs. *)

(* The word offset of instruction [idx] in program [code]. *)
Fixpoint word_offset_of (code : list instruction) (idx : nat) : nat :=
  match code, idx with
  | _, O => 0
  | i :: rest, S idx' => instr_word_size i + word_offset_of rest idx'
  | [], _ => 0
  end.

(* Helper: build_offset_list with accumulator produces correct offsets. *)
Lemma build_offset_list_correct : forall code acc idx,
  idx < List.length code ->
  List.nth_error (build_offset_list code acc) idx =
    Some (acc + word_offset_of code idx).
Proof.
  induction code as [|i rest IH]; intros acc idx Hlt.
  - simpl in Hlt. lia.
  - destruct idx as [|idx'].
    + simpl. f_equal. lia.
    + simpl in Hlt.
      simpl. rewrite IH by lia.
      f_equal. lia.
Qed.

Lemma offset_map_correct : forall code idx,
  idx < List.length code ->
  List.nth_error (offset_map code) idx = Some (word_offset_of code idx).
Proof.
  intros code idx Hlt.
  unfold offset_map.
  rewrite build_offset_list_correct by assumption.
  f_equal.
Qed.

(* ================================================================== *)
(* Total byte length of encoded program                                *)
(* ================================================================== *)

Definition total_word_size (code : list instruction) : nat :=
  fold_left (fun acc i => acc + instr_word_size i) code 0.

Definition total_byte_size (code : list instruction) : nat :=
  4 * total_word_size code.

(* Helper: fold_left with addition and accumulator *)
Lemma fold_left_add_acc : forall code acc,
  fold_left (fun a i => a + instr_word_size i) code acc =
    acc + fold_left (fun a i => a + instr_word_size i) code 0.
Proof.
  induction code as [|i rest IH]; intros acc.
  - simpl. lia.
  - simpl.
    rewrite IH.
    replace (0 + instr_word_size i) with (instr_word_size i) by lia.
    rewrite (IH (instr_word_size i)).
    lia.
Qed.

(* Length of flat_map encode_word_le *)
Lemma emit_words_length : forall ws,
  List.length (emit_words ws) = 4 * List.length ws.
Proof.
  induction ws as [| w ws' IH].
  - reflexivity.
  - unfold emit_words.
    change (List.flat_map encode_word_le (w :: ws'))
      with (encode_word_le w ++ List.flat_map encode_word_le ws').
    rewrite length_app. rewrite encode_word_le_length.
    change (List.flat_map encode_word_le ws') with (emit_words ws').
    rewrite IH. simpl. lia.
Qed.

(* Length of encode_instr matches instr_word_size * 4.
   Each instruction encodes via emit_words on a word list whose
   length equals instr_word_size. *)
Lemma encode_instr_length : forall omap idx i,
  List.length (encode_instr omap idx i) = 4 * instr_word_size i.
Proof.
  intros omap idx i.
  destruct i; unfold encode_instr;
    rewrite ?emit_words_length;
    rewrite ?app_length, ?map_length;
    simpl length; simpl instr_word_size;
    lia.
Qed.

Lemma encode_instrs_length : forall omap idx code,
  List.length (encode_instrs omap idx code) =
    4 * fold_left (fun acc i => acc + instr_word_size i) code 0.
Proof.
  intros omap idx code. revert idx.
  induction code as [|i rest IH]; intros idx.
  - simpl. lia.
  - simpl encode_instrs.
    rewrite length_app.
    rewrite encode_instr_length.
    rewrite IH.
    set (s := fold_left (fun acc i0 => acc + instr_word_size i0) rest 0).
    change (fold_left (fun acc i0 => acc + instr_word_size i0) (i :: rest) 0)
      with (fold_left (fun acc i0 => acc + instr_word_size i0) rest (0 + instr_word_size i)).
    rewrite fold_left_add_acc.
    subst s. lia.
Qed.

Lemma encode_bytecode_length : forall code,
  List.length (encode_bytecode code) = 4 * fold_left (fun acc i => acc + instr_word_size i) code 0.
Proof.
  intros code.
  unfold encode_bytecode.
  apply encode_instrs_length.
Qed.

(* ================================================================== *)
(* Simple instruction roundtrip (no branch targets)                    *)
(* ================================================================== *)

(* For instructions without branch targets, the roundtrip is simpler:
   the encoded bytes decode to the same instruction regardless of
   offset map details. We prove a representative case. *)

Lemma decode_raw_simple_opcode : forall data code_offset code_length pos fuel op,
  (pos + 4 <= code_length) ->
  read_u32_le data (code_offset + pos) = op ->
  (0 <= op)%Z ->
  operand_count op = Some 0 ->
  op <> 87%Z -> op <> 44%Z -> op <> 141%Z ->
  exists rest,
    decode_raw_aux data code_offset code_length pos (S fuel) =
    mk_raw (pos / 4) op [] :: rest.
Proof.
  intros data code_offset code_length pos fuel op Hle Hread Hop Hcount Hne87 Hne44 Hne141.
  simpl.
  destruct (Nat.leb code_length pos) eqn:Hleb.
  - apply Nat.leb_le in Hleb. lia.
  - rewrite Hread.
    destruct (Z.eqb op 87) eqn:E87.
    + apply Z.eqb_eq in E87. contradiction.
    + destruct (Z.eqb op 44) eqn:E44.
      * apply Z.eqb_eq in E44. contradiction.
      * destruct (Z.eqb op 141) eqn:E141.
        -- apply Z.eqb_eq in E141. contradiction.
        -- rewrite Hcount. simpl. eauto.
Qed.

(* ================================================================== *)
(* byte_at on appended lists: right part                               *)
(* ================================================================== *)

Lemma byte_at_app_r : forall (l1 l2 : list Z) (n : nat),
  List.length l1 <= n ->
  byte_at (l1 ++ l2) n = byte_at l2 (n - List.length l1).
Proof.
  induction l1 as [| b l1' IH]; intros l2 n Hle.
  - simpl. replace (n - 0) with n by lia. reflexivity.
  - destruct n.
    + simpl in Hle. lia.
    + simpl. rewrite IH by (simpl in Hle; lia).
      f_equal.
Qed.

(* ================================================================== *)
(* read_u32_le / read_i32_le on appended lists                         *)
(* ================================================================== *)

Lemma read_u32_le_app_l : forall l1 l2 off,
  off + 4 <= List.length l1 ->
  read_u32_le (l1 ++ l2) off = read_u32_le l1 off.
Proof.
  intros l1 l2 off Hle.
  unfold read_u32_le.
  repeat rewrite byte_at_app_l by (simpl; lia).
  reflexivity.
Qed.

Lemma read_i32_le_app_l : forall l1 l2 off,
  off + 4 <= List.length l1 ->
  read_i32_le (l1 ++ l2) off = read_i32_le l1 off.
Proof.
  intros l1 l2 off Hle.
  unfold read_i32_le.
  rewrite read_u32_le_app_l by assumption.
  reflexivity.
Qed.

(* When data = prefix ++ suffix and we read at an offset within suffix *)
Lemma read_u32_le_app_r : forall l1 l2 off,
  List.length l1 <= off ->
  read_u32_le (l1 ++ l2) off = read_u32_le l2 (off - List.length l1).
Proof.
  intros l1 l2 off Hle.
  unfold read_u32_le.
  rewrite byte_at_app_r by lia.
  rewrite byte_at_app_r by lia.
  rewrite byte_at_app_r by lia.
  rewrite byte_at_app_r by lia.
  repeat f_equal; lia.
Qed.

Lemma read_i32_le_app_r : forall l1 l2 off,
  List.length l1 <= off ->
  read_i32_le (l1 ++ l2) off = read_i32_le l2 (off - List.length l1).
Proof.
  intros l1 l2 off Hle.
  unfold read_i32_le.
  rewrite read_u32_le_app_r by assumption.
  reflexivity.
Qed.

(* ================================================================== *)
(* read_u32_le / read_i32_le on emit_words                             *)
(* ================================================================== *)

Lemma emit_words_cons : forall w ws,
  emit_words (w :: ws) = encode_word_le w ++ emit_words ws.
Proof. reflexivity. Qed.

(* General unsigned: read_u32_le at word offset n in emit_words *)
Lemma read_u32_le_emit_words_gen : forall ws n rest,
  n < List.length ws ->
  read_u32_le (emit_words ws ++ rest) (4 * n) =
    Z.land (nth n ws 0%Z) (Z.ones 32).
Proof.
  induction ws as [| w ws' IH]; intros n rest Hlt.
  - simpl in Hlt. lia.
  - destruct n as [|n'].
    + simpl nth.
      rewrite emit_words_cons, <- app_assoc.
      rewrite read_u32_le_app_l
        by (rewrite encode_word_le_length; lia).
      apply read_u32_le_encode_word_le_gen.
    + simpl nth. rewrite emit_words_cons, <- app_assoc.
      replace (4 * S n') with (4 + 4 * n') by lia.
      unfold read_u32_le.
      repeat rewrite byte_at_app_r
        by (rewrite encode_word_le_length; lia).
      rewrite encode_word_le_length.
      replace (4 + 4 * n' - 4) with (4 * n') by lia.
      replace (S (4 + 4 * n') - 4) with (S (4 * n')) by lia.
      replace (S (S (4 + 4 * n')) - 4) with (S (S (4 * n'))) by lia.
      replace (S (S (S (4 + 4 * n'))) - 4) with (S (S (S (4 * n')))) by lia.
      fold (read_u32_le (emit_words ws' ++ rest) (4 * n')).
      apply IH. simpl in Hlt. lia.
Qed.

(* General signed: read_i32_le at word offset n in emit_words *)
Lemma read_i32_le_emit_words_gen : forall ws n rest,
  n < List.length ws ->
  z_fits_i32b (nth n ws 0%Z) = true ->
  read_i32_le (emit_words ws ++ rest) (4 * n) = nth n ws 0%Z.
Proof.
  induction ws as [| w ws' IH]; intros n rest Hlt Hwf.
  - simpl in Hlt. lia.
  - destruct n as [|n'].
    + simpl nth in *.
      rewrite emit_words_cons, <- app_assoc.
      rewrite read_i32_le_app_l
        by (rewrite encode_word_le_length; lia).
      apply read_i32_le_encode_word_le. exact Hwf.
    + simpl nth in *. rewrite emit_words_cons, <- app_assoc.
      replace (4 * S n') with (4 + 4 * n') by lia.
      unfold read_i32_le, read_u32_le.
      repeat rewrite byte_at_app_r
        by (rewrite encode_word_le_length; lia).
      rewrite encode_word_le_length.
      replace (4 + 4 * n' - 4) with (4 * n') by lia.
      replace (S (4 + 4 * n') - 4) with (S (4 * n')) by lia.
      replace (S (S (4 + 4 * n')) - 4) with (S (S (4 * n'))) by lia.
      replace (S (S (S (4 + 4 * n'))) - 4) with (S (S (S (4 * n')))) by lia.
      fold (read_u32_le (emit_words ws' ++ rest) (4 * n')).
      fold (read_i32_le (emit_words ws' ++ rest) (4 * n')).
      apply IH; [simpl in Hlt; lia | exact Hwf].
Qed.

(* ================================================================== *)
(* read_operands position tracking                                     *)
(* ================================================================== *)

Lemma read_operands_length : forall data code_offset pos n,
  snd (read_operands data code_offset pos n) = pos + 4 * n.
Proof.
  intros data code_offset pos n. revert pos.
  induction n as [|n' IH]; intros pos.
  - simpl. lia.
  - simpl.
    destruct (read_operands data code_offset (pos + 4) n') as [ops pos'] eqn:Heq.
    simpl.
    assert (Hpos' : pos' = pos + 4 + 4 * n').
    { pose proof (IH (pos + 4)) as IHp. rewrite Heq in IHp. simpl in IHp. exact IHp. }
    lia.
Qed.

(* ================================================================== *)
(* Well-formedness helpers                                             *)
(* ================================================================== *)

Lemma opcode_fits_u32 : forall (op : Z),
  (0 <= op <= 255)%Z ->
  (0 <= op < 4294967296)%Z.
Proof. intros. lia. Qed.

Lemma nat_fits_u32_z : forall (n : nat),
  nat_fits_i32b n = true ->
  (0 <= Z.of_nat n < 4294967296)%Z.
Proof.
  intros n Hwf.
  unfold nat_fits_i32b, z_fits_i32b in Hwf.
  apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. lia.
Qed.

Lemma z_fits_i32b_of_nat : forall n,
  nat_fits_i32b n = true ->
  z_fits_i32b (Z.of_nat n) = true.
Proof. intros. exact H. Qed.

Lemma nat_of_z_of_nat : forall n, nat_of_z (Z.of_nat n) = n.
Proof.
  intros n. unfold nat_of_z. apply Nat2Z.id.
Qed.

Lemma wf_instrb_from_well_formed : forall code i,
  well_formed code = true ->
  In i code ->
  wf_instrb (List.length code) i = true.
Proof.
  intros code i Hwf Hin.
  unfold well_formed in Hwf.
  rewrite forallb_forall in Hwf.
  apply Hwf. exact Hin.
Qed.

(* ================================================================== *)
(* Fuel sufficiency                                                    *)
(* ================================================================== *)

Lemma fuel_sufficient : forall code,
  List.length code <= List.length (encode_bytecode code) + 1.
Proof.
  intros code.
  rewrite encode_bytecode_length.
  induction code as [|i rest IH].
  - simpl. lia.
  - simpl length at 1.
    simpl fold_left. rewrite fold_left_add_acc.
    assert (Hws : 1 <= instr_word_size i) by (destruct i; simpl; lia).
    lia.
Qed.

(* ================================================================== *)
(* Offset map: length and lookup properties                            *)
(* ================================================================== *)

Lemma build_offset_list_length : forall code acc,
  List.length (build_offset_list code acc) = List.length code.
Proof.
  induction code as [|i rest IH]; intros acc.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma offset_map_length : forall code,
  List.length (offset_map code) = List.length code.
Proof.
  intros. unfold offset_map. apply build_offset_list_length.
Qed.

(* The encoder's lookup_offset on offset_map code at target_idx gives the
   word offset of instruction target_idx. *)
Lemma lookup_offset_correct : forall code (target_idx : Z),
  (0 <= target_idx)%Z ->
  Z.to_nat target_idx < List.length code ->
  Encode.lookup_offset (offset_map code) target_idx =
    Z.of_nat (word_offset_of code (Z.to_nat target_idx)).
Proof.
  intros code target_idx Hnn Hlt.
  unfold Encode.lookup_offset.
  rewrite offset_map_correct by assumption.
  reflexivity.
Qed.

(* ================================================================== *)
(* Decoder's build_offset_map consistency with encoder's offset_map     *)
(* ================================================================== *)

(* When decode_raw_aux produces raw instructions with ri_word_offset values
   that match word_offset_of, the decoder's build_offset_map inverts the
   encoder's offset_map.

   Specifically: if raw instruction i has ri_word_offset = word_offset_of code i,
   then Decode.lookup_offset (build_offset_map raws) (word_offset_of code i) = i.

   This is the key property that makes resolve_branch recover the original
   instruction index from a relative branch offset. *)

(* If the raw instruction list has word offsets [w0, w1, w2, ...] and all
   are distinct, then lookup_offset (build_offset_map_aux raws base) wi = base + i. *)

Lemma build_offset_map_aux_correct : forall raws base k,
  k < List.length raws ->
  (forall j, j < List.length raws ->
    ri_word_offset (nth j raws (mk_raw 0 0 [])) <>
    ri_word_offset (nth k raws (mk_raw 0 0 [])) \/ j = k) ->
  Decode.lookup_offset (build_offset_map_aux raws base)
    (ri_word_offset (nth k raws (mk_raw 0 0 []))) = (base + k)%nat.
Proof.
  induction raws as [|r raws' IH]; intros base k Hlt Hdistinct.
  - simpl in Hlt. lia.
  - destruct k as [|k'].
    + simpl. rewrite Nat.eqb_refl. lia.
    + simpl.
      destruct (Nat.eqb (ri_word_offset r)
        (ri_word_offset (nth k' raws' (mk_raw 0 0 [])))) eqn:Heqb.
      * (* The word offsets match -- this contradicts distinctness *)
        apply Nat.eqb_eq in Heqb.
        exfalso.
        specialize (Hdistinct 0%nat ltac:(simpl; lia)).
        simpl in Hdistinct.
        destruct Hdistinct as [Hneq | Heq].
        -- apply Hneq. exact Heqb.
        -- lia.
      * rewrite IH.
        -- lia.
        -- simpl in Hlt. lia.
        -- intros j Hj.
           specialize (Hdistinct (S j) ltac:(simpl; lia)).
           simpl in Hdistinct.
           destruct Hdistinct as [Hneq | Heq].
           ++ left. exact Hneq.
           ++ right. lia.
Qed.

(* ================================================================== *)
(* read_operands on encoded data with code_offset=0                    *)
(* ================================================================== *)

(* When we read n operands starting at byte position start_pos from data,
   and data contains the encoded words at those positions, we get back
   the original values. This is used for the operand reading in decode_raw_aux. *)

Lemma read_operands_on_emit_words : forall ws start rest n,
  n <= List.length ws ->
  (forall k, k < n -> z_fits_i32b (nth (start + k) ws 0%Z) = true) ->
  start + n <= List.length ws ->
  fst (read_operands (emit_words ws ++ rest) 0 (4 * start) n) =
    map (fun k => nth k ws 0%Z) (seq start n).
Proof.
  intros ws start rest n.
  revert start.
  induction n as [|n' IH]; intros start Hle Hwf Hle2.
  - simpl. reflexivity.
  - change (read_operands (emit_words ws ++ rest) 0 (4 * start) (S n'))
      with (let v := read_i32_le (emit_words ws ++ rest) (0 + 4 * start)%nat in
            let '(r, p') := read_operands (emit_words ws ++ rest) 0 (4 * start + 4)%nat n' in
            (v :: r, p')).
    replace (0 + 4 * start)%nat with (4 * start) by lia.
    assert (Hwf0 : z_fits_i32b (nth start ws 0%Z) = true).
    { replace start with (start + 0) at 1 by lia. apply Hwf. lia. }
    rewrite read_i32_le_emit_words_gen by (try lia; exact Hwf0).
    replace (4 * start + 4)%nat with (4 * S start) by lia.
    destruct (read_operands (emit_words ws ++ rest) 0 (4 * S start) n') as [ops pos'] eqn:Heq.
    simpl fst.
    assert (Hfst: fst (read_operands (emit_words ws ++ rest) 0 (4 * S start) n') =
                  map (fun k => nth k ws 0%Z) (seq (S start) n')).
    { apply IH; try lia.
      intros k Hk. replace (S start + k) with (start + S k) by lia.
      apply Hwf. lia. }
    rewrite Heq in Hfst. simpl in Hfst.
    simpl. rewrite Hfst. reflexivity.
Qed.

(* ================================================================== *)
(* Opcode: small positive integers are identity under Z.land _ (Z.ones 32) *)
(* ================================================================== *)

Lemma small_Z_land_ones_32 : forall z,
  (0 <= z < 4294967296)%Z ->
  Z.land z (Z.ones 32) = z.
Proof.
  intros z Hz.
  apply land_mask_32_id. lia.
Qed.

(* ================================================================== *)
(* Main roundtrip theorem                                              *)
(* ================================================================== *)

Definition decode (data : list Z) : list instruction :=
  decode_bytecode data 0 (List.length data).

(* ------------------------------------------------------------------ *)
(* The inductive core: decode_raw_aux on encoded instructions produces  *)
(* the raw instructions that resolve_all will turn back into code.     *)
(* ------------------------------------------------------------------ *)

(* We need a strong induction lemma about decode_raw_aux on encoded bytes.
   The key challenge: decode_raw_aux operates on the FULL data byte list,
   using a position pointer, while encode_instrs concatenates per-instruction
   byte blocks. We bridge this with the read_*_app_l/app_r lemmas.

   The approach:
   - data = encode_bytecode full_code  (the complete encoded program)
   - code_offset = 0
   - code_length = length data
   - We induct on the suffix of code starting at instruction idx,
     with pos = 4 * word_offset_of full_code idx being the byte position.
*)

(* Helper: encode_instrs as suffix of encode_bytecode *)
Lemma encode_instrs_suffix : forall omap idx code_prefix code_suffix,
  encode_instrs omap idx (code_prefix ++ code_suffix) =
    encode_instrs omap idx code_prefix ++
    encode_instrs omap (idx + List.length code_prefix) code_suffix.
Proof.
  intros omap idx code_prefix.
  revert idx.
  induction code_prefix as [|i rest IH]; intros idx code_suffix.
  - simpl. replace (idx + 0) with idx by lia. reflexivity.
  - simpl encode_instrs at 1.
    rewrite IH.
    rewrite app_assoc.
    replace (S idx + List.length rest) with (idx + S (List.length rest)) by lia.
    reflexivity.
Qed.

(* Total word size as fold *)
Lemma total_word_size_cons : forall i rest,
  total_word_size (i :: rest) = instr_word_size i + total_word_size rest.
Proof.
  intros i rest. unfold total_word_size. simpl.
  rewrite fold_left_add_acc. lia.
Qed.

(* word_offset_of relates to total_word_size *)
Lemma word_offset_of_length : forall code,
  word_offset_of code (List.length code) = total_word_size code.
Proof.
  induction code as [|i rest IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite total_word_size_cons. lia.
Qed.

(* The position for instruction idx is 4 * word_offset_of code idx *)
Lemma encode_instrs_split_at : forall code idx omap,
  idx <= List.length code ->
  encode_instrs omap 0 code =
    encode_instrs omap 0 (firstn idx code) ++
    encode_instrs omap idx (skipn idx code).
Proof.
  intros code idx omap Hle.
  rewrite <- (firstn_skipn idx code) at 1.
  rewrite encode_instrs_suffix.
  rewrite firstn_length_le by lia.
  replace (0 + idx) with idx by lia.
  reflexivity.
Qed.

(* word_offset_of = fold_left of instr_word_size over the prefix *)
Lemma word_offset_of_fold : forall code idx,
  idx <= List.length code ->
  word_offset_of code idx =
    fold_left (fun acc i => acc + instr_word_size i) (firstn idx code) 0.
Proof.
  induction code as [|i rest IH]; intros idx Hle.
  - destruct idx; simpl; [reflexivity | lia].
  - destruct idx as [|idx'].
    + simpl. reflexivity.
    + simpl firstn. simpl word_offset_of.
      simpl fold_left. rewrite fold_left_add_acc.
      rewrite <- IH by (simpl in Hle; lia).
      lia.
Qed.

(* Length of encode_instrs for prefix = 4 * word_offset_of *)
Lemma encode_instrs_prefix_length : forall code idx omap,
  idx <= List.length code ->
  List.length (encode_instrs omap 0 (firstn idx code)) =
    4 * word_offset_of code idx.
Proof.
  intros code idx omap Hle.
  rewrite encode_instrs_length.
  rewrite word_offset_of_fold by assumption.
  reflexivity.
Qed.

(* ================================================================== *)
(* Expected raw instruction for each encoded instruction               *)
(* ================================================================== *)

(* Given the encoder's offset map and instruction, what raw_instr
   does decode_raw_aux produce? *)
Local Open Scope Z_scope.

Definition expected_raw (omap : list nat) (idx : nat)
    (i : instruction) (woff : nat) : raw_instr :=
  let w := Z.of_nat (match nth_error omap idx with
                      | Some n => n | None => 0 end) in
  match i with
  | ACC n => mk_raw woff 8 [Z.of_nat n]
  | PUSH => mk_raw woff 9 []
  | PUSHACC n => mk_raw woff 18 [Z.of_nat n]
  | POP n => mk_raw woff 19 [Z.of_nat n]
  | ASSIGN n => mk_raw woff 20 [Z.of_nat n]
  | ENVACC n => mk_raw woff 25 [Z.of_nat n]
  | PUSHENVACC n => mk_raw woff 30 [Z.of_nat n]
  | PUSH_RETADDR t => mk_raw woff 31 [rel_offset omap (w + 1) t]
  | APPLY n => mk_raw woff 32 [Z.of_nat n]
  | APPLY1 => mk_raw woff 33 []
  | APPLY2 => mk_raw woff 34 []
  | APPLY3 => mk_raw woff 35 []
  | APPTERM n s => mk_raw woff 36 [Z.of_nat n; Z.of_nat s]
  | APPTERM1 s => mk_raw woff 37 [Z.of_nat s]
  | APPTERM2 s => mk_raw woff 38 [Z.of_nat s]
  | APPTERM3 s => mk_raw woff 39 [Z.of_nat s]
  | RETURN n => mk_raw woff 40 [Z.of_nat n]
  | RESTART => mk_raw woff 41 []
  | GRAB n => mk_raw woff 42 [Z.of_nat n]
  | CLOSURE nv cp => mk_raw woff 43 [Z.of_nat nv; rel_offset omap (w + 2) cp]
  | CLOSUREREC nf nv ofs =>
      mk_raw woff 44
        (Z.of_nat nf :: Z.of_nat nv ::
         List.map (fun t => rel_offset omap (w + 3) t) ofs)
  | OFFSETCLOSURE v => mk_raw woff 48 [v]
  | PUSHOFFSETCLOSURE v => mk_raw woff 52 [v]
  | GETGLOBAL n => mk_raw woff 53 [Z.of_nat n]
  | PUSHGETGLOBAL n => mk_raw woff 54 [Z.of_nat n]
  | GETGLOBALFIELD n p => mk_raw woff 55 [Z.of_nat n; Z.of_nat p]
  | PUSHGETGLOBALFIELD n p => mk_raw woff 56 [Z.of_nat n; Z.of_nat p]
  | SETGLOBAL n => mk_raw woff 57 [Z.of_nat n]
  | ATOM t => mk_raw woff 59 [Z.of_nat t]
  | PUSHATOM t => mk_raw woff 61 [Z.of_nat t]
  | MAKEBLOCK tag sz => mk_raw woff 62 [Z.of_nat sz; Z.of_nat tag]
  | MAKEBLOCK1 t => mk_raw woff 63 [Z.of_nat t]
  | MAKEBLOCK2 t => mk_raw woff 64 [Z.of_nat t]
  | MAKEBLOCK3 t => mk_raw woff 65 [Z.of_nat t]
  | MAKEFLOATBLOCK s => mk_raw woff 66 [Z.of_nat s]
  | GETFIELD n => mk_raw woff 71 [Z.of_nat n]
  | GETFLOATFIELD n => mk_raw woff 72 [Z.of_nat n]
  | SETFIELD n => mk_raw woff 77 [Z.of_nat n]
  | SETFLOATFIELD n => mk_raw woff 78 [Z.of_nat n]
  | VECTLENGTH => mk_raw woff 79 []
  | GETVECTITEM => mk_raw woff 80 []
  | SETVECTITEM => mk_raw woff 81 []
  | GETBYTESCHAR => mk_raw woff 82 []
  | SETBYTESCHAR => mk_raw woff 83 []
  | GETSTRINGCHAR => mk_raw woff 148 []
  | BRANCH t => mk_raw woff 84 [rel_offset omap (w + 1) t]
  | BRANCHIF t => mk_raw woff 85 [rel_offset omap (w + 1) t]
  | BRANCHIFNOT t => mk_raw woff 86 [rel_offset omap (w + 1) t]
  | SWITCH nc nb ct bt =>
      let sizes := Z.lor (Z.of_nat nc) (Z.shiftl (Z.of_nat nb) 16) in
      mk_raw woff 87
        (sizes ::
         List.map (fun t => rel_offset omap (w + 2) t) ct ++
         List.map (fun t => rel_offset omap (w + 2) t) bt)
  | BOOLNOT => mk_raw woff 88 []
  | PUSHTRAP t => mk_raw woff 89 [rel_offset omap (w + 1) t]
  | POPTRAP => mk_raw woff 90 []
  | RAISE => mk_raw woff 91 []
  | RERAISE => mk_raw woff 146 []
  | RAISE_NOTRACE => mk_raw woff 147 []
  | CHECK_SIGNALS => mk_raw woff 92 []
  | C_CALL narg prim => mk_raw woff 98 [Z.of_nat narg; Z.of_nat prim]
  | CONSTINT v => mk_raw woff 103 [v]
  | PUSHCONSTINT v => mk_raw woff 108 [v]
  | NEGINT => mk_raw woff 109 []
  | ADDINT => mk_raw woff 110 []
  | SUBINT => mk_raw woff 111 []
  | MULINT => mk_raw woff 112 []
  | DIVINT => mk_raw woff 113 []
  | MODINT => mk_raw woff 114 []
  | ANDINT => mk_raw woff 115 []
  | ORINT => mk_raw woff 116 []
  | XORINT => mk_raw woff 117 []
  | LSLINT => mk_raw woff 118 []
  | LSRINT => mk_raw woff 119 []
  | ASRINT => mk_raw woff 120 []
  | EQ => mk_raw woff 121 []
  | NEQ => mk_raw woff 122 []
  | LTINT => mk_raw woff 123 []
  | LEINT => mk_raw woff 124 []
  | GTINT => mk_raw woff 125 []
  | GEINT => mk_raw woff 126 []
  | OFFSETINT v => mk_raw woff 127 [v]
  | OFFSETREF v => mk_raw woff 128 [v]
  | ISINT => mk_raw woff 129 []
  | GETMETHOD => mk_raw woff 130 []
  | BEQ n t => mk_raw woff 131 [n; rel_offset omap (w + 2) t]
  | BNEQ n t => mk_raw woff 132 [n; rel_offset omap (w + 2) t]
  | BLTINT n t => mk_raw woff 133 [n; rel_offset omap (w + 2) t]
  | BLEINT n t => mk_raw woff 134 [n; rel_offset omap (w + 2) t]
  | BGTINT n t => mk_raw woff 135 [n; rel_offset omap (w + 2) t]
  | BGEINT n t => mk_raw woff 136 [n; rel_offset omap (w + 2) t]
  | ULTINT => mk_raw woff 137 []
  | UGEINT => mk_raw woff 138 []
  | BULTINT n t => mk_raw woff 139 [n; rel_offset omap (w + 2) t]
  | BUGEINT n t => mk_raw woff 140 [n; rel_offset omap (w + 2) t]
  | GETPUBMET t => mk_raw woff 141 [t]
  | GETDYNMET => mk_raw woff 142 []
  | STOP => mk_raw woff 143 []
  | EVENT => mk_raw woff 144 []
  | BREAK => mk_raw woff 145 []
  | PERFORM => mk_raw woff 149 []
  | RESUME => mk_raw woff 150 []
  | RESUMETERM n => mk_raw woff 151 [Z.of_nat n]
  | REPERFORMTERM n => mk_raw woff 152 [Z.of_nat n]
  end.

Local Close Scope Z_scope.

(* The expected raw instructions for a list of instructions *)
Fixpoint expected_raws (omap : list nat) (idx : nat)
    (code : list instruction) (woff : nat) : list raw_instr :=
  match code with
  | [] => []
  | i :: rest =>
      expected_raw omap idx i woff ::
      expected_raws omap (S idx) rest (woff + instr_word_size i)
  end.

(* ================================================================== *)
(* Layer 2: resolve_one on expected_raw recovers original instruction  *)
(* ================================================================== *)

(* For resolve_one to work, we need the decoder's offset map (built from
   the raw instructions) to be consistent with the encoder's offset map.

   Key property: if raw instruction k has ri_word_offset = word_offset_of code k,
   then the decoder's lookup_offset inverts the encoder's lookup_offset.

   Specifically, for a branch target t in instruction idx:
   - Encoder stores: rel_offset enc_omap from_word t
                    = lookup_offset enc_omap t - from_word
                    = word_offset_of code (Z.to_nat t) - from_word
   - Decoder reads this value, then resolve_branch computes:
     resolve_branch dec_omap from_word rel
     = Z.of_nat (lookup_offset dec_omap (Z.to_nat (from_word + rel)))
     = Z.of_nat (lookup_offset dec_omap (Z.to_nat (from_word + word_offset_of code (Z.to_nat t) - from_word)))
     = Z.of_nat (lookup_offset dec_omap (word_offset_of code (Z.to_nat t)))
     = Z.of_nat (Z.to_nat t)  [by offset map consistency]
     = t  [since t >= 0 by well-formedness]
*)

(* ================================================================== *)
(* Main roundtrip theorem                                              *)
(* ================================================================== *)

(* The proof decomposes into:
   Layer 1: decode_raw_aux on encode_bytecode produces expected_raws
   Layer 2: resolve_one on each expected_raw recovers the original instruction
   Layer 3: The decoder's offset map is consistent with the encoder's

   All three layers require case analysis over ~107 instruction variants.
   The helper lemmas above establish all the properties needed for each case.
   The main theorem is Admitted while these case analyses are completed. *)

(* Sanity check: the roundtrip works on a concrete program by computation *)
Lemma decode_encode_STOP : decode (encode_bytecode [STOP]) = [STOP].
Proof. native_compute. reflexivity. Qed.

Lemma decode_encode_PUSH_STOP :
  decode (encode_bytecode [PUSH; STOP]) = [PUSH; STOP].
Proof. native_compute. reflexivity. Qed.

Lemma decode_encode_ACC_STOP :
  decode (encode_bytecode [ACC 3; STOP]) = [ACC 3; STOP].
Proof. native_compute. reflexivity. Qed.

Lemma decode_encode_BRANCH :
  decode (encode_bytecode [BRANCH 1; STOP]) = [BRANCH 1; STOP].
Proof. native_compute. reflexivity. Qed.

(* ================================================================== *)
(* Layer 1 (partial): decode_raw step for zero-operand instructions    *)
(* ================================================================== *)

(* For a zero-operand instruction with opcode op (not 87, 44, 141),
   decode_raw_aux on emit_words [op] ++ rest_bytes produces
   mk_raw (pos/4) op [] :: decode_raw_aux ... rest_bytes. *)

Lemma decode_raw_aux_zero_op :
  forall data total_len pos fuel op rest_raw,
    pos + 4 <= total_len ->
    read_u32_le data pos = op ->
    (Z.eqb op 87 = false)%Z ->
    (Z.eqb op 44 = false)%Z ->
    (Z.eqb op 141 = false)%Z ->
    operand_count op = Some 0%nat ->
    decode_raw_aux data 0 total_len (pos + 4) fuel = rest_raw ->
    decode_raw_aux data 0 total_len pos (S fuel) =
      mk_raw (pos / 4) op [] :: rest_raw.
Proof.
  intros data total_len pos fuel op rest_raw Hpos Hread H87 H44 H141 Hcount Hrest.
  simpl decode_raw_aux.
  destruct (Nat.leb total_len pos) eqn:Hleb.
  - apply Nat.leb_le in Hleb. lia.
  - replace (0 + pos) with pos by lia.
    rewrite Hread, H87, H44, H141, Hcount.
    change (read_operands data 0 (pos + 4) 0) with (@nil Z, pos + 4).
    subst rest_raw. reflexivity.
Qed.

(* For a one-operand instruction (not 87, 44, 141), decode_raw_aux on
   data at position pos produces mk_raw (pos/4) op [operand] :: rest. *)
Lemma decode_raw_aux_one_op :
  forall data total_len pos fuel op operand rest_raw,
    pos + 4 <= total_len ->
    read_u32_le data pos = op ->
    (Z.eqb op 87 = false)%Z ->
    (Z.eqb op 44 = false)%Z ->
    (Z.eqb op 141 = false)%Z ->
    operand_count op = Some 1%nat ->
    read_i32_le data (pos + 4) = operand ->
    decode_raw_aux data 0 total_len (pos + 8) fuel = rest_raw ->
    decode_raw_aux data 0 total_len pos (S fuel) =
      mk_raw (pos / 4) op [operand] :: rest_raw.
Proof.
  intros data total_len pos fuel op operand rest_raw
    Hpos Hread H87 H44 H141 Hcount Hop1 Hrest.
  simpl decode_raw_aux.
  destruct (Nat.leb total_len pos) eqn:Hleb.
  - apply Nat.leb_le in Hleb. lia.
  - replace (0 + pos) with pos by lia.
    rewrite Hread, H87, H44, H141, Hcount.
    (* read_operands data 0 (pos+4) 1 = (read_i32_le data (0+(pos+4)) :: nil, pos+4+4) *)
    simpl read_operands.
    replace (0 + (pos + 4)) with (pos + 4) by lia.
    rewrite Hop1.
    replace (pos + 4 + 4) with (pos + 8) by lia.
    subst rest_raw. reflexivity.
Qed.

(* For a two-operand instruction *)
Lemma decode_raw_aux_two_op :
  forall data total_len pos fuel op op1 op2 rest_raw,
    pos + 4 <= total_len ->
    read_u32_le data pos = op ->
    (Z.eqb op 87 = false)%Z ->
    (Z.eqb op 44 = false)%Z ->
    (Z.eqb op 141 = false)%Z ->
    operand_count op = Some 2%nat ->
    read_i32_le data (pos + 4) = op1 ->
    read_i32_le data (pos + 8) = op2 ->
    decode_raw_aux data 0 total_len (pos + 12) fuel = rest_raw ->
    decode_raw_aux data 0 total_len pos (S fuel) =
      mk_raw (pos / 4) op [op1; op2] :: rest_raw.
Proof.
  intros data total_len pos fuel op op1 op2 rest_raw
    Hpos Hread H87 H44 H141 Hcount Hop1 Hop2 Hrest.
  simpl decode_raw_aux.
  destruct (Nat.leb total_len pos) eqn:Hleb.
  - apply Nat.leb_le in Hleb. lia.
  - replace (0 + pos) with pos by lia.
    rewrite Hread, H87, H44, H141, Hcount.
    (* Manually reduce read_operands for n=2 *)
    change (read_operands data 0 (pos + 4) 2) with
      (let v1 := read_i32_le data (0 + (pos + 4))%nat in
       let '(r1, p1) := read_operands data 0 ((pos + 4) + 4)%nat 1 in
       (v1 :: r1, p1)).
    change (read_operands data 0 ((pos + 4) + 4) 1) with
      (let v2 := read_i32_le data (0 + ((pos + 4) + 4))%nat in
       let '(r2, p2) := read_operands data 0 (((pos + 4) + 4) + 4)%nat 0 in
       (v2 :: r2, p2)).
    change (read_operands data 0 (((pos + 4) + 4) + 4) 0)
      with (@nil Z, ((pos + 4) + 4) + 4).
    replace (0 + (pos + 4))%nat with (pos + 4) by lia.
    rewrite Hop1.
    replace (0 + ((pos + 4) + 4))%nat with (pos + 8) by lia.
    rewrite Hop2.
    replace (((pos + 4) + 4) + 4) with (pos + 12) by lia.
    subst rest_raw. reflexivity.
Qed.

(* GETPUBMET (opcode 141) step lemma *)
Lemma decode_raw_aux_getpubmet :
  forall data total_len pos fuel tag rest_raw,
    pos + 4 <= total_len ->
    read_u32_le data pos = 141%Z ->
    read_i32_le data (pos + 4) = tag ->
    decode_raw_aux data 0 total_len (pos + 12) fuel = rest_raw ->
    decode_raw_aux data 0 total_len pos (S fuel) =
      mk_raw (pos / 4) 141%Z [tag] :: rest_raw.
Proof.
  intros data total_len pos fuel tag rest_raw
    Hpos Hread Htag Hrest.
  simpl decode_raw_aux.
  destruct (Nat.leb total_len pos) eqn:Hleb.
  - apply Nat.leb_le in Hleb. lia.
  - replace (0 + pos) with pos by lia.
    rewrite Hread. simpl Z.eqb.
    replace (0 + (pos + 4)) with (pos + 4) by lia.
    rewrite Htag.
    replace (pos + 4 + 4 + 4) with (pos + 12) by lia.
    subst rest_raw. reflexivity.
Qed.

(* ================================================================== *)
(* Layer 2: resolve_one on expected_raw recovers original instruction  *)
(* ================================================================== *)

(* For non-branch instructions with nat operands, resolve_one just
   applies nat_of_z to each operand, recovering the original value.
   For branch instructions, we need the resolve_branch_correct hypothesis
   which says the decoder's offset map inverts the encoder's rel_offset. *)

(* Helper: nth_error on offset_map at a valid index yields word_offset_of *)
Lemma enc_omap_nth_error : forall code idx,
  idx < List.length code ->
  nth_error (offset_map code) idx = Some (word_offset_of code idx).
Proof.
  intros. apply offset_map_correct. exact H.
Qed.

(* Helper: the w computed in expected_raw equals Z.of_nat woff when omap
   and woff are the encoder's offset_map/word_offset_of *)
Lemma enc_w_eq : forall code idx,
  idx < List.length code ->
  Z.of_nat (match nth_error (offset_map code) idx with
            | Some n => n | None => 0 end) =
  Z.of_nat (word_offset_of code idx).
Proof.
  intros code idx Hlt.
  rewrite enc_omap_nth_error by exact Hlt. reflexivity.
Qed.

(* Helper: extract valid_targetb info *)
Lemma valid_targetb_props : forall n t,
  valid_targetb n t = true ->
  (0 <= t)%Z /\ Z.to_nat t < n.
Proof.
  intros n t H. unfold valid_targetb in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Nat.ltb_lt in H2.
  split; assumption.
Qed.

(* Helper for CLOSUREREC: resolve_branch over a mapped list *)
Lemma resolve_branch_map_rel_offset :
  forall dec_omap enc_omap base targets n,
    (forall t from, (0 <= t)%Z -> Z.to_nat t < n ->
       resolve_branch dec_omap from (rel_offset enc_omap from t) = t) ->
    all_valid_targetsb n targets = true ->
    map (fun o => resolve_branch dec_omap base o)
        (map (fun t => rel_offset enc_omap base t) targets) = targets.
Proof.
  intros dec_omap enc_omap base targets n Hbranch Hvalid.
  induction targets as [|t rest IH].
  - reflexivity.
  - simpl in Hvalid. apply Bool.andb_true_iff in Hvalid.
    destruct Hvalid as [Ht Hrest].
    simpl. rewrite Hbranch.
    + f_equal. apply IH. exact Hrest.
    + apply valid_targetb_props in Ht. tauto.
    + apply valid_targetb_props in Ht. tauto.
Qed.

(* Helper: the local fix resolve_list in resolve_one for CLOSUREREC
   is equivalent to map (fun o => resolve_branch omap base o) *)
Lemma resolve_list_is_map : forall dec_omap base ofs,
  (fix resolve_list (ofs_list : list Z) : list Z :=
    match ofs_list with
    | [] => []
    | o :: rest => resolve_branch dec_omap base o :: resolve_list rest
    end) ofs = map (fun o => resolve_branch dec_omap base o) ofs.
Proof.
  intros. induction ofs as [|o rest IH]; simpl; [reflexivity | f_equal; exact IH].
Qed.

(* Helper: for SWITCH, resolve_n is also equivalent to a map *)
Lemma resolve_n_is_map : forall dec_omap base ops start count,
  (fix resolve_n (s : nat) (c : nat) : list Z :=
    match c with
    | O => []
    | S c' => resolve_branch dec_omap base (znth (S s) ops) :: resolve_n (S s) c'
    end) start count =
  map (fun k => resolve_branch dec_omap base (znth (S k) ops)) (seq start count).
Proof.
  intros. revert start.
  induction count as [|c' IH]; intros start; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

(* ---- SWITCH helpers: sizes encoding roundtrip ---- *)

(* Low 16 bits of Z.lor nc (Z.shiftl nb 16) = nc *)
Lemma lor_land_low16 : forall nc nb : nat,
  (Z.of_nat nc < 2^16)%Z ->
  (Z.of_nat nb < 2^16)%Z ->
  Z.land (Z.lor (Z.of_nat nc) (Z.shiftl (Z.of_nat nb) 16)) (Z.ones 16)
  = Z.of_nat nc.
Proof.
  intros nc nb Hnc Hnb.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z_lt_dec i 16).
  - rewrite Z.ones_spec_low by lia.
    rewrite Bool.andb_true_r.
    rewrite (Z.testbit_neg_r (Z.of_nat nb) (i - 16)) by lia.
    rewrite Bool.orb_false_r. reflexivity.
  - rewrite Z.ones_spec_high by lia.
    rewrite Bool.andb_false_r.
    symmetry. apply Z.bits_above_log2; try lia.
    destruct (Z.eq_dec (Z.of_nat nc) 0%Z).
    + rewrite e. simpl. lia.
    + pose proof (Z.log2_lt_pow2 (Z.of_nat nc) 16 ltac:(lia)). lia.
Qed.

(* High 16 bits: Z.shiftr (Z.lor nc (Z.shiftl nb 16)) 16 = nb *)
Lemma lor_shiftr_high16 : forall nc nb : nat,
  (Z.of_nat nc < 2^16)%Z ->
  (Z.of_nat nb < 2^16)%Z ->
  Z.shiftr (Z.lor (Z.of_nat nc) (Z.shiftl (Z.of_nat nb) 16)) 16
  = Z.of_nat nb.
Proof.
  intros nc nb Hnc Hnb.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  replace (i + 16 - 16)%Z with i by lia.
  assert (Hnc_high : Z.testbit (Z.of_nat nc) (i + 16) = false).
  { apply Z.bits_above_log2; try lia.
    destruct (Z.eq_dec (Z.of_nat nc) 0%Z).
    - rewrite e. simpl. lia.
    - pose proof (Z.log2_lt_pow2 (Z.of_nat nc) 16 ltac:(lia)). lia. }
  rewrite Hnc_high. simpl. reflexivity.
Qed.

(* Helper: znth on appended lists *)
Lemma znth_app_l : forall k (l1 l2 : list Z),
  k < List.length l1 ->
  znth k (l1 ++ l2) = znth k l1.
Proof.
  intros k l1 l2 Hk. unfold znth.
  rewrite nth_error_app1 by assumption. reflexivity.
Qed.

Lemma znth_app_r : forall k (l1 l2 : list Z),
  List.length l1 <= k ->
  znth k (l1 ++ l2) = znth (k - List.length l1) l2.
Proof.
  intros k l1 l2 Hk. unfold znth.
  rewrite nth_error_app2 by assumption. reflexivity.
Qed.

(* Helper: znth on a map *)
Lemma znth_map : forall k (f : Z -> Z) (l : list Z),
  k < List.length l ->
  znth k (map f l) = f (nth k l 0%Z).
Proof.
  intros k f l Hk. unfold znth.
  rewrite nth_error_map.
  destruct (nth_error l k) eqn:E.
  - simpl. f_equal.
    symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E. lia.
Qed.

(* resolve_n recovers targets from the ops list *)
Lemma resolve_n_recover :
  forall dec_omap enc_omap base (targets : list Z) (ops : list Z)
         (start : nat) (n : nat),
    (forall t from : Z,
       (0 <= t)%Z -> Z.to_nat t < n ->
       resolve_branch dec_omap from (rel_offset enc_omap from t) = t) ->
    all_valid_targetsb n targets = true ->
    (forall k, k < List.length targets ->
       znth (S (start + k)) ops =
         nth k (map (fun t => rel_offset enc_omap base t) targets) 0%Z) ->
    (fix resolve_n (s : nat) (c : nat) : list Z :=
       match c with
       | O => []
       | S c' =>
         resolve_branch dec_omap base (znth (S s) ops) :: resolve_n (S s) c'
       end) start (List.length targets) = targets.
Proof.
  intros dec_omap enc_omap base targets ops start n Hbranch Hvalid Hops.
  revert start Hops.
  induction targets as [|t rest IH]; intros start Hops.
  - simpl. reflexivity.
  - simpl in Hvalid. apply Bool.andb_true_iff in Hvalid.
    destruct Hvalid as [Ht Hrest].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    simpl length.
    simpl.
    assert (Hop0 : znth (S start) ops = rel_offset enc_omap base t).
    { specialize (Hops 0%nat ltac:(simpl; lia)).
      replace (start + 0) with start in Hops by lia.
      simpl in Hops. exact Hops. }
    rewrite Hop0.
    rewrite Hbranch by assumption.
    f_equal.
    apply IH.
    + exact Hrest.
    + intros k Hk.
      specialize (Hops (S k) ltac:(simpl; lia)).
      replace (start + S k) with (S start + k) in Hops by lia.
      simpl in Hops. exact Hops.
Qed.

(* nat_fits_i32b implies the nat < 2^16 constraint we need for SWITCH.
   Actually we need a tighter bound. For SWITCH, nc and nb fit in 16 bits.
   But wf_instrb only checks nat_fits_i32b. We need nc < 2^16 and nb < 2^16
   which is guaranteed by nat_fits_i32b (since 2^16 < 2^31).
   Actually nat_fits_i32b only bounds below 2^31, not 2^16.
   But the Z.land/Z.shiftr roundtrip works as long as values are nonneg. *)

(* Actually, the SWITCH sizes encoding works for any nonneg nc, nb < 2^16.
   We need to derive this from wf_instrb somehow. Let me check... actually
   wf_instrb only checks nat_fits_i32b for nc and nb, which means they're
   < 2^31. But the encoding packs them into 32 bits as low16/high16.
   For this to roundtrip, we need nc < 2^16 AND nb < 2^16.

   However, in practice OCaml's SWITCH instruction packs sizes in 16 bits,
   so nc and nb must be < 2^16. But our wf_instrb doesn't enforce this.

   This means the roundtrip for SWITCH only works if nc < 2^16 and nb < 2^16.
   For now, let's add these as assumptions and prove the SWITCH case. *)

(* Helper tactic: simplify resolve_one after unfolding.
   Since resolve_one, znth, nat_of_z are in a separate theory (Manual.Bytecode),
   simpl alone does not unfold them. We unfold resolve_one, then reduce the
   Z.eqb if-then-else chain, then handle znth/nat_of_z/skipn. *)
Local Ltac resolve_simpl :=
  unfold resolve_one;
  simpl ri_opcode; simpl ri_operands; simpl ri_word_offset;
  simpl Z.eqb;
  (* After Z.eqb reduction, record accessors may still be present in the
     selected branch body (e.g., in let-bindings). Use cbn to reduce them. *)
  cbn [ri_word_offset ri_operands ri_opcode];
  (* Now reduce znth, nat_of_z, skipn which are from Decode.v *)
  unfold znth; simpl nth_error;
  unfold nat_of_z; rewrite ?Nat2Z.id;
  simpl skipn.

Lemma resolve_one_expected_raw :
  forall (code : list instruction) (enc_omap : list nat)
         (dec_omap : list (nat * nat)) (idx : nat) (i : instruction)
         (woff : nat),
    enc_omap = offset_map code ->
    woff = word_offset_of code idx ->
    idx < List.length code ->
    wf_instrb (List.length code) i = true ->
    (forall t from,
       (0 <= t)%Z ->
       Z.to_nat t < List.length code ->
       resolve_branch dec_omap from (rel_offset enc_omap from t) = t) ->
    resolve_one dec_omap (expected_raw enc_omap idx i woff) = i.
Proof.
  intros code enc_omap dec_omap idx i woff Henc Hwoff Hidx Hwf Hbranch.
  subst enc_omap woff.
  (* Rewrite the w in expected_raw using enc_w_eq *)
  assert (Hw : Z.of_nat (match nth_error (offset_map code) idx with
                          | Some n => n | None => 0 end) =
               Z.of_nat (word_offset_of code idx)).
  { apply enc_w_eq. exact Hidx. }
  (* Set short name for the word offset *)
  set (W := word_offset_of code idx) in *.
  (* Useful Z arithmetic facts for matching resolve_one's Z.of_nat (W + k + n)
     with expected_raw's (Z.of_nat W + k)%Z *)
  assert (HWn : forall a b : nat,
    Z.of_nat (W + a + b) = (Z.of_nat W + Z.of_nat (a + b))%Z) by lia.
  assert (HW2 : Z.of_nat (W + 2) = (Z.of_nat W + 2)%Z) by lia.
  assert (HW3 : Z.of_nat (W + 3) = (Z.of_nat W + 3)%Z) by lia.
  destruct i; simpl expected_raw; rewrite ?Hw;
    resolve_simpl;
    try reflexivity.
  (* Branch-target instructions remain. For each, we need to apply Hbranch. *)
  (* PUSH_RETADDR t -- branch at br 0, from = Z.of_nat (W+1+0) *)
  - simpl wf_instrb in Hwf.
    apply valid_targetb_props in Hwf. destruct Hwf as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* CLOSURE nv codeptr -- from = Z.of_nat (W+2) *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hnv Hcp].
    apply valid_targetb_props in Hcp. destruct Hcp as [Hcp0 Hcplt].
    rewrite HW2.
    rewrite Hbranch by assumption.
    reflexivity.
  (* CLOSUREREC nf nv ofs *)
  - simpl wf_instrb in Hwf.
    repeat (apply Bool.andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
    (* Hwf : nat_fits_i32b n, H0 : all_valid_targetsb ... l = true,
       H : Nat.eqb (length l) n = true *)
    (* After resolve_simpl, the fix resolve_list is applied to
       map (rel_offset ...) l, with base = Z.of_nat (W + 3).
       The rel_offset uses (Z.of_nat W + 3)%Z. Unify them. *)
    replace (Z.of_nat (W + 3)) with (Z.of_nat W + 3)%Z by lia.
    rewrite resolve_list_is_map.
    apply f_equal.
    apply resolve_branch_map_rel_offset with (n := List.length code); auto.
  (* BRANCH t *)
  - simpl wf_instrb in Hwf.
    apply valid_targetb_props in Hwf. destruct Hwf as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BRANCHIF t *)
  - simpl wf_instrb in Hwf.
    apply valid_targetb_props in Hwf. destruct Hwf as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BRANCHIFNOT t *)
  - simpl wf_instrb in Hwf.
    apply valid_targetb_props in Hwf. destruct Hwf as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* SWITCH nc nb ct bt *)
  - simpl wf_instrb in Hwf.
    repeat (apply Bool.andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
    (* Hwf : Nat.eqb (length l) n, H2 : Nat.eqb (length l0) n0,
       H1 : all_valid_targetsb ... l, H0 : all_valid_targetsb ... l0,
       H : Nat.ltb n 65536, latest: Nat.ltb n0 32768 *)
    rename H into Hnc16, H3 into Hnb15.
    apply Nat.ltb_lt in Hnc16. apply Nat.ltb_lt in Hnb15.
    apply Nat.eqb_eq in Hwf. apply Nat.eqb_eq in H2.
    (* Now we have nc < 2^16, nb < 2^15 < 2^16 *)
    set (sizes := Z.lor (Z.of_nat n) (Z.shiftl (Z.of_nat n0) 16)) in *.
    (* Show Z.to_nat (Z.land sizes (Z.ones 16)) = n *)
    assert (Hnc_eq : Z.to_nat (Z.land sizes (Z.ones 16)) = n).
    { subst sizes. rewrite lor_land_low16 by lia. lia. }
    (* Show Z.to_nat (Z.shiftr sizes 16) = n0 *)
    assert (Hnb_eq : Z.to_nat (Z.shiftr sizes 16) = n0).
    { subst sizes. rewrite lor_shiftr_high16 by lia. lia. }
    rewrite Hnc_eq, Hnb_eq.
    (* Now we need resolve_n to recover l and l0 *)
    rewrite !resolve_n_is_map.
    (* The ops list is: sizes :: map (rel_offset ...) l ++ map (rel_offset ...) l0.
       We need to show that resolve_branch applied to each element recovers the targets. *)
    replace (Z.of_nat (W + 2)) with (Z.of_nat W + 2)%Z by lia.
    f_equal.
    + (* const table: map over seq 0 n *)
      apply map_ext_in. intros k Hk.
      apply in_seq in Hk. destruct Hk as [_ Hk].
      (* znth (S k) (sizes :: ct_rels ++ bt_rels) = nth k ct_rels 0 *)
      unfold znth. simpl nth_error.
      rewrite nth_error_app1 by (rewrite map_length; lia).
      rewrite nth_error_map.
      destruct (nth_error l k) eqn:Ek.
      * simpl. apply Hbranch.
        -- apply forallb_forall in H1.
           apply (H1 z). eapply nth_error_In. exact Ek.
           Unshelve.
           apply valid_targetb_props.
           apply forallb_forall in H1.
           apply (H1 z). eapply nth_error_In. exact Ek.
        -- apply valid_targetb_props.
           apply forallb_forall in H1.
           apply (H1 z). eapply nth_error_In. exact Ek.
      * apply nth_error_None in Ek. lia.
    + (* block table: map over seq n n0 *)
      apply map_ext_in. intros k Hk.
      apply in_seq in Hk. destruct Hk as [Hkge Hklt].
      unfold znth. simpl nth_error.
      rewrite nth_error_app2 by (rewrite map_length; lia).
      rewrite map_length. replace (k - n) with (k - n) by lia.
      rewrite nth_error_map.
      destruct (nth_error l0 (k - n)) eqn:Ek.
      * simpl. apply Hbranch.
        -- apply forallb_forall in H0.
           apply (H0 z). eapply nth_error_In. exact Ek.
           Unshelve.
           apply valid_targetb_props.
           apply forallb_forall in H0.
           apply (H0 z). eapply nth_error_In. exact Ek.
        -- apply valid_targetb_props.
           apply forallb_forall in H0.
           apply (H0 z). eapply nth_error_In. exact Ek.
      * apply nth_error_None in Ek. lia.
  (* PUSHTRAP t *)
  - simpl wf_instrb in Hwf.
    apply valid_targetb_props in Hwf. destruct Hwf as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BEQ n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BNEQ n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BLTINT n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BLEINT n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BGTINT n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BGEINT n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BULTINT n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
  (* BUGEINT n t *)
  - simpl wf_instrb in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hv Ht].
    apply valid_targetb_props in Ht. destruct Ht as [Ht0 Htlt].
    rewrite HWn. simpl Nat.add.
    rewrite Hbranch by assumption.
    reflexivity.
Qed.

(* Corollary: resolve_one works for each instruction in the full program *)
Lemma resolve_one_expected_raw_in_code :
  forall (code : list instruction) (dec_omap : list (nat * nat))
         (idx : nat),
    well_formed code = true ->
    idx < List.length code ->
    (forall t from,
       (0 <= t)%Z ->
       Z.to_nat t < List.length code ->
       resolve_branch dec_omap from
         (rel_offset (offset_map code) from t) = t) ->
    resolve_one dec_omap
      (expected_raw (offset_map code) idx
         (nth idx code STOP) (word_offset_of code idx)) =
      nth idx code STOP.
Proof.
  intros code dec_omap idx Hwf Hidx Hbranch.
  apply resolve_one_expected_raw with (code := code); auto.
  apply wf_instrb_from_well_formed; auto.
  apply nth_In. exact Hidx.
Qed.

(* ================================================================== *)
(* More computational roundtrip tests (concrete programs)              *)
(* ================================================================== *)

(* These demonstrate the theorem holds for specific programs,
   validating the overall architecture. *)

Lemma decode_encode_closure :
  decode (encode_bytecode [CLOSURE 2 1; STOP]) = [CLOSURE 2 1; STOP].
Proof. native_compute. reflexivity. Qed.

Lemma decode_encode_constint_neg :
  decode (encode_bytecode [CONSTINT (-42); STOP]) = [CONSTINT (-42); STOP].
Proof. native_compute. reflexivity. Qed.

Lemma decode_encode_switch :
  well_formed [BRANCH 3; BRANCH 3; SWITCH 1 1 [3%Z] [3%Z]; STOP] = true /\
  decode (encode_bytecode [BRANCH 3; BRANCH 3; SWITCH 1 1 [3%Z] [3%Z]; STOP]) =
    [BRANCH 3; BRANCH 3; SWITCH 1 1 [3%Z] [3%Z]; STOP].
Proof. split; native_compute; reflexivity. Qed.

Lemma decode_encode_closurerec :
  well_formed [CLOSUREREC 2 0 [0%Z; 0%Z]; STOP] = true /\
  decode (encode_bytecode [CLOSUREREC 2 0 [0%Z; 0%Z]; STOP]) =
    [CLOSUREREC 2 0 [0%Z; 0%Z]; STOP].
Proof. split; native_compute; reflexivity. Qed.

Lemma decode_encode_getpubmet :
  decode (encode_bytecode [GETPUBMET 42; STOP]) = [GETPUBMET 42; STOP].
Proof. native_compute. reflexivity. Qed.

Lemma decode_encode_beq :
  well_formed [BEQ 10 1; STOP] = true /\
  decode (encode_bytecode [BEQ 10 1; STOP]) = [BEQ 10 1; STOP].
Proof. split; native_compute; reflexivity. Qed.

Lemma decode_encode_pushtrap :
  well_formed [PUSHTRAP 3; STOP; STOP; STOP] = true /\
  decode (encode_bytecode [PUSHTRAP 3; STOP; STOP; STOP]) =
    [PUSHTRAP 3; STOP; STOP; STOP].
Proof. split; native_compute; reflexivity. Qed.

Lemma decode_encode_many_instrs :
  well_formed [PUSH; ACC 3; CONSTINT 42; NEGINT; ADDINT;
               BRANCH 6; STOP] = true /\
  decode (encode_bytecode [PUSH; ACC 3; CONSTINT 42; NEGINT; ADDINT;
                           BRANCH 6; STOP]) =
    [PUSH; ACC 3; CONSTINT 42; NEGINT; ADDINT; BRANCH 6; STOP].
Proof. split; native_compute; reflexivity. Qed.

(* ================================================================== *)
(* Layer 1: decode_raw on encode_bytecode produces expected_raws       *)
(* ================================================================== *)

(* Helper: word_offset_of for expected_raws *)
Lemma expected_raws_word_offsets : forall omap idx code woff k,
  k < List.length code ->
  ri_word_offset (nth k (expected_raws omap idx code woff) (mk_raw 0 0%Z [])) =
    woff + word_offset_of code k.
Proof.
  intros omap idx code. revert idx.
  induction code as [|i rest IH]; intros idx woff k Hk.
  - simpl in Hk. lia.
  - destruct k as [|k'].
    + simpl. destruct i; simpl; lia.
    + simpl in Hk. simpl expected_raws. simpl nth.
      rewrite IH by lia.
      simpl word_offset_of. lia.
Qed.

Lemma expected_raws_length : forall omap idx code woff,
  List.length (expected_raws omap idx code woff) = List.length code.
Proof.
  intros omap idx code. revert idx.
  induction code as [|i rest IH]; intros idx woff.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Key property: word offsets in expected_raws are distinct.
   Since word_offset_of is strictly increasing (each instruction has size >= 1),
   all word offsets are distinct. *)
Lemma word_offset_of_strict_mono : forall code j k,
  j < k -> k <= List.length code ->
  word_offset_of code j < word_offset_of code k.
Proof.
  induction code as [|i rest IH]; intros j k Hjk Hk.
  - simpl in Hk. lia.
  - destruct j as [|j']; destruct k as [|k']; try lia.
    + simpl. assert (1 <= instr_word_size i) by (destruct i; simpl; lia). lia.
    + simpl. assert (1 <= instr_word_size i) by (destruct i; simpl; lia).
      simpl in Hk.
      specialize (IH j' k' ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma expected_raws_distinct_offsets : forall omap idx code woff j k,
  j < List.length code ->
  k < List.length code ->
  ri_word_offset (nth j (expected_raws omap idx code woff) (mk_raw 0 0%Z [])) <>
  ri_word_offset (nth k (expected_raws omap idx code woff) (mk_raw 0 0%Z [])) \/
  j = k.
Proof.
  intros omap idx code woff j k Hj Hk.
  destruct (Nat.eq_dec j k) as [|Hne]; [right; assumption | left].
  rewrite !expected_raws_word_offsets by assumption.
  destruct (Nat.lt_ge_cases j k).
  - pose proof (word_offset_of_strict_mono code j k H ltac:(lia)). lia.
  - assert (k < j) by lia.
    pose proof (word_offset_of_strict_mono code k j H0 ltac:(lia)). lia.
Qed.

(* Layer 3: The decoder's offset map from expected_raws correctly inverts
   the encoder's rel_offset. *)

Lemma lookup_offset_expected_raws : forall code omap woff_base idx k,
  omap = offset_map code ->
  k < List.length code ->
  Decode.lookup_offset
    (build_offset_map_aux (expected_raws omap idx code woff_base) 0)
    (woff_base + word_offset_of code k) = k.
Proof.
  intros code omap woff_base idx k Homap Hk.
  rewrite (build_offset_map_aux_correct
    (expected_raws omap idx code woff_base) 0 k).
  - lia.
  - rewrite expected_raws_length. exact Hk.
  - intros j Hj.
    rewrite expected_raws_length in Hj.
    apply expected_raws_distinct_offsets; assumption.
Qed.

(* The resolve_branch with the expected_raws offset map inverts rel_offset *)
Lemma resolve_branch_expected_raws :
  forall code (t from : Z),
    (0 <= t)%Z ->
    Z.to_nat t < List.length code ->
    resolve_branch
      (build_offset_map (expected_raws (offset_map code) 0 code 0))
      from
      (rel_offset (offset_map code) from t) = t.
Proof.
  intros code t from Ht Htlt.
  unfold resolve_branch, rel_offset, Encode.lookup_offset, Encode.rel_offset.
  (* rel_offset omap from t = lookup_offset omap t - from
     = Z.of_nat (word_offset_of code (Z.to_nat t)) - from *)
  rewrite offset_map_correct by exact Htlt.
  (* resolve_branch: target = Z.to_nat (from + (Z.of_nat (word_offset_of ...) - from))
     = word_offset_of code (Z.to_nat t) *)
  replace (from + (Z.of_nat (word_offset_of code (Z.to_nat t)) - from))%Z
    with (Z.of_nat (word_offset_of code (Z.to_nat t))) by lia.
  rewrite Nat2Z.id.
  unfold build_offset_map.
  rewrite lookup_offset_expected_raws with (omap := offset_map code) by (auto; lia).
  lia.
Qed.

(* Now the main theorem combines all layers *)

(* Helper: resolve_all on expected_raws recovers code *)
Lemma resolve_all_expected_raws :
  forall code,
    well_formed code = true ->
    let raws := expected_raws (offset_map code) 0 code 0 in
    map (resolve_one (build_offset_map raws)) raws = code.
Proof.
  intros code Hwf raws.
  subst raws.
  (* We need to show: for each instruction i at index k in code,
     resolve_one (build_offset_map ...) (expected_raw ... k i ...) = i *)
  set (omap := offset_map code).
  set (eraws := expected_raws omap 0 code 0).
  assert (Hlen : List.length eraws = List.length code).
  { subst eraws. apply expected_raws_length. }
  (* Proceed by showing the two lists are equal element-wise *)
  apply nth_ext with (d := STOP) (d' := STOP).
  { rewrite map_length. exact Hlen. }
  intros k Hk.
  rewrite map_length in Hk. rewrite Hlen in Hk.
  rewrite nth_map with (d := mk_raw 0 0%Z []) by (rewrite Hlen; exact Hk).
  (* Show: nth k eraws = expected_raw omap k (nth k code STOP) (word_offset_of code k) *)
  assert (Hnth : nth k eraws (mk_raw 0 0%Z []) =
                 expected_raw omap k (nth k code STOP) (word_offset_of code k)).
  { subst eraws omap.
    clear Hlen Hk. revert k.
    induction code as [|i rest IH]; intros k.
    - destruct k; reflexivity.
    - destruct k as [|k'].
      + simpl. reflexivity.
      + simpl expected_raws. simpl nth.
        rewrite IH.
        simpl word_offset_of.
        reflexivity. }
  rewrite Hnth.
  apply resolve_one_expected_raw_in_code.
  - exact Hwf.
  - exact Hk.
  - intros t from Ht Htlt.
    apply resolve_branch_expected_raws; assumption.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Lemma instr_word_size_ge_1 : forall i, 1 <= instr_word_size i.
Proof. destruct i; simpl; lia. Qed.

(* Layer 1 helper: properties of reading from encode_instr ++ rest_bytes *)

(* Helper to show in_skipn_in for wf_instrb *)
Lemma in_cons_skipn {A : Type} (x : A) (l : list A) (n : nat) :
  In x (skipn n l) -> In x l.
Proof.
  intros H. apply in_skipn_iff in H. destruct H as [j [Hj Hin]].
  eapply nth_error_In. exact Hin.
Qed.

(* Helper: extract the byte-length bound from well_formed *)
Lemma well_formed_byte_bound : forall code,
  well_formed code = true ->
  List.length (encode_bytecode code) <= 2147483647.
Proof.
  intros code Hwf. unfold well_formed in Hwf.
  apply Bool.andb_true_iff in Hwf. destruct Hwf as [_ Hlen].
  apply Nat.leb_le in Hlen. exact Hlen.
Qed.

Lemma well_formed_forallb : forall code,
  well_formed code = true ->
  forallb (wf_instrb (List.length code)) code = true.
Proof.
  intros code Hwf. unfold well_formed in Hwf.
  apply Bool.andb_true_iff in Hwf. tauto.
Qed.

(* Helper: word offsets fit in i32 for well-formed programs *)
Lemma word_offset_fits : forall code idx,
  well_formed code = true ->
  idx <= List.length code ->
  Z.of_nat (word_offset_of code idx) < 536870912.
Proof.
  intros code idx Hwf Hidx.
  assert (Hbl : List.length (encode_bytecode code) <= 2147483647).
  { apply well_formed_byte_bound. exact Hwf. }
  rewrite encode_bytecode_length in Hbl.
  assert (4 * word_offset_of code idx <= 4 * fold_left (fun a i => a + instr_word_size i) code 0).
  { assert (word_offset_of code idx <= total_word_size code).
    { unfold total_word_size.
      destruct (Nat.eq_dec idx (List.length code)).
      - subst. rewrite word_offset_of_length. lia.
      - assert (idx < List.length code) by lia.
        pose proof (word_offset_of_strict_mono code idx (List.length code) H ltac:(lia)).
        rewrite word_offset_of_length in H0. lia. }
    unfold total_word_size in H. lia. }
  lia.
Qed.

(* Relative offsets fit in i32 for well-formed programs *)
Lemma rel_offset_fits_i32b : forall code omap from_word target_idx,
  well_formed code = true ->
  omap = offset_map code ->
  (0 <= target_idx)%Z ->
  Z.to_nat target_idx < List.length code ->
  (0 <= from_word)%Z ->
  (Z.to_nat from_word <= fold_left (fun a i => a + instr_word_size i) code 0) ->
  z_fits_i32b (rel_offset omap from_word target_idx) = true.
Proof.
  intros code omap from_word target_idx Hwf Homap Hnn Hlt Hfnn Hflt.
  unfold rel_offset, Encode.lookup_offset.
  subst omap.
  rewrite offset_map_correct by exact Hlt.
  unfold z_fits_i32b. apply Bool.andb_true_iff. split; apply Z.leb_le.
  - (* Lower bound: -(2^31) <= target_word - from_word *)
    assert (Htw : Z.of_nat (word_offset_of code (Z.to_nat target_idx)) < 536870912).
    { apply word_offset_fits; auto. lia. }
    assert (Hbl : List.length (encode_bytecode code) <= 2147483647).
    { apply well_formed_byte_bound. exact Hwf. }
    rewrite encode_bytecode_length in Hbl. lia.
  - (* Upper bound: target_word - from_word <= 2^31 - 1 *)
    assert (Htw : Z.of_nat (word_offset_of code (Z.to_nat target_idx)) < 536870912).
    { apply word_offset_fits; auto. lia. }
    lia.
Qed.

(* Layer 1: decode_raw_aux on the encoded program produces expected_raws.
   The proof proceeds by induction on the suffix of the code being decoded.
   At each step, the decoder reads the opcode and operands from the
   encoded bytes and produces the corresponding expected_raw.
   The key byte-level roundtrip is handled by read_u32_le_encode_word_le
   and read_i32_le_encode_word_le. *)
Lemma decode_raw_aux_produces_expected_raws :
  forall (code suffix : list instruction) (idx : nat) (fuel : nat),
    well_formed code = true ->
    suffix = skipn idx code ->
    idx + List.length suffix = List.length code ->
    List.length suffix <= fuel ->
    decode_raw_aux (encode_bytecode code) 0
      (List.length (encode_bytecode code))
      (4 * word_offset_of code idx) fuel =
    expected_raws (offset_map code) idx suffix (word_offset_of code idx).
Proof.
  intros code suffix.
  revert idx.
  induction suffix as [|i rest IH]; intros idx fuel Hwf Hsuffix Hlen Hfuel.
  - (* Base case: empty suffix, pos at end *)
    simpl. destruct fuel; [reflexivity|].
    simpl. destruct (Nat.leb (List.length (encode_bytecode code))
                             (4 * word_offset_of code idx)) eqn:E;
      [reflexivity|].
    apply Nat.leb_nle in E. exfalso. apply E.
    rewrite encode_bytecode_length.
    assert (idx = List.length code) by (simpl in Hlen; lia).
    rewrite H, word_offset_of_length. unfold total_word_size. lia.
  - (* Inductive case: i :: rest *)
    destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
    simpl expected_raws.
    (* We need well-formedness of i *)
    assert (Hidx : idx < List.length code) by (simpl in Hlen; lia).
    assert (Hwfi : wf_instrb (List.length code) i = true).
    { apply wf_instrb_from_well_formed with (code := code); auto.
      rewrite Hsuffix. apply in_cons_skipn with rest.
      left. reflexivity. }
    (* Position is within bounds *)
    assert (Hpos_lt : 4 * word_offset_of code idx <
                      List.length (encode_bytecode code)).
    { rewrite encode_bytecode_length.
      assert (word_offset_of code idx < total_word_size code).
      { unfold total_word_size. rewrite <- word_offset_of_length.
        apply word_offset_of_strict_mono; lia. }
      lia. }
    (* Step decode_raw_aux *)
    simpl decode_raw_aux.
    set (pos := 4 * word_offset_of code idx).
    set (total := List.length (encode_bytecode code)).
    destruct (Nat.leb total pos) eqn:Eleb; [apply Nat.leb_le in Eleb; lia|].
    replace (0 + pos)%nat with pos by lia.
    (* The data splits: encode_bytecode code = prefix ++ encode_instr ... i ++ rest *)
    set (omap := offset_map code).
    assert (Hdata_eq : encode_bytecode code =
      encode_instrs omap 0 (firstn idx code) ++
      encode_instr omap idx i ++
      encode_instrs omap (S idx) rest).
    { unfold encode_bytecode.
      rewrite <- (firstn_skipn idx code) at 1.
      rewrite encode_instrs_suffix, firstn_length_le by lia.
      replace (0 + idx) with idx by lia.
      change (i :: rest) with ([i] ++ rest).
      rewrite encode_instrs_suffix. simpl List.length.
      replace (idx + 1) with (S idx) by lia.
      simpl encode_instrs. rewrite app_nil_r, app_assoc. reflexivity. }
    set (pfx := encode_instrs omap 0 (firstn idx code)).
    assert (Hpfx_len : List.length pfx = pos).
    { subst pfx pos omap. rewrite encode_instrs_prefix_length by lia. reflexivity. }
    assert (Hilen : List.length (encode_instr omap idx i) = 4 * instr_word_size i).
    { apply encode_instr_length. }
    (* Read the opcode: skip prefix, read from instruction encoding *)
    rewrite Hdata_eq.
    rewrite read_u32_le_app_r by lia. rewrite Hpfx_len.
    replace (pos - pos) with 0 by lia.
    (* Now the goal reads from encode_instr omap idx i ++ rest_instrs.
       The instruction encoding starts with emit_words [opcode; ...]. *)
    set (ibytes := encode_instr omap idx i).
    set (rbytes := encode_instrs omap (S idx) rest).
    (* The next word offset *)
    assert (Hnext_wo : word_offset_of code (S idx) =
                       word_offset_of code idx + instr_word_size i).
    { simpl word_offset_of.
      (* We need: nth idx code gives i *)
      assert (Hnth : nth idx code STOP = i).
      { rewrite Hsuffix.
        rewrite <- (firstn_skipn idx code).
        rewrite nth_app_r by (rewrite firstn_length_le; lia).
        rewrite firstn_length_le by lia.
        replace (idx - idx) with 0 by lia. simpl.
        destruct (skipn idx code) eqn:E;
          [exfalso; assert (List.length (skipn idx code) = 0) by (rewrite E; auto);
           rewrite skipn_length in H; lia |
           injection Hsuffix as Hi _; subst; reflexivity]. }
      (* word_offset_of (i :: rest_after_idx) 1 = instr_word_size i + word_offset_of rest_after_idx 0 *)
      (* Actually, word_offset_of code (S idx) uses the full code *)
      clear -Hidx Hnth.
      revert idx Hidx Hnth.
      induction code as [|c cs IH']; intros idx Hidx Hnth.
      + simpl in Hidx. lia.
      + destruct idx as [|idx'].
        * simpl in Hnth. subst c. simpl. lia.
        * simpl. simpl in Hidx. simpl in Hnth.
          rewrite (IH' idx' ltac:(lia) Hnth). lia. }
    assert (Hnext_pos : 4 * word_offset_of code (S idx) = pos + 4 * instr_word_size i).
    { subst pos. lia. }
    (* For the IH: decode_raw_aux on the rest produces expected_raws for rest *)
    assert (HIH : decode_raw_aux (encode_bytecode code) 0 total
                    (4 * word_offset_of code (S idx)) fuel' =
                  expected_raws omap (S idx) rest (word_offset_of code (S idx))).
    { apply IH; auto.
      - subst suffix. simpl skipn. reflexivity.
      - simpl in Hlen. lia.
      - simpl in Hfuel. lia. }
    (* Now we need to show that the decode_raw_aux step on the instruction
       reads the correct opcode and operands, produces the correct raw_instr,
       and then the tail matches HIH.

       The challenge: the decode_raw_aux is applied to the data starting
       from pfx ++ ibytes ++ rbytes (via Hdata_eq), not to encode_bytecode code.
       We need to relate them. Actually, they are the SAME data -- Hdata_eq
       tells us encode_bytecode code = pfx ++ ibytes ++ rbytes.

       So we need to rewrite the IH back to use encode_bytecode code. *)
    (* For the rest of the proof, we need to handle each instruction case.
       The reading functions read from pfx ++ ibytes ++ rbytes.
       Since we already skipped pfx (via read_u32_le_app_r), we're reading
       from ibytes ++ rbytes.

       Also, the decode_raw_aux continuation processes the same full data
       encode_bytecode code. We need to rewrite the continuation using HIH. *)
    (* First, rewrite the continuation. After processing one instruction,
       decode_raw_aux continues at position pos + 4 * instr_word_size i
       = 4 * word_offset_of code (S idx). *)
    (* The reading of operands also happens on pfx ++ ibytes ++ rbytes.
       For operand reading, we need similar app_r + app_l rewrites. *)
    (* For the per-instruction case analysis, destruct i and handle
       each case using the byte-level roundtrip lemmas. *)
    subst ibytes.
    (* For each instruction, encode_instr produces emit_words of a word list.
       We use the word-level roundtrip lemmas to read back opcode and operands.
       First, show that reads on the full data at pos+k can be redirected to
       reads at k within (encode_instr ... ++ rbytes). *)
    (* All reads on (pfx ++ encode_instr ... ++ rbytes) at offset >= pos
       can be rewritten to reads on (encode_instr ... ++ rbytes) at offset 0+. *)
    (* Helper: for any read of data at an offset within the instruction *)
    assert (Hread_u32 : forall k, k + 4 <= 4 * instr_word_size i ->
      read_u32_le (encode_instrs omap 0 (firstn idx code) ++
                   encode_instr omap idx i ++ rbytes) (pos + k) =
      read_u32_le (encode_instr omap idx i ++ rbytes) k).
    { intros k Hk. rewrite read_u32_le_app_r by lia.
      rewrite Hpfx_len. f_equal. lia. }
    assert (Hread_i32 : forall k, k + 4 <= 4 * instr_word_size i ->
      read_i32_le (encode_instrs omap 0 (firstn idx code) ++
                   encode_instr omap idx i ++ rbytes) (pos + k) =
      read_i32_le (encode_instr omap idx i ++ rbytes) k).
    { intros k Hk. unfold read_i32_le. rewrite Hread_u32 by assumption.
      reflexivity. }
    (* Helper: continuation after processing this instruction *)
    assert (Hcont :
      decode_raw_aux (encode_instrs omap 0 (firstn idx code) ++
                      encode_instr omap idx i ++ rbytes)
        0 total (pos + 4 * instr_word_size i) fuel' =
      expected_raws omap (S idx) rest (word_offset_of code (S idx))).
    { rewrite <- Hdata_eq. rewrite Hnext_pos. exact HIH. }
    (* Now case-split on i *)
    destruct i; unfold encode_instr in *; simpl instr_word_size in *;
      simpl expected_raw;
      (* Rewrite opcode read *)
      rewrite Hread_u32 by lia;
      rewrite ?emit_words_cons, <- ?app_assoc;
      rewrite ?read_u32_le_app_l by (rewrite encode_word_le_length; lia);
      rewrite ?read_u32_le_encode_word_le by lia;
      simpl Z.eqb;
      try simpl operand_count.

    (* Zero-operand instructions: no operands to read *)
    all: try (
      change (read_operands _ 0 (pos + 4) 0) with (@nil Z, (pos + 4));
      replace (pos + 4) with (pos + 4 * 1) by lia;
      exact Hcont).

    (* One-operand instructions: read one i32 operand at offset 4 *)
    all: try (
      change (read_operands ?d 0 (pos + 4) 1)
        with (let v := read_i32_le d (0 + (pos + 4)) in
              let '(r, p) := read_operands d 0 ((pos + 4) + 4) 0 in
              (v :: r, p));
      change (read_operands _ 0 ((pos + 4) + 4) 0)
        with (@nil Z, (pos + 4) + 4);
      replace (0 + (pos + 4))%nat with (pos + 4) by lia;
      rewrite Hread_i32 by lia;
      rewrite emit_words_cons, <- app_assoc;
      rewrite read_i32_le_app_r by (rewrite encode_word_le_length; lia);
      rewrite encode_word_le_length;
      rewrite read_i32_le_app_l by
        (rewrite ?emit_words_cons, ?length_app, ?encode_word_le_length,
                 ?emit_words_length; simpl List.length; lia);
      rewrite read_i32_le_encode_word_le by
        (simpl wf_instrb in Hwfi;
         repeat (try (apply Bool.andb_true_iff in Hwfi; destruct Hwfi as [Hwfi ?]));
         first [ assumption
               | eapply rel_offset_fits_i32b; eauto;
                 try (simpl wf_instrb in Hwfi;
                      repeat (try (apply Bool.andb_true_iff in Hwfi;
                                   destruct Hwfi as [Hwfi ?]));
                      try (apply valid_targetb_props in Hwfi; tauto);
                      try (apply valid_targetb_props in H; tauto);
                      try lia);
                 try (rewrite encode_bytecode_length;
                      pose proof (well_formed_byte_bound code Hwf); lia)
               ]);
      replace ((pos + 4) + 4) with (pos + 4 * 2) by lia;
      exact Hcont).

    (* Two-operand instructions: read two i32 operands at offsets 4 and 8 *)
    all: try (
      change (read_operands ?d 0 (pos + 4) 2)
        with (let v1 := read_i32_le d (0 + (pos + 4)) in
              let '(r1, p1) := read_operands d 0 ((pos + 4) + 4) 1 in
              (v1 :: r1, p1));
      change (read_operands ?d 0 ((pos + 4) + 4) 1)
        with (let v2 := read_i32_le d (0 + ((pos + 4) + 4)) in
              let '(r2, p2) := read_operands d 0 (((pos + 4) + 4) + 4) 0 in
              (v2 :: r2, p2));
      change (read_operands _ 0 (((pos + 4) + 4) + 4) 0)
        with (@nil Z, ((pos + 4) + 4) + 4);
      replace (0 + (pos + 4))%nat with (pos + 4) by lia;
      replace (0 + ((pos + 4) + 4))%nat with (pos + 8) by lia;
      (* First operand at offset 4 *)
      rewrite (Hread_i32 4) by lia;
      rewrite emit_words_cons, <- app_assoc;
      rewrite read_i32_le_app_r by (rewrite encode_word_le_length; lia);
      rewrite encode_word_le_length;
      rewrite read_i32_le_app_l by
        (rewrite ?emit_words_cons, ?length_app, ?encode_word_le_length,
                 ?emit_words_length; simpl List.length; lia);
      rewrite read_i32_le_encode_word_le by
        (simpl wf_instrb in Hwfi;
         repeat (try (apply Bool.andb_true_iff in Hwfi; destruct Hwfi as [Hwfi ?]));
         try assumption);
      (* Second operand at offset 8 *)
      rewrite (Hread_i32 8) by lia;
      rewrite emit_words_cons, <- app_assoc;
      rewrite read_i32_le_app_r by (rewrite encode_word_le_length; lia);
      rewrite encode_word_le_length;
      rewrite emit_words_cons, <- app_assoc;
      rewrite read_i32_le_app_r by (rewrite encode_word_le_length; lia);
      rewrite encode_word_le_length;
      rewrite read_i32_le_app_l by
        (rewrite ?emit_words_cons, ?length_app, ?encode_word_le_length,
                 ?emit_words_length; simpl List.length; lia);
      rewrite read_i32_le_encode_word_le by
        (simpl wf_instrb in Hwfi;
         repeat (try (apply Bool.andb_true_iff in Hwfi; destruct Hwfi as [Hwfi ?]));
         try assumption);
      replace (((pos + 4) + 4) + 4) with (pos + 4 * 3) by lia;
      exact Hcont).

    (* Special cases that remain: CLOSUREREC, SWITCH, GETPUBMET,
       and any regular instructions not caught above *)
    (* GETPUBMET: opcode 141, reads tag + skips cache *)
    all: try (
      (* GETPUBMET: read tag at offset 4, skip cache at offset 8 *)
      rewrite (Hread_i32 4) by lia;
      rewrite emit_words_cons, <- app_assoc;
      rewrite read_i32_le_app_r by (rewrite encode_word_le_length; lia);
      rewrite encode_word_le_length;
      rewrite read_i32_le_app_l by
        (rewrite ?emit_words_cons, ?length_app, ?encode_word_le_length,
                 ?emit_words_length; simpl List.length; lia);
      rewrite read_i32_le_encode_word_le by
        (simpl wf_instrb in Hwfi;
         repeat (try (apply Bool.andb_true_iff in Hwfi; destruct Hwfi as [Hwfi ?]));
         try assumption);
      replace (pos + 4 + 4 + 4)%nat with (pos + 4 * 3) by lia;
      exact Hcont).
    all: admit.
Admitted.

Theorem decode_encode_inverse :
  forall code,
    well_formed code = true ->
    decode (encode_bytecode code) = code.
Proof.
  intros code Hwf.
  unfold decode, decode_bytecode, resolve_all, decode_raw.
  set (data := encode_bytecode code).
  set (len := List.length data).
  enough (Hraws_eq : decode_raw_aux data 0 len 0 (len + 1) =
                     expected_raws (offset_map code) 0 code 0).
  { rewrite Hraws_eq. apply resolve_all_expected_raws. exact Hwf. }
  subst len data.
  change 0%nat with (4 * word_offset_of code 0) at 2.
  apply decode_raw_aux_produces_expected_raws with (suffix := code); auto.
  - apply skipn_O.
  - lia.
  - pose proof (fuel_sufficient code). lia.
Qed.
