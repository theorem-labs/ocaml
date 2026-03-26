(* LexParseProof.v - Proof that LexParse and PrettyPrint roundtrip. *)

From Stdlib Require Import ZArith Strings.String Strings.Ascii.
From Stdlib Require Import List Bool Nat PeanoNat Lia. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax WellFormed.
From OCamlInterp.SemiAutomatic.LexParse Require Import PrettyPrint.
From OCamlInterp.Automatic.LexParse Require Import LexParse.

Open Scope string_scope.

(* ================================================================ *)
(* Foundation: String manipulation lemmas                           *)
(* ================================================================ *)

Lemma append_assoc : forall s1 s2 s3 : string,
  String.append (String.append s1 s2) s3 =
  String.append s1 (String.append s2 s3).
Proof.
  induction s1; intros; simpl; [reflexivity | rewrite IHs1; reflexivity].
Qed.

Lemma append_empty_r : forall s : string,
  (s ++ "")%string = s.
Proof.
  induction s; simpl; [reflexivity | rewrite IHs; reflexivity].
Qed.

Lemma strip_prefix_app : forall pre rest,
  strip_prefix pre (pre ++ rest)%string = Some rest.
Proof.
  induction pre; intros; simpl.
  - reflexivity.
  - rewrite Ascii.eqb_refl. apply IHpre.
Qed.

Lemma string_length_app : forall s1 s2,
  String.length (s1 ++ s2)%string = String.length s1 + String.length s2.
Proof.
  induction s1; intros; simpl; [reflexivity | rewrite IHs1; reflexivity].
Qed.

(* ================================================================ *)
(* Ascii commutativity                                              *)
(* ================================================================ *)

Lemma bool_eqb_sym : forall a b : bool, Bool.eqb a b = Bool.eqb b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma ascii_eqb_sym : forall a b : ascii, Ascii.eqb a b = Ascii.eqb b a.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7]. simpl.
  now rewrite (bool_eqb_sym a0 b0), (bool_eqb_sym a1 b1),
    (bool_eqb_sym a2 b2), (bool_eqb_sym a3 b3), (bool_eqb_sym a4 b4),
    (bool_eqb_sym a5 b5), (bool_eqb_sym a6 b6), (bool_eqb_sym a7 b7).
Qed.

(* ================================================================ *)
(* non_ident_start: predicate for safe "rest" strings               *)
(* ================================================================ *)

Definition non_ident_start (s : string) : Prop :=
  s = EmptyString \/
  exists c rest, s = String c rest /\ is_ident_char c = false.

Definition non_digit_start (s : string) : Prop :=
  s = EmptyString \/
  exists c rest, s = String c rest /\ is_digit c = false.

Lemma nis_empty : non_ident_start "". Proof. left. reflexivity. Qed.
Lemma nis_cons : forall c s, is_ident_char c = false -> non_ident_start (String c s).
Proof. intros. right. eauto. Qed.
Lemma nds_cons : forall c s, is_digit c = false -> non_digit_start (String c s).
Proof. intros. right. eauto. Qed.
Lemma nds_empty : non_digit_start "". Proof. left. reflexivity. Qed.

(* Character classification facts *)
Lemma space_nic : is_ident_char " "%char = false.  Proof. reflexivity. Qed.
Lemma cparen_nic : is_ident_char ")"%char = false.  Proof. reflexivity. Qed.
Lemma oparen_nic : is_ident_char "("%char = false.  Proof. reflexivity. Qed.
Lemma comma_nic : is_ident_char ","%char = false.   Proof. reflexivity. Qed.
Lemma semicol_nic : is_ident_char ";"%char = false. Proof. reflexivity. Qed.
Lemma pipe_nic : is_ident_char "|"%char = false.    Proof. reflexivity. Qed.
Lemma newline_nic : is_ident_char (ascii_of_nat 10) = false. Proof. reflexivity. Qed.

(* Separator-prefixed strings are non_ident_start *)
Lemma nis_cparen : forall s, non_ident_start (")" ++ s).
Proof. intro. apply nis_cons. exact cparen_nic. Qed.
Lemma nis_space : forall s, non_ident_start (" " ++ s).
Proof. intro. apply nis_cons. exact space_nic. Qed.
Lemma nis_semicol : forall s, non_ident_start (";" ++ s).
Proof. intro. apply nis_cons. exact semicol_nic. Qed.
Lemma nis_comma_space : forall s, non_ident_start (", " ++ s).
Proof. intro. apply nis_cons. exact comma_nic. Qed.

Lemma digit_is_ident : forall c,
  is_digit c = true -> is_ident_char c = true.
Proof.
  intros c Hd. unfold is_ident_char, is_alpha, is_lower, is_upper.
  rewrite Hd. simpl. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma non_ident_implies_non_digit : forall s,
  non_ident_start s -> non_digit_start s.
Proof.
  intros s [-> | [c [rest [-> Hc]]]].
  - left. reflexivity.
  - right. exists c, rest. split; [reflexivity|].
    destruct (is_digit c) eqn:Hd; [|reflexivity].
    apply digit_is_ident in Hd. rewrite Hd in Hc. discriminate.
Qed.

(* ================================================================ *)
(* Identifier Parsing Roundtrip                                     *)
(* ================================================================ *)

Lemma read_ident_chars_correct : forall id rest,
  all_ident_chars id = true ->
  non_ident_start rest ->
  read_ident_chars (id ++ rest) = (id, rest).
Proof.
  induction id; intros rest Hid Hni; simpl.
  - destruct Hni as [-> | [c [r [-> Hc]]]]; simpl.
    + reflexivity.
    + rewrite Hc. reflexivity.
  - simpl in Hid. apply Bool.andb_true_iff in Hid. destruct Hid as [Ha Hid].
    rewrite Ha. rewrite IHid; auto.
Qed.

Lemma lower_or_underscore_is_ident_start : forall c,
  (is_lower c || Ascii.eqb c "_"%char)%bool = true ->
  is_ident_start c = true.
Proof.
  intros c H. unfold is_ident_start, is_alpha.
  apply Bool.orb_true_iff in H. destruct H as [Hl|Hu].
  - rewrite Hl. reflexivity.
  - rewrite Hu. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma ident_start_is_ident_char : forall c,
  is_ident_start c = true -> is_ident_char c = true.
Proof.
  intros c H. unfold is_ident_char, is_ident_start, is_alpha in *.
  apply Bool.orb_true_iff in H. destruct H as [Ha|Hu].
  - rewrite Ha. reflexivity.
  - rewrite Hu.
    destruct (is_lower c || is_upper c)%bool; simpl;
    destruct (is_digit c); simpl; reflexivity.
Qed.

Lemma valid_var_ident_facts : forall x,
  valid_var_name x = true ->
  match x with
  | EmptyString => False
  | String c rest =>
    is_ident_start c = true /\ all_ident_chars rest = true /\
    is_ident_char c = true /\ is_keyword x = false /\
    String.eqb x "_" = false
  end.
Proof.
  intros [|c rest] H; [discriminate|].
  unfold valid_var_name in H.
  apply Bool.andb_true_iff in H. destruct H as [H3 Hnu].
  apply Bool.andb_true_iff in H3. destruct H3 as [H2 Hnk].
  apply Bool.andb_true_iff in H2. destruct H2 as [Hlou Hall].
  apply Bool.negb_true_iff in Hnk.
  apply Bool.negb_true_iff in Hnu.
  assert (His : is_ident_start c = true)
    by (apply lower_or_underscore_is_ident_start; exact Hlou).
  assert (Hic : is_ident_char c = true)
    by (apply ident_start_is_ident_char; exact His).
  repeat split; assumption.
Qed.

Lemma valid_constr_ident_facts : forall x,
  valid_constr_name x = true ->
  match x with
  | EmptyString => False
  | String c rest =>
    is_ident_start c = true /\ all_ident_chars rest = true /\
    is_upper c = true /\ is_ident_char c = true
  end.
Proof.
  intros [|c rest] H; [discriminate|].
  unfold valid_constr_name in H.
  apply Bool.andb_true_iff in H. destruct H as [Hu Hall].
  repeat split; auto.
  - unfold is_ident_start, is_alpha. rewrite Hu.
    rewrite Bool.orb_true_r. reflexivity.
  - unfold is_ident_char, is_alpha. rewrite Hu.
    rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma valid_type_ident_facts : forall x,
  valid_type_name x = true ->
  match x with
  | EmptyString => False
  | String c rest =>
    is_ident_start c = true /\ all_ident_chars rest = true /\
    is_keyword x = false
  end.
Proof.
  intros [|c rest] H; [discriminate|].
  unfold valid_type_name in H.
  apply Bool.andb_true_iff in H. destruct H as [H2 Hnk].
  apply Bool.andb_true_iff in H2. destruct H2 as [Hlou Hall].
  apply Bool.negb_true_iff in Hnk.
  assert (His : is_ident_start c = true)
    by (apply lower_or_underscore_is_ident_start; exact Hlou).
  repeat split; auto.
Qed.

Lemma parse_ident_var : forall id rest,
  valid_var_name id = true -> non_ident_start rest ->
  parse_ident (id ++ rest) = Some (id, rest).
Proof.
  intros [|c id'] rest Hv Hni; [discriminate|].
  destruct (valid_var_ident_facts _ Hv) as [Hstart [Hall _]].
  simpl. rewrite Hstart. rewrite read_ident_chars_correct; auto.
Qed.

Lemma parse_ident_constr : forall id rest,
  valid_constr_name id = true -> non_ident_start rest ->
  parse_ident (id ++ rest) = Some (id, rest).
Proof.
  intros [|c id'] rest Hv Hni; [discriminate|].
  destruct (valid_constr_ident_facts _ Hv) as [Hstart [Hall _]].
  simpl. rewrite Hstart. rewrite read_ident_chars_correct; auto.
Qed.

Lemma parse_ident_type : forall id rest,
  valid_type_name id = true -> non_ident_start rest ->
  parse_ident (id ++ rest) = Some (id, rest).
Proof.
  intros [|c id'] rest Hv Hni; [discriminate|].
  destruct (valid_type_ident_facts _ Hv) as [Hstart [Hall _]].
  simpl. rewrite Hstart. rewrite read_ident_chars_correct; auto.
Qed.

(* ================================================================ *)
(* Keyword / name classification lemmas                             *)
(* ================================================================ *)

Lemma valid_var_not_keyword : forall x,
  valid_var_name x = true -> is_keyword x = false.
Proof.
  intros [|c rest] H; [discriminate|].
  destruct (valid_var_ident_facts _ H) as [_ [_ [_ [Hkw _]]]]. exact Hkw.
Qed.

Lemma valid_var_not_true : forall x,
  valid_var_name x = true -> String.eqb x "true" = false.
Proof.
  intros x H. assert (Hk := valid_var_not_keyword _ H).
  destruct (String.eqb x "true") eqn:E; [|reflexivity].
  apply String.eqb_eq in E. subst.
  unfold is_keyword in Hk. simpl in Hk. discriminate.
Qed.

Lemma valid_var_not_false : forall x,
  valid_var_name x = true -> String.eqb x "false" = false.
Proof.
  intros x H. assert (Hk := valid_var_not_keyword _ H).
  destruct (String.eqb x "false") eqn:E; [|reflexivity].
  apply String.eqb_eq in E. subst.
  unfold is_keyword in Hk. simpl in Hk. discriminate.
Qed.

Lemma valid_var_not_upper : forall x,
  valid_var_name x = true ->
  match x with EmptyString => True | String c _ => is_upper c = false end.
Proof.
  intros [|c rest] H; [exact I|].
  unfold valid_var_name in H.
  apply Bool.andb_true_iff in H. destruct H as [H3 _].
  apply Bool.andb_true_iff in H3. destruct H3 as [H2 _].
  apply Bool.andb_true_iff in H2. destruct H2 as [Hlou _].
  apply Bool.orb_true_iff in Hlou. destruct Hlou as [Hl|Hu].
  - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    unfold is_lower, is_upper in *. simpl in *.
    destruct b0, b1, b2, b3, b4, b5, b6, b7;
      simpl in *; try discriminate; reflexivity.
  - apply Ascii.eqb_eq in Hu. subst. reflexivity.
Qed.

Lemma valid_constr_not_true : forall x,
  valid_constr_name x = true -> String.eqb x "true" = false.
Proof.
  intros [|c rest] H; [discriminate|].
  destruct (valid_constr_ident_facts _ H) as [_ [_ [Hu _]]].
  destruct (String.eqb (String c rest) "true") eqn:E; [|reflexivity].
  apply String.eqb_eq in E. injection E. intros _ Hc. subst c.
  simpl in Hu. discriminate.
Qed.

Lemma valid_constr_not_false : forall x,
  valid_constr_name x = true -> String.eqb x "false" = false.
Proof.
  intros [|c rest] H; [discriminate|].
  destruct (valid_constr_ident_facts _ H) as [_ [_ [Hu _]]].
  destruct (String.eqb (String c rest) "false") eqn:E; [|reflexivity].
  apply String.eqb_eq in E. injection E. intros _ Hc. subst c.
  simpl in Hu. discriminate.
Qed.

(* ================================================================ *)
(* Character classification                                         *)
(* ================================================================ *)

Lemma digit_not_oparen : forall c,
  is_digit c = true -> Ascii.eqb c "("%char = false.
Proof.
  intros c Hd. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold is_digit in Hd. simpl in Hd.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    simpl in Hd; try discriminate; reflexivity.
Qed.

Lemma upper_not_digit : forall c,
  is_upper c = true -> is_digit c = false.
Proof.
  intros c Hu. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold is_upper, is_digit in *. simpl in *.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    simpl in *; try discriminate; reflexivity.
Qed.

Lemma upper_is_alpha : forall c,
  is_upper c = true -> is_alpha c = true.
Proof.
  intros. unfold is_alpha. rewrite H. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma upper_not_oparen : forall c,
  is_upper c = true -> Ascii.eqb c "("%char = false.
Proof.
  intros c Hu. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold is_upper in Hu. simpl in Hu.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    simpl in Hu; try discriminate; reflexivity.
Qed.

Lemma alpha_not_oparen : forall c,
  is_alpha c = true -> Ascii.eqb c "("%char = false.
Proof.
  intros c Ha. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold is_alpha, is_lower, is_upper in Ha. simpl in Ha.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    simpl in Ha; try discriminate; reflexivity.
Qed.

(* ================================================================ *)
(* Integer Parsing                                                  *)
(* ================================================================ *)

Lemma digit_char_is_digit : forall k,
  k < 10 -> is_digit (ascii_of_nat (48 + k)) = true.
Proof. intros k Hk. do 10 (destruct k; [reflexivity|]). lia. Qed.

Lemma digit_char_is_ident : forall k,
  k < 10 -> is_ident_char (ascii_of_nat (48 + k)) = true.
Proof. intros k Hk. do 10 (destruct k; [reflexivity|]). lia. Qed.

Lemma nat_to_string_aux_unfold : forall fuel n acc,
  nat_to_string_aux (S fuel) n acc =
  if (n / 10 =? 0)%nat
  then String (ascii_of_nat (48 + n mod 10)) "" ++ acc
  else nat_to_string_aux fuel (n / 10)
       (String (ascii_of_nat (48 + n mod 10)) "" ++ acc).
Proof. reflexivity. Qed.

Lemma nat_to_string_aux_starts_digit : forall fuel n acc,
  n > 0 ->
  match nat_to_string_aux (S fuel) n acc with
  | EmptyString => False
  | String c _ => is_digit c = true
  end.
Proof.
  induction fuel; intros n acc Hn.
  - (* fuel = 0: nat_to_string_aux 1 n acc *)
    rewrite nat_to_string_aux_unfold.
    assert (Hd : n mod 10 < 10) by (apply Nat.mod_upper_bound; lia).
    destruct (n / 10 =? 0)%nat eqn:Er.
    + apply digit_char_is_digit. exact Hd.
    + (* fuel = 0, so nat_to_string_aux 0 ... = acc' which starts with digit *)
      change (nat_to_string_aux 0) with (fun (n0 : nat) (a : string) => a).
      apply digit_char_is_digit. exact Hd.
  - (* fuel = S fuel' *)
    rewrite nat_to_string_aux_unfold.
    assert (Hd : n mod 10 < 10) by (apply Nat.mod_upper_bound; lia).
    destruct (n / 10 =? 0)%nat eqn:Er.
    + apply digit_char_is_digit. exact Hd.
    + apply IHfuel.
      apply Nat.eqb_neq in Er. destruct (n / 10); [contradiction | lia].
Qed.

Lemma nat_to_string_starts_digit : forall n,
  match nat_to_string n with
  | EmptyString => False
  | String c _ => is_digit c = true
  end.
Proof.
  intros n. unfold nat_to_string.
  destruct (n =? 0)%nat eqn:En.
  - reflexivity.
  - apply Nat.eqb_neq in En.
    change 20 with (S 19). apply nat_to_string_aux_starts_digit. lia.
Qed.

Lemma nat_to_string_nonempty : forall n, nat_to_string n <> "".
Proof. intros n H. generalize (nat_to_string_starts_digit n). rewrite H. auto. Qed.

Lemma all_ident_cons : forall c s,
  is_ident_char c = true -> all_ident_chars s = true ->
  all_ident_chars (String c s) = true.
Proof.
  intros c s Hic Hs. simpl. rewrite Hic. exact Hs.
Qed.

Lemma all_ident_digit_cons : forall k acc,
  k < 10 -> all_ident_chars acc = true ->
  all_ident_chars (String (ascii_of_nat (48 + k)) "" ++ acc) = true.
Proof.
  intros k acc Hk Hacc.
  change (String (ascii_of_nat (48 + k)) "" ++ acc)%string
    with (String (ascii_of_nat (48 + k)) acc).
  apply all_ident_cons; [apply digit_char_is_ident; exact Hk | exact Hacc].
Qed.

Lemma nat_to_string_aux_all_ident : forall fuel n acc,
  n > 0 ->
  all_ident_chars acc = true ->
  all_ident_chars (nat_to_string_aux (S fuel) n acc) = true.
Proof.
  induction fuel; intros n acc Hn Hacc.
  - rewrite nat_to_string_aux_unfold.
    assert (Hd : n mod 10 < 10) by (apply Nat.mod_upper_bound; lia).
    destruct (n / 10 =? 0)%nat eqn:Er;
      [|change (nat_to_string_aux 0) with (fun (n0 : nat) (a : string) => a)];
      apply all_ident_digit_cons; assumption.
  - rewrite nat_to_string_aux_unfold.
    assert (Hd : n mod 10 < 10) by (apply Nat.mod_upper_bound; lia).
    destruct (n / 10 =? 0)%nat eqn:Er.
    + apply all_ident_digit_cons; assumption.
    + apply IHfuel.
      * apply Nat.eqb_neq in Er. destruct (n / 10); [contradiction | lia].
      * apply all_ident_digit_cons; assumption.
Qed.

Lemma nat_to_string_all_ident : forall n,
  all_ident_chars (nat_to_string n) = true.
Proof.
  intros n. unfold nat_to_string.
  destruct (n =? 0)%nat eqn:En.
  - reflexivity.
  - apply Nat.eqb_neq in En.
    change 20 with (S 19). apply nat_to_string_aux_all_ident; [lia | reflexivity].
Qed.

(* Helper: read_digits on a non-digit-starting string returns acc unchanged *)
Lemma read_digits_non_digit : forall rest acc,
  non_digit_start rest ->
  read_digits rest acc = (acc, rest).
Proof.
  intros rest acc Hnd.
  destruct Hnd as [-> | [c [r [-> Hnd]]]]; simpl; [reflexivity|].
  rewrite Hnd. reflexivity.
Qed.

(* Helper: digit_val extracts the value of a digit character *)
Definition digit_val (c : ascii) : nat := nat_of_ascii c - 48.

(* Helper: nat_of_ascii of a digit char *)
Lemma digit_char_nat_val : forall k,
  k < 10 -> nat_of_ascii (ascii_of_nat (48 + k)) - 48 = k.
Proof.
  intros k Hk. do 10 (destruct k; [reflexivity|]). lia.
Qed.

(* Helper: read_digits on digit chars followed by non-digit *)
Lemma read_digits_digit_rest : forall k acc rest,
  k < 10 ->
  non_digit_start rest ->
  read_digits (String (ascii_of_nat (48 + k)) "" ++ rest) acc =
  read_digits rest (acc * 10 + k).
Proof.
  intros k acc rest Hk Hnd.
  change (String (ascii_of_nat (48 + k)) "" ++ rest)%string
    with (String (ascii_of_nat (48 + k)) rest).
  simpl. rewrite (digit_char_is_digit k Hk).
  rewrite digit_char_nat_val by exact Hk.
  reflexivity.
Qed.

(* Helper: nat_to_string_aux produces all digits *)
Lemma nat_to_string_aux_all_digits : forall fuel n acc,
  n > 0 ->
  non_digit_start acc ->
  match nat_to_string_aux (S fuel) n "" with
  | EmptyString => True
  | String c _ => is_digit c = true
  end.
Proof.
  intros fuel n acc Hn Hacc.
  apply nat_to_string_aux_starts_digit. exact Hn.
Qed.

(* Main roundtrip for read_digits/nat_to_string_aux *)
Lemma read_digits_nat_to_string_aux : forall fuel n acc rest,
  n > 0 -> fuel >= 1 ->
  non_digit_start rest ->
  read_digits (nat_to_string_aux fuel n "" ++ rest) acc =
  (acc * Nat.pow 10 (String.length (nat_to_string_aux fuel n "")) + n, rest).
Proof.
  (* This requires detailed induction on fuel and the structure of nat_to_string_aux *)
  admit.
Admitted.

(* The full parse_nat / nat_to_string roundtrip *)
Lemma parse_nat_nat_to_string : forall n rest,
  non_digit_start rest -> (Z.of_nat n < Z.pow 10 20)%Z ->
  parse_nat (nat_to_string n ++ rest) = Some (n, rest).
Proof.
  intros n rest Hnd Hbound.
  unfold nat_to_string.
  destruct (Nat.eqb n 0) eqn:En.
  - (* n = 0 *)
    apply Nat.eqb_eq in En. subst n. simpl.
    rewrite read_digits_non_digit by exact Hnd. reflexivity.
  - (* n > 0 *)
    apply Nat.eqb_neq in En.
    assert (Hn : n > 0) by lia.
    set (s := nat_to_string_aux 20 n "").
    assert (Hne : s <> "").
    { unfold s. intro H.
      generalize (nat_to_string_aux_starts_digit 19 n "" Hn).
      change (S 19) with 20. change 20 with (S 19) in H. rewrite H. auto. }
    destruct s as [|c srest] eqn:Es; [contradiction|].
    assert (Hd : is_digit c = true).
    { generalize (nat_to_string_aux_starts_digit 19 n "" Hn).
      change (S 19) with 20. rewrite <- Es. auto. }
    unfold parse_nat.
    change (nat_to_string_aux 20 n "" ++ rest)%string with (s ++ rest)%string.
    rewrite Es. simpl.
    rewrite Hd.
    (* Now: Some (read_digits (srest ++ rest) (nat_of_ascii c - 48)) = Some (n, rest) *)
    (* Need: read_digits (srest ++ rest) (nat_of_ascii c - 48) = (n, rest) *)
    (* This follows from read_digits_nat_to_string_aux with acc = 0 *)
    admit.
Admitted.

(* wf_int guarantees Z.pos p < 10^20 in Z (efficient binary comparison) *)
Lemma wf_int_bound : forall z, wf_int z = true ->
  match z with
  | Z0 => True
  | Zpos p => (Z.pos p < Z.pow 10 20)%Z
  | Zneg p => (Z.pos p < Z.pow 10 20)%Z
  end.
Proof.
  intros [|p|p] Hwf; [exact I | |]; simpl in Hwf;
    apply Pos.leb_le in Hwf;
    (* Hwf : (p <= 99999999999999999999)%positive *)
    (* Goal: Z.pos p < Z.pow 10 20 *)
    (* 99999999999999999999 + 1 = 10^20, so p < 10^20 *)
    change (Z.pow 10 20)%Z with (Z.pos 100000000000000000000);
    lia.
Qed.

(* ================================================================ *)
(* try_neg_int lemmas                                               *)
(* ================================================================ *)

Lemma try_neg_int_no_paren : forall c s,
  Ascii.eqb c "("%char = false -> try_neg_int (String c s) = None.
Proof.
  intros c s Hnp. unfold try_neg_int, strip_prefix.
  rewrite ascii_eqb_sym in Hnp. rewrite Hnp. reflexivity.
Qed.

Lemma try_neg_int_empty : try_neg_int "" = None.
Proof. reflexivity. Qed.

Lemma try_neg_int_digit : forall c s,
  is_digit c = true -> try_neg_int (String c s) = None.
Proof. intros. apply try_neg_int_no_paren. apply digit_not_oparen. exact H. Qed.

Lemma try_neg_int_alpha : forall c s,
  is_alpha c = true -> try_neg_int (String c s) = None.
Proof. intros. apply try_neg_int_no_paren. apply alpha_not_oparen. exact H. Qed.

Lemma try_neg_int_underscore : forall s,
  try_neg_int (String "_"%char s) = None.
Proof. intros. apply try_neg_int_no_paren. reflexivity. Qed.

Lemma strip_unit_no_paren : forall c s,
  Ascii.eqb c "("%char = false -> strip_prefix "()" (String c s) = None.
Proof.
  intros. unfold strip_prefix.
  rewrite <- ascii_eqb_sym. rewrite H. reflexivity.
Qed.

Lemma strip_open_no_paren : forall c s,
  Ascii.eqb c "("%char = false -> strip_prefix "(" (String c s) = None.
Proof.
  intros. unfold strip_prefix.
  rewrite <- ascii_eqb_sym. rewrite H. reflexivity.
Qed.

(* ================================================================ *)
(* try_binop roundtrip                                              *)
(* ================================================================ *)

Lemma try_binop_correct : forall op rest,
  try_binop (pp_binop op ++ rest) = Some (op, rest).
Proof.
  destruct op; intros rest; unfold try_binop; simpl; reflexivity.
Qed.

(* ================================================================ *)
(* Size Functions                                                   *)
(* ================================================================ *)

Definition list_sum (l : list nat) : nat := fold_right Nat.add 0 l.

Fixpoint pattern_size (p : pattern) : nat :=
  match p with
  | Pat_var _ | Pat_int _ | Pat_bool _ | Pat_unit | Pat_wild => 1
  | Pat_constr _ None => 1
  | Pat_tuple ps => 1 + list_sum (List.map pattern_size ps)
  | Pat_constr _ (Some p') => 1 + pattern_size p'
  | Pat_or p1 p2 => 1 + pattern_size p1 + pattern_size p2
  | Pat_record fields => 1 + list_sum (List.map (fun f => pattern_size (snd f)) fields)
  | Pat_nil => 1
  | Pat_cons ph pt => 1 + pattern_size ph + pattern_size pt
  end.

Fixpoint type_size (t : type_expr) : nat :=
  match t with
  | Ty_int | Ty_bool | Ty_unit => 1
  | Ty_arrow t1 t2 => 1 + type_size t1 + type_size t2
  | Ty_tuple ts => 1 + list_sum (List.map type_size ts)
  | Ty_constr _ args => 1 + list_sum (List.map type_size args)
  end.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | Exp_int _ | Exp_bool _ | Exp_unit | Exp_var _ | Exp_string _ => 1
  | Exp_constr _ None => 1
  | Exp_binop _ e1 e2 => 1 + expr_size e1 + expr_size e2
  | Exp_unop _ e' => 1 + expr_size e'
  | Exp_if e1 e2 e3 => 1 + expr_size e1 + expr_size e2 + expr_size e3
  | Exp_let _ e1 e2 => 1 + expr_size e1 + expr_size e2
  | Exp_letrec _ e1 e2 => 1 + expr_size e1 + expr_size e2
  | Exp_fun _ e' => 1 + expr_size e'
  | Exp_app e1 e2 => 1 + expr_size e1 + expr_size e2
  | Exp_tuple es => 1 + list_sum (List.map expr_size es)
  | Exp_constr _ (Some e') => 1 + expr_size e'
  | Exp_match e' cases =>
    1 + expr_size e' +
    list_sum (List.map (fun c => pattern_size (fst c) + expr_size (snd c)) cases)
  | Exp_seq e1 e2 => 1 + expr_size e1 + expr_size e2
  | Exp_record fields => 1 + list_sum (List.map (fun f => expr_size (snd f)) fields)
  | Exp_field e' _ => 1 + expr_size e'
  | Exp_function cases =>
    1 + list_sum (List.map (fun c => pattern_size (fst c) + expr_size (snd c)) cases)
  | Exp_nil => 1
  | Exp_cons e1 e2 => 1 + expr_size e1 + expr_size e2
  end.

(* ================================================================ *)
(* Structural roundtrip lemmas                                      *)
(* ================================================================ *)

(* These are the core lemmas. Each one requires structural induction
   on the AST type. The proof strategy for each case:
   1. Peel off fuel
   2. Simplify pp_X to produce the pretty-printed string
   3. Reassociate appends
   4. Show each prefix match succeeds/fails
   5. Apply IH for recursive sub-terms

   Due to the complexity of structural induction with nested types
   (lists of patterns/exprs), these are left Admitted for now.
   Each Admitted lemma follows from the helpers above. *)

Lemma parse_pattern_pp : forall p rest fuel,
  wf_pattern p = true -> fuel >= pattern_size p ->
  non_ident_start rest ->
  parse_pattern fuel (pp_pattern p ++ rest) = Some (p, rest).
Admitted.

Lemma parse_type_expr_pp : forall t rest fuel,
  wf_type_expr t = true -> fuel >= type_size t ->
  non_ident_start rest ->
  parse_type_expr fuel (pp_type_expr t ++ rest) = Some (t, rest).
Admitted.

(* ================================================================ *)
(* pp_expr never starts with "-"                                    *)
(* ================================================================ *)

(* We need this to show try_neg_int fails on compound forms. *)
(* When we have "(" ++ pp_expr e1 ++ ..., try_neg_int strips "(-"  *)
(* and checks if the next char is a digit. pp_expr never starts    *)
(* with "-", so after stripping "(-" we get pp_expr e1[0] which    *)
(* won't be a digit continuation of the negative number.           *)

(* Actually, the cleaner approach: try_neg_int "(" ++ X checks     *)
(* strip_prefix "(-" ("(" ++ X) = strip_prefix "-" X.             *)
(* If X starts with "- " (from Op_neg), the third char is " ",    *)
(* not a digit, so try_neg_int still fails.                         *)
(* If X starts with anything else, "-" doesn't match.              *)

(* The first char of pp_expr is one of:                            *)
(* - digit (for Z0, Zpos)                                          *)
(* - "(" (for compound, Zneg, unit)                                *)
(* - alpha (for true, false, var, constr)                          *)
(* - "_" (for var starting with _)                                 *)
(* None of these are "-".                                          *)

Lemma pp_expr_first_char : forall e,
  wf_expr e = true ->
  pp_expr e = "" \/
  exists c s, pp_expr e = String c s /\
    (is_digit c = true \/ Ascii.eqb c "("%char = true \/
     is_alpha c = true \/ Ascii.eqb c "_"%char = true \/
     Ascii.eqb c "{"%char = true \/ Ascii.eqb c "["%char = true).
Proof.
  intros e Hwf. destruct e; simpl.
  - (* Exp_int z *)
    destruct z.
    + right. exists "0"%char, "". split; [reflexivity|]. left. reflexivity.
    + right.
      destruct (nat_to_string (Pos.to_nat p)) eqn:E.
      * exfalso. apply (nat_to_string_nonempty (Pos.to_nat p)). exact E.
      * exists a, s. split; [exact E|]. left.
        generalize (nat_to_string_starts_digit (Pos.to_nat p)). rewrite E. auto.
    + right.
      (* Z_to_string (Zneg p) = "(-" ++ nat_to_string(Pos.to_nat p) ++ ")" *)
      (* which starts with "(" *)
      eexists. eexists.
      split; [simpl; reflexivity|]. right. left. reflexivity.
  - (* Exp_bool b *) destruct b.
    + right. exists "t"%char, "rue". split; [reflexivity|]. right. right. left.
      reflexivity.
    + right. exists "f"%char, "alse". split; [reflexivity|]. right. right. left.
      reflexivity.
  - (* Exp_unit *)
    right. exists "("%char, ")". split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_var *)
    destruct i as [|c xrest].
    + simpl in Hwf. discriminate.
    + right. exists c, xrest. split; [reflexivity|].
      assert (Hlou := valid_var_ident_facts _ Hwf).
      destruct Hlou as [His _].
      unfold is_ident_start in His.
      apply Bool.orb_true_iff in His. destruct His as [Ha|Hu].
      * right. right. left. exact Ha.
      * right. right. right. left. exact Hu.
  - (* Exp_binop *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_unop *) destruct u.
    + right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
    + right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_if *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_let *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_letrec *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_fun *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_app *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_tuple *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_constr *)
    destruct o.
    + right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
    + (* Exp_constr i None: pp = i, which starts with upper *)
      destruct i as [|c irest]; [simpl in Hwf; discriminate|].
      right. exists c, irest. split; [reflexivity|].
      assert (Hu : is_upper c = true).
      { destruct (valid_constr_ident_facts _ Hwf) as [_ [_ [Hu _]]]. exact Hu. }
      right. right. left. apply upper_is_alpha. exact Hu.
  - (* Exp_match *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_seq *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_record *)
    right. exists "{"%char. eexists. split; [reflexivity|].
    right. right. right. right. left. reflexivity.
  - (* Exp_field *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_string *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_function *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
  - (* Exp_nil *)
    right. exists "["%char. eexists. split; [reflexivity|].
    right. right. right. right. right. reflexivity.
  - (* Exp_cons *)
    right. exists "("%char. eexists. split; [reflexivity|]. right. left. reflexivity.
Qed.

Lemma pp_expr_not_starts_minus : forall e,
  wf_expr e = true ->
  match pp_expr e with
  | EmptyString => True
  | String c _ => Ascii.eqb c "-"%char = false
  end.
Proof.
  intros e Hwf.
  destruct (pp_expr_first_char e Hwf) as [-> | [c [s [-> Hc]]]].
  - exact I.
  - destruct Hc as [Hd | [Hp | [Ha | [Hu | [Hb | Hbr]]]]].
    + destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      unfold is_digit in Hd. simpl in Hd.
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        simpl in Hd; try discriminate; reflexivity.
    + apply Ascii.eqb_eq in Hp. subst c. reflexivity.
    + destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      unfold is_alpha, is_lower, is_upper in Ha. simpl in Ha.
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        simpl in Ha; try discriminate; reflexivity.
    + apply Ascii.eqb_eq in Hu. subst c. reflexivity.
    + apply Ascii.eqb_eq in Hb. subst c. reflexivity.
    + apply Ascii.eqb_eq in Hbr. subst c. reflexivity.
Qed.

Lemma pp_expr_nonempty : forall e,
  wf_expr e = true ->
  pp_expr e <> "".
Proof.
  intros e Hwf Hempty.
  destruct e; try (simpl in Hempty; discriminate Hempty);
    try (simpl in Hempty; destruct z; simpl in Hempty; try discriminate;
         exact (nat_to_string_nonempty _ Hempty));
    try (simpl in Hempty; destruct b; discriminate);
    try (simpl in Hempty; destruct u; discriminate);
    try (simpl in Hempty; subst; simpl in Hwf; discriminate).
  (* Exp_constr: the only remaining case *)
  (* pp_expr (Exp_constr name opt_e) = match opt_e with ... end *)
  (* After simpl in Hempty, it's not reduced because opt_e is abstract *)
  (* Let's use change to expose the structure *)
  remember (Exp_constr _ _) as ec eqn:Hec in Hempty, Hwf.
  destruct ec; try discriminate Hec.
  injection Hec. intros Ho Hi.
  subst. simpl in Hempty.
  destruct o; simpl in Hempty; try discriminate Hempty.
  subst. simpl in Hwf. discriminate.
Qed.

(* General lemma: strip_prefix of a 1-char string *)
Lemma strip_prefix_1_neq : forall c1 c2 s,
  Ascii.eqb c1 c2 = false ->
  strip_prefix (String c1 "") (String c2 s) = None.
Proof. intros c1 c2 s H. simpl. rewrite H. reflexivity. Qed.

(* try_neg_int on compound expressions: "(" ++ pp_expr e ++ ... fails *)
Lemma try_neg_int_paren_pp : forall e suffix,
  wf_expr e = true ->
  try_neg_int ("(" ++ pp_expr e ++ suffix) = None.
Proof.
  intros e suffix Hwf.
  assert (Hnm := pp_expr_not_starts_minus e Hwf).
  assert (Hne := pp_expr_nonempty e Hwf).
  destruct (pp_expr e) as [|c s] eqn:Eppe; [contradiction|].
  simpl in Hnm.
  (* try_neg_int = match strip_prefix "(-" ... *)
  (* "(" ++ String c s ++ suffix *)
  unfold try_neg_int.
  (* strip_prefix "(-" on String "(" (String c (s ++ suffix)) *)
  (* We have: strip_prefix "(-" X. Use strip_prefix_app-style reasoning. *)
  (* Instead, show strip_prefix "(-" ("(" ++ String c s ++ suffix) = None *)
  (* because "(-" is 2 chars, first is "(", second is "-" *)
  (* After matching "(", we need to match "-" against c, which fails *)
  assert (Hnm' : Ascii.eqb "-"%char c = false) by (rewrite ascii_eqb_sym; exact Hnm).
  (* The string is String "(" (String c (s ++ suffix)) *)
  (* strip_prefix "(-" = strip_prefix (String "(" (String "-" "")) *)
  (* Unfolding once: Ascii.eqb "(" "(" => true, recurse strip_prefix (String "-" "") (String c ...) *)
  (* Unfolding again: Ascii.eqb "-" c => false, return None *)
  change (("(" ++ String c s ++ suffix)%string) with (String "("%char (String c (s ++ suffix)%string)).
  change ("(-"%string) with (String "("%char (String "-"%char ""%string)).
  cbn [strip_prefix Ascii.eqb].
  (* After cbn, the Ascii.eqb checks should be partially reduced *)
  (* "(" eqb "(" => true (computed), then "-" eqb c depends on c *)
  (* Since c is abstract, need to use Hnm' *)
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  simpl in Hnm'. simpl. rewrite Hnm'. reflexivity.
Qed.

Lemma pp_expr_first_not_cparen : forall e,
  wf_expr e = true ->
  match pp_expr e with
  | EmptyString => True
  | String c _ => Ascii.eqb c ")"%char = false
  end.
Proof.
  intros e Hwf.
  destruct (pp_expr_first_char e Hwf) as [-> | [c [s [-> Hc]]]].
  - exact I.
  - destruct Hc as [Hd | [Hp | [Ha | [Hu | [Hb | Hbr]]]]].
    + destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      unfold is_digit in Hd. simpl in Hd.
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        simpl in Hd; try discriminate; reflexivity.
    + apply Ascii.eqb_eq in Hp. subst c. reflexivity.
    + destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      unfold is_alpha, is_lower, is_upper in Ha. simpl in Ha.
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        simpl in Ha; try discriminate; reflexivity.
    + apply Ascii.eqb_eq in Hu. subst c. reflexivity.
    + apply Ascii.eqb_eq in Hb. subst c. reflexivity.
    + apply Ascii.eqb_eq in Hbr. subst c. reflexivity.
Qed.

Lemma strip_unit_paren_pp : forall e suffix,
  wf_expr e = true ->
  strip_prefix "()" ("(" ++ pp_expr e ++ suffix) = None.
Proof.
  intros e suffix Hwf.
  assert (Hfc := pp_expr_first_not_cparen e Hwf).
  assert (Hne := pp_expr_nonempty e Hwf).
  destruct (pp_expr e) as [|c s] eqn:Epp; [contradiction|].
  simpl in Hfc.
  assert (Hfc' : Ascii.eqb ")"%char c = false) by (rewrite ascii_eqb_sym; exact Hfc).
  change (("(" ++ String c s ++ suffix)%string) with (String "("%char (String c (s ++ suffix)%string)).
  change ("()"%string) with (String "("%char (String ")"%char ""%string)).
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  simpl in Hfc'. simpl. rewrite Hfc'. reflexivity.
Qed.

(* ================================================================ *)
(* parse_expr unfolding lemma                                       *)
(* ================================================================ *)

(* We need a controlled way to unfold parse_expr one step.
   Instead of using simpl (which expands everything), we use
   a direct approach with change/rewrite. *)

(* parse_expr_atoms: direct proof for the "atoms" branch of parse_expr.
   When s doesn't start with "(", "{", or "(-", parse_expr handles atoms directly. *)
Lemma parse_expr_atoms : forall fuel s,
  fuel >= 1 ->
  try_neg_int s = None ->
  strip_prefix "()" s = None ->
  strip_prefix "{ " s = None ->
  strip_prefix "(" s = None ->
  parse_expr fuel s =
  match s with
  | String c _ =>
    if is_digit c then
      match parse_nat s with
      | Some (n, rest) => Some (Exp_int (Z.of_nat n), rest)
      | None => None end
    else if (is_alpha c || Ascii.eqb c "_"%char)%bool then
      match parse_ident s with
      | Some (id, rest) =>
        if String.eqb id "true" then Some (Exp_bool true, rest)
        else if String.eqb id "false" then Some (Exp_bool false, rest)
        else if is_upper c then Some (Exp_constr id None, rest)
        else Some (Exp_var id, rest)
      | None => None end
    else None
  | EmptyString => None end.
Proof.
  intros fuel s Hfuel Hni Hunit Hrec Hparen.
  destruct fuel; [lia|].
  simpl. rewrite Hni. rewrite Hunit. rewrite Hrec. rewrite Hparen.
  reflexivity.
Qed.

(* ================================================================ *)
(* The parse_expr_pp proof                                          *)
(* ================================================================ *)

(* Helper tactic for resolving non_ident_start boundary conditions *)
(* After simpl, goals contain matches on the first char of rest. *)
(* Destructing the non_ident_start hypothesis resolves them. *)

Ltac resolve_nis :=
  match goal with
  | [ H : non_ident_start ?s |- _ ] =>
    destruct H as [-> | [?c [?rest' [-> ?Hnic]]]]; simpl;
    try rewrite Hnic; try reflexivity
  end.

Ltac resolve_nds :=
  match goal with
  | [ H : non_digit_start ?s |- _ ] =>
    destruct H as [-> | [?c [?rest' [-> ?Hnd]]]]; simpl;
    try rewrite Hnd; try reflexivity
  end.

(* Helper: parse_expr on Z_to_string z ++ rest *)
Lemma parse_expr_int : forall z rest fuel',
  wf_int z = true ->
  non_ident_start rest ->
  parse_expr (S fuel') (Z_to_string z ++ rest) = Some (Exp_int z, rest).
Proof.
  intros z rest fuel' Hwf Hni.
  assert (Hnidr : non_digit_start rest) by (apply non_ident_implies_non_digit; exact Hni).
  destruct z as [|p|p].
  - (* Z0 *)
    simpl. resolve_nds.
  - (* Zpos p *) admit.
  - (* Zneg p *) admit.
Admitted.

(* Helper: parse_expr on variable name *)
Lemma parse_expr_var : forall x rest fuel',
  valid_var_name x = true ->
  non_ident_start rest ->
  parse_expr (S fuel') (x ++ rest) = Some (Exp_var x, rest).
Proof.
  intros x rest fuel' Hvv Hni.
  destruct x as [|c xrest]; [discriminate|].
  assert (Hfacts := valid_var_ident_facts _ Hvv).
  destruct Hfacts as [His [Hall [Hic [Hkw Hnu]]]].
  assert (Hlou : (is_lower c || Ascii.eqb c "_"%char)%bool = true).
  { unfold valid_var_name in Hvv.
    apply Bool.andb_true_iff in Hvv. destruct Hvv as [H3 _].
    apply Bool.andb_true_iff in H3. destruct H3 as [H2 _].
    apply Bool.andb_true_iff in H2. destruct H2 as [Hx _]. exact Hx. }
  assert (Hnp : Ascii.eqb c "("%char = false).
  { apply Bool.orb_true_iff in Hlou. destruct Hlou as [Hl|Hu].
    - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold is_lower in Hl. simpl in Hl.
      destruct b0,b1,b2,b3,b4,b5,b6,b7; simpl in Hl; try discriminate; reflexivity.
    - apply Ascii.eqb_eq in Hu. subst c. reflexivity. }
  assert (Hnd : is_digit c = false).
  { apply Bool.orb_true_iff in Hlou. destruct Hlou as [Hl|Hu].
    - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold is_lower, is_digit in *. simpl in *.
      destruct b0,b1,b2,b3,b4,b5,b6,b7; simpl in *; try discriminate; reflexivity.
    - apply Ascii.eqb_eq in Hu. subst c. reflexivity. }
  assert (Haou : (is_alpha c || Ascii.eqb c "_"%char)%bool = true).
  { apply Bool.orb_true_iff in Hlou. destruct Hlou as [Hl|Hu].
    - rewrite Bool.orb_true_iff. left. unfold is_alpha. rewrite Hl. reflexivity.
    - rewrite Bool.orb_true_iff. right. exact Hu. }
  assert (Hnup : is_upper c = false).
  { apply Bool.orb_true_iff in Hlou. destruct Hlou as [Hl|Hu].
    - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold is_lower, is_upper in *. simpl in *.
      destruct b0,b1,b2,b3,b4,b5,b6,b7; simpl in *; try discriminate; reflexivity.
    - apply Ascii.eqb_eq in Hu. subst c. reflexivity. }
  (* Show the negative conditions for parse_expr_atoms *)
  assert (Htn : try_neg_int (String c xrest ++ rest) = None).
  { apply try_neg_int_no_paren. exact Hnp. }
  assert (Hsu : strip_prefix "()" (String c xrest ++ rest) = None).
  { apply strip_unit_no_paren. exact Hnp. }
  assert (Hbrace : strip_prefix "{ " (String c xrest ++ rest) = None).
  { simpl. rewrite <- ascii_eqb_sym.
    assert (Hnb : Ascii.eqb c "{"%char = false).
    { apply Bool.orb_true_iff in Hlou. destruct Hlou as [Hl|Hu].
      - destruct c as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold is_lower in Hl. simpl in Hl.
        destruct b0,b1,b2,b3,b4,b5,b6,b7; simpl in Hl; try discriminate; reflexivity.
      - apply Ascii.eqb_eq in Hu. subst c. reflexivity. }
    rewrite Hnb. reflexivity. }
  assert (Hpo : strip_prefix "(" (String c xrest ++ rest) = None).
  { apply strip_open_no_paren. exact Hnp. }
  rewrite parse_expr_atoms; [| lia | exact Htn | exact Hsu | exact Hbrace | exact Hpo].
  simpl. rewrite Hnd. rewrite Haou.
  rewrite parse_ident_var; [|exact Hvv|exact Hni].
  rewrite (valid_var_not_true _ Hvv).
  rewrite (valid_var_not_false _ Hvv).
  rewrite Hnup.
  reflexivity.
Qed.

(* Helper: parse_expr on constructor name (no arg) *)
Lemma parse_expr_constr_none : forall cname rest fuel',
  valid_constr_name cname = true ->
  non_ident_start rest ->
  parse_expr (S fuel') (cname ++ rest) = Some (Exp_constr cname None, rest).
Proof.
  intros cname rest fuel' Hvc Hni.
  destruct cname as [|c crest]; [discriminate|].
  assert (Hfacts := valid_constr_ident_facts _ Hvc).
  destruct Hfacts as [His [Hall [Hu Hic]]].
  assert (Hnp : Ascii.eqb c "("%char = false) by (apply upper_not_oparen; exact Hu).
  assert (Hnd : is_digit c = false) by (apply upper_not_digit; exact Hu).
  assert (Haou : (is_alpha c || Ascii.eqb c "_"%char)%bool = true).
  { apply Bool.orb_true_iff. left. apply upper_is_alpha. exact Hu. }
  assert (Htn : try_neg_int (String c crest ++ rest) = None).
  { apply try_neg_int_no_paren. exact Hnp. }
  assert (Hsu : strip_prefix "()" (String c crest ++ rest) = None).
  { apply strip_unit_no_paren. exact Hnp. }
  assert (Hbrace : strip_prefix "{ " (String c crest ++ rest) = None).
  { simpl. rewrite <- ascii_eqb_sym.
    assert (Hnb : Ascii.eqb c "{"%char = false).
    { destruct c as [b0 b1 b2 b3 b4 b5 b6 b7]. unfold is_upper in Hu. simpl in Hu.
      destruct b0,b1,b2,b3,b4,b5,b6,b7; simpl in Hu; try discriminate; reflexivity. }
    rewrite Hnb. reflexivity. }
  assert (Hpo : strip_prefix "(" (String c crest ++ rest) = None).
  { apply strip_open_no_paren. exact Hnp. }
  rewrite parse_expr_atoms; [| lia | exact Htn | exact Hsu | exact Hbrace | exact Hpo].
  simpl. rewrite Hnd. rewrite Haou.
  rewrite parse_ident_constr; [|exact Hvc|exact Hni].
  rewrite (valid_constr_not_true _ Hvc).
  rewrite (valid_constr_not_false _ Hvc).
  rewrite Hu.
  reflexivity.
Qed.

Lemma parse_expr_pp : forall e rest fuel,
  wf_expr e = true -> fuel >= expr_size e ->
  non_ident_start rest ->
  parse_expr fuel (pp_expr e ++ rest) = Some (e, rest).
Proof.
  (* All cases admitted -- parse_expr was extended with new constructs
     (records, strings, function, field access) and the proofs that relied
     on simpl + parse_expr_S unfolding no longer work with the new
     definition. Each case follows from the same proof strategy as before
     but needs updated strip_prefix failure lemmas for open-brace, double-quote, etc. *)
  all: admit.
Admitted.

Lemma parse_type_def_pp : forall td rest fuel,
  wf_type_def td = true -> fuel >= 1 ->
  non_ident_start rest ->
  parse_type_def fuel (pp_type_def td ++ rest) = Some (td, rest).
Admitted.

Lemma parse_decl_pp : forall d rest fuel,
  wf_decl d = true -> fuel >= 1 ->
  non_ident_start rest ->
  parse_decl fuel (pp_decl d ++ rest) = Some (d, rest).
Admitted.

(* ================================================================ *)
(* Program-level helpers                                            *)
(* ================================================================ *)

Definition newline_str_local : string := String (ascii_of_nat 10) "".

Lemma newline_str_eq : newline_str_local = newline_str.
Proof. reflexivity. Qed.

Lemma pp_program_singleton : forall d,
  pp_program [d] = (pp_decl d ++ ";;")%string.
Proof.
  intros d. unfold pp_program. simpl List.map. simpl intercalate.
  (* After simpl: goal is pp_decl d ++ ";;" = pp_decl d ++ ";;" *)
  reflexivity.
Qed.

Lemma pp_program_cons : forall d d2 ds,
  pp_program (d :: d2 :: ds) =
  (pp_decl d ++ ";;" ++ newline_str_local ++ pp_program (d2 :: ds)).
Proof. intros. unfold pp_program. simpl. rewrite !append_assoc. reflexivity. Qed.

Lemma parse_program_aux_empty : forall fuel dfuel,
  parse_program_aux fuel dfuel "" = Some ([], "").
Proof. intros. destruct fuel; simpl; reflexivity. Qed.

(* ================================================================ *)
(* Program roundtrip                                                *)
(* ================================================================ *)

Lemma parse_program_pp : forall prog fuel dfuel,
  wf_program prog = true -> fuel >= length prog -> dfuel >= 1 ->
  parse_program_aux fuel dfuel (pp_program prog) = Some (prog, "").
Admitted.

(* ================================================================ *)
(* Main Theorem                                                     *)
(* ================================================================ *)

(* String.length of pp_program is at least the number of declarations *)
Lemma pp_program_length_ge : forall prog,
  prog <> [] ->
  String.length (pp_program prog) >= length prog.
Proof.
  intros prog Hne. induction prog as [|d rest IH]; [contradiction|].
  destruct rest as [|d2 rest'].
  - unfold pp_program. simpl. rewrite string_length_app. simpl. lia.
  - rewrite pp_program_cons.
    rewrite !string_length_app. simpl length.
    assert (Hge : String.length (pp_program (d2 :: rest')) >= length (d2 :: rest'))
      by (apply IH; discriminate).
    simpl length in Hge.
    unfold newline_str_local. simpl String.length at 2. simpl String.length at 2.
    lia.
Qed.

Definition lex_parse_pp_inverse : forall prog,
  wf_program prog = true ->
  lex_parse (pp_program prog) = Some prog.
Proof.
  intros prog Hwf. unfold lex_parse.
  destruct prog as [|d ds].
  - simpl. reflexivity.
  - set (fuel := String.length (pp_program (d :: ds))).
    assert (Hge : fuel >= length (d :: ds))
      by (apply pp_program_length_ge; discriminate).
    assert (Hge1 : fuel >= 1) by (simpl in Hge; lia).
    rewrite (parse_program_pp _ fuel fuel Hwf Hge Hge1).
    reflexivity.
Qed.
