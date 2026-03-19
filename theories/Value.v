(* Value.v - [TRUSTED] OCaml runtime value representation. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.

Inductive value : Type :=
  | Val_int : Z -> value
  | Val_block : nat -> list value -> value.

Definition Closure_tag    := 247.
Definition Object_tag     := 248.
Definition Infix_tag      := 249.
Definition String_tag     := 252.
Definition Double_tag     := 253.

Definition val_unit  : value := Val_int 0.
Definition val_true  : value := Val_int 1.
Definition val_false : value := Val_int 0.

Definition val_bool (b : bool) : value :=
  if b then val_true else val_false.

Definition is_int (v : value) : bool :=
  match v with Val_int _ => true | Val_block _ _ => false end.

Definition int_val (v : value) : option Z :=
  match v with Val_int n => Some n | Val_block _ _ => None end.

Definition tag (v : value) : option nat :=
  match v with Val_int _ => None | Val_block t _ => Some t end.

Definition field (v : value) (n : nat) : option value :=
  match v with
  | Val_int _ => None
  | Val_block _ fields => nth_error fields n
  end.

Definition block_size (v : value) : option nat :=
  match v with
  | Val_int _ => None
  | Val_block _ fields => Some (length fields)
  end.

Fixpoint set_nth {A : Type} (l : list A) (n : nat) (x : A) : option (list A) :=
  match l, n with
  | [], _ => None
  | _ :: rest, O => Some (x :: rest)
  | h :: rest, S n' =>
    match set_nth rest n' x with
    | Some rest' => Some (h :: rest')
    | None => None
    end
  end.

Definition set_field (v : value) (n : nat) (x : value) : option value :=
  match v with
  | Val_int _ => None
  | Val_block t fields =>
    match set_nth fields n x with
    | Some fields' => Some (Val_block t fields')
    | None => None
    end
  end.

Definition closure_code (v : value) : option Z :=
  match v with
  | Val_block t fields =>
    if Nat.eqb t Closure_tag then
      match fields with Val_int pc :: _ => Some pc | _ => None end
    else None
  | _ => None
  end.

Fixpoint value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Val_int n1, Val_int n2 => Z.eqb n1 n2
  | Val_block t1 fs1, Val_block t2 fs2 =>
    Nat.eqb t1 t2 &&
    (fix list_eqb (l1 l2 : list value) : bool :=
      match l1, l2 with
      | [], [] => true
      | v1 :: r1, v2 :: r2 => value_eqb v1 v2 && list_eqb r1 r2
      | _, _ => false
      end) fs1 fs2
  | _, _ => false
  end.
