(* Value.v - [TRUSTED] OCaml runtime value representation. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.

Inductive value : Type :=
  | Val_int : Z -> value
  | Val_block : nat -> list value -> value
  | Val_ptr : nat -> value  (* heap pointer for mutable blocks *)
  | Val_closure : nat -> nat -> value.  (* heap addr, field offset within block *)

Definition Closure_tag    := 247.
Definition Infix_tag      := 249.
Definition String_tag     := 252.

Definition val_unit  : value := Val_int 0.
Definition val_true  : value := Val_int 1.
Definition val_false : value := Val_int 0.

Definition val_bool (b : bool) : value :=
  if b then val_true else val_false.

Definition is_int (v : value) : bool :=
  match v with Val_int _ => true | _ => false end.

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
  | Val_ptr a1, Val_ptr a2 => Nat.eqb a1 a2
  | Val_closure a1 o1, Val_closure a2 o2 => Nat.eqb a1 a2 && Nat.eqb o1 o2
  | _, _ => false
  end.

(* Physical equality comparison for EQ/NEQ bytecodes (OCaml's == / !=).
   Val_int: unboxed, so physical equality is integer equality.
   Val_ptr: heap-allocated, physical equality is pointer (address) equality.
   Val_closure: physical equality is address + offset equality.
   Val_block: conservative false — two Val_block values represent distinct
   allocations (e.g. from the DATA section or C-calls). If they were the same
   heap object, they would share a Val_ptr instead. *)
Definition value_phys_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Val_int n1, Val_int n2 => Z.eqb n1 n2
  | Val_ptr a1, Val_ptr a2 => Nat.eqb a1 a2
  | Val_closure a1 o1, Val_closure a2 o2 => Nat.eqb a1 a2 && Nat.eqb o1 o2
  | Val_block _ _, Val_block _ _ => false
  | _, _ => false
  end.
