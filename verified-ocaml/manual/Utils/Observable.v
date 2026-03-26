(* Observable.v - [TRUSTED] Observable program behavior.
   Defines the type that both the source interpreter and bytecode interpreter
   produce, enabling the correctness theorem to compare them.

   Design: A program's observable behavior is a trace of output events
   plus a termination status. This is the simplest model that captures
   what users can observe from running a program. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
Open Scope string_scope.

(* An output event: a character written to stdout *)
Inductive event : Type :=
  | Out_char : Z -> event.   (* character code *)

(* How a program terminates *)
Inductive termination : Type :=
  | Term_normal  : value -> termination       (* normal exit with value *)
  | Term_error   : string -> termination      (* runtime error *)
  | Term_timeout : termination.               (* ran out of fuel *)

(* A program's complete observable behavior *)
Record behavior : Type := mk_behavior {
  trace : list event;        (* output events in order *)
  result : termination;      (* how it ended *)
}.

(* === Integer to character events (for print_int) === *)

Fixpoint nat_to_events_aux (fuel n : nat) (acc : list event) : list event :=
  match fuel with
  | O => acc
  | S fuel' =>
    let digit := Out_char (Z.of_nat (48 + Nat.modulo n 10)) in
    let rest := Nat.div n 10 in
    if Nat.eqb rest 0 then digit :: acc
    else nat_to_events_aux fuel' rest (digit :: acc)
  end.

Definition z_to_events (z : Z) : list event :=
  match z with
  | Z0 => [Out_char 48]  (* "0" *)
  | Zpos p => nat_to_events_aux 20 (Pos.to_nat p) []
  | Zneg p => Out_char 45 :: nat_to_events_aux 20 (Pos.to_nat p) []  (* "-" prefix *)
  end.
