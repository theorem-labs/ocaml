(* Observable.v - [TRUSTED] Observable program behavior.
   Defines the type that both the source interpreter and bytecode interpreter
   produce, enabling the correctness theorem to compare them.

   Design: A program's observable behavior is a trace of output events
   plus a termination status. This is the simplest model that captures
   what users can observe from running a program. *)

From Stdlib Require Import ZArith Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp Require Import Value.
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
