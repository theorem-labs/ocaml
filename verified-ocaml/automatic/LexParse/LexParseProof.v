(* LexParseProof.v - Proof that LexParse and PrettyPrint roundtrip. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.SemiAutomatic.LexParse Require Import PrettyPrint.
From OCamlInterp.Automatic.LexParse Require Import LexParse.

Definition lex_parse_pp_inverse : forall prog,
  lex_parse (pp_program prog) = Some prog.
Proof.
Admitted.
