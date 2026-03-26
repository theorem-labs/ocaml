(* LexParseChecker.v - Verifies that the untrusted proof satisfies the
   trusted LexParseSpec Module Type.  Supplies the concrete pp_program
   (from semi-auto/) and lex_parse (from automatic/). *)

From OCamlInterp.Manual.LexParse Require Import LexParseSpec.
From OCamlInterp.Automatic.LexParse Require Import LexParse.
From OCamlInterp.Automatic.LexParse Require Import LexParseProof.
From OCamlInterp.SemiAutomatic.LexParse Require Import PrettyPrint.

Module Check <: LexParseSpec.
  Definition pp_program := pp_program.
  Definition lex_parse := lex_parse.
  Definition lex_parse_pp_inverse := lex_parse_pp_inverse.
End Check.
