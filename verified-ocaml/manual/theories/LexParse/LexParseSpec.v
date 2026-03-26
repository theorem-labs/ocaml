(* LexParseSpec.v - [TRUSTED] Module Type specifying the contract
   for the pretty-print/lex-parse roundtrip. The pretty-printer (Trusted)
   produces source strings; the lex-parser (Untrusted) must invert it.
   The theorem statement is trusted; the proof is untrusted and checked here. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Manual.Utils Require Import WellFormed.
From OCamlInterp.SemiAutomatic.LexParse Require Import PrettyPrint.

Module Type LexParseSpec.

  (* Lex-parser (provided by Untrusted): takes source string, returns AST *)
  Parameter lex_parse : string -> option program.

  (* Roundtrip theorem: parsing a pretty-printed well-formed program
     recovers the original *)
  Axiom lex_parse_pp_inverse : forall prog,
    wf_program prog = true ->
    lex_parse (pp_program prog) = Some prog.

End LexParseSpec.

(* Check that the untrusted proof satisfies the spec *)
From OCamlInterp.Automatic.LexParse Require Import LexParse.
From OCamlInterp.Automatic.LexParse Require Import LexParseProof.

Module Check <: LexParseSpec.
  Definition lex_parse := lex_parse.
  Definition lex_parse_pp_inverse := lex_parse_pp_inverse.
End Check.
