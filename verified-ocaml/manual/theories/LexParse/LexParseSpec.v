(* LexParseSpec.v - [TRUSTED] Module Type specifying the contract
   for the pretty-print/lex-parse roundtrip. The pretty-printer (Trusted)
   produces source strings; the lex-parser (Untrusted) must invert it.
   The theorem statement is trusted; the proof is untrusted.

   This file has NO dependencies outside manual/ — it is fully self-contained.
   The concrete pp_program and lex_parse are supplied by the checker module
   in automatic/LexParse/LexParseChecker.v. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Manual.Utils Require Import WellFormed.

Module Type LexParseSpec.

  (* Pretty-printer (provided by semi-auto): AST -> source string *)
  Parameter pp_program : program -> string.

  (* Lex-parser (provided by Untrusted): takes source string, returns AST *)
  Parameter lex_parse : string -> option program.

  (* Roundtrip theorem: parsing a pretty-printed well-formed program
     recovers the original *)
  Axiom lex_parse_pp_inverse : forall prog,
    wf_program prog = true ->
    lex_parse (pp_program prog) = Some prog.

End LexParseSpec.
