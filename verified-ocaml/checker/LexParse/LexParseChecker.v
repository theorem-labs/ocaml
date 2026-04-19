(* LexParseChecker.v - Verifies that the untrusted proof satisfies the
   trusted LexParseSpec Module Type.  Supplies the concrete pp_program
   (from semi-auto/) and lex_parse (from automatic/). *)

From OCamlInterp.Manual.LexParse Require Import LexParseSpec.
From OCamlInterp.Automatic.LexParse Require LexParse.
From OCamlInterp.Automatic.LexParse Require LexParseProof.
From OCamlInterp.SemiAutomatic.LexParse Require PrettyPrint.

Module Check <: LexParseSpec.
  Definition pp_program := OCamlInterp.SemiAutomatic.LexParse.PrettyPrint.pp_program.
  Definition lex_parse := OCamlInterp.Automatic.LexParse.LexParse.lex_parse.
  Definition lex_parse_pp_inverse := OCamlInterp.Automatic.LexParse.LexParseProof.lex_parse_pp_inverse.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<pp_program>".
    idtac "<PrintAssumptions>".
    Print Assumptions pp_program.
    idtac "</PrintAssumptions>".
    idtac "</pp_program>".
  Abort.
  Goal True.
    idtac "<lex_parse>".
    idtac "<PrintAssumptions>".
    Print Assumptions lex_parse.
    idtac "</PrintAssumptions>".
    idtac "</lex_parse>".
  Abort.
  Goal True.
    idtac "<lex_parse_pp_inverse>".
    idtac "<PrintAssumptions>".
    Print Assumptions lex_parse_pp_inverse.
    idtac "</PrintAssumptions>".
    idtac "</lex_parse_pp_inverse>".
  Abort.
  End __.
End Check.
