(* MetaSpecChecker.v - Verifies that the untrusted meta-spec proof satisfies
   the trusted MetaSpec module type. *)

From OCamlInterp.Manual.Bytecode.Interpret Require MetaSpec.
From OCamlInterp.Automatic.Bytecode Require MetaSpecProof.

Module Check <: MetaSpec.MetaSpec.
  Definition handler_unique_mod_errors :=
    OCamlInterp.Automatic.Bytecode.MetaSpecProof.handler_unique_mod_errors.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<handler_unique_mod_errors>".
    idtac "<PrintAssumptions>".
    Print Assumptions handler_unique_mod_errors.
    idtac "</PrintAssumptions>".
    idtac "</handler_unique_mod_errors>".
  Abort.
  End __.

End Check.
