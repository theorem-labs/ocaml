(* DecodeChecker.v - Verifies that the untrusted proof satisfies the
   trusted DecodeSpec Module Type. *)

From OCamlInterp.Manual.Bytecode Require Import DecodeSpec.
From OCamlInterp.Automatic.Bytecode Require DecodeProof.

Module Check <: DecodeSpec.
  Definition decode := OCamlInterp.Automatic.Bytecode.DecodeProof.decode.
  Definition decode_encode_inverse := OCamlInterp.Automatic.Bytecode.DecodeProof.decode_encode_inverse.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<decode>".
    idtac "<PrintAssumptions>".
    Print Assumptions decode.
    idtac "</PrintAssumptions>".
    idtac "</decode>".
  Abort.
  Goal True.
    idtac "<decode_encode_inverse>".
    idtac "<PrintAssumptions>".
    Print Assumptions decode_encode_inverse.
    idtac "</PrintAssumptions>".
    idtac "</decode_encode_inverse>".
  Abort.
  End __.
End Check.
