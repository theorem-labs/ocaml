(* LoaderCorrectness.v - Checker: verifies that the untrusted decoder
   and roundtrip proofs satisfy the trusted LoaderCorrectnessSpec. *)

From OCamlInterp.Trusted.Bytecode Require Import LoaderCorrectnessSpec.
From OCamlInterp.Untrusted Require Import LoaderCorrectnessProofs.

Module Check <: LoaderCorrectnessSpec.
  Definition decode := decode.
  Definition decode_encode_inverse := decode_encode_inverse.
End Check.
