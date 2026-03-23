(* LoaderCorrectness.v - Checker: verifies that the untrusted decoder
   and roundtrip proofs satisfy the trusted LoaderCorrectnessSpec. *)

From OCamlInterp.Trusted Require Import LoaderCorrectnessSpec.
From OCamlInterp.Untrusted Require Import Loader LoaderCorrectnessProofs.

Module Check <: LoaderCorrectnessSpec.
  Definition decode_bytecode := decode_bytecode.
  Definition decode_encode_inverse := decode_encode_inverse.
End Check.
