(* LoaderCorrectnessSpec.v - [TRUSTED] Module Type specifying the contract
   for the encode/decode roundtrip. The encoder (Trusted) produces bytes;
   the decoder (Untrusted) must invert it. The theorem statement is trusted;
   the proof is untrusted and checked in Checker. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
From OCamlInterp.Trusted Require Import Bytecode Encode WellFormed.

Module Type LoaderCorrectnessSpec.

  (* Decoder (provided by Untrusted) *)
  Parameter decode_bytecode : list Z -> nat -> nat -> list instruction.

  (* Main roundtrip theorem: decoding encoded bytecode recovers the original *)
  Axiom decode_encode_inverse : forall code,
    well_formed code = true ->
    decode_bytecode (encode_bytecode code) 0
                    (List.length (encode_bytecode code)) = code.

End LoaderCorrectnessSpec.
