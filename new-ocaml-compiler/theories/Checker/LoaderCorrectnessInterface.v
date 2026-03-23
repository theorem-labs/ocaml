(* LoaderCorrectnessInterface.v - Module Type specifying the contract
   that LoaderCorrectness must satisfy. If any admitted theorem's type
   signature drifts from this interface, Rocq will reject the file. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
From OCamlInterp.Trusted Require Import Bytecode Loader.
From OCamlInterp.Checker Require Import Encode.

Module Type LoaderCorrectnessInterface.

  (* Well-formedness predicates *)
  Parameter z_fits_i32 : Z -> Prop.
  Parameter z_fits_u32 : Z -> Prop.
  Parameter nat_fits_i32 : nat -> Prop.
  Parameter valid_target : nat -> Z -> Prop.
  Parameter all_valid_targets : nat -> list Z -> Prop.
  Parameter wf_instr : nat -> instruction -> Prop.
  Parameter well_formed : list instruction -> Prop.

  Axiom well_formed_unfold : forall code,
    well_formed code <-> Forall (wf_instr (List.length code)) code.

  (* Byte-level roundtrip lemmas *)
  Axiom read_u32_le_encode_word_le : forall v,
    (0 <= v < 4294967296)%Z ->
    read_u32_le (encode_word_le v) 0 = v.

  Axiom read_i32_le_encode_word_le : forall v,
    z_fits_i32 v ->
    read_i32_le (encode_word_le v) 0 = v.

  (* Encoding length *)
  Parameter total_word_size : list instruction -> nat.
  Parameter total_byte_size : list instruction -> nat.

  Axiom encode_bytecode_length : forall code,
    List.length (encode_bytecode code) = total_byte_size code.

  (* Main roundtrip theorem *)
  Parameter decode_encoded : list instruction -> list instruction.

  Axiom encode_decode_roundtrip : forall code,
    well_formed code ->
    decode_encoded code = code.

  Axiom decode_encode_inverse : forall code,
    well_formed code ->
    decode_bytecode (encode_bytecode code) 0
                    (List.length (encode_bytecode code)) = code.

End LoaderCorrectnessInterface.
