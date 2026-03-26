(* DecodeSpec.v - [TRUSTED] Module Type specifying the contract
   for the encode/decode roundtrip, plus the well-formedness predicate that
   serves as its precondition. The encoder (Trusted) produces bytes;
   the decoder (Untrusted) must invert it. The theorem statement is trusted;
   the proof is untrusted and checked below. *)

From Stdlib Require Import ZArith PeanoNat Bool List.
Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Bytecode Require Import Encode.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Well-formedness predicate                                           *)
(* ------------------------------------------------------------------ *)

Definition z_fits_i32b (z : Z) : bool :=
  Z.leb (-2147483648) z && Z.leb z 2147483647.

Definition z_fits_u32b (z : Z) : bool :=
  Z.leb 0 z && Z.leb z 4294967295.

Definition nat_fits_i32b (n : nat) : bool :=
  z_fits_i32b (Z.of_nat n).

Definition valid_targetb (n : nat) (t : Z) : bool :=
  Z.leb 0 t && Nat.ltb (Z.to_nat t) n.

Definition all_valid_targetsb (n : nat) (ts : list Z) : bool :=
  forallb (valid_targetb n) ts.

Definition wf_instrb (n : nat) (i : instruction) : bool :=
  match i with
  | ACC k | PUSHACC k | POP k | ASSIGN k
  | ENVACC k | PUSHENVACC k
  | APPLY k | APPTERM1 k | APPTERM2 k | APPTERM3 k
  | RETURN k | GRAB k
  | GETGLOBAL k | PUSHGETGLOBAL k | SETGLOBAL k
  | ATOM k | PUSHATOM k
  | MAKEBLOCK1 k | MAKEBLOCK2 k | MAKEBLOCK3 k
  | MAKEFLOATBLOCK k
  | GETFIELD k | GETFLOATFIELD k | SETFIELD k | SETFLOATFIELD k
  | RESUMETERM k | REPERFORMTERM k
    => nat_fits_i32b k
  | APPTERM a b | GETGLOBALFIELD a b | PUSHGETGLOBALFIELD a b
  | MAKEBLOCK a b | C_CALL a b
    => nat_fits_i32b a && nat_fits_i32b b
  | PUSH_RETADDR t | BRANCH t | BRANCHIF t | BRANCHIFNOT t | PUSHTRAP t
    => valid_targetb n t
  | CLOSURE nv codeptr
    => nat_fits_i32b nv && valid_targetb n codeptr
  | CLOSUREREC nf nv ofs
    => nat_fits_i32b nf && nat_fits_i32b nv
       && all_valid_targetsb n ofs
       && Nat.eqb (List.length ofs) nf
  | SWITCH nc nb ct bt
    => Nat.eqb (List.length ct) nc && Nat.eqb (List.length bt) nb
       && all_valid_targetsb n ct && all_valid_targetsb n bt
       && Nat.ltb nc 65536 && Nat.ltb nb 32768
  | BEQ v t | BNEQ v t | BLTINT v t | BLEINT v t
  | BGTINT v t | BGEINT v t | BULTINT v t | BUGEINT v t
    => z_fits_i32b v && valid_targetb n t
  | CONSTINT v | PUSHCONSTINT v | OFFSETINT v | OFFSETREF v
    => z_fits_i32b v
  | OFFSETCLOSURE v | PUSHOFFSETCLOSURE v
    => z_fits_i32b v
  | GETPUBMET v
    => z_fits_i32b v
  | _ => true
  end.

Definition well_formed (code : list instruction) : bool :=
  let n := List.length code in
  forallb (wf_instrb n) code
  && Nat.leb (List.length (encode_bytecode code)) 2147483647.

(* ------------------------------------------------------------------ *)
(* Roundtrip spec                                                      *)
(* ------------------------------------------------------------------ *)

Module Type DecodeSpec.

  (* Decoder (provided by Untrusted): takes raw bytes, returns instructions *)
  Parameter decode : list Z -> list instruction.

  (* Main roundtrip theorem: decoding encoded bytecode recovers the original *)
  Axiom decode_encode_inverse : forall code,
    well_formed code = true ->
    decode (encode_bytecode code) = code.

End DecodeSpec.

(* ------------------------------------------------------------------ *)
(* File-format types shared by Decode.v and Main.v                     *)
(* ------------------------------------------------------------------ *)

Record section : Type := mk_section {
  sec_name   : Z;
  sec_offset : nat;
  sec_length : nat;
}.

Module Type DecoderSpec.
  Parameter load_code_section : list Z -> nat -> option (list instruction).
  Parameter parse_sections    : list Z -> nat -> list section.
  Parameter find_section      : list section -> Z -> option section.
End DecoderSpec.
