(* ExtractionProof.v - [UNTRUSTED] Stage 2 extraction obligations.

   This module exposes the roadmap Theorem 3 interface. Extraction,
   external build/run results, and translation validation remain explicit
   untrusted obligations. *)

From Stdlib Require Import ZArith Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Compile Require Import ExtractionSpec.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Automatic.Compile Require Import Compile.

Module ExtractionValidation <: ExtractionSpec.
  Definition compile_program := Compile.compile_program.

  Parameter extract_to_ocaml : (program -> list instruction) -> string.
  Parameter ocaml_build : string -> option (list Z).
  Parameter extracted_run : list Z -> program -> option (list instruction).

  Axiom extraction_validates :
    forall (prog : program),
      let extracted_source := extract_to_ocaml compile_program in
      match ocaml_build extracted_source with
      | Some binary =>
        match extracted_run binary prog with
        | Some extracted_instrs =>
          extracted_instrs = compile_program prog
        | None => True
        end
      | None => False
      end.

  Parameter golden_program : program.
  Axiom golden_extraction_succeeds :
    let extracted_source := extract_to_ocaml compile_program in
    match ocaml_build extracted_source with
    | Some binary =>
      match extracted_run binary golden_program with
      | Some _ => True
      | None => False
      end
    | None => False
    end.
End ExtractionValidation.
