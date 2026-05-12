(* ExtractionSpec.v - [TRUSTED] Module Type for translation validation
   of Rocq extraction.

   Following the pattern from the Go verified compiler: the extraction
   pipeline (extract to OCaml source, build with ocamlc, run on a
   program) is modeled as Parameters. The theorem is universally
   quantified over all programs.

   The auto side fills extract_to_ocaml with the actual extraction
   output, ocaml_build with the result of compiling it, and
   extracted_run with the results of running the binary on test
   programs. For tested programs, instruction-list equality with the
   Rocq-level compile_program is verified by native_compute. For
   untested programs, extracted_run returns None (obligation is True).

   Trust model: this file defines the correctness statement. The
   untrusted code provides all Parameters and a proof of
   extraction_validates.

   This file has NO dependencies outside manual/. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Utils Require Import Syntax.

Module Type ExtractionSpec.

  (* Compiler (the Rocq definition, from automatic/) *)
  Parameter compile_program : program -> list instruction.

  (* Extraction: takes the compile function and produces OCaml
     source code as a string. Represents Rocq's extraction mechanism
     applied to compile_program. *)
  Parameter extract_to_ocaml : (program -> list instruction) -> string.

  (* External: compile extracted OCaml source with ocamlc into a
     binary. Returns None if compilation fails. *)
  Parameter ocaml_build : string -> option (list Z).

  (* External: run the extracted compiler binary on a program,
     returning the instruction list it produces. Returns None if
     the binary fails on this input or the program has not been
     tested. *)
  Parameter extracted_run : list Z -> program -> option (list instruction).

  (* Translation validation: the extracted+built compiler, when run
     on any program where it succeeds, produces IDENTICAL bytecode
     to the Rocq-level compile_program.

     Instruction-list equality (not behavioral equivalence) is the
     right notion here: the extracted code IS the same function
     translated to OCaml, so any difference in the instruction list
     indicates a translation error.

     None => True for extracted_run is honest: untested programs are
     not claimed to match. The theorem's strength grows as more
     programs are verified.

     None => False for ocaml_build requires extraction to produce
     compilable code -- a verified compiler whose extraction doesn't
     build is useless. *)
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

  (* Anti-vacuity: at least one program succeeds through the full
     extraction pipeline, preventing extract_to_ocaml/ocaml_build/
     extracted_run from trivially failing on all inputs. *)
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

End ExtractionSpec.
