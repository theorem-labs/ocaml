(* Extract.v - Extraction directives.
   Run with: coqc -R _build/default/theories OCamlInterp theories/Extract.v
   Output goes to Interp_extracted.ml in the current directory. *)

From Stdlib Require Import ZArith Strings.String List.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.

From OCamlInterp.Trusted Require Import Value Bytecode Machine Interp Loader IO Main.
From OCamlInterp.Trusted Require Import Observable.
From OCamlInterp.SemiTrusted Require Import Syntax PrettyPrint.
From OCamlInterp.Untrusted Require Import SourceInterp Compile Encode CorrectnessProofs.

Extraction "Interp_extracted.ml"
  (* Value *)
  value Val_int Val_block Val_ptr Val_closure
  (* Bytecode *)
  instruction
  (* Machine / bytecode interpreter *)
  state mk_state step run run_pure
  step_result run_result
  set_accu initial_state
  field_or_heap tag_or_heap size_or_heap
  heap_alloc heap_lookup heap_update
  (* Pretty-printer *)
  pp_expr pp_pattern pp_decl pp_program
  (* Observable behavior *)
  event behavior termination mk_behavior
  (* Source interpreter *)
  svalue env eval eval_program interpret
  (* Compiler *)
  compile_program
  (* Encoder *)
  encode_bytecode
  (* Loader / decoder *)
  decode_bytecode load_code_section
  parse_sections find_section section
  read_u32_le read_i32_le read_u32_be
  (* Standalone entry point *)
  main.
