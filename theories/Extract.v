(* Extract.v - Extraction directives.
   Run with: coqc -R _build/default/theories OCamlInterp theories/Extract.v
   Output goes to Interp_extracted.ml in the current directory. *)

From Stdlib Require Import ZArith Strings.String List.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.

From OCamlInterp Require Import Value Bytecode Machine Interp Syntax PrettyPrint.

Extraction "Interp_extracted.ml"
  value Val_int Val_block Val_ptr
  instruction
  state mk_state step run run_pure
  step_result run_result
  set_accu initial_state
  field_or_heap tag_or_heap size_or_heap
  heap_alloc heap_lookup heap_update
  pp_expr pp_pattern pp_decl pp_program.
