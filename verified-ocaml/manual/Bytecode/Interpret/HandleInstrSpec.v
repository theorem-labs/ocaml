(* HandleInstrSpec.v - [TRUSTED] Module Type declaring the signature of the
   per-instruction dispatcher.  The functor in Run.v builds step/run/etc.
   on top of this interface; the concrete implementation lives in
   automatic/Bytecode/HandleInstr.v and is ascribed to this spec inside
   checker/Bytecode/InterpretChecker.v. *)

From Stdlib Require Import ZArith.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.

Module Type HandleInstrSpec.
  Parameter handle_instr :
    instruction -> Z -> state -> step_result.
End HandleInstrSpec.
