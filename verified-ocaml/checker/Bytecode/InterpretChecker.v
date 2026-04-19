(* InterpretChecker.v - Trust-boundary ascription for the bytecode
   interpreter.  Verifies that Dispatch.handle_instr satisfies the
   spec in manual/Bytecode/Interpret/HandleInstrSpec.v, then instantiates
   the Run functor at the checked module.  Downstream code (Main.v,
   Extract.v, PBT) consumes the flat re-exports below. *)

From OCamlInterp.Manual.Bytecode.Interpret Require HandleInstrSpec Run Dispatch.

(* Ascription: Rocq verifies that Dispatch.handle_instr has the type
   declared in HandleInstrSpec.handle_instr.  If Dispatch ever drifts
   from the spec, compilation of this file fails. *)
Module HandleInstrCheck <: HandleInstrSpec.HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.
End HandleInstrCheck.

(* Instantiate the functor at the checked module. *)
Module Interp := Run.Make HandleInstrCheck.

(* Re-export the names downstream callers expect.  Extraction picks these
   up as flat top-level definitions. *)
Definition step := Interp.step.
Definition run_micro := Interp.run_micro.
Definition handle_bcmicro := Interp.handle_bcmicro.
Definition run := Interp.run.
Definition run_pure := Interp.run_pure.
Definition fetch_instr := Run.fetch_instr.
Definition list_to_code_array := Run.list_to_code_array.
