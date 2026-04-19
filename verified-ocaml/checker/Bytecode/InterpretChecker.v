(* InterpretChecker.v - Verifies that Dispatch.handle_instr (the concrete
   107-arm dispatcher in manual/Bytecode/Interpret/Dispatch.v) satisfies
   the HandleInstrSpec module type, then instantiates the Run functor
   at the checked module and re-exports step / run_micro / handle_bcmicro
   / run / run_pure alongside fetch_instr / list_to_code_array.

   Downstream code (checker/Bytecode/Main.v, checker/Extract.v, PBT
   harnesses) consumes the flat re-exports below. *)

From OCamlInterp.Manual.Bytecode.Interpret Require Export Handlers.
From OCamlInterp.Manual.Bytecode.Interpret Require HandleInstrSpec Run Dispatch.

Module Check <: HandleInstrSpec.HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<handle_instr>".
    idtac "<PrintAssumptions>".
    Print Assumptions handle_instr.
    idtac "</PrintAssumptions>".
    idtac "</handle_instr>".
  Abort.
  End __.
End Check.

(* Instantiate the functor at the checked module. *)
Module Interp := Run.Make Check.

(* Re-export the names downstream callers expect.  Extraction picks these
   up as flat top-level definitions. *)
Definition step := Interp.step.
Definition run_micro := Interp.run_micro.
Definition handle_bcmicro := Interp.handle_bcmicro.
Definition run := Interp.run.
Definition run_pure := Interp.run_pure.
Definition fetch_instr := Run.fetch_instr.
Definition list_to_code_array := Run.list_to_code_array.
