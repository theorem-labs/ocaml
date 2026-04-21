(* CompileChecker.v - Verifies that the untrusted proof satisfies the
   trusted CompileSpec Module Type (from manual/Compile/CompileSpec.v).
   Supplies the concrete compile_program (from automatic/), interpret
   (from semi-auto/), and the correctness proof (from automatic/). *)

From OCamlInterp.Manual.Compile Require Import CompileSpec.
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.SemiAutomatic.Interpret Require Interpret.
From OCamlInterp.Automatic.Compile Require Compile.
From OCamlInterp.Automatic.Compile Require CompileProof.

Module DispatchHI <: HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.
End DispatchHI.

Module Check <: CompileSpec DispatchHI.
  Definition step_fn := step_list_of DispatchHI.handle_instr.
  Definition compile_program := OCamlInterp.Automatic.Compile.Compile.compile_program.
  Definition interpret := OCamlInterp.SemiAutomatic.Interpret.Interpret.interpret.
  Definition compiler_correctness := OCamlInterp.Automatic.Compile.CompileProof.compiler_correctness.

  Section __.
  Set Printing All.
  Set Printing Fully Qualified.
  Set Printing Depth 10000000000.
  Set Printing Width 2000.
  Goal True.
    idtac "<compile_program>".
    idtac "<PrintAssumptions>".
    Print Assumptions compile_program.
    idtac "</PrintAssumptions>".
    idtac "</compile_program>".
  Abort.
  Goal True.
    idtac "<interpret>".
    idtac "<PrintAssumptions>".
    Print Assumptions interpret.
    idtac "</PrintAssumptions>".
    idtac "</interpret>".
  Abort.
  Goal True.
    idtac "<compiler_correctness>".
    idtac "<PrintAssumptions>".
    Print Assumptions compiler_correctness.
    idtac "</PrintAssumptions>".
    idtac "</compiler_correctness>".
  Abort.
  End __.
End Check.
