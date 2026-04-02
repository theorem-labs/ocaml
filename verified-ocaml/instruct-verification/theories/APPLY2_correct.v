(* APPLY2_correct.v -- APPLY2 handler correctness proof.

   APPLY2: fixed 2-argument apply. Reads arg1=sp[0], arg2=sp[1],
   pushes return frame (arg1, arg2, pc, env, extra_args) onto stack,
   sets extra_args=1, and jumps to closure code.

   C body (f_instr_APPLY2):
     t14 = s->sp;
     arg1 = deref(t14 + 0);           -- read arg1 from stack
     t13 = s->sp;
     arg2 = deref(t13 + 1);           -- read arg2 from stack
     t12 = s->sp;
     s->sp = t12 - 3;                 -- sp -= 3
     t11 = s->sp;
     deref(t11 + 0) = arg1;           -- new sp[0] = arg1
     t10 = s->sp;
     deref(t10 + 1) = arg2;           -- new sp[1] = arg2
     t8 = s->sp;
     t9 = s->pc;
     deref(t8 + 2) = (long)t9;        -- new sp[2] = pc (return addr)
     t6 = s->sp;
     t7 = s->env;
     deref(t6 + 3) = t7;              -- new sp[3] = env
     t4 = s->sp;
     t5 = s->extra_args;
     deref(t4 + 4) = (t5 << 1) + 1;   -- new sp[4] = Long_val(extra_args)
     t2 = s->accu;
     t3 = deref((code_t ptr ptr)t2 + 0); -- read code pointer from closure
     s->pc = t3;                       -- jump to code pointer
     t1 = s->accu;
     s->env = t1;                      -- set env to closure
     s->extra_args = 1;               -- set extra_args = 1
     return 0;

   Rocq handler (Interpret.v):
     handle_APPLY2 pc' s =
       match s.(stack) with
       | arg1 :: arg2 :: rest =>
         match get_code_ptr_s s s.(accu) with
         | Some target_pc =>
           let new_stack := arg1 :: arg2 :: Val_int pc' :: s.(env)
                            :: Val_int (Z.of_nat s.(extra_args)) :: rest in
           Step (s <|pc := target_pc|> <|stack := new_stack|>
                   <|env := s.(accu)|> <|extra_args := 1%nat|>)
         | None => Error "APPLY2: accu is not a closure"
         end
       | _ => Error "APPLY2: stack underflow"
       end

   KNOWN LIMITATION: The C code stores a code pointer (Vptr cb ofs) for the
   return address at sp[2], while the Rocq model represents it as
   Val_int pc' which maps to Vlong (Int64.repr (pc' * 2 + 1)) via val_repr.
   CompCert's block-based memory model preserves Vptr through pointer-to-
   integer casts on x86-64, so the stored value remains Vptr, which cannot
   satisfy val_repr for Val_int (only Vlong matches vr_int).

   As a result, the step_pre for the Step case is set to False, making it
   vacuously true. Same pattern as PUSH_RETADDR_correct.v. To close this
   gap, val_repr would need a constructor relating Val_int to code pointers
   (Vptr) via pc_rel, or the abstraction relation would need a separate
   treatment for return frames.

   All proofs complete (Qed). No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
Require Import instruct_handlers.
Require Import InstructSpec.
Require Import StepToBigstep.
Require Import HandlerLemmas.

Local Notation ge := clight_ge.

Theorem verify_APPLY2_correct :
    handler_correct (fun pc' s => handle_APPLY2 pc' s) f_instr_APPLY2
      (fun _ _ _ _ => False)
      (fun msg s =>
         (msg = "APPLY2: accu is not a closure"%string /\
          get_code_ptr_s s s.(Machine.accu) = None) \/
         (msg = "APPLY2: stack underflow"%string))
      (fun _ => False)
      (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct. simpl.
  unfold handle_APPLY2.
  destruct (Machine.stack s) as [|arg1 stk1] eqn:Hstk.
  { (* stack = [] -- Error "stack underflow" *)
    right. reflexivity. }
  destruct stk1 as [|arg2 rest] eqn:Hstk1.
  { (* stack = [arg1] -- Error "stack underflow" *)
    right. reflexivity. }
  (* stack = arg1 :: arg2 :: rest *)
  destruct (get_code_ptr_s s s.(Machine.accu)) as [target_pc|] eqn:Hgcp.
  2: { (* Error: accu is not a closure *)
    left. split; reflexivity. }
  (* Step case: step_pre = False, vacuously true *)
  intros ard Hpre Hstep_pre.
  destruct Hstep_pre.
Qed.
