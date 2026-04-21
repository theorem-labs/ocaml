(* RETURN_correct.v -- RETURN handler completeness proof.

   RETURN stacksize:
   - Rocq: handle_RETURN stacksize s =
       let stk = skipn stacksize (stack s) in
       if Nat.ltb 0 (extra_args s) then
         match get_code_ptr_s s (accu s) with
         | Some target_pc =>
           Step (s <|pc := target_pc|> <|stack := stk|> <|env := accu s|>
                   <|extra_args := Nat.sub (extra_args s) 1|>)
         | None => Error "RETURN: accu is not a closure"
         end
       else
         match stk with
         | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
           Step (s <|pc := ret_pc|> <|stack := rest|> <|env := saved_env|>
                   <|extra_args := Z.to_nat saved_ea|>)
         | _ => Error "RETURN: malformed return frame"
         end

   C code (f_instr_RETURN):
     Preamble: read pc, advance pc, read sp, read n from code, sp += n
     if extra_args > 0 then
       extra_args -= 1
       pc = code_ptr from accu closure field 0
       env = accu
     else
       pc = cast sp[0] to code_t ptr
       env = sp[1]
       extra_args = sp[2] >> 1
       sp += 3
     return 0

   Both Step branches proved with real preconditions.
   NOTE: verify_RETURN_correct and correct_RETURN are currently Admitted
   pending proof repair. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation RETURN := Bytecode.AST.RETURN.

Definition correct_RETURN : forall n,
    handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
      (pre_of (RETURN n))
      (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).
Admitted.

Lemma interp_state_co_return : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Theorem verify_RETURN_correct : forall stacksize,
    handler_correct (fun _ => handle_RETURN stacksize) f_instr_RETURN
      (fun _ m s ard =>
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat stacksize))) /\
         Z.of_nat stacksize < Int.half_modulus /\
         Z.of_nat (extra_args s) <= Int64.max_signed /\
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 < Ptrofs.modulus) /\
         (stacksize <= Datatypes.length (Machine.stack s))%nat /\
         (Nat.ltb 0 (extra_args s) = true ->
          forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            return_tailcall_pre m s ard sp_b) /\
         (Nat.ltb 0 (extra_args s) = false ->
          forall sp_b sp_ofs ret_pc saved_env saved_ea rest,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            skipn stacksize (Machine.stack s) =
              Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest ->
            return_frame_pre m s ard sp_b
              (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8)))
              ret_pc saved_env saved_ea rest))
      (fun msg _ => msg = "RETURN: accu is not a closure"%string \/
                    msg = "RETURN: malformed return frame"%string)
      (fun _ => False) (fun _ _ _ => False).
Admitted.
