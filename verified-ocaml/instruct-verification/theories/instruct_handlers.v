From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.17".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "gen/instruct_handlers.c".
  Definition normalized := true.
End Info.

Definition _Alloc_small : ident := $"Alloc_small".
Definition _Val_not : ident := $"Val_not".
Definition __190 : ident := $"_190".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _accu : ident := $"accu".
Definition _block : ident := $"block".
Definition _caml_modify : ident := $"caml_modify".
Definition _caml_raise_zero_divide : ident := $"caml_raise_zero_divide".
Definition _divisor : ident := $"divisor".
Definition _env : ident := $"env".
Definition _extra_args : ident := $"extra_args".
Definition _global_data : ident := $"global_data".
Definition _instr_ACC : ident := $"instr_ACC".
Definition _instr_ACC0 : ident := $"instr_ACC0".
Definition _instr_ACC1 : ident := $"instr_ACC1".
Definition _instr_ACC2 : ident := $"instr_ACC2".
Definition _instr_ACC3 : ident := $"instr_ACC3".
Definition _instr_ACC4 : ident := $"instr_ACC4".
Definition _instr_ACC5 : ident := $"instr_ACC5".
Definition _instr_ACC6 : ident := $"instr_ACC6".
Definition _instr_ACC7 : ident := $"instr_ACC7".
Definition _instr_ASSIGN : ident := $"instr_ASSIGN".
Definition _instr_BOOLNOT : ident := $"instr_BOOLNOT".
Definition _instr_BRANCH : ident := $"instr_BRANCH".
Definition _instr_BRANCHIF : ident := $"instr_BRANCHIF".
Definition _instr_BRANCHIFNOT : ident := $"instr_BRANCHIFNOT".
Definition _instr_CHECK_SIGNALS : ident := $"instr_CHECK_SIGNALS".
Definition _instr_CONST0 : ident := $"instr_CONST0".
Definition _instr_CONST1 : ident := $"instr_CONST1".
Definition _instr_CONST2 : ident := $"instr_CONST2".
Definition _instr_CONST3 : ident := $"instr_CONST3".
Definition _instr_CONSTINT : ident := $"instr_CONSTINT".
Definition _instr_DIVINT : ident := $"instr_DIVINT".
Definition _instr_GETFIELD0 : ident := $"instr_GETFIELD0".
Definition _instr_GETFIELD1 : ident := $"instr_GETFIELD1".
Definition _instr_GETFIELD2 : ident := $"instr_GETFIELD2".
Definition _instr_GETFIELD3 : ident := $"instr_GETFIELD3".
Definition _instr_GETGLOBAL : ident := $"instr_GETGLOBAL".
Definition _instr_GETVECTITEM : ident := $"instr_GETVECTITEM".
Definition _instr_ISINT : ident := $"instr_ISINT".
Definition _instr_MAKEBLOCK1 : ident := $"instr_MAKEBLOCK1".
Definition _instr_MAKEBLOCK2 : ident := $"instr_MAKEBLOCK2".
Definition _instr_MAKEBLOCK3 : ident := $"instr_MAKEBLOCK3".
Definition _instr_MODINT : ident := $"instr_MODINT".
Definition _instr_OFFSETINT : ident := $"instr_OFFSETINT".
Definition _instr_OFFSETREF : ident := $"instr_OFFSETREF".
Definition _instr_POP : ident := $"instr_POP".
Definition _instr_PUSH : ident := $"instr_PUSH".
Definition _instr_PUSHACC1 : ident := $"instr_PUSHACC1".
Definition _instr_PUSHACC2 : ident := $"instr_PUSHACC2".
Definition _instr_PUSHACC3 : ident := $"instr_PUSHACC3".
Definition _instr_PUSHACC4 : ident := $"instr_PUSHACC4".
Definition _instr_PUSHACC5 : ident := $"instr_PUSHACC5".
Definition _instr_PUSHACC6 : ident := $"instr_PUSHACC6".
Definition _instr_PUSHACC7 : ident := $"instr_PUSHACC7".
Definition _instr_PUSHATOM : ident := $"instr_PUSHATOM".
Definition _instr_PUSHCONST0 : ident := $"instr_PUSHCONST0".
Definition _instr_PUSHCONST1 : ident := $"instr_PUSHCONST1".
Definition _instr_PUSHCONST2 : ident := $"instr_PUSHCONST2".
Definition _instr_PUSHCONST3 : ident := $"instr_PUSHCONST3".
Definition _instr_PUSHCONSTINT : ident := $"instr_PUSHCONSTINT".
Definition _instr_PUSHGETGLOBAL : ident := $"instr_PUSHGETGLOBAL".
Definition _instr_SETFIELD : ident := $"instr_SETFIELD".
Definition _instr_SETFIELD0 : ident := $"instr_SETFIELD0".
Definition _instr_SETFIELD1 : ident := $"instr_SETFIELD1".
Definition _instr_SETFIELD2 : ident := $"instr_SETFIELD2".
Definition _instr_SETFIELD3 : ident := $"instr_SETFIELD3".
Definition _instr_SETGLOBAL : ident := $"instr_SETGLOBAL".
Definition _instr_SETVECTITEM : ident := $"instr_SETVECTITEM".
Definition _instr_STOP : ident := $"instr_STOP".
Definition _instr_VECTLENGTH : ident := $"instr_VECTLENGTH".
Definition _main : ident := $"main".
Definition _pc : ident := $"pc".
Definition _s : ident := $"s".
Definition _size : ident := $"size".
Definition _sp : ident := $"sp".
Definition _tag : ident := $"tag".
Definition _trap_sp : ident := $"trap_sp".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.

Definition f_instr_ACC0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC5 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 5) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC6 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 6) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC7 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 7) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHACC1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC5 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 5) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC6 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 6) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC7 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 7) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_CONST0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
        (Tstruct __190 noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_CONST1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
        (Tstruct __190 noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_CONST2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
        (Tstruct __190 noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 2) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_CONST3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
        (Tstruct __190 noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 3) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHCONST0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONST1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONST2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 2) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONST3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 3) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_GETFIELD0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETFIELD1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETFIELD2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETFIELD3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_SETFIELD0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'3 tlong)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
          (Etempvar _t'3 tlong)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
          (Etempvar _t'3 tlong)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong)
          (Etempvar _t'3 tlong)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_STOP := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_instr_CHECK_SIGNALS := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition f_instr_ACC := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'4, tlong) :: (_t'3, tint) ::
               (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _t'2 (tptr tlong)) (Etempvar _t'3 tint)
                (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'4 tlong))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_POP := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'3, tint) :: (_t'2, (tptr tlong)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'2 (tptr tlong)) (Etempvar _t'3 tint)
            (tptr tlong))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ASSIGN := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'4, tlong) :: (_t'3, tint) ::
               (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _accu tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'2 (tptr tlong)) (Etempvar _t'3 tint)
                (tptr tlong)) tlong) (Etempvar _t'4 tlong))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_CONSTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, (tptr tint)) :: (_t'1, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _pc (tptr tint)))
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _t'2 (tptr tint)) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong)
        (Ebinop Oadd
          (Ebinop Oshl (Ecast (Etempvar _t'3 tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONSTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'6, (tptr tlong)) ::
               (_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'6 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'5 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl (Ecast (Etempvar _t'4 tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_DIVINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_divisor, tlong) :: (_t'1, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
      (Sset _divisor
        (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
          (Econst_int (Int.repr 1) tint) tlong))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _divisor tlong)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None
        (Evar _caml_raise_zero_divide (Tfunction nil tint
                                        {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
        nil)
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Odiv
                  (Ebinop Oshr (Ecast (Etempvar _t'2 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong)
                  (Etempvar _divisor tlong) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_MODINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_divisor, tlong) :: (_t'1, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
      (Sset _divisor
        (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
          (Econst_int (Int.repr 1) tint) tlong))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _divisor tlong)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None
        (Evar _caml_raise_zero_divide (Tfunction nil tint
                                        {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
        nil)
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Omod
                  (Ebinop Oshr (Ecast (Etempvar _t'2 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong)
                  (Etempvar _divisor tlong) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_ISINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl
          (Ecast
            (Ebinop Oand (Etempvar _t'1 tlong) (Econst_int (Int.repr 1) tint)
              tlong) tlong) (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BOOLNOT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Scall (Some _t'1)
        (Evar _Val_not (Tfunction nil tint
                         {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
        ((Etempvar _t'2 tlong) :: nil)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'1 tint)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_OFFSETINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, (tptr tint)) :: (_t'2, tlong) ::
               (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong)
          (Ebinop Oadd (Etempvar _t'2 tlong)
            (Ebinop Oshl (Etempvar _t'4 tint) (Econst_int (Int.repr 1) tint)
              tint) tlong)))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_OFFSETREF := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tint) :: (_t'5, (tptr tint)) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'6 (Ederef (Etempvar _t'5 (tptr tint)) tint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
              (Ebinop Oadd (Etempvar _t'4 tlong)
                (Ebinop Oshl (Etempvar _t'6 tint)
                  (Econst_int (Int.repr 1) tint) tint) tlong)))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_BRANCH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, (tptr tint)) :: (_t'1, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _pc (tptr tint)))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'2 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Etempvar _t'3 tint)
            (tptr tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BRANCHIF := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tint)) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Sifthenelse (Ebinop One (Etempvar _t'1 tlong)
                   (Ebinop Oadd
                     (Ebinop Oshl
                       (Ecast (Econst_int (Int.repr 0) tint) tlong)
                       (Econst_int (Int.repr 1) tint) tlong)
                     (Econst_int (Int.repr 1) tint) tlong) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'3 (tptr tint)) (Etempvar _t'5 tint)
                (tptr tint))))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BRANCHIFNOT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tint)) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tlong)
                   (Ebinop Oadd
                     (Ebinop Oshl
                       (Ecast (Econst_int (Int.repr 0) tint) tlong)
                       (Econst_int (Int.repr 1) tint) tlong)
                     (Econst_int (Int.repr 1) tint) tlong) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'3 (tptr tint)) (Etempvar _t'5 tint)
                (tptr tint))))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHATOM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_MAKEBLOCK1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuchar) :: (_block, tlong) :: (_t'1, (tptr tint)) ::
               (_t'3, tint) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _tag (Ecast (Etempvar _t'3 tint) tuchar))))
  (Ssequence
    (Scall None
      (Evar _Alloc_small (Tfunction nil tint
                           {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
      ((Etempvar _block tlong) :: (Econst_int (Int.repr 1) tint) ::
       (Etempvar _tag tuchar) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'2 tlong)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong) (Etempvar _block tlong))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_instr_MAKEBLOCK2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuchar) :: (_block, tlong) :: (_t'1, (tptr tint)) ::
               (_t'6, tint) :: (_t'5, tlong) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'6 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _tag (Ecast (Etempvar _t'6 tint) tuchar))))
  (Ssequence
    (Scall None
      (Evar _Alloc_small (Tfunction nil tint
                           {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
      ((Etempvar _block tlong) :: (Econst_int (Int.repr 2) tint) ::
       (Etempvar _tag tuchar) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'5 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Etempvar _t'4 tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _sp (tptr tlong)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _sp (tptr tlong))
              (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _accu tlong)
              (Etempvar _block tlong))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_instr_MAKEBLOCK3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuchar) :: (_block, tlong) :: (_t'1, (tptr tint)) ::
               (_t'8, tint) :: (_t'7, tlong) :: (_t'6, tlong) ::
               (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'8 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _tag (Ecast (Etempvar _t'8 tint) tuchar))))
  (Ssequence
    (Scall None
      (Evar _Alloc_small (Tfunction nil tint
                           {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
      ((Etempvar _block tlong) :: (Econst_int (Int.repr 3) tint) ::
       (Etempvar _tag tuchar) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _accu tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'7 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Etempvar _t'6 tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                (Etempvar _t'4 tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                    (Tstruct __190 noattr)) _sp (tptr tlong)))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                    (Tstruct __190 noattr)) _sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                  (Econst_int (Int.repr 2) tint) (tptr tlong))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                    (Tstruct __190 noattr)) _accu tlong)
                (Etempvar _block tlong))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_SETFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'6, tlong) :: (_t'5, tint) ::
               (_t'4, (tptr tint)) :: (_t'3, tlong) :: (_t'2, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
          (Ssequence
            (Sset _t'6 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
            (Scall None
              (Evar _caml_modify (Tfunction nil tint
                                   {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
              ((Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                 (Etempvar _t'5 tint) (tptr tlong)) ::
               (Etempvar _t'6 tlong) :: nil)))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_VECTLENGTH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_size, tulong) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tuchar) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'4
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) (tptr tlong))
          tlong))
      (Sset _size
        (Ebinop Oshr (Etempvar _t'4 tlong) (Econst_int (Int.repr 10) tint)
          tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Ssequence
        (Sset _t'2
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tuchar))
              (Eunop Oneg (Esizeof tlong tulong) tulong) (tptr tuchar))
            tuchar))
        (Sifthenelse (Ebinop Oeq
                       (Ebinop Oand (Etempvar _t'2 tuchar)
                         (Econst_int (Int.repr 255) tint) tint)
                       (Econst_int (Int.repr 254) tint) tint)
          (Sset _size
            (Ebinop Odiv (Etempvar _size tulong)
              (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong)
                tulong) tulong))
          Sskip)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong)
        (Ebinop Oadd
          (Ebinop Oshl (Ecast (Etempvar _size tulong) tlong)
            (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_GETVECTITEM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tlong) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'5 tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETVECTITEM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tlong) :: (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, tlong) ::
               (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
            (Scall None
              (Evar _caml_modify (Tfunction nil tint
                                   {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
              ((Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                 (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                   (Econst_int (Int.repr 1) tint) tlong) (tptr tlong)) ::
               (Etempvar _t'6 tlong) :: nil)))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_GETGLOBAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tlong)) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _global_data (tptr tlong)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 (tptr tlong)) (tptr tlong))
                (Etempvar _t'4 tint) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'5 tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHGETGLOBAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'8, (tptr tlong)) ::
               (_t'7, tlong) :: (_t'6, tlong) :: (_t'5, tint) ::
               (_t'4, (tptr tint)) :: (_t'3, (tptr tlong)) ::
               (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'8 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'7 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _global_data (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd
                  (Ecast (Etempvar _t'3 (tptr tlong)) (tptr tlong))
                  (Etempvar _t'5 tint) (tptr tlong)) tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                  (Tstruct __190 noattr)) _accu tlong) (Etempvar _t'6 tlong))))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_SETGLOBAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __190 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tlong)) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _global_data (tptr tlong)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
            (Tstruct __190 noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
                (Tstruct __190 noattr)) _accu tlong))
          (Scall None
            (Evar _caml_modify (Tfunction nil tint
                                 {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
            ((Ebinop Oadd (Ecast (Etempvar _t'2 (tptr tlong)) (tptr tlong))
               (Etempvar _t'4 tint) (tptr tlong)) :: (Etempvar _t'5 tlong) ::
             nil))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
          (Tstruct __190 noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct __190 noattr)))
              (Tstruct __190 noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition composites : list composite_definition :=
(Composite __190 Struct
   (Member_plain _pc (tptr tint) :: Member_plain _accu tlong ::
    Member_plain _sp (tptr tlong) :: Member_plain _env tlong ::
    Member_plain _extra_args tlong ::
    Member_plain _global_data (tptr tlong) ::
    Member_plain _trap_sp (tptr tlong) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_instr_ACC0, Gfun(Internal f_instr_ACC0)) ::
 (_instr_ACC1, Gfun(Internal f_instr_ACC1)) ::
 (_instr_ACC2, Gfun(Internal f_instr_ACC2)) ::
 (_instr_ACC3, Gfun(Internal f_instr_ACC3)) ::
 (_instr_ACC4, Gfun(Internal f_instr_ACC4)) ::
 (_instr_ACC5, Gfun(Internal f_instr_ACC5)) ::
 (_instr_ACC6, Gfun(Internal f_instr_ACC6)) ::
 (_instr_ACC7, Gfun(Internal f_instr_ACC7)) ::
 (_instr_PUSH, Gfun(Internal f_instr_PUSH)) ::
 (_instr_PUSHACC1, Gfun(Internal f_instr_PUSHACC1)) ::
 (_instr_PUSHACC2, Gfun(Internal f_instr_PUSHACC2)) ::
 (_instr_PUSHACC3, Gfun(Internal f_instr_PUSHACC3)) ::
 (_instr_PUSHACC4, Gfun(Internal f_instr_PUSHACC4)) ::
 (_instr_PUSHACC5, Gfun(Internal f_instr_PUSHACC5)) ::
 (_instr_PUSHACC6, Gfun(Internal f_instr_PUSHACC6)) ::
 (_instr_PUSHACC7, Gfun(Internal f_instr_PUSHACC7)) ::
 (_instr_CONST0, Gfun(Internal f_instr_CONST0)) ::
 (_instr_CONST1, Gfun(Internal f_instr_CONST1)) ::
 (_instr_CONST2, Gfun(Internal f_instr_CONST2)) ::
 (_instr_CONST3, Gfun(Internal f_instr_CONST3)) ::
 (_instr_PUSHCONST0, Gfun(Internal f_instr_PUSHCONST0)) ::
 (_instr_PUSHCONST1, Gfun(Internal f_instr_PUSHCONST1)) ::
 (_instr_PUSHCONST2, Gfun(Internal f_instr_PUSHCONST2)) ::
 (_instr_PUSHCONST3, Gfun(Internal f_instr_PUSHCONST3)) ::
 (_instr_GETFIELD0, Gfun(Internal f_instr_GETFIELD0)) ::
 (_instr_GETFIELD1, Gfun(Internal f_instr_GETFIELD1)) ::
 (_instr_GETFIELD2, Gfun(Internal f_instr_GETFIELD2)) ::
 (_instr_GETFIELD3, Gfun(Internal f_instr_GETFIELD3)) ::
 (_instr_SETFIELD0, Gfun(Internal f_instr_SETFIELD0)) ::
 (_instr_SETFIELD1, Gfun(Internal f_instr_SETFIELD1)) ::
 (_instr_SETFIELD2, Gfun(Internal f_instr_SETFIELD2)) ::
 (_instr_SETFIELD3, Gfun(Internal f_instr_SETFIELD3)) ::
 (_instr_STOP, Gfun(Internal f_instr_STOP)) ::
 (_instr_CHECK_SIGNALS, Gfun(Internal f_instr_CHECK_SIGNALS)) ::
 (_instr_ACC, Gfun(Internal f_instr_ACC)) ::
 (_instr_POP, Gfun(Internal f_instr_POP)) ::
 (_instr_ASSIGN, Gfun(Internal f_instr_ASSIGN)) ::
 (_instr_CONSTINT, Gfun(Internal f_instr_CONSTINT)) ::
 (_instr_PUSHCONSTINT, Gfun(Internal f_instr_PUSHCONSTINT)) ::
 (_instr_DIVINT, Gfun(Internal f_instr_DIVINT)) ::
 (_caml_raise_zero_divide,
   Gfun(External (EF_external "caml_raise_zero_divide"
                   (mksignature nil AST.Xint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     nil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_instr_MODINT, Gfun(Internal f_instr_MODINT)) ::
 (_instr_ISINT, Gfun(Internal f_instr_ISINT)) ::
 (_Val_not,
   Gfun(External (EF_external "Val_not"
                   (mksignature nil AST.Xint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     nil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_instr_BOOLNOT, Gfun(Internal f_instr_BOOLNOT)) ::
 (_instr_OFFSETINT, Gfun(Internal f_instr_OFFSETINT)) ::
 (_instr_OFFSETREF, Gfun(Internal f_instr_OFFSETREF)) ::
 (_instr_BRANCH, Gfun(Internal f_instr_BRANCH)) ::
 (_instr_BRANCHIF, Gfun(Internal f_instr_BRANCHIF)) ::
 (_instr_BRANCHIFNOT, Gfun(Internal f_instr_BRANCHIFNOT)) ::
 (_instr_PUSHATOM, Gfun(Internal f_instr_PUSHATOM)) ::
 (_instr_MAKEBLOCK1, Gfun(Internal f_instr_MAKEBLOCK1)) ::
 (_instr_MAKEBLOCK2, Gfun(Internal f_instr_MAKEBLOCK2)) ::
 (_Alloc_small,
   Gfun(External (EF_external "Alloc_small"
                   (mksignature nil AST.Xint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     nil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_instr_MAKEBLOCK3, Gfun(Internal f_instr_MAKEBLOCK3)) ::
 (_instr_SETFIELD, Gfun(Internal f_instr_SETFIELD)) ::
 (_instr_VECTLENGTH, Gfun(Internal f_instr_VECTLENGTH)) ::
 (_instr_GETVECTITEM, Gfun(Internal f_instr_GETVECTITEM)) ::
 (_instr_SETVECTITEM, Gfun(Internal f_instr_SETVECTITEM)) ::
 (_instr_GETGLOBAL, Gfun(Internal f_instr_GETGLOBAL)) ::
 (_instr_PUSHGETGLOBAL, Gfun(Internal f_instr_PUSHGETGLOBAL)) ::
 (_caml_modify,
   Gfun(External (EF_external "caml_modify"
                   (mksignature nil AST.Xint
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     nil tint {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_instr_SETGLOBAL, Gfun(Internal f_instr_SETGLOBAL)) :: nil).

Definition public_idents : list ident :=
(_instr_SETGLOBAL :: _caml_modify :: _instr_PUSHGETGLOBAL ::
 _instr_GETGLOBAL :: _instr_SETVECTITEM :: _instr_GETVECTITEM ::
 _instr_VECTLENGTH :: _instr_SETFIELD :: _instr_MAKEBLOCK3 :: _Alloc_small ::
 _instr_MAKEBLOCK2 :: _instr_MAKEBLOCK1 :: _instr_PUSHATOM ::
 _instr_BRANCHIFNOT :: _instr_BRANCHIF :: _instr_BRANCH ::
 _instr_OFFSETREF :: _instr_OFFSETINT :: _instr_BOOLNOT :: _Val_not ::
 _instr_ISINT :: _instr_MODINT :: _caml_raise_zero_divide :: _instr_DIVINT ::
 _instr_PUSHCONSTINT :: _instr_CONSTINT :: _instr_ASSIGN :: _instr_POP ::
 _instr_ACC :: _instr_CHECK_SIGNALS :: _instr_STOP :: _instr_SETFIELD3 ::
 _instr_SETFIELD2 :: _instr_SETFIELD1 :: _instr_SETFIELD0 ::
 _instr_GETFIELD3 :: _instr_GETFIELD2 :: _instr_GETFIELD1 ::
 _instr_GETFIELD0 :: _instr_PUSHCONST3 :: _instr_PUSHCONST2 ::
 _instr_PUSHCONST1 :: _instr_PUSHCONST0 :: _instr_CONST3 :: _instr_CONST2 ::
 _instr_CONST1 :: _instr_CONST0 :: _instr_PUSHACC7 :: _instr_PUSHACC6 ::
 _instr_PUSHACC5 :: _instr_PUSHACC4 :: _instr_PUSHACC3 :: _instr_PUSHACC2 ::
 _instr_PUSHACC1 :: _instr_PUSH :: _instr_ACC7 :: _instr_ACC6 ::
 _instr_ACC5 :: _instr_ACC4 :: _instr_ACC3 :: _instr_ACC2 :: _instr_ACC1 ::
 _instr_ACC0 :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


