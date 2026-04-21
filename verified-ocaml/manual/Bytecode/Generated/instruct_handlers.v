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
Definition _arg1 : ident := $"arg1".
Definition _arg2 : ident := $"arg2".
Definition _arg3 : ident := $"arg3".
Definition _blksize : ident := $"blksize".
Definition _block : ident := $"block".
Definition _caml_raise_zero_divide : ident := $"caml_raise_zero_divide".
Definition _d : ident := $"d".
Definition _divisor : ident := $"divisor".
Definition _env : ident := $"env".
Definition _envofs : ident := $"envofs".
Definition _extra_args : ident := $"extra_args".
Definition _global_data : ident := $"global_data".
Definition _heap_alloc : ident := $"heap_alloc".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _index : ident := $"index".
Definition _index__1 : ident := $"index__1".
Definition _instr_ACC : ident := $"instr_ACC".
Definition _instr_ACC0 : ident := $"instr_ACC0".
Definition _instr_ACC1 : ident := $"instr_ACC1".
Definition _instr_ACC2 : ident := $"instr_ACC2".
Definition _instr_ACC3 : ident := $"instr_ACC3".
Definition _instr_ACC4 : ident := $"instr_ACC4".
Definition _instr_ACC5 : ident := $"instr_ACC5".
Definition _instr_ACC6 : ident := $"instr_ACC6".
Definition _instr_ACC7 : ident := $"instr_ACC7".
Definition _instr_ADDINT : ident := $"instr_ADDINT".
Definition _instr_ANDINT : ident := $"instr_ANDINT".
Definition _instr_APPLY : ident := $"instr_APPLY".
Definition _instr_APPLY1 : ident := $"instr_APPLY1".
Definition _instr_APPLY2 : ident := $"instr_APPLY2".
Definition _instr_APPLY3 : ident := $"instr_APPLY3".
Definition _instr_APPTERM : ident := $"instr_APPTERM".
Definition _instr_APPTERM1 : ident := $"instr_APPTERM1".
Definition _instr_APPTERM2 : ident := $"instr_APPTERM2".
Definition _instr_APPTERM3 : ident := $"instr_APPTERM3".
Definition _instr_ASRINT : ident := $"instr_ASRINT".
Definition _instr_ASSIGN : ident := $"instr_ASSIGN".
Definition _instr_ATOM : ident := $"instr_ATOM".
Definition _instr_ATOM0 : ident := $"instr_ATOM0".
Definition _instr_BEQ : ident := $"instr_BEQ".
Definition _instr_BGEINT : ident := $"instr_BGEINT".
Definition _instr_BGTINT : ident := $"instr_BGTINT".
Definition _instr_BLEINT : ident := $"instr_BLEINT".
Definition _instr_BLTINT : ident := $"instr_BLTINT".
Definition _instr_BNEQ : ident := $"instr_BNEQ".
Definition _instr_BOOLNOT : ident := $"instr_BOOLNOT".
Definition _instr_BRANCH : ident := $"instr_BRANCH".
Definition _instr_BRANCHIF : ident := $"instr_BRANCHIF".
Definition _instr_BRANCHIFNOT : ident := $"instr_BRANCHIFNOT".
Definition _instr_BUGEINT : ident := $"instr_BUGEINT".
Definition _instr_BULTINT : ident := $"instr_BULTINT".
Definition _instr_CHECK_SIGNALS : ident := $"instr_CHECK_SIGNALS".
Definition _instr_CLOSURE : ident := $"instr_CLOSURE".
Definition _instr_CLOSUREREC : ident := $"instr_CLOSUREREC".
Definition _instr_CONST0 : ident := $"instr_CONST0".
Definition _instr_CONST1 : ident := $"instr_CONST1".
Definition _instr_CONST2 : ident := $"instr_CONST2".
Definition _instr_CONST3 : ident := $"instr_CONST3".
Definition _instr_CONSTINT : ident := $"instr_CONSTINT".
Definition _instr_C_CALL1 : ident := $"instr_C_CALL1".
Definition _instr_C_CALL2 : ident := $"instr_C_CALL2".
Definition _instr_C_CALL3 : ident := $"instr_C_CALL3".
Definition _instr_C_CALL4 : ident := $"instr_C_CALL4".
Definition _instr_C_CALL5 : ident := $"instr_C_CALL5".
Definition _instr_C_CALLN : ident := $"instr_C_CALLN".
Definition _instr_DIVINT : ident := $"instr_DIVINT".
Definition _instr_ENVACC : ident := $"instr_ENVACC".
Definition _instr_ENVACC1 : ident := $"instr_ENVACC1".
Definition _instr_ENVACC2 : ident := $"instr_ENVACC2".
Definition _instr_ENVACC3 : ident := $"instr_ENVACC3".
Definition _instr_ENVACC4 : ident := $"instr_ENVACC4".
Definition _instr_EQ : ident := $"instr_EQ".
Definition _instr_GEINT : ident := $"instr_GEINT".
Definition _instr_GETBYTESCHAR : ident := $"instr_GETBYTESCHAR".
Definition _instr_GETDYNMET : ident := $"instr_GETDYNMET".
Definition _instr_GETFIELD : ident := $"instr_GETFIELD".
Definition _instr_GETFIELD0 : ident := $"instr_GETFIELD0".
Definition _instr_GETFIELD1 : ident := $"instr_GETFIELD1".
Definition _instr_GETFIELD2 : ident := $"instr_GETFIELD2".
Definition _instr_GETFIELD3 : ident := $"instr_GETFIELD3".
Definition _instr_GETFLOATFIELD : ident := $"instr_GETFLOATFIELD".
Definition _instr_GETGLOBAL : ident := $"instr_GETGLOBAL".
Definition _instr_GETGLOBALFIELD : ident := $"instr_GETGLOBALFIELD".
Definition _instr_GETMETHOD : ident := $"instr_GETMETHOD".
Definition _instr_GETPUBMET : ident := $"instr_GETPUBMET".
Definition _instr_GETSTRINGCHAR : ident := $"instr_GETSTRINGCHAR".
Definition _instr_GETVECTITEM : ident := $"instr_GETVECTITEM".
Definition _instr_GRAB : ident := $"instr_GRAB".
Definition _instr_GTINT : ident := $"instr_GTINT".
Definition _instr_ISINT : ident := $"instr_ISINT".
Definition _instr_LEINT : ident := $"instr_LEINT".
Definition _instr_LSLINT : ident := $"instr_LSLINT".
Definition _instr_LSRINT : ident := $"instr_LSRINT".
Definition _instr_LTINT : ident := $"instr_LTINT".
Definition _instr_MAKEBLOCK : ident := $"instr_MAKEBLOCK".
Definition _instr_MAKEBLOCK1 : ident := $"instr_MAKEBLOCK1".
Definition _instr_MAKEBLOCK2 : ident := $"instr_MAKEBLOCK2".
Definition _instr_MAKEBLOCK3 : ident := $"instr_MAKEBLOCK3".
Definition _instr_MAKEFLOATBLOCK : ident := $"instr_MAKEFLOATBLOCK".
Definition _instr_MODINT : ident := $"instr_MODINT".
Definition _instr_MULINT : ident := $"instr_MULINT".
Definition _instr_NEGINT : ident := $"instr_NEGINT".
Definition _instr_NEQ : ident := $"instr_NEQ".
Definition _instr_OFFSETCLOSURE : ident := $"instr_OFFSETCLOSURE".
Definition _instr_OFFSETCLOSURE0 : ident := $"instr_OFFSETCLOSURE0".
Definition _instr_OFFSETCLOSURE3 : ident := $"instr_OFFSETCLOSURE3".
Definition _instr_OFFSETCLOSUREM3 : ident := $"instr_OFFSETCLOSUREM3".
Definition _instr_OFFSETINT : ident := $"instr_OFFSETINT".
Definition _instr_OFFSETREF : ident := $"instr_OFFSETREF".
Definition _instr_ORINT : ident := $"instr_ORINT".
Definition _instr_POP : ident := $"instr_POP".
Definition _instr_POPTRAP : ident := $"instr_POPTRAP".
Definition _instr_PUSH : ident := $"instr_PUSH".
Definition _instr_PUSHACC1 : ident := $"instr_PUSHACC1".
Definition _instr_PUSHACC2 : ident := $"instr_PUSHACC2".
Definition _instr_PUSHACC3 : ident := $"instr_PUSHACC3".
Definition _instr_PUSHACC4 : ident := $"instr_PUSHACC4".
Definition _instr_PUSHACC5 : ident := $"instr_PUSHACC5".
Definition _instr_PUSHACC6 : ident := $"instr_PUSHACC6".
Definition _instr_PUSHACC7 : ident := $"instr_PUSHACC7".
Definition _instr_PUSHATOM : ident := $"instr_PUSHATOM".
Definition _instr_PUSHATOM0 : ident := $"instr_PUSHATOM0".
Definition _instr_PUSHCONST0 : ident := $"instr_PUSHCONST0".
Definition _instr_PUSHCONST1 : ident := $"instr_PUSHCONST1".
Definition _instr_PUSHCONST2 : ident := $"instr_PUSHCONST2".
Definition _instr_PUSHCONST3 : ident := $"instr_PUSHCONST3".
Definition _instr_PUSHCONSTINT : ident := $"instr_PUSHCONSTINT".
Definition _instr_PUSHENVACC : ident := $"instr_PUSHENVACC".
Definition _instr_PUSHENVACC1 : ident := $"instr_PUSHENVACC1".
Definition _instr_PUSHENVACC2 : ident := $"instr_PUSHENVACC2".
Definition _instr_PUSHENVACC3 : ident := $"instr_PUSHENVACC3".
Definition _instr_PUSHENVACC4 : ident := $"instr_PUSHENVACC4".
Definition _instr_PUSHGETGLOBAL : ident := $"instr_PUSHGETGLOBAL".
Definition _instr_PUSHGETGLOBALFIELD : ident := $"instr_PUSHGETGLOBALFIELD".
Definition _instr_PUSHOFFSETCLOSURE : ident := $"instr_PUSHOFFSETCLOSURE".
Definition _instr_PUSHOFFSETCLOSURE0 : ident := $"instr_PUSHOFFSETCLOSURE0".
Definition _instr_PUSHOFFSETCLOSURE3 : ident := $"instr_PUSHOFFSETCLOSURE3".
Definition _instr_PUSHOFFSETCLOSUREM3 : ident := $"instr_PUSHOFFSETCLOSUREM3".
Definition _instr_PUSHTRAP : ident := $"instr_PUSHTRAP".
Definition _instr_PUSH_RETADDR : ident := $"instr_PUSH_RETADDR".
Definition _instr_RAISE : ident := $"instr_RAISE".
Definition _instr_RAISE_NOTRACE : ident := $"instr_RAISE_NOTRACE".
Definition _instr_RERAISE : ident := $"instr_RERAISE".
Definition _instr_RESTART : ident := $"instr_RESTART".
Definition _instr_RETURN : ident := $"instr_RETURN".
Definition _instr_SETBYTESCHAR : ident := $"instr_SETBYTESCHAR".
Definition _instr_SETFIELD : ident := $"instr_SETFIELD".
Definition _instr_SETFIELD0 : ident := $"instr_SETFIELD0".
Definition _instr_SETFIELD1 : ident := $"instr_SETFIELD1".
Definition _instr_SETFIELD2 : ident := $"instr_SETFIELD2".
Definition _instr_SETFIELD3 : ident := $"instr_SETFIELD3".
Definition _instr_SETFLOATFIELD : ident := $"instr_SETFLOATFIELD".
Definition _instr_SETGLOBAL : ident := $"instr_SETGLOBAL".
Definition _instr_SETVECTITEM : ident := $"instr_SETVECTITEM".
Definition _instr_STOP : ident := $"instr_STOP".
Definition _instr_SUBINT : ident := $"instr_SUBINT".
Definition _instr_SWITCH : ident := $"instr_SWITCH".
Definition _instr_UGEINT : ident := $"instr_UGEINT".
Definition _instr_ULTINT : ident := $"instr_ULTINT".
Definition _instr_VECTLENGTH : ident := $"instr_VECTLENGTH".
Definition _instr_XORINT : ident := $"instr_XORINT".
Definition _interp_state : ident := $"interp_state".
Definition _li : ident := $"li".
Definition _main : ident := $"main".
Definition _meths : ident := $"meths".
Definition _mi : ident := $"mi".
Definition _nargs : ident := $"nargs".
Definition _newsp : ident := $"newsp".
Definition _nfuncs : ident := $"nfuncs".
Definition _num_args : ident := $"num_args".
Definition _nvars : ident := $"nvars".
Definition _p : ident := $"p".
Definition _pc : ident := $"pc".
Definition _required : ident := $"required".
Definition _s : ident := $"s".
Definition _size : ident := $"size".
Definition _sizes : ident := $"sizes".
Definition _slotsize : ident := $"slotsize".
Definition _sp : ident := $"sp".
Definition _tag : ident := $"tag".
Definition _trap_sp : ident := $"trap_sp".
Definition _wosize : ident := $"wosize".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_instr_ACC0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC5 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 5) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC6 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 6) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ACC7 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 7) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHACC1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC5 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 5) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC6 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 6) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHACC7 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Econst_int (Int.repr 7) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_ENVACC1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ENVACC2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ENVACC3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ENVACC4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHENVACC1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHENVACC2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHENVACC3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHENVACC4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _t'3 tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_CONST0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
        (Tstruct _interp_state noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_CONST1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
        (Tstruct _interp_state noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_CONST2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
        (Tstruct _interp_state noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 2) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_CONST3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
        (Tstruct _interp_state noattr)) _accu tlong)
    (Ebinop Oadd
      (Ebinop Oshl (Ecast (Econst_int (Int.repr 3) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong) (Econst_int (Int.repr 1) tint)
      tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHCONST0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONST1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONST2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 2) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONST3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 3) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_GETFIELD0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETFIELD1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETFIELD2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETFIELD3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'1 tlong) (tptr tlong))
            (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_SETFIELD0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
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
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
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
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
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
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
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
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_OFFSETCLOSURE := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'3, tint) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd (Etempvar _t'2 tlong)
            (Ebinop Omul (Etempvar _t'3 tint) (Esizeof tlong tulong) tulong)
            tulong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_OFFSETCLOSUREM3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Osub (Etempvar _t'1 tlong)
        (Ebinop Omul (Econst_int (Int.repr 3) tint) (Esizeof tlong tulong)
          tulong) tulong)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_OFFSETCLOSURE0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong) (Etempvar _t'1 tlong)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_OFFSETCLOSURE3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd (Etempvar _t'1 tlong)
        (Ebinop Omul (Econst_int (Int.repr 3) tint) (Esizeof tlong tulong)
          tulong) tulong)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHOFFSETCLOSURE := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tint)) :: (_t'1, (tptr tlong)) ::
               (_t'6, (tptr tlong)) :: (_t'5, tlong) :: (_t'4, tint) ::
               (_t'3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'6 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'5 tlong))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _env tlong))
        (Ssequence
          (Sset _t'4 (Ederef (Etempvar _t'2 (tptr tint)) tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Ebinop Oadd (Etempvar _t'3 tlong)
              (Ebinop Omul (Etempvar _t'4 tint) (Esizeof tlong tulong)
                tulong) tulong)))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHOFFSETCLOSUREM3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'4, (tptr tlong)) ::
               (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'4 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'3 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Ebinop Osub (Etempvar _t'2 tlong)
          (Ebinop Omul (Econst_int (Int.repr 3) tint) (Esizeof tlong tulong)
            tulong) tulong)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHOFFSETCLOSURE0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'4, (tptr tlong)) ::
               (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'4 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'3 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHOFFSETCLOSURE3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'4, (tptr tlong)) ::
               (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'4 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'3 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Ebinop Oadd (Etempvar _t'2 tlong)
          (Ebinop Omul (Econst_int (Int.repr 3) tint) (Esizeof tlong tulong)
            tulong) tulong)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_CHECK_SIGNALS := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence Sskip (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_EQ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Oeq (Ecast (Etempvar _t'2 tlong) tlong)
                  (Ecast (Etempvar _t'3 tlong) tlong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_NEQ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop One (Ecast (Etempvar _t'2 tlong) tlong)
                  (Ecast (Etempvar _t'3 tlong) tlong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_LTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Olt (Ecast (Etempvar _t'2 tlong) tlong)
                  (Ecast (Etempvar _t'3 tlong) tlong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_LEINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Ole (Ecast (Etempvar _t'2 tlong) tlong)
                  (Ecast (Etempvar _t'3 tlong) tlong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Ogt (Ecast (Etempvar _t'2 tlong) tlong)
                  (Ecast (Etempvar _t'3 tlong) tlong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GEINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Oge (Ecast (Etempvar _t'2 tlong) tlong)
                  (Ecast (Etempvar _t'3 tlong) tlong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ULTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Olt (Ecast (Etempvar _t'2 tlong) tulong)
                  (Ecast (Etempvar _t'3 tlong) tulong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_UGEINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Oge (Ecast (Etempvar _t'2 tlong) tulong)
                  (Ecast (Etempvar _t'3 tlong) tulong) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BEQ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Oeq (Ecast (Etempvar _t'2 tint) tlong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tlong) tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BNEQ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop One (Ecast (Etempvar _t'2 tint) tlong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tlong) tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BLTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Olt (Ecast (Etempvar _t'2 tint) tlong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tlong) tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BLEINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Ole (Ecast (Etempvar _t'2 tint) tlong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tlong) tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BGTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Ogt (Ecast (Etempvar _t'2 tint) tlong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tlong) tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BGEINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Oge (Ecast (Etempvar _t'2 tint) tlong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tlong) tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BULTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Olt (Ecast (Etempvar _t'2 tint) tulong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tulong)
                       tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BUGEINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, (tptr tint)) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sifthenelse (Ebinop Oge (Ecast (Etempvar _t'2 tint) tulong)
                       (Ecast
                         (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                           (Econst_int (Int.repr 1) tint) tlong) tulong)
                       tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                    (Etempvar _t'7 tint) (tptr tint))))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETSTRINGCHAR := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tuchar) :: (_t'4, tlong) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tuchar))
                (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong) (tptr tuchar))
              tuchar))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Ebinop Oadd
              (Ebinop Oshl (Ecast (Etempvar _t'5 tuchar) tlong)
                (Econst_int (Int.repr 1) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_GETBYTESCHAR := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tuchar) :: (_t'4, tlong) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tuchar))
                (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong) (tptr tuchar))
              tuchar))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Ebinop Oadd
              (Ebinop Oshl (Ecast (Etempvar _t'5 tuchar) tlong)
                (Econst_int (Int.repr 1) tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETBYTESCHAR := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tlong) :: (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, tlong) ::
               (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tuchar))
                  (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) (tptr tuchar))
                tuchar)
              (Ebinop Oshr (Ecast (Etempvar _t'6 tlong) tlong)
                (Econst_int (Int.repr 1) tint) tlong)))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 2) tint) (tptr tlong))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Ebinop Oadd
          (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_PUSH_RETADDR := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'10, (tptr tlong)) :: (_t'9, tint) ::
               (_t'8, (tptr tint)) :: (_t'7, (tptr tint)) ::
               (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, (tptr tlong)) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'10
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong))
      (Ebinop Osub (Etempvar _t'10 (tptr tlong))
        (Econst_int (Int.repr 3) tint) (tptr tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'9 (Ederef (Etempvar _t'8 (tptr tint)) tint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
              (Ecast
                (Ebinop Oadd (Etempvar _t'7 (tptr tint)) (Etempvar _t'9 tint)
                  (tptr tint)) tlong))))))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _env tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
            (Etempvar _t'5 tlong))))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _extra_args tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                  (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
              (Ebinop Oadd
                (Ebinop Oshl (Ecast (Etempvar _t'3 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_instr_APPLY := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Ssequence
      (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _extra_args tlong)
        (Ebinop Osub (Etempvar _t'5 tint) (Econst_int (Int.repr 1) tint)
          tint))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr (tptr tint)))
              (Econst_int (Int.repr 0) tint) (tptr (tptr tint))) (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Etempvar _t'3 (tptr tint)))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _env tlong)
          (Etempvar _t'1 tlong)))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_APPLY1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_arg1, tlong) :: (_t'12, (tptr tlong)) ::
               (_t'11, (tptr tlong)) :: (_t'10, (tptr tlong)) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tlong)) ::
               (_t'7, tlong) :: (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'12
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sset _arg1
      (Ederef
        (Ebinop Oadd (Etempvar _t'12 (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Osub (Etempvar _t'11 (tptr tlong))
          (Econst_int (Int.repr 3) tint) (tptr tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _t'10 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _arg1 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Ecast (Etempvar _t'9 (tptr tint)) tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _env tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                    (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                (Etempvar _t'7 tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _extra_args tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                      (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong)
                  (Ebinop Oadd
                    (Ebinop Oshl (Ecast (Etempvar _t'5 tlong) tlong)
                      (Econst_int (Int.repr 1) tint) tlong)
                    (Econst_int (Int.repr 1) tint) tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong))
                (Ssequence
                  (Sset _t'3
                    (Ederef
                      (Ebinop Oadd
                        (Ecast (Etempvar _t'2 tlong) (tptr (tptr tint)))
                        (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                      (tptr tint)))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _pc (tptr tint))
                    (Etempvar _t'3 (tptr tint)))))
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _env tlong)
                    (Etempvar _t'1 tlong)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _extra_args tlong)
                    (Econst_int (Int.repr 0) tint))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))
|}.

Definition f_instr_APPLY2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_arg1, tlong) :: (_arg2, tlong) :: (_t'14, (tptr tlong)) ::
               (_t'13, (tptr tlong)) :: (_t'12, (tptr tlong)) ::
               (_t'11, (tptr tlong)) :: (_t'10, (tptr tlong)) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tlong)) ::
               (_t'7, tlong) :: (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'14
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sset _arg1
      (Ederef
        (Ebinop Oadd (Etempvar _t'14 (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
  (Ssequence
    (Ssequence
      (Sset _t'13
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sset _arg2
        (Ederef
          (Ebinop Oadd (Etempvar _t'13 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Osub (Etempvar _t'12 (tptr tlong))
            (Econst_int (Int.repr 3) tint) (tptr tlong))))
      (Ssequence
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'11 (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
            (Etempvar _arg1 tlong)))
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'10 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Etempvar _arg2 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
                      (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                  (Ecast (Etempvar _t'9 (tptr tint)) tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _env tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                        (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong)
                    (Etempvar _t'7 tlong))))
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _extra_args tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                          (Econst_int (Int.repr 4) tint) (tptr tlong)) tlong)
                      (Ebinop Oadd
                        (Ebinop Oshl (Ecast (Etempvar _t'5 tlong) tlong)
                          (Econst_int (Int.repr 1) tint) tlong)
                        (Econst_int (Int.repr 1) tint) tlong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Ssequence
                      (Sset _t'3
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _t'2 tlong) (tptr (tptr tint)))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (tptr tint))) (tptr tint)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _pc (tptr tint))
                        (Etempvar _t'3 (tptr tint)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'1
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _accu tlong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _env tlong)
                        (Etempvar _t'1 tlong)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _extra_args
                          tlong) (Econst_int (Int.repr 1) tint))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
|}.

Definition f_instr_APPLY3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_arg1, tlong) :: (_arg2, tlong) :: (_arg3, tlong) ::
               (_t'16, (tptr tlong)) :: (_t'15, (tptr tlong)) ::
               (_t'14, (tptr tlong)) :: (_t'13, (tptr tlong)) ::
               (_t'12, (tptr tlong)) :: (_t'11, (tptr tlong)) ::
               (_t'10, (tptr tlong)) :: (_t'9, (tptr tint)) ::
               (_t'8, (tptr tlong)) :: (_t'7, tlong) ::
               (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'16
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sset _arg1
      (Ederef
        (Ebinop Oadd (Etempvar _t'16 (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
  (Ssequence
    (Ssequence
      (Sset _t'15
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sset _arg2
        (Ederef
          (Ebinop Oadd (Etempvar _t'15 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'14
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _arg3
          (Ederef
            (Ebinop Oadd (Etempvar _t'14 (tptr tlong))
              (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Ebinop Osub (Etempvar _t'13 (tptr tlong))
              (Econst_int (Int.repr 3) tint) (tptr tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'12 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
              (Etempvar _arg1 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'11 (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                (Etempvar _arg2 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'10 (tptr tlong))
                      (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                  (Etempvar _arg3 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'9
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _pc (tptr tint)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
                          (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong)
                      (Ecast (Etempvar _t'9 (tptr tint)) tlong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _env tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                            (Econst_int (Int.repr 4) tint) (tptr tlong))
                          tlong) (Etempvar _t'7 tlong))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Ssequence
                        (Sset _t'5
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _extra_args
                            tlong))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                              (Econst_int (Int.repr 5) tint) (tptr tlong))
                            tlong)
                          (Ebinop Oadd
                            (Ebinop Oshl (Ecast (Etempvar _t'5 tlong) tlong)
                              (Econst_int (Int.repr 1) tint) tlong)
                            (Econst_int (Int.repr 1) tint) tlong))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'2
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _accu tlong))
                        (Ssequence
                          (Sset _t'3
                            (Ederef
                              (Ebinop Oadd
                                (Ecast (Etempvar _t'2 tlong)
                                  (tptr (tptr tint)))
                                (Econst_int (Int.repr 0) tint)
                                (tptr (tptr tint))) (tptr tint)))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _pc
                              (tptr tint)) (Etempvar _t'3 (tptr tint)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'1
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _accu tlong))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _env tlong)
                            (Etempvar _t'1 tlong)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _extra_args
                              tlong) (Econst_int (Int.repr 2) tint))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))
|}.

Definition f_instr_APPTERM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_nargs, tint) :: (_slotsize, tint) ::
               (_newsp, (tptr tlong)) :: (_i, tint) :: (_t'1, (tptr tint)) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tlong)) ::
               (_t'7, tlong) :: (_t'6, (tptr tlong)) ::
               (_t'5, (tptr tint)) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sset _nargs (Ederef (Etempvar _t'1 (tptr tint)) tint)))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sset _slotsize (Ederef (Etempvar _t'9 (tptr tint)) tint)))
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _newsp
          (Ebinop Osub
            (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
              (Etempvar _slotsize tint) (tptr tlong)) (Etempvar _nargs tint)
            (tptr tlong))))
      (Ssequence
        (Ssequence
          (Sset _i
            (Ebinop Osub (Etempvar _nargs tint)
              (Econst_int (Int.repr 1) tint) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                             (Econst_int (Int.repr 0) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'7
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                        (Etempvar _i tint) (tptr tlong)) tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _newsp (tptr tlong))
                        (Etempvar _i tint) (tptr tlong)) tlong)
                    (Etempvar _t'7 tlong)))))
            (Sset _i
              (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Etempvar _newsp (tptr tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _t'4 tlong) (tptr (tptr tint)))
                      (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                    (tptr tint)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Etempvar _t'5 (tptr tint)))))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _env tlong)
                  (Etempvar _t'3 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _extra_args tlong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _extra_args tlong)
                    (Ebinop Oadd (Etempvar _t'2 tlong)
                      (Ebinop Osub (Etempvar _nargs tint)
                        (Econst_int (Int.repr 1) tint) tint) tlong)))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_instr_APPTERM1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_arg1, tlong) :: (_t'8, (tptr tlong)) :: (_t'7, tint) ::
               (_t'6, (tptr tint)) :: (_t'5, (tptr tlong)) ::
               (_t'4, (tptr tlong)) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'8
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sset _arg1
      (Ederef
        (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tint)) tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Ebinop Osub
              (Ebinop Oadd (Etempvar _t'5 (tptr tlong)) (Etempvar _t'7 tint)
                (tptr tlong)) (Econst_int (Int.repr 1) tint) (tptr tlong))))))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _arg1 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr (tptr tint)))
                  (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Etempvar _t'3 (tptr tint)))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _env tlong)
              (Etempvar _t'1 tlong)))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_instr_APPTERM2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_arg1, tlong) :: (_arg2, tlong) :: (_t'11, (tptr tlong)) ::
               (_t'10, (tptr tlong)) :: (_t'9, tint) ::
               (_t'8, (tptr tint)) :: (_t'7, (tptr tlong)) ::
               (_t'6, (tptr tlong)) :: (_t'5, (tptr tlong)) ::
               (_t'4, (tptr tint)) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'11
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sset _arg1
      (Ederef
        (Ebinop Oadd (Etempvar _t'11 (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sset _arg2
        (Ederef
          (Ebinop Oadd (Etempvar _t'10 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'9 (Ederef (Etempvar _t'8 (tptr tint)) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong))
              (Ebinop Osub
                (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                  (Etempvar _t'9 tint) (tptr tlong))
                (Econst_int (Int.repr 2) tint) (tptr tlong))))))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
            (Etempvar _arg1 tlong)))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Etempvar _arg2 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Ssequence
                (Sset _t'4
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _t'3 tlong) (tptr (tptr tint)))
                      (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                    (tptr tint)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Etempvar _t'4 (tptr tint)))))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _env tlong)
                  (Etempvar _t'2 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _extra_args tlong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _extra_args tlong)
                    (Ebinop Oadd (Etempvar _t'1 tlong)
                      (Econst_int (Int.repr 1) tint) tlong)))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_instr_APPTERM3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_arg1, tlong) :: (_arg2, tlong) :: (_arg3, tlong) ::
               (_t'13, (tptr tlong)) :: (_t'12, (tptr tlong)) ::
               (_t'11, (tptr tlong)) :: (_t'10, tint) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tlong)) ::
               (_t'7, (tptr tlong)) :: (_t'6, (tptr tlong)) ::
               (_t'5, (tptr tlong)) :: (_t'4, (tptr tint)) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'13
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sset _arg1
      (Ederef
        (Ebinop Oadd (Etempvar _t'13 (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)))
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sset _arg2
        (Ederef
          (Ebinop Oadd (Etempvar _t'12 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _arg3
          (Ederef
            (Ebinop Oadd (Etempvar _t'11 (tptr tlong))
              (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'10 (Ederef (Etempvar _t'9 (tptr tint)) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Ebinop Osub
                  (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
                    (Etempvar _t'10 tint) (tptr tlong))
                  (Econst_int (Int.repr 3) tint) (tptr tlong))))))
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
              (Etempvar _arg1 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
                (Etempvar _arg2 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                      (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                  (Etempvar _arg3 tlong)))
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong))
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd
                          (Ecast (Etempvar _t'3 tlong) (tptr (tptr tint)))
                          (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                        (tptr tint)))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _pc (tptr tint))
                      (Etempvar _t'4 (tptr tint)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _env tlong)
                      (Etempvar _t'2 tlong)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'1
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _extra_args
                          tlong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _extra_args
                          tlong)
                        (Ebinop Oadd (Etempvar _t'1 tlong)
                          (Econst_int (Int.repr 2) tint) tlong)))
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))
|}.

Definition f_instr_RETURN := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'15, tint) ::
               (_t'14, (tptr tlong)) :: (_t'13, tlong) ::
               (_t'12, (tptr tint)) :: (_t'11, tlong) :: (_t'10, tlong) ::
               (_t'9, tlong) :: (_t'8, (tptr tlong)) :: (_t'7, tlong) ::
               (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'14
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'15 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'14 (tptr tlong)) (Etempvar _t'15 tint)
            (tptr tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _extra_args tlong))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tlong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _extra_args tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _extra_args tlong)
              (Ebinop Osub (Etempvar _t'13 tlong)
                (Econst_int (Int.repr 1) tint) tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Ssequence
                (Sset _t'12
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _t'11 tlong) (tptr (tptr tint)))
                      (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                    (tptr tint)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Etempvar _t'12 (tptr tint)))))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _env tlong)
                (Etempvar _t'10 tlong)))))
        (Ssequence
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint))
                (Ecast (Etempvar _t'9 tlong) tint))))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'7
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _env tlong)
                  (Etempvar _t'7 tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                        (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _extra_args tlong)
                    (Ebinop Oshr (Ecast (Etempvar _t'5 tlong) tlong)
                      (Econst_int (Int.repr 1) tint) tlong))))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                    (Econst_int (Int.repr 3) tint) (tptr tlong)))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_RESTART := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_num_args, tint) :: (_i, tint) :: (_t'9, tlong) ::
               (_t'8, tlong) :: (_t'7, (tptr tlong)) :: (_t'6, tlong) ::
               (_t'5, tlong) :: (_t'4, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'8
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _env tlong))
    (Ssequence
      (Sset _t'9
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'8 tlong) (tptr tlong))
            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) (tptr tlong))
          tlong))
      (Sset _num_args
        (Ecast
          (Ebinop Osub
            (Ebinop Oshr (Etempvar _t'9 tlong)
              (Econst_int (Int.repr 10) tint) tlong)
            (Econst_int (Int.repr 3) tint) tlong) tint))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Osub (Etempvar _t'7 (tptr tlong)) (Etempvar _num_args tint)
          (tptr tlong))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Etempvar _num_args tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _env tlong))
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd (Ecast (Etempvar _t'5 tlong) (tptr tlong))
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 3) tint) tint) (tptr tlong))
                      tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                        (Etempvar _i tint) (tptr tlong)) tlong)
                    (Etempvar _t'6 tlong))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _env tlong))
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                  (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _env tlong)
              (Etempvar _t'3 tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _extra_args tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _extra_args tlong)
              (Ebinop Oadd (Etempvar _t'1 tlong) (Etempvar _num_args tint)
                tlong)))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_instr_GRAB := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_required, tint) :: (_num_args, tulong) :: (_i, tulong) ::
               (_t'2, tlong) :: (_t'1, (tptr tint)) :: (_t'21, tlong) ::
               (_t'20, tlong) :: (_t'19, tlong) :: (_t'18, tlong) ::
               (_t'17, tlong) :: (_t'16, (tptr tlong)) :: (_t'15, tlong) ::
               (_t'14, (tptr tint)) :: (_t'13, tlong) :: (_t'12, tlong) ::
               (_t'11, (tptr tlong)) :: (_t'10, tlong) ::
               (_t'9, (tptr tlong)) :: (_t'8, tlong) ::
               (_t'7, (tptr tlong)) :: (_t'6, tlong) ::
               (_t'5, (tptr tlong)) :: (_t'4, (tptr tlong)) ::
               (_t'3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sset _required (Ederef (Etempvar _t'1 (tptr tint)) tint)))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _extra_args tlong))
      (Sifthenelse (Ebinop Oge (Etempvar _t'3 tlong)
                     (Etempvar _required tint) tint)
        (Ssequence
          (Sset _t'21
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _extra_args tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _extra_args tlong)
            (Ebinop Osub (Etempvar _t'21 tlong) (Etempvar _required tint)
              tlong)))
        (Ssequence
          (Ssequence
            (Sset _t'20
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _extra_args tlong))
            (Sset _num_args
              (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                (Etempvar _t'20 tlong) tlong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _heap_alloc (Tfunction
                                    ((tptr (Tstruct _interp_state noattr)) ::
                                     tlong :: tlong :: nil) tlong cc_default))
                ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                 (Ebinop Oadd (Etempvar _num_args tulong)
                   (Econst_int (Int.repr 3) tint) tulong) ::
                 (Econst_int (Int.repr 247) tint) :: nil))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong)
                (Etempvar _t'2 tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'18
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong))
                (Ssequence
                  (Sset _t'19
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _env tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Ecast (Etempvar _t'18 tlong) (tptr tlong))
                        (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                    (Etempvar _t'19 tlong))))
              (Ssequence
                (Ssequence
                  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                     (Etempvar _num_args tulong) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _t'15
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _accu tlong))
                        (Ssequence
                          (Sset _t'16
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _sp
                              (tptr tlong)))
                          (Ssequence
                            (Sset _t'17
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'16 (tptr tlong))
                                  (Etempvar _i tulong) (tptr tlong)) tlong))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Ecast (Etempvar _t'15 tlong) (tptr tlong))
                                  (Ebinop Oadd (Etempvar _i tulong)
                                    (Econst_int (Int.repr 3) tint) tulong)
                                  (tptr tlong)) tlong)
                              (Etempvar _t'17 tlong))))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'13
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Ssequence
                      (Sset _t'14
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _pc (tptr tint)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _t'13 tlong) (tptr (tptr tint)))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (tptr tint))) (tptr tint))
                        (Ebinop Osub (Etempvar _t'14 (tptr tint))
                          (Econst_int (Int.repr 3) tint) (tptr tint)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'12
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _accu tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _t'12 tlong) (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong))
                          tlong)
                        (Ebinop Oor
                          (Ecast
                            (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                              (Econst_int (Int.repr 1) tint) tint) tlong)
                          (Econst_int (Int.repr 1) tint) tlong)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _sp
                            (tptr tlong)))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _sp
                            (tptr tlong))
                          (Ebinop Oadd (Etempvar _t'11 (tptr tlong))
                            (Etempvar _num_args tulong) (tptr tlong))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'9
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _sp
                              (tptr tlong)))
                          (Ssequence
                            (Sset _t'10
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'9 (tptr tlong))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr tlong)) tlong))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                  (Tstruct _interp_state noattr)) _pc
                                (tptr tint))
                              (Ecast (Etempvar _t'10 tlong) tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                  (Tstruct _interp_state noattr)) _sp
                                (tptr tlong)))
                            (Ssequence
                              (Sset _t'8
                                (Ederef
                                  (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tlong)) tlong))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                    (Tstruct _interp_state noattr)) _env
                                  tlong) (Etempvar _t'8 tlong))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                    (Tstruct _interp_state noattr)) _sp
                                  (tptr tlong)))
                              (Ssequence
                                (Sset _t'6
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tlong)) tlong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                      (Tstruct _interp_state noattr))
                                    _extra_args tlong)
                                  (Ebinop Oshr
                                    (Ecast (Etempvar _t'6 tlong) tlong)
                                    (Econst_int (Int.repr 1) tint) tlong))))
                            (Ssequence
                              (Sset _t'4
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                    (Tstruct _interp_state noattr)) _sp
                                  (tptr tlong)))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                    (Tstruct _interp_state noattr)) _sp
                                  (tptr tlong))
                                (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                                  (Econst_int (Int.repr 3) tint)
                                  (tptr tlong))))))))))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_CLOSURE := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_nvars, tint) :: (_i, tint) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, (tptr tlong)) ::
               (_t'1, (tptr tint)) :: (_t'19, (tptr tlong)) ::
               (_t'18, tlong) :: (_t'17, tlong) :: (_t'16, (tptr tlong)) ::
               (_t'15, tlong) :: (_t'14, tlong) :: (_t'13, (tptr tlong)) ::
               (_t'12, tlong) :: (_t'11, tint) :: (_t'10, (tptr tint)) ::
               (_t'9, (tptr tint)) :: (_t'8, tlong) :: (_t'7, tlong) ::
               (_t'6, (tptr tint)) :: (_t'5, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sset _nvars (Ederef (Etempvar _t'1 (tptr tint)) tint)))
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _nvars tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'19
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sset _t'2
              (Ecast
                (Ebinop Osub (Etempvar _t'19 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong))
            (Etempvar _t'2 (tptr tlong))))
        (Ssequence
          (Sset _t'18
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Sassign (Ederef (Etempvar _t'2 (tptr tlong)) tlong)
            (Etempvar _t'18 tlong))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _nvars tint)
                     (Ebinop Osub (Econst_int (Int.repr 256) tint)
                       (Econst_int (Int.repr 2) tint) tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _heap_alloc (Tfunction
                                  ((tptr (Tstruct _interp_state noattr)) ::
                                   tlong :: tlong :: nil) tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Ebinop Oadd (Econst_int (Int.repr 2) tint)
                 (Etempvar _nvars tint) tint) ::
               (Econst_int (Int.repr 247) tint) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'3 tlong)))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _nvars tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'15
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong))
                  (Ssequence
                    (Sset _t'16
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Ssequence
                      (Sset _t'17
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'16 (tptr tlong))
                            (Etempvar _i tint) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _t'15 tlong) (tptr tlong))
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 2) tint) tint)
                            (tptr tlong)) tlong) (Etempvar _t'17 tlong))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _heap_alloc (Tfunction
                                  ((tptr (Tstruct _interp_state noattr)) ::
                                   tlong :: tlong :: nil) tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Ebinop Oadd (Econst_int (Int.repr 2) tint)
                 (Etempvar _nvars tint) tint) ::
               (Econst_int (Int.repr 247) tint) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'4 tlong)))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _nvars tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong))
                  (Ssequence
                    (Sset _t'13
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                    (Ssequence
                      (Sset _t'14
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'13 (tptr tlong))
                            (Etempvar _i tint) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _t'12 tlong) (tptr tlong))
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 2) tint) tint)
                            (tptr tlong)) tlong) (Etempvar _t'14 tlong))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))))
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'11 (Ederef (Etempvar _t'10 (tptr tint)) tint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Ecast (Etempvar _t'8 tlong) (tptr (tptr tint)))
                      (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                    (tptr tint))
                  (Ebinop Oadd (Etempvar _t'9 (tptr tint))
                    (Etempvar _t'11 tint) (tptr tint)))))))
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'7 tlong) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Ebinop Oor
                (Ecast
                  (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                    (Econst_int (Int.repr 1) tint) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint))
                (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                  (Econst_int (Int.repr 1) tint) (tptr tint))))
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                    (Etempvar _nvars tint) (tptr tlong))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_CLOSUREREC := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_nfuncs, tint) :: (_nvars, tint) :: (_envofs, tulong) ::
               (_blksize, tulong) :: (_i, tint) :: (_p, (tptr tlong)) ::
               (_t'12, (tptr tlong)) :: (_t'11, (tptr tlong)) ::
               (_t'10, (tptr tlong)) :: (_t'9, (tptr tlong)) ::
               (_t'8, (tptr tlong)) :: (_t'7, (tptr tlong)) ::
               (_t'6, (tptr tlong)) :: (_t'5, tlong) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tint)) ::
               (_t'1, (tptr tint)) :: (_t'32, (tptr tlong)) ::
               (_t'31, tlong) :: (_t'30, tlong) :: (_t'29, tlong) ::
               (_t'28, (tptr tlong)) :: (_t'27, tlong) :: (_t'26, tlong) ::
               (_t'25, (tptr tlong)) :: (_t'24, (tptr tlong)) ::
               (_t'23, (tptr tlong)) :: (_t'22, tlong) :: (_t'21, tlong) ::
               (_t'20, tint) :: (_t'19, (tptr tint)) ::
               (_t'18, (tptr tint)) :: (_t'17, (tptr tlong)) ::
               (_t'16, tint) :: (_t'15, (tptr tint)) ::
               (_t'14, (tptr tint)) :: (_t'13, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sset _nfuncs (Ederef (Etempvar _t'1 (tptr tint)) tint)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sset _nvars (Ederef (Etempvar _t'2 (tptr tint)) tint)))
    (Ssequence
      (Sset _envofs
        (Ecast
          (Ebinop Osub
            (Ebinop Omul (Etempvar _nfuncs tint)
              (Econst_int (Int.repr 3) tint) tint)
            (Econst_int (Int.repr 1) tint) tint) tulong))
      (Ssequence
        (Sset _blksize
          (Ebinop Oadd (Etempvar _envofs tulong) (Etempvar _nvars tint)
            tulong))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _nvars tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'32
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Sset _t'3
                    (Ecast
                      (Ebinop Osub (Etempvar _t'32 (tptr tlong))
                        (Econst_int (Int.repr 1) tint) (tptr tlong))
                      (tptr tlong))))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Etempvar _t'3 (tptr tlong))))
              (Ssequence
                (Sset _t'31
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong))
                (Sassign (Ederef (Etempvar _t'3 (tptr tlong)) tlong)
                  (Etempvar _t'31 tlong))))
            Sskip)
          (Ssequence
            (Sifthenelse (Ebinop Ole (Etempvar _blksize tulong)
                           (Econst_int (Int.repr 256) tint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _heap_alloc (Tfunction
                                        ((tptr (Tstruct _interp_state noattr)) ::
                                         tlong :: tlong :: nil) tlong
                                        cc_default))
                    ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                     (Etempvar _blksize tulong) ::
                     (Econst_int (Int.repr 247) tint) :: nil))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                    (Etempvar _t'4 tlong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'30
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Sset _p
                      (Ebinop Oadd
                        (Ecast (Etempvar _t'30 tlong) (tptr tlong))
                        (Etempvar _envofs tulong) (tptr tlong))))
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                       (Etempvar _nvars tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _t'28
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _sp
                              (tptr tlong)))
                          (Ssequence
                            (Sset _t'29
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'28 (tptr tlong))
                                  (Etempvar _i tint) (tptr tlong)) tlong))
                            (Sassign
                              (Ederef (Etempvar _p (tptr tlong)) tlong)
                              (Etempvar _t'29 tlong)))))
                      (Ssequence
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))
                        (Sset _p
                          (Ebinop Oadd (Etempvar _p (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong))))))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _heap_alloc (Tfunction
                                        ((tptr (Tstruct _interp_state noattr)) ::
                                         tlong :: tlong :: nil) tlong
                                        cc_default))
                    ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
                     (Etempvar _blksize tulong) ::
                     (Econst_int (Int.repr 247) tint) :: nil))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                    (Etempvar _t'5 tlong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'27
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Sset _p
                      (Ebinop Oadd
                        (Ecast (Etempvar _t'27 tlong) (tptr tlong))
                        (Etempvar _envofs tulong) (tptr tlong))))
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                       (Etempvar _nvars tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _t'25
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _sp
                              (tptr tlong)))
                          (Ssequence
                            (Sset _t'26
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'25 (tptr tlong))
                                  (Etempvar _i tint) (tptr tlong)) tlong))
                            (Sassign
                              (Ederef (Etempvar _p (tptr tlong)) tlong)
                              (Etempvar _t'26 tlong)))))
                      (Ssequence
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))
                        (Sset _p
                          (Ebinop Oadd (Etempvar _p (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong)))))))))
            (Ssequence
              (Ssequence
                (Sset _t'24
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'24 (tptr tlong))
                    (Etempvar _nvars tint) (tptr tlong))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'23
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Sset _t'6
                        (Ecast
                          (Ebinop Osub (Etempvar _t'23 (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong))
                          (tptr tlong))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _sp (tptr tlong))
                      (Etempvar _t'6 (tptr tlong))))
                  (Ssequence
                    (Sset _t'22
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Sassign (Ederef (Etempvar _t'6 (tptr tlong)) tlong)
                      (Etempvar _t'22 tlong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'21
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Sset _p
                      (Ebinop Oadd
                        (Ecast (Etempvar _t'21 tlong) (tptr tlong))
                        (Econst_int (Int.repr 0) tint) (tptr tlong))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'7 (Etempvar _p (tptr tlong)))
                        (Sset _p
                          (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                            (Econst_int (Int.repr 1) tint) (tptr tlong))))
                      (Ssequence
                        (Sset _t'18
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                              (Tstruct _interp_state noattr)) _pc
                            (tptr tint)))
                        (Ssequence
                          (Sset _t'19
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                (Tstruct _interp_state noattr)) _pc
                              (tptr tint)))
                          (Ssequence
                            (Sset _t'20
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'19 (tptr tint))
                                  (Econst_int (Int.repr 0) tint) (tptr tint))
                                tint))
                            (Sassign
                              (Ederef (Etempvar _t'7 (tptr tlong)) tlong)
                              (Ecast
                                (Ebinop Oadd (Etempvar _t'18 (tptr tint))
                                  (Etempvar _t'20 tint) (tptr tint)) tlong))))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'8 (Etempvar _p (tptr tlong)))
                          (Sset _p
                            (Ebinop Oadd (Etempvar _t'8 (tptr tlong))
                              (Econst_int (Int.repr 1) tint) (tptr tlong))))
                        (Sassign (Ederef (Etempvar _t'8 (tptr tlong)) tlong)
                          (Ebinop Oor
                            (Ecast
                              (Ebinop Oshl (Etempvar _envofs tulong)
                                (Econst_int (Int.repr 1) tint) tulong) tlong)
                            (Econst_int (Int.repr 1) tint) tlong)))
                      (Ssequence
                        (Ssequence
                          (Sset _i (Econst_int (Int.repr 1) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                             (Etempvar _nfuncs tint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9 (Etempvar _p (tptr tlong)))
                                    (Sset _p
                                      (Ebinop Oadd
                                        (Etempvar _t'9 (tptr tlong))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tlong))))
                                  (Sassign
                                    (Ederef (Etempvar _t'9 (tptr tlong))
                                      tlong)
                                    (Ecast
                                      (Ebinop Oor
                                        (Ebinop Oshl
                                          (Ebinop Omul (Etempvar _i tint)
                                            (Econst_int (Int.repr 3) tint)
                                            tint)
                                          (Econst_int (Int.repr 10) tint)
                                          tint)
                                        (Econst_int (Int.repr 249) tint)
                                        tint) tlong)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'17
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                              (Tstruct _interp_state noattr))
                                            _sp (tptr tlong)))
                                        (Sset _t'10
                                          (Ecast
                                            (Ebinop Osub
                                              (Etempvar _t'17 (tptr tlong))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tlong)) (tptr tlong))))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                            (Tstruct _interp_state noattr))
                                          _sp (tptr tlong))
                                        (Etempvar _t'10 (tptr tlong))))
                                    (Sassign
                                      (Ederef (Etempvar _t'10 (tptr tlong))
                                        tlong)
                                      (Ecast (Etempvar _p (tptr tlong))
                                        tlong)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'11
                                          (Etempvar _p (tptr tlong)))
                                        (Sset _p
                                          (Ebinop Oadd
                                            (Etempvar _t'11 (tptr tlong))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tlong))))
                                      (Ssequence
                                        (Sset _t'14
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                              (Tstruct _interp_state noattr))
                                            _pc (tptr tint)))
                                        (Ssequence
                                          (Sset _t'15
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                                (Tstruct _interp_state noattr))
                                              _pc (tptr tint)))
                                          (Ssequence
                                            (Sset _t'16
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'15 (tptr tint))
                                                  (Etempvar _i tint)
                                                  (tptr tint)) tint))
                                            (Sassign
                                              (Ederef
                                                (Etempvar _t'11 (tptr tlong))
                                                tlong)
                                              (Ecast
                                                (Ebinop Oadd
                                                  (Etempvar _t'14 (tptr tint))
                                                  (Etempvar _t'16 tint)
                                                  (tptr tint)) tlong))))))
                                    (Ssequence
                                      (Sset _envofs
                                        (Ebinop Osub
                                          (Etempvar _envofs tulong)
                                          (Econst_int (Int.repr 3) tint)
                                          tulong))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'12
                                            (Etempvar _p (tptr tlong)))
                                          (Sset _p
                                            (Ebinop Oadd
                                              (Etempvar _t'12 (tptr tlong))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tlong))))
                                        (Sassign
                                          (Ederef
                                            (Etempvar _t'12 (tptr tlong))
                                            tlong)
                                          (Ebinop Oor
                                            (Ecast
                                              (Ebinop Oshl
                                                (Etempvar _envofs tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong) tlong)
                                            (Econst_int (Int.repr 1) tint)
                                            tlong))))))))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                  (Tstruct _interp_state noattr)) _pc
                                (tptr tint)))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                                  (Tstruct _interp_state noattr)) _pc
                                (tptr tint))
                              (Ebinop Oadd (Etempvar _t'13 (tptr tint))
                                (Etempvar _nfuncs tint) (tptr tint))))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))
|}.

Definition f_instr_GETGLOBALFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'10, tlong) :: (_t'9, tint) :: (_t'8, (tptr tint)) ::
               (_t'7, (tptr tlong)) :: (_t'6, (tptr tint)) ::
               (_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'7
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _global_data (tptr tlong)))
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'9 (Ederef (Etempvar _t'8 (tptr tint)) tint))
        (Ssequence
          (Sset _t'10
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'7 (tptr tlong)) (tptr tlong))
                (Etempvar _t'9 tint) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _t'10 tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'6 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
            (Ssequence
              (Sset _t'5
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                    (Etempvar _t'4 tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong)
                (Etempvar _t'5 tlong))))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Ebinop Oadd (Etempvar _t'1 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_instr_PUSHGETGLOBALFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'13, (tptr tlong)) ::
               (_t'12, tlong) :: (_t'11, tlong) :: (_t'10, tint) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tlong)) ::
               (_t'7, (tptr tint)) :: (_t'6, tlong) :: (_t'5, tint) ::
               (_t'4, (tptr tint)) :: (_t'3, tlong) :: (_t'2, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'13
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'13 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'12 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _global_data (tptr tlong)))
      (Ssequence
        (Sset _t'9
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'10 (Ederef (Etempvar _t'9 (tptr tint)) tint))
          (Ssequence
            (Sset _t'11
              (Ederef
                (Ebinop Oadd
                  (Ecast (Etempvar _t'8 (tptr tlong)) (tptr tlong))
                  (Etempvar _t'10 tint) (tptr tlong)) tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'11 tlong))))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'7 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
              (Ssequence
                (Sset _t'6
                  (Ederef
                    (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                      (Etempvar _t'5 tint) (tptr tlong)) tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _accu tlong)
                  (Etempvar _t'6 tlong))))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'2 (tptr tint))
                (Econst_int (Int.repr 1) tint) (tptr tint))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_instr_MAKEBLOCK := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_wosize, tulong) :: (_tag, tuchar) :: (_i, tulong) ::
               (_block, tlong) :: (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, (tptr tint)) :: (_t'1, (tptr tint)) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tlong) :: (_t'9, tlong) ::
               (_t'8, tlong) :: (_t'7, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'12 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _wosize (Ecast (Etempvar _t'12 tint) tulong))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Ssequence
        (Sset _t'11 (Ederef (Etempvar _t'2 (tptr tint)) tint))
        (Sset _tag (Ecast (Etempvar _t'11 tint) tuchar))))
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _wosize tulong)
                     (Econst_int (Int.repr 256) tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _heap_alloc (Tfunction
                                  ((tptr (Tstruct _interp_state noattr)) ::
                                   tlong :: tlong :: nil) tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Etempvar _wosize tulong) :: (Etempvar _tag tuchar) :: nil))
            (Sset _block (Etempvar _t'3 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                (Etempvar _t'10 tlong)))
            (Ssequence
              (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                 (Etempvar _wosize tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong))
                        (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                          (Econst_int (Int.repr 1) tint) (tptr tlong))))
                    (Ssequence
                      (Sset _t'9 (Ederef (Etempvar _t'4 (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _block tlong) (tptr tlong))
                            (Etempvar _i tulong) (tptr tlong)) tlong)
                        (Etempvar _t'9 tlong)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _heap_alloc (Tfunction
                                  ((tptr (Tstruct _interp_state noattr)) ::
                                   tlong :: tlong :: nil) tlong cc_default))
              ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
               (Etempvar _wosize tulong) :: (Etempvar _tag tuchar) :: nil))
            (Sset _block (Etempvar _t'5 tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                (Etempvar _t'8 tlong)))
            (Ssequence
              (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                 (Etempvar _wosize tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                            (Tstruct _interp_state noattr)) _sp (tptr tlong))
                        (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                          (Econst_int (Int.repr 1) tint) (tptr tlong))))
                    (Ssequence
                      (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _block tlong) (tptr tlong))
                            (Etempvar _i tulong) (tptr tlong)) tlong)
                        (Etempvar _t'7 tlong)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tulong)
                    (Econst_int (Int.repr 1) tint) tulong)))))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _block tlong))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_instr_MAKEBLOCK1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuchar) :: (_block, tlong) :: (_t'2, tlong) ::
               (_t'1, (tptr tint)) :: (_t'4, tint) :: (_t'3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'4 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _tag (Ecast (Etempvar _t'4 tint) tuchar))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _heap_alloc (Tfunction
                            ((tptr (Tstruct _interp_state noattr)) ::
                             tlong :: tlong :: nil) tlong cc_default))
        ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
         (Econst_int (Int.repr 1) tint) :: (Etempvar _tag tuchar) :: nil))
      (Sset _block (Etempvar _t'2 tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'3 tlong)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Etempvar _block tlong))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_instr_MAKEBLOCK2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuchar) :: (_block, tlong) :: (_t'2, tlong) ::
               (_t'1, (tptr tint)) :: (_t'7, tint) :: (_t'6, tlong) ::
               (_t'5, tlong) :: (_t'4, (tptr tlong)) ::
               (_t'3, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'7 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _tag (Ecast (Etempvar _t'7 tint) tuchar))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _heap_alloc (Tfunction
                            ((tptr (Tstruct _interp_state noattr)) ::
                             tlong :: tlong :: nil) tlong cc_default))
        ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
         (Econst_int (Int.repr 2) tint) :: (Etempvar _tag tuchar) :: nil))
      (Sset _block (Etempvar _t'2 tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'6 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'5
              (Ederef
                (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Etempvar _t'5 tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong))
              (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _block tlong))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_instr_MAKEBLOCK3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuchar) :: (_block, tlong) :: (_t'2, tlong) ::
               (_t'1, (tptr tint)) :: (_t'9, tint) :: (_t'8, tlong) ::
               (_t'7, tlong) :: (_t'6, (tptr tlong)) :: (_t'5, tlong) ::
               (_t'4, (tptr tlong)) :: (_t'3, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'9 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _tag (Ecast (Etempvar _t'9 tint) tuchar))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _heap_alloc (Tfunction
                            ((tptr (Tstruct _interp_state noattr)) ::
                             tlong :: tlong :: nil) tlong cc_default))
        ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
         (Econst_int (Int.repr 3) tint) :: (Etempvar _tag tuchar) :: nil))
      (Sset _block (Etempvar _t'2 tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t'8 tlong)))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'7
              (Ederef
                (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Etempvar _t'7 tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'5
                (Ederef
                  (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                    (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
                (Etempvar _t'5 tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                  (Econst_int (Int.repr 2) tint) (tptr tlong))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong)
                (Etempvar _block tlong))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_MAKEFLOATBLOCK := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_size, tulong) :: (_i, tulong) :: (_block, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, (tptr tint)) ::
               (_t'10, tint) :: (_t'9, tdouble) :: (_t'8, tlong) ::
               (_t'7, tdouble) :: (_t'6, tlong) :: (_t'5, (tptr tlong)) ::
               (_t'4, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'10 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sset _size (Ecast (Etempvar _t'10 tint) tulong))))
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _size tulong)
                   (Ebinop Odiv (Econst_int (Int.repr 256) tint)
                     (Ebinop Odiv (Esizeof tdouble tulong)
                       (Esizeof tlong tulong) tulong) tulong) tint)
      (Ssequence
        (Scall (Some _t'2)
          (Evar _heap_alloc (Tfunction
                              ((tptr (Tstruct _interp_state noattr)) ::
                               tlong :: tlong :: nil) tlong cc_default))
          ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
           (Ebinop Omul (Etempvar _size tulong)
             (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong)
               tulong) tulong) :: (Econst_int (Int.repr 254) tint) :: nil))
        (Sset _block (Etempvar _t'2 tlong)))
      (Ssequence
        (Scall (Some _t'3)
          (Evar _heap_alloc (Tfunction
                              ((tptr (Tstruct _interp_state noattr)) ::
                               tlong :: tlong :: nil) tlong cc_default))
          ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
           (Ebinop Omul (Etempvar _size tulong)
             (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong)
               tulong) tulong) :: (Econst_int (Int.repr 254) tint) :: nil))
        (Sset _block (Etempvar _t'3 tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Ssequence
          (Sset _t'9
            (Ederef (Ecast (Etempvar _t'8 tlong) (tptr tdouble)) tdouble))
          (Sassign
            (Ederef
              (Ecast
                (Ebinop Oadd (Ecast (Etempvar _block tlong) (tptr tlong))
                  (Ebinop Omul (Econst_int (Int.repr 0) tint)
                    (Ebinop Odiv (Esizeof tdouble tulong)
                      (Esizeof tlong tulong) tulong) tulong) (tptr tlong))
                (tptr tdouble)) tdouble) (Etempvar _t'9 tdouble))))
      (Ssequence
        (Ssequence
          (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                             (Etempvar _size tulong) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Ssequence
                    (Sset _t'6 (Ederef (Etempvar _t'5 (tptr tlong)) tlong))
                    (Ssequence
                      (Sset _t'7
                        (Ederef (Ecast (Etempvar _t'6 tlong) (tptr tdouble))
                          tdouble))
                      (Sassign
                        (Ederef
                          (Ecast
                            (Ebinop Oadd
                              (Ecast (Etempvar _block tlong) (tptr tlong))
                              (Ebinop Omul (Etempvar _i tulong)
                                (Ebinop Odiv (Esizeof tdouble tulong)
                                  (Esizeof tlong tulong) tulong) tulong)
                              (tptr tlong)) (tptr tdouble)) tdouble)
                        (Etempvar _t'7 tdouble)))))
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _sp (tptr tlong))
                    (Ebinop Oadd (Etempvar _t'4 (tptr tlong))
                      (Econst_int (Int.repr 1) tint) (tptr tlong))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tulong)
                (Econst_int (Int.repr 1) tint) tulong))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _block tlong))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_instr_GETFLOATFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tdouble) :: (_t'2, tlong) :: (_t'1, (tptr tint)) ::
               (_t'5, tint) :: (_t'4, tlong) :: (_t'3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'5 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Sset _d
          (Ederef
            (Ecast
              (Ebinop Oadd (Ecast (Etempvar _t'4 tlong) (tptr tlong))
                (Ebinop Omul (Etempvar _t'5 tint)
                  (Ebinop Odiv (Esizeof tdouble tulong)
                    (Esizeof tlong tulong) tulong) tulong) (tptr tlong))
              (tptr tdouble)) tdouble)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _heap_alloc (Tfunction
                            ((tptr (Tstruct _interp_state noattr)) ::
                             tlong :: tlong :: nil) tlong cc_default))
        ((Etempvar _s (tptr (Tstruct _interp_state noattr))) ::
         (Ebinop Odiv (Esizeof tdouble tulong) (Esizeof tlong tulong) tulong) ::
         (Econst_int (Int.repr 253) tint) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Etempvar _t'2 tlong)))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Ederef (Ecast (Etempvar _t'3 tlong) (tptr tdouble)) tdouble)
          (Etempvar _d tdouble)))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_SETFLOATFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, tdouble) :: (_t'7, tlong) :: (_t'6, (tptr tlong)) ::
               (_t'5, tint) :: (_t'4, (tptr tint)) :: (_t'3, tlong) ::
               (_t'2, (tptr tlong)) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'7 (Ederef (Etempvar _t'6 (tptr tlong)) tlong))
            (Ssequence
              (Sset _t'8
                (Ederef (Ecast (Etempvar _t'7 tlong) (tptr tdouble)) tdouble))
              (Sassign
                (Ederef
                  (Ecast
                    (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                      (Ebinop Omul (Etempvar _t'5 tint)
                        (Ebinop Odiv (Esizeof tdouble tulong)
                          (Esizeof tlong tulong) tulong) tulong)
                      (tptr tlong)) (tptr tdouble)) tdouble)
                (Etempvar _t'8 tdouble))))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
            (Econst_int (Int.repr 1) tint) (tptr tlong))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Ebinop Oadd (Etempvar _t'1 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_instr_PUSHTRAP := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'14, (tptr tlong)) :: (_t'13, tint) ::
               (_t'12, (tptr tint)) :: (_t'11, (tptr tint)) ::
               (_t'10, (tptr tlong)) :: (_t'9, (tptr tlong)) ::
               (_t'8, (tptr tlong)) :: (_t'7, (tptr tlong)) ::
               (_t'6, tlong) :: (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) ::
               (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'14
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong))
      (Ebinop Osub (Etempvar _t'14 (tptr tlong))
        (Econst_int (Int.repr 4) tint) (tptr tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'12
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'13 (Ederef (Etempvar _t'12 (tptr tint)) tint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Ecast (Etempvar _t'10 (tptr tlong)) (tptr (tptr tint)))
                  (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
                (tptr tint))
              (Ebinop Oadd (Etempvar _t'11 (tptr tint)) (Etempvar _t'13 tint)
                (tptr tint)))))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _trap_sp (tptr tlong)))
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Ecast (Etempvar _t'7 (tptr tlong)) (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong)
              (Ebinop Oadd
                (Ebinop Oshl
                  (Ecast
                    (Ebinop Osub (Etempvar _t'8 (tptr tlong))
                      (Etempvar _t'9 (tptr tlong)) tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong)
                (Econst_int (Int.repr 1) tint) tlong)))))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _env tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong)
              (Etempvar _t'6 tlong))))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _extra_args tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                    (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong)
                (Ebinop Oadd
                  (Ebinop Oshl (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong)
                  (Econst_int (Int.repr 1) tint) tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _trap_sp (tptr tlong))
                (Etempvar _t'2 (tptr tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'1 (tptr tint))
                    (Econst_int (Int.repr 1) tint) (tptr tint))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_POPTRAP := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, (tptr tint)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) ::
               (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Econst_int (Int.repr 0) tint)
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Osub (Etempvar _t'5 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'3 (tptr tlong)) (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _trap_sp (tptr tlong))
            (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
              (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 4) tint) (tptr tlong))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_RAISE := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'14, (tptr tlong)) ::
               (_t'13, (tptr tint)) :: (_t'12, (tptr tlong)) ::
               (_t'11, (tptr tint)) :: (_t'10, (tptr tlong)) ::
               (_t'9, tlong) :: (_t'8, (tptr tlong)) ::
               (_t'7, (tptr tlong)) :: (_t'6, tlong) ::
               (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Econst_int (Int.repr 0) tint)
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sset _t'1
            (Ecast
              (Ebinop Osub (Etempvar _t'14 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Etempvar _t'1 (tptr tlong))))
      (Ssequence
        (Sset _t'13
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
          (Ecast
            (Ebinop Osub (Etempvar _t'13 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)) tlong))))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _trap_sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'12 (tptr tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'11
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _t'10 (tptr tlong)) (tptr (tptr tint)))
                (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
              (tptr tint)))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Etempvar _t'11 (tptr tint)))))
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ebinop Oadd
                    (Ecast (Etempvar _t'8 (tptr tlong)) (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _trap_sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                  (Ebinop Oshr (Ecast (Etempvar _t'9 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))))))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'6
                (Ederef
                  (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                    (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _env tlong)
                (Etempvar _t'6 tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'4
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                      (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _extra_args tlong)
                  (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                    (Econst_int (Int.repr 4) tint) (tptr tlong))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_RERAISE := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'14, (tptr tlong)) ::
               (_t'13, (tptr tint)) :: (_t'12, (tptr tlong)) ::
               (_t'11, (tptr tint)) :: (_t'10, (tptr tlong)) ::
               (_t'9, tlong) :: (_t'8, (tptr tlong)) ::
               (_t'7, (tptr tlong)) :: (_t'6, tlong) ::
               (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Econst_int (Int.repr 0) tint)
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sset _t'1
            (Ecast
              (Ebinop Osub (Etempvar _t'14 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Etempvar _t'1 (tptr tlong))))
      (Ssequence
        (Sset _t'13
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
          (Ecast
            (Ebinop Osub (Etempvar _t'13 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)) tlong))))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _trap_sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'12 (tptr tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'11
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _t'10 (tptr tlong)) (tptr (tptr tint)))
                (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
              (tptr tint)))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Etempvar _t'11 (tptr tint)))))
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ebinop Oadd
                    (Ecast (Etempvar _t'8 (tptr tlong)) (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _trap_sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                  (Ebinop Oshr (Ecast (Etempvar _t'9 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))))))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'6
                (Ederef
                  (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                    (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _env tlong)
                (Etempvar _t'6 tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'4
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                      (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _extra_args tlong)
                  (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                    (Econst_int (Int.repr 4) tint) (tptr tlong))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_RAISE_NOTRACE := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'14, (tptr tlong)) ::
               (_t'13, (tptr tint)) :: (_t'12, (tptr tlong)) ::
               (_t'11, (tptr tint)) :: (_t'10, (tptr tlong)) ::
               (_t'9, tlong) :: (_t'8, (tptr tlong)) ::
               (_t'7, (tptr tlong)) :: (_t'6, tlong) ::
               (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Econst_int (Int.repr 0) tint)
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Sset _t'1
            (Ecast
              (Ebinop Osub (Etempvar _t'14 (tptr tlong))
                (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Etempvar _t'1 (tptr tlong))))
      (Ssequence
        (Sset _t'13
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
          (Ecast
            (Ebinop Osub (Etempvar _t'13 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)) tlong))))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'12
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _trap_sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'12 (tptr tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Ssequence
          (Sset _t'11
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _t'10 (tptr tlong)) (tptr (tptr tint)))
                (Econst_int (Int.repr 0) tint) (tptr (tptr tint)))
              (tptr tint)))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Etempvar _t'11 (tptr tint)))))
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'9
                (Ederef
                  (Ebinop Oadd
                    (Ecast (Etempvar _t'8 (tptr tlong)) (tptr tlong))
                    (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _trap_sp (tptr tlong))
                (Ebinop Oadd (Etempvar _t'7 (tptr tlong))
                  (Ebinop Oshr (Ecast (Etempvar _t'9 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))))))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _sp (tptr tlong)))
            (Ssequence
              (Sset _t'6
                (Ederef
                  (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                    (Econst_int (Int.repr 2) tint) (tptr tlong)) tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _env tlong)
                (Etempvar _t'6 tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _sp (tptr tlong)))
              (Ssequence
                (Sset _t'4
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
                      (Econst_int (Int.repr 3) tint) (tptr tlong)) tlong))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _extra_args tlong)
                  (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _sp (tptr tlong))
                  (Ebinop Oadd (Etempvar _t'2 (tptr tlong))
                    (Econst_int (Int.repr 4) tint) (tptr tlong))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_instr_ATOM0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
        (Tstruct _interp_state noattr)) _accu tlong)
    (Ecast
      (Ebinop Oshl (Econst_int (Int.repr 0) tint)
        (Econst_int (Int.repr 10) tint) tint) tlong))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHATOM0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'2 tlong))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ecast
        (Ebinop Oshl (Econst_int (Int.repr 0) tint)
          (Econst_int (Int.repr 10) tint) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_GETMETHOD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Ssequence
            (Sset _t'5
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                  (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))
                tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'5 tlong)))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_GETPUBMET := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_meths, tlong) :: (_li, tint) :: (_hi, tint) ::
               (_mi, tint) :: (_t'1, (tptr tlong)) ::
               (_t'12, (tptr tlong)) :: (_t'11, tlong) :: (_t'10, tint) ::
               (_t'9, (tptr tint)) :: (_t'8, (tptr tint)) :: (_t'7, tlong) ::
               (_t'6, (tptr tlong)) :: (_t'5, tlong) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'12 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'11
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'11 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'10 (Ederef (Etempvar _t'9 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl (Ecast (Etempvar _t'10 tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'8 (tptr tint))
            (Econst_int (Int.repr 2) tint) (tptr tint))))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'7
              (Ederef
                (Ebinop Oadd (Etempvar _t'6 (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
            (Sset _meths
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'7 tlong) (tptr tlong))
                  (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))))
        (Ssequence
          (Sset _li (Econst_int (Int.repr 3) tint))
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
              (Sset _hi (Ecast (Etempvar _t'5 tlong) tint)))
            (Ssequence
              (Swhile
                (Ebinop Olt (Etempvar _li tint) (Etempvar _hi tint) tint)
                (Ssequence
                  (Sset _mi
                    (Ebinop Oor
                      (Ebinop Oshr
                        (Ebinop Oadd (Etempvar _li tint) (Etempvar _hi tint)
                          tint) (Econst_int (Int.repr 1) tint) tint)
                      (Econst_int (Int.repr 1) tint) tint))
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                          (Tstruct _interp_state noattr)) _accu tlong))
                    (Ssequence
                      (Sset _t'4
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar _meths tlong) (tptr tlong))
                            (Etempvar _mi tint) (tptr tlong)) tlong))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'3 tlong)
                                     (Etempvar _t'4 tlong) tint)
                        (Sset _hi
                          (Ebinop Osub (Etempvar _mi tint)
                            (Econst_int (Int.repr 2) tint) tint))
                        (Sset _li (Etempvar _mi tint)))))))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Ecast (Etempvar _meths tlong) (tptr tlong))
                        (Ebinop Osub (Etempvar _li tint)
                          (Econst_int (Int.repr 1) tint) tint) (tptr tlong))
                      tlong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                        (Tstruct _interp_state noattr)) _accu tlong)
                    (Etempvar _t'2 tlong)))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_instr_GETDYNMET := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_meths, tlong) :: (_li, tint) :: (_hi, tint) ::
               (_mi, tint) :: (_t'6, tlong) :: (_t'5, (tptr tlong)) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _sp (tptr tlong)))
    (Ssequence
      (Sset _t'6
        (Ederef
          (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
      (Sset _meths
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _t'6 tlong) (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))))
  (Ssequence
    (Sset _li (Econst_int (Int.repr 3) tint))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Sset _hi (Ecast (Etempvar _t'4 tlong) tint)))
      (Ssequence
        (Swhile
          (Ebinop Olt (Etempvar _li tint) (Etempvar _hi tint) tint)
          (Ssequence
            (Sset _mi
              (Ebinop Oor
                (Ebinop Oshr
                  (Ebinop Oadd (Etempvar _li tint) (Etempvar _hi tint) tint)
                  (Econst_int (Int.repr 1) tint) tint)
                (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _accu tlong))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                      (Etempvar _mi tint) (tptr tlong)) tlong))
                (Sifthenelse (Ebinop Olt (Etempvar _t'2 tlong)
                               (Etempvar _t'3 tlong) tint)
                  (Sset _hi
                    (Ebinop Osub (Etempvar _mi tint)
                      (Econst_int (Int.repr 2) tint) tint))
                  (Sset _li (Etempvar _mi tint)))))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _meths tlong) (tptr tlong))
                  (Ebinop Osub (Etempvar _li tint)
                    (Econst_int (Int.repr 1) tint) tint) (tptr tlong)) tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'1 tlong)))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_instr_SWITCH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_sizes, tuint) :: (_index, tlong) :: (_index__1, tlong) ::
               (_t'1, (tptr tint)) :: (_t'11, tuchar) :: (_t'10, tlong) ::
               (_t'9, tint) :: (_t'8, (tptr tint)) :: (_t'7, (tptr tint)) ::
               (_t'6, tlong) :: (_t'5, tint) :: (_t'4, (tptr tint)) ::
               (_t'3, (tptr tint)) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sset _sizes (Ederef (Etempvar _t'1 (tptr tint)) tint)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sifthenelse (Ebinop Oeq
                     (Ebinop Oand (Etempvar _t'2 tlong)
                       (Econst_int (Int.repr 1) tint) tlong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong))
            (Ssequence
              (Sset _t'11
                (Ederef
                  (Ebinop Oadd (Ecast (Etempvar _t'10 tlong) (tptr tuchar))
                    (Eunop Oneg (Esizeof tlong tulong) tulong) (tptr tuchar))
                  tuchar))
              (Sset _index
                (Ecast
                  (Ebinop Oand (Etempvar _t'11 tuchar)
                    (Econst_int (Int.repr 255) tint) tint) tlong))))
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'9
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'8 (tptr tint))
                      (Ebinop Oadd
                        (Ebinop Oand (Etempvar _sizes tuint)
                          (Econst_int (Int.repr 65535) tint) tuint)
                        (Etempvar _index tlong) tlong) (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'7 (tptr tint))
                    (Etempvar _t'9 tint) (tptr tint)))))))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong))
            (Sset _index__1
              (Ebinop Oshr (Ecast (Etempvar _t'6 tlong) tlong)
                (Econst_int (Int.repr 1) tint) tlong)))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint)))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                    (Tstruct _interp_state noattr)) _pc (tptr tint)))
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'4 (tptr tint))
                      (Etempvar _index__1 tlong) (tptr tint)) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                      (Tstruct _interp_state noattr)) _pc (tptr tint))
                  (Ebinop Oadd (Etempvar _t'3 (tptr tint))
                    (Etempvar _t'5 tint) (tptr tint)))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_ACC := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'4, tlong) :: (_t'3, tint) ::
               (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _t'2 (tptr tlong)) (Etempvar _t'3 tint)
                (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _t'4 tlong))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_POP := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'3, tint) :: (_t'2, (tptr tlong)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'2 (tptr tlong)) (Etempvar _t'3 tint)
            (tptr tlong))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ASSIGN := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'4, tlong) :: (_t'3, tint) ::
               (_t'2, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'2 (tptr tlong)) (Etempvar _t'3 tint)
                (tptr tlong)) tlong) (Etempvar _t'4 tlong))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_CONSTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, (tptr tint)) :: (_t'1, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _t'2 (tptr tint)) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Ebinop Oadd
          (Ebinop Oshl (Ecast (Etempvar _t'3 tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHCONSTINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'6 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'5 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl (Ecast (Etempvar _t'4 tint) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_NEGINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ecast
        (Ebinop Osub (Econst_int (Int.repr 2) tint)
          (Ecast (Etempvar _t'1 tlong) tlong) tlong) tlong)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ADDINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Osub
              (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) tlong)
                (Ecast (Etempvar _t'3 tlong) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_SUBINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oadd
              (Ebinop Osub (Ecast (Etempvar _t'2 tlong) tlong)
                (Ecast (Etempvar _t'3 tlong) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_MULINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd
            (Ebinop Oshl
              (Ecast
                (Ebinop Omul
                  (Ebinop Oshr (Ecast (Etempvar _t'2 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong)
                  (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong)
            (Econst_int (Int.repr 1) tint) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_DIVINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_divisor, tlong) :: (_t'1, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
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
        (Evar _caml_raise_zero_divide (Tfunction nil tvoid cc_default)) nil)
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
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
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_divisor, tlong) :: (_t'1, (tptr tlong)) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
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
        (Evar _caml_raise_zero_divide (Tfunction nil tvoid cc_default)) nil)
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
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

Definition f_instr_ANDINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oand (Ecast (Etempvar _t'2 tlong) tlong)
              (Ecast (Etempvar _t'3 tlong) tlong) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ORINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oor (Ecast (Etempvar _t'2 tlong) tlong)
              (Ecast (Etempvar _t'3 tlong) tlong) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_XORINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oor
              (Ebinop Oxor (Ecast (Etempvar _t'2 tlong) tlong)
                (Ecast (Etempvar _t'3 tlong) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_LSLINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oadd
              (Ebinop Oshl
                (Ebinop Osub (Ecast (Etempvar _t'2 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong)
                (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_LSRINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oor
              (Ebinop Oshr (Ecast (Etempvar _t'2 tlong) tulong)
                (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong) tulong)
              (Econst_int (Int.repr 1) tint) tulong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ASRINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tlong)) :: (_t'3, tlong) :: (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oor
              (Ebinop Oshr (Ecast (Etempvar _t'2 tlong) tlong)
                (Ebinop Oshr (Ecast (Etempvar _t'3 tlong) tlong)
                  (Econst_int (Int.repr 1) tint) tlong) tlong)
              (Econst_int (Int.repr 1) tint) tlong) tlong)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ISINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
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
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Osub (Econst_int (Int.repr 4) tint) (Etempvar _t'1 tlong)
        tlong)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_OFFSETINT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, (tptr tint)) :: (_t'2, tlong) ::
               (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ebinop Oadd (Etempvar _t'2 tlong)
            (Ebinop Oshl (Etempvar _t'4 tint) (Econst_int (Int.repr 1) tint)
              tint) tlong)))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_OFFSETREF := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tint) :: (_t'5, (tptr tint)) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
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
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_BRANCH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, (tptr tint)) :: (_t'1, (tptr tint)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'2 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Etempvar _t'3 tint)
            (tptr tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BRANCHIF := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tint)) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Sifthenelse (Ebinop One (Etempvar _t'1 tlong)
                   (Ebinop Oadd
                     (Ebinop Oshl
                       (Ecast (Econst_int (Int.repr 0) tint) tlong)
                       (Econst_int (Int.repr 1) tint) tlong)
                     (Econst_int (Int.repr 1) tint) tlong) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'3 (tptr tint)) (Etempvar _t'5 tint)
                (tptr tint))))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_BRANCHIFNOT := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, (tptr tint)) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tint)) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tlong)
                   (Ebinop Oadd
                     (Ebinop Oshl
                       (Ecast (Econst_int (Int.repr 0) tint) tlong)
                       (Econst_int (Int.repr 1) tint) tlong)
                     (Econst_int (Int.repr 1) tint) tlong) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          (Ssequence
            (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _pc (tptr tint))
              (Ebinop Oadd (Etempvar _t'3 (tptr tint)) (Etempvar _t'5 tint)
                (tptr tint))))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_ATOM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2 (Ederef (Etempvar _t'1 (tptr tint)) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Ecast
          (Ebinop Oshl (Etempvar _t'2 tint) (Econst_int (Int.repr 10) tint)
            tint) tlong))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHATOM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tint)) :: (_t'1, (tptr tlong)) ::
               (_t'5, (tptr tlong)) :: (_t'4, tlong) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'5 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'4 tlong))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'2 (tptr tint)) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _accu tlong)
          (Ecast
            (Ebinop Oshl (Etempvar _t'3 tint) (Econst_int (Int.repr 10) tint)
              tint) tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_GETFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, tlong) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                (Etempvar _t'4 tint) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _t'5 tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETFIELD := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Ssequence
          (Sset _t'5 (Ederef (Etempvar _t'4 (tptr tint)) tint))
          (Ssequence
            (Sset _t'6 (Ederef (Etempvar _t'1 (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                  (Etempvar _t'5 tint) (tptr tlong)) tlong)
              (Etempvar _t'6 tlong)))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_VECTLENGTH := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_size, tulong) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tuchar) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
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
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
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
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong)
        (Ebinop Oadd
          (Ebinop Oshl (Ecast (Etempvar _size tulong) tlong)
            (Econst_int (Int.repr 1) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_GETVECTITEM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tlong) :: (_t'3, (tptr tlong)) ::
               (_t'2, tlong) :: (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
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
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _t'5 tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
          (Econst_int (Int.repr 1) tint) (tptr tlong))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_SETVECTITEM := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'6, tlong) :: (_t'5, (tptr tlong)) :: (_t'4, tlong) ::
               (_t'3, (tptr tlong)) :: (_t'2, tlong) ::
               (_t'1, (tptr tlong)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _t'3 (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _sp (tptr tlong)))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd (Etempvar _t'5 (tptr tlong))
                  (Econst_int (Int.repr 1) tint) (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                  (Ebinop Oshr (Ecast (Etempvar _t'4 tlong) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))
                tlong) (Etempvar _t'6 tlong)))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong))
          (Ebinop Oadd (Etempvar _t'1 (tptr tlong))
            (Econst_int (Int.repr 2) tint) (tptr tlong))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_GETGLOBAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tlong)) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _global_data (tptr tlong)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 (tptr tlong)) (tptr tlong))
                (Etempvar _t'4 tint) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _t'5 tlong))))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_PUSHGETGLOBAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
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
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'8 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'7 tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _global_data (tptr tlong)))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
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
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'6 tlong))))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_SETGLOBAL := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tlong) :: (_t'4, tint) :: (_t'3, (tptr tint)) ::
               (_t'2, (tptr tlong)) :: (_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _global_data (tptr tlong)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Ssequence
        (Sset _t'4 (Ederef (Etempvar _t'3 (tptr tint)) tint))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 (tptr tlong)) (tptr tlong))
                (Etempvar _t'4 tint) (tptr tlong)) tlong)
            (Etempvar _t'5 tlong))))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _accu tlong)
      (Ebinop Oadd
        (Ebinop Oshl (Ecast (Econst_int (Int.repr 0) tint) tlong)
          (Econst_int (Int.repr 1) tint) tlong)
        (Econst_int (Int.repr 1) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'1 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_instr_ENVACC := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: (_t'4, tlong) :: (_t'3, tint) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _env tlong))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'1 (tptr tint)) tint))
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _t'2 tlong) (tptr tlong))
                (Etempvar _t'3 tint) (tptr tlong)) tlong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _accu tlong)
            (Etempvar _t'4 tlong))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_instr_PUSHENVACC := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tint)) :: (_t'1, (tptr tlong)) ::
               (_t'7, (tptr tlong)) :: (_t'6, tlong) :: (_t'5, tlong) ::
               (_t'4, tint) :: (_t'3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _sp (tptr tlong)))
        (Sset _t'1
          (Ecast
            (Ebinop Osub (Etempvar _t'7 (tptr tlong))
              (Econst_int (Int.repr 1) tint) (tptr tlong)) (tptr tlong))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _sp (tptr tlong))
        (Etempvar _t'1 (tptr tlong))))
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _accu tlong))
      (Sassign (Ederef (Etempvar _t'1 (tptr tlong)) tlong)
        (Etempvar _t'6 tlong))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint)))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _pc (tptr tint))
          (Ebinop Oadd (Etempvar _t'2 (tptr tint))
            (Econst_int (Int.repr 1) tint) (tptr tint))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
              (Tstruct _interp_state noattr)) _env tlong))
        (Ssequence
          (Sset _t'4 (Ederef (Etempvar _t'2 (tptr tint)) tint))
          (Ssequence
            (Sset _t'5
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) (tptr tlong))
                  (Etempvar _t'4 tint) (tptr tlong)) tlong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                  (Tstruct _interp_state noattr)) _accu tlong)
              (Etempvar _t'5 tlong))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_instr_STOP := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_instr_C_CALL1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint))
      (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Econst_int (Int.repr 1) tint)
        (tptr tint))))
  (Sreturn (Some (Econst_int (Int.repr 3) tint))))
|}.

Definition f_instr_C_CALL2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint))
      (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Econst_int (Int.repr 1) tint)
        (tptr tint))))
  (Sreturn (Some (Econst_int (Int.repr 3) tint))))
|}.

Definition f_instr_C_CALL3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint))
      (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Econst_int (Int.repr 1) tint)
        (tptr tint))))
  (Sreturn (Some (Econst_int (Int.repr 3) tint))))
|}.

Definition f_instr_C_CALL4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint))
      (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Econst_int (Int.repr 1) tint)
        (tptr tint))))
  (Sreturn (Some (Econst_int (Int.repr 3) tint))))
|}.

Definition f_instr_C_CALL5 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
          (Tstruct _interp_state noattr)) _pc (tptr tint))
      (Ebinop Oadd (Etempvar _t'1 (tptr tint)) (Econst_int (Int.repr 1) tint)
        (tptr tint))))
  (Sreturn (Some (Econst_int (Int.repr 3) tint))))
|}.

Definition f_instr_C_CALLN := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _interp_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_nargs, tint) :: (_t'1, (tptr tint)) ::
               (_t'2, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'1 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sset _nargs (Ederef (Etempvar _t'1 (tptr tint)) tint)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint)))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
            (Tstruct _interp_state noattr)) _pc (tptr tint))
        (Ebinop Oadd (Etempvar _t'2 (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint))))
    (Sreturn (Some (Econst_int (Int.repr 3) tint)))))
|}.

Definition composites : list composite_definition :=
(Composite _interp_state Struct
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
 (_heap_alloc,
   Gfun(External (EF_external "heap_alloc"
                   (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil) tlong
     cc_default)) ::
 (_caml_raise_zero_divide,
   Gfun(External (EF_external "caml_raise_zero_divide"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) :: (_instr_ACC0, Gfun(Internal f_instr_ACC0)) ::
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
 (_instr_ENVACC1, Gfun(Internal f_instr_ENVACC1)) ::
 (_instr_ENVACC2, Gfun(Internal f_instr_ENVACC2)) ::
 (_instr_ENVACC3, Gfun(Internal f_instr_ENVACC3)) ::
 (_instr_ENVACC4, Gfun(Internal f_instr_ENVACC4)) ::
 (_instr_PUSHENVACC1, Gfun(Internal f_instr_PUSHENVACC1)) ::
 (_instr_PUSHENVACC2, Gfun(Internal f_instr_PUSHENVACC2)) ::
 (_instr_PUSHENVACC3, Gfun(Internal f_instr_PUSHENVACC3)) ::
 (_instr_PUSHENVACC4, Gfun(Internal f_instr_PUSHENVACC4)) ::
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
 (_instr_OFFSETCLOSURE, Gfun(Internal f_instr_OFFSETCLOSURE)) ::
 (_instr_OFFSETCLOSUREM3, Gfun(Internal f_instr_OFFSETCLOSUREM3)) ::
 (_instr_OFFSETCLOSURE0, Gfun(Internal f_instr_OFFSETCLOSURE0)) ::
 (_instr_OFFSETCLOSURE3, Gfun(Internal f_instr_OFFSETCLOSURE3)) ::
 (_instr_PUSHOFFSETCLOSURE, Gfun(Internal f_instr_PUSHOFFSETCLOSURE)) ::
 (_instr_PUSHOFFSETCLOSUREM3, Gfun(Internal f_instr_PUSHOFFSETCLOSUREM3)) ::
 (_instr_PUSHOFFSETCLOSURE0, Gfun(Internal f_instr_PUSHOFFSETCLOSURE0)) ::
 (_instr_PUSHOFFSETCLOSURE3, Gfun(Internal f_instr_PUSHOFFSETCLOSURE3)) ::
 (_instr_CHECK_SIGNALS, Gfun(Internal f_instr_CHECK_SIGNALS)) ::
 (_instr_EQ, Gfun(Internal f_instr_EQ)) ::
 (_instr_NEQ, Gfun(Internal f_instr_NEQ)) ::
 (_instr_LTINT, Gfun(Internal f_instr_LTINT)) ::
 (_instr_LEINT, Gfun(Internal f_instr_LEINT)) ::
 (_instr_GTINT, Gfun(Internal f_instr_GTINT)) ::
 (_instr_GEINT, Gfun(Internal f_instr_GEINT)) ::
 (_instr_ULTINT, Gfun(Internal f_instr_ULTINT)) ::
 (_instr_UGEINT, Gfun(Internal f_instr_UGEINT)) ::
 (_instr_BEQ, Gfun(Internal f_instr_BEQ)) ::
 (_instr_BNEQ, Gfun(Internal f_instr_BNEQ)) ::
 (_instr_BLTINT, Gfun(Internal f_instr_BLTINT)) ::
 (_instr_BLEINT, Gfun(Internal f_instr_BLEINT)) ::
 (_instr_BGTINT, Gfun(Internal f_instr_BGTINT)) ::
 (_instr_BGEINT, Gfun(Internal f_instr_BGEINT)) ::
 (_instr_BULTINT, Gfun(Internal f_instr_BULTINT)) ::
 (_instr_BUGEINT, Gfun(Internal f_instr_BUGEINT)) ::
 (_instr_GETSTRINGCHAR, Gfun(Internal f_instr_GETSTRINGCHAR)) ::
 (_instr_GETBYTESCHAR, Gfun(Internal f_instr_GETBYTESCHAR)) ::
 (_instr_SETBYTESCHAR, Gfun(Internal f_instr_SETBYTESCHAR)) ::
 (_instr_PUSH_RETADDR, Gfun(Internal f_instr_PUSH_RETADDR)) ::
 (_instr_APPLY, Gfun(Internal f_instr_APPLY)) ::
 (_instr_APPLY1, Gfun(Internal f_instr_APPLY1)) ::
 (_instr_APPLY2, Gfun(Internal f_instr_APPLY2)) ::
 (_instr_APPLY3, Gfun(Internal f_instr_APPLY3)) ::
 (_instr_APPTERM, Gfun(Internal f_instr_APPTERM)) ::
 (_instr_APPTERM1, Gfun(Internal f_instr_APPTERM1)) ::
 (_instr_APPTERM2, Gfun(Internal f_instr_APPTERM2)) ::
 (_instr_APPTERM3, Gfun(Internal f_instr_APPTERM3)) ::
 (_instr_RETURN, Gfun(Internal f_instr_RETURN)) ::
 (_instr_RESTART, Gfun(Internal f_instr_RESTART)) ::
 (_instr_GRAB, Gfun(Internal f_instr_GRAB)) ::
 (_instr_CLOSURE, Gfun(Internal f_instr_CLOSURE)) ::
 (_instr_CLOSUREREC, Gfun(Internal f_instr_CLOSUREREC)) ::
 (_instr_GETGLOBALFIELD, Gfun(Internal f_instr_GETGLOBALFIELD)) ::
 (_instr_PUSHGETGLOBALFIELD, Gfun(Internal f_instr_PUSHGETGLOBALFIELD)) ::
 (_instr_MAKEBLOCK, Gfun(Internal f_instr_MAKEBLOCK)) ::
 (_instr_MAKEBLOCK1, Gfun(Internal f_instr_MAKEBLOCK1)) ::
 (_instr_MAKEBLOCK2, Gfun(Internal f_instr_MAKEBLOCK2)) ::
 (_instr_MAKEBLOCK3, Gfun(Internal f_instr_MAKEBLOCK3)) ::
 (_instr_MAKEFLOATBLOCK, Gfun(Internal f_instr_MAKEFLOATBLOCK)) ::
 (_instr_GETFLOATFIELD, Gfun(Internal f_instr_GETFLOATFIELD)) ::
 (_instr_SETFLOATFIELD, Gfun(Internal f_instr_SETFLOATFIELD)) ::
 (_instr_PUSHTRAP, Gfun(Internal f_instr_PUSHTRAP)) ::
 (_instr_POPTRAP, Gfun(Internal f_instr_POPTRAP)) ::
 (_instr_RAISE, Gfun(Internal f_instr_RAISE)) ::
 (_instr_RERAISE, Gfun(Internal f_instr_RERAISE)) ::
 (_instr_RAISE_NOTRACE, Gfun(Internal f_instr_RAISE_NOTRACE)) ::
 (_instr_ATOM0, Gfun(Internal f_instr_ATOM0)) ::
 (_instr_PUSHATOM0, Gfun(Internal f_instr_PUSHATOM0)) ::
 (_instr_GETMETHOD, Gfun(Internal f_instr_GETMETHOD)) ::
 (_instr_GETPUBMET, Gfun(Internal f_instr_GETPUBMET)) ::
 (_instr_GETDYNMET, Gfun(Internal f_instr_GETDYNMET)) ::
 (_instr_SWITCH, Gfun(Internal f_instr_SWITCH)) ::
 (_instr_ACC, Gfun(Internal f_instr_ACC)) ::
 (_instr_POP, Gfun(Internal f_instr_POP)) ::
 (_instr_ASSIGN, Gfun(Internal f_instr_ASSIGN)) ::
 (_instr_CONSTINT, Gfun(Internal f_instr_CONSTINT)) ::
 (_instr_PUSHCONSTINT, Gfun(Internal f_instr_PUSHCONSTINT)) ::
 (_instr_NEGINT, Gfun(Internal f_instr_NEGINT)) ::
 (_instr_ADDINT, Gfun(Internal f_instr_ADDINT)) ::
 (_instr_SUBINT, Gfun(Internal f_instr_SUBINT)) ::
 (_instr_MULINT, Gfun(Internal f_instr_MULINT)) ::
 (_instr_DIVINT, Gfun(Internal f_instr_DIVINT)) ::
 (_instr_MODINT, Gfun(Internal f_instr_MODINT)) ::
 (_instr_ANDINT, Gfun(Internal f_instr_ANDINT)) ::
 (_instr_ORINT, Gfun(Internal f_instr_ORINT)) ::
 (_instr_XORINT, Gfun(Internal f_instr_XORINT)) ::
 (_instr_LSLINT, Gfun(Internal f_instr_LSLINT)) ::
 (_instr_LSRINT, Gfun(Internal f_instr_LSRINT)) ::
 (_instr_ASRINT, Gfun(Internal f_instr_ASRINT)) ::
 (_instr_ISINT, Gfun(Internal f_instr_ISINT)) ::
 (_instr_BOOLNOT, Gfun(Internal f_instr_BOOLNOT)) ::
 (_instr_OFFSETINT, Gfun(Internal f_instr_OFFSETINT)) ::
 (_instr_OFFSETREF, Gfun(Internal f_instr_OFFSETREF)) ::
 (_instr_BRANCH, Gfun(Internal f_instr_BRANCH)) ::
 (_instr_BRANCHIF, Gfun(Internal f_instr_BRANCHIF)) ::
 (_instr_BRANCHIFNOT, Gfun(Internal f_instr_BRANCHIFNOT)) ::
 (_instr_ATOM, Gfun(Internal f_instr_ATOM)) ::
 (_instr_PUSHATOM, Gfun(Internal f_instr_PUSHATOM)) ::
 (_instr_GETFIELD, Gfun(Internal f_instr_GETFIELD)) ::
 (_instr_SETFIELD, Gfun(Internal f_instr_SETFIELD)) ::
 (_instr_VECTLENGTH, Gfun(Internal f_instr_VECTLENGTH)) ::
 (_instr_GETVECTITEM, Gfun(Internal f_instr_GETVECTITEM)) ::
 (_instr_SETVECTITEM, Gfun(Internal f_instr_SETVECTITEM)) ::
 (_instr_GETGLOBAL, Gfun(Internal f_instr_GETGLOBAL)) ::
 (_instr_PUSHGETGLOBAL, Gfun(Internal f_instr_PUSHGETGLOBAL)) ::
 (_instr_SETGLOBAL, Gfun(Internal f_instr_SETGLOBAL)) ::
 (_instr_ENVACC, Gfun(Internal f_instr_ENVACC)) ::
 (_instr_PUSHENVACC, Gfun(Internal f_instr_PUSHENVACC)) ::
 (_instr_STOP, Gfun(Internal f_instr_STOP)) ::
 (_instr_C_CALL1, Gfun(Internal f_instr_C_CALL1)) ::
 (_instr_C_CALL2, Gfun(Internal f_instr_C_CALL2)) ::
 (_instr_C_CALL3, Gfun(Internal f_instr_C_CALL3)) ::
 (_instr_C_CALL4, Gfun(Internal f_instr_C_CALL4)) ::
 (_instr_C_CALL5, Gfun(Internal f_instr_C_CALL5)) ::
 (_instr_C_CALLN, Gfun(Internal f_instr_C_CALLN)) :: nil).

Definition public_idents : list ident :=
(_instr_C_CALLN :: _instr_C_CALL5 :: _instr_C_CALL4 :: _instr_C_CALL3 ::
 _instr_C_CALL2 :: _instr_C_CALL1 :: _instr_STOP :: _instr_PUSHENVACC ::
 _instr_ENVACC :: _instr_SETGLOBAL :: _instr_PUSHGETGLOBAL ::
 _instr_GETGLOBAL :: _instr_SETVECTITEM :: _instr_GETVECTITEM ::
 _instr_VECTLENGTH :: _instr_SETFIELD :: _instr_GETFIELD ::
 _instr_PUSHATOM :: _instr_ATOM :: _instr_BRANCHIFNOT :: _instr_BRANCHIF ::
 _instr_BRANCH :: _instr_OFFSETREF :: _instr_OFFSETINT :: _instr_BOOLNOT ::
 _instr_ISINT :: _instr_ASRINT :: _instr_LSRINT :: _instr_LSLINT ::
 _instr_XORINT :: _instr_ORINT :: _instr_ANDINT :: _instr_MODINT ::
 _instr_DIVINT :: _instr_MULINT :: _instr_SUBINT :: _instr_ADDINT ::
 _instr_NEGINT :: _instr_PUSHCONSTINT :: _instr_CONSTINT :: _instr_ASSIGN ::
 _instr_POP :: _instr_ACC :: _instr_SWITCH :: _instr_GETDYNMET ::
 _instr_GETPUBMET :: _instr_GETMETHOD :: _instr_PUSHATOM0 :: _instr_ATOM0 ::
 _instr_RAISE_NOTRACE :: _instr_RERAISE :: _instr_RAISE :: _instr_POPTRAP ::
 _instr_PUSHTRAP :: _instr_SETFLOATFIELD :: _instr_GETFLOATFIELD ::
 _instr_MAKEFLOATBLOCK :: _instr_MAKEBLOCK3 :: _instr_MAKEBLOCK2 ::
 _instr_MAKEBLOCK1 :: _instr_MAKEBLOCK :: _instr_PUSHGETGLOBALFIELD ::
 _instr_GETGLOBALFIELD :: _instr_CLOSUREREC :: _instr_CLOSURE ::
 _instr_GRAB :: _instr_RESTART :: _instr_RETURN :: _instr_APPTERM3 ::
 _instr_APPTERM2 :: _instr_APPTERM1 :: _instr_APPTERM :: _instr_APPLY3 ::
 _instr_APPLY2 :: _instr_APPLY1 :: _instr_APPLY :: _instr_PUSH_RETADDR ::
 _instr_SETBYTESCHAR :: _instr_GETBYTESCHAR :: _instr_GETSTRINGCHAR ::
 _instr_BUGEINT :: _instr_BULTINT :: _instr_BGEINT :: _instr_BGTINT ::
 _instr_BLEINT :: _instr_BLTINT :: _instr_BNEQ :: _instr_BEQ ::
 _instr_UGEINT :: _instr_ULTINT :: _instr_GEINT :: _instr_GTINT ::
 _instr_LEINT :: _instr_LTINT :: _instr_NEQ :: _instr_EQ ::
 _instr_CHECK_SIGNALS :: _instr_PUSHOFFSETCLOSURE3 ::
 _instr_PUSHOFFSETCLOSURE0 :: _instr_PUSHOFFSETCLOSUREM3 ::
 _instr_PUSHOFFSETCLOSURE :: _instr_OFFSETCLOSURE3 ::
 _instr_OFFSETCLOSURE0 :: _instr_OFFSETCLOSUREM3 :: _instr_OFFSETCLOSURE ::
 _instr_SETFIELD3 :: _instr_SETFIELD2 :: _instr_SETFIELD1 ::
 _instr_SETFIELD0 :: _instr_GETFIELD3 :: _instr_GETFIELD2 ::
 _instr_GETFIELD1 :: _instr_GETFIELD0 :: _instr_PUSHCONST3 ::
 _instr_PUSHCONST2 :: _instr_PUSHCONST1 :: _instr_PUSHCONST0 ::
 _instr_CONST3 :: _instr_CONST2 :: _instr_CONST1 :: _instr_CONST0 ::
 _instr_PUSHENVACC4 :: _instr_PUSHENVACC3 :: _instr_PUSHENVACC2 ::
 _instr_PUSHENVACC1 :: _instr_ENVACC4 :: _instr_ENVACC3 :: _instr_ENVACC2 ::
 _instr_ENVACC1 :: _instr_PUSHACC7 :: _instr_PUSHACC6 :: _instr_PUSHACC5 ::
 _instr_PUSHACC4 :: _instr_PUSHACC3 :: _instr_PUSHACC2 :: _instr_PUSHACC1 ::
 _instr_PUSH :: _instr_ACC7 :: _instr_ACC6 :: _instr_ACC5 :: _instr_ACC4 ::
 _instr_ACC3 :: _instr_ACC2 :: _instr_ACC1 :: _instr_ACC0 ::
 _caml_raise_zero_divide :: _heap_alloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


