
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  type mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val div2 : int -> int

  val div2_up : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val of_succ_nat : int -> int
 end

module Coq0_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val size : int -> int

  val testbit : int -> int -> bool

  val eq_dec : int -> int -> bool
 end

module N :
 sig
  val succ_double : int -> int

  val double : int -> int

  val succ_pos : int -> int

  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val pos_div_eucl : int -> int -> int * int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int
 end

module Coq_N :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val testbit : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val eqb : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int

  val of_N : int -> int

  val pos_div_eucl : int -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val quotrem : int -> int -> int * int

  val quot : int -> int -> int

  val rem : int -> int -> int

  val div2 : int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val pred : int -> int

  val geb : int -> int -> bool

  val gtb : int -> int -> bool

  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val odd : int -> bool

  val log2 : int -> int

  val testbit : int -> int -> bool

  val eq_dec : int -> int -> bool

  val lnot : int -> int

  val ones : int -> int
 end

val z_lt_dec : int -> int -> bool

val z_le_dec : int -> int -> bool

val z_le_gt_dec : int -> int -> bool

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val nth_error : 'a1 list -> int -> 'a1 option

val rev : 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val shift_nat : int -> int -> int

val shift_pos : int -> int -> int

val two_power_nat : int -> int

val two_power_pos : int -> int

val two_p : int -> int

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : int -> char

val ascii_of_N : int -> char

val ascii_of_nat : int -> char

val n_of_digits : bool list -> int

val n_of_ascii : char -> int

val nat_of_ascii : char -> int

val eqb0 : char list -> char list -> bool

val append : char list -> char list -> char list

val length0 : char list -> int

val lsl0 : int -> int -> int

val lor0 : int -> int -> int

val sub0 : int -> int -> int

val ltb0 : int -> int -> bool

val size0 : int

val of_pos_rec : int -> int -> int

val of_pos : int -> int

val of_Z : int -> int

type value =
| Val_int of int
| Val_block of int * value list
| Val_ptr of int
| Val_closure of int * int

val closure_tag : int

val infix_tag : int

val string_tag : int

val val_unit : value

val val_true : value

val val_false : value

val val_bool : bool -> value

val is_int : value -> bool

val set_nth : 'a1 list -> int -> 'a1 -> 'a1 list option

val value_eqb : value -> value -> bool

val value_phys_eqb : value -> value -> bool

type instruction =
| ACC of int
| PUSH
| PUSHACC of int
| POP of int
| ASSIGN of int
| ENVACC of int
| PUSHENVACC of int
| PUSH_RETADDR of int
| APPLY of int
| APPLY1
| APPLY2
| APPLY3
| APPTERM of int * int
| APPTERM1 of int
| APPTERM2 of int
| APPTERM3 of int
| RETURN of int
| RESTART
| GRAB of int
| CLOSURE of int * int
| CLOSUREREC of int * int * int list
| OFFSETCLOSURE of int
| PUSHOFFSETCLOSURE of int
| GETGLOBAL of int
| PUSHGETGLOBAL of int
| GETGLOBALFIELD of int * int
| PUSHGETGLOBALFIELD of int * int
| SETGLOBAL of int
| ATOM of int
| PUSHATOM of int
| MAKEBLOCK of int * int
| MAKEBLOCK1 of int
| MAKEBLOCK2 of int
| MAKEBLOCK3 of int
| MAKEFLOATBLOCK of int
| GETFIELD of int
| GETFLOATFIELD of int
| SETFIELD of int
| SETFLOATFIELD of int
| VECTLENGTH
| GETVECTITEM
| SETVECTITEM
| GETBYTESCHAR
| SETBYTESCHAR
| GETSTRINGCHAR
| BRANCH of int
| BRANCHIF of int
| BRANCHIFNOT of int
| SWITCH of int * int * int list * int list
| BOOLNOT
| PUSHTRAP of int
| POPTRAP
| RAISE
| RERAISE
| RAISE_NOTRACE
| CHECK_SIGNALS
| C_CALL of int * int
| CONSTINT of int
| PUSHCONSTINT of int
| NEGINT
| ADDINT
| SUBINT
| MULINT
| DIVINT
| MODINT
| ANDINT
| ORINT
| XORINT
| LSLINT
| LSRINT
| ASRINT
| EQ
| NEQ
| LTINT
| LEINT
| GTINT
| GEINT
| OFFSETINT of int
| OFFSETREF of int
| ISINT
| GETMETHOD
| GETPUBMET of int
| GETDYNMET
| BEQ of int * int
| BNEQ of int * int
| BLTINT of int * int
| BLEINT of int * int
| BGTINT of int * int
| BGEINT of int * int
| ULTINT
| UGEINT
| BULTINT of int * int
| BUGEINT of int * int
| STOP

module PositiveMap :
 sig
  type key = int

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val add : key -> 'a1 -> 'a1 t -> 'a1 t
 end

type ('r, 't) setter = ('t -> 't) -> 'r -> 'r

val set : ('a1 -> 'a2) -> ('a1, 'a2) setter -> ('a2 -> 'a2) -> 'a1 -> 'a1

type heap = (int * value list) PositiveMap.t

type state = { pc : int; accu : value; stack : value list; env : value;
               extra_args : int; global : value list; trap_sp : int;
               hp : heap; next_addr : int }

type 's step_result_gen =
| Step of 's
| Halt of value
| Error of char list
| CCall_request of int * value list * 's

type step_result = state step_result_gen

type run_result =
| Finished of value
| Run_error of char list
| Out_of_fuel of state

val heap_lookup : heap -> int -> (int * value list) option

val heap_alloc : state -> int -> value list -> state * value

val heap_update : heap -> int -> value list -> heap

val field_or_heap : state -> value -> int -> value option

val tag_or_heap : state -> value -> int option

val size_or_heap : state -> value -> int option

type bcmicro =
| MRet of value
| MErr of char list
| MFuel of state
| MVis of int * value list * (value option -> bcmicro)

val initial_state : value list -> state

val instr_word_size : instruction -> int

val build_offset_list : instruction list -> int -> int list

val offset_map : instruction list -> int list

val lookup_offset : int list -> int -> int

val encode_word_le : int -> int list

val emit_words : int list -> int list

val rel_offset : int list -> int -> int -> int

val encode_instr : int list -> int -> instruction -> int list

val encode_instrs : int list -> int -> instruction list -> int list

val encode_bytecode : instruction list -> int list

val zeq : int -> int -> bool

val zlt : int -> int -> bool

val zle : int -> int -> bool

val proj_sumbool : bool -> bool

val p_mod_two_p : int -> int -> int

val zshiftin : bool -> int -> int

val zzero_ext : int -> int -> int

val zsign_ext : int -> int -> int

val z_one_bits : int -> int -> int -> int list

val p_is_power2 : int -> bool

val z_is_power2 : int -> int option

val zsize : int -> int

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : int
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : int

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val size : int -> int

  val unsigned_bitfield_extract : int -> int -> int -> int

  val signed_bitfield_extract : int -> int -> int -> int

  val bitfield_insert : int -> int -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : int
 end

module Int :
 sig
  val wordsize : int

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val size : int -> int

  val unsigned_bitfield_extract : int -> int -> int -> int

  val signed_bitfield_extract : int -> int -> int -> int

  val bitfield_insert : int -> int -> int -> int -> int
 end

val get_code_ptr_from : value list -> int -> int option

val get_code_ptr_s : state -> value -> int option

val z_lsr : int -> int -> int

val z_flip_sign : int -> int

val make_exn_string : int list -> value

val div_by_zero_list_Z : int list

val div_by_zero_exn : value

val do_raise : value -> state -> step_result

val handle_ACC : int -> int -> state -> step_result

val handle_PUSH : int -> state -> step_result

val handle_PUSHACC : int -> int -> state -> step_result

val handle_POP : int -> int -> state -> step_result

val handle_ASSIGN : int -> int -> state -> step_result

val handle_ENVACC : int -> int -> state -> step_result

val handle_PUSHENVACC : int -> int -> state -> step_result

val handle_PUSH_RETADDR : int -> int -> state -> step_result

val handle_APPLY : int -> state -> step_result

val handle_APPLY1 : int -> state -> step_result

val handle_APPLY2 : int -> state -> step_result

val handle_APPLY3 : int -> state -> step_result

val handle_APPTERM : int -> int -> state -> step_result

val handle_APPTERM1 : int -> state -> step_result

val handle_APPTERM2 : int -> state -> step_result

val handle_APPTERM3 : int -> state -> step_result

val handle_RETURN : int -> state -> step_result

val handle_RESTART : int -> state -> step_result

val handle_GRAB : int -> int -> state -> step_result

val handle_CLOSURE : int -> int -> int -> state -> step_result

val handle_CLOSUREREC : int -> int -> int list -> int -> state -> step_result

val handle_OFFSETCLOSURE : int -> int -> state -> step_result

val handle_PUSHOFFSETCLOSURE : int -> int -> state -> step_result

val handle_GETGLOBAL : int -> int -> state -> step_result

val handle_PUSHGETGLOBAL : int -> int -> state -> step_result

val handle_GETGLOBALFIELD : int -> int -> int -> state -> step_result

val handle_PUSHGETGLOBALFIELD : int -> int -> int -> state -> step_result

val handle_SETGLOBAL : int -> int -> state -> step_result

val handle_ATOM : int -> int -> state -> step_result

val handle_PUSHATOM : int -> int -> state -> step_result

val handle_MAKEBLOCK : int -> int -> int -> state -> step_result

val handle_MAKEBLOCK1 : int -> int -> state -> step_result

val handle_MAKEBLOCK2 : int -> int -> state -> step_result

val handle_MAKEBLOCK3 : int -> int -> state -> step_result

val handle_MAKEFLOATBLOCK : int -> int -> state -> step_result

val handle_GETFIELD : int -> int -> state -> step_result

val handle_GETFLOATFIELD : int -> int -> state -> step_result

val handle_SETFIELD : int -> int -> state -> step_result

val handle_SETFLOATFIELD : int -> int -> state -> step_result

val handle_VECTLENGTH : int -> state -> step_result

val handle_GETVECTITEM : int -> state -> step_result

val handle_SETVECTITEM : int -> state -> step_result

val handle_GETSTRINGCHAR : int -> state -> step_result

val handle_SETBYTESCHAR : int -> state -> step_result

val handle_BRANCH : int -> state -> step_result

val handle_BRANCHIF : int -> int -> state -> step_result

val handle_BRANCHIFNOT : int -> int -> state -> step_result

val handle_SWITCH : int -> int -> int list -> int list -> state -> step_result

val handle_BOOLNOT : int -> state -> step_result

val handle_PUSHTRAP : int -> int -> state -> step_result

val handle_POPTRAP : int -> state -> step_result

val handle_CHECK_SIGNALS : int -> state -> step_result

val handle_C_CALL : int -> int -> int -> state -> step_result

val handle_CONSTINT : int -> int -> state -> step_result

val handle_PUSHCONSTINT : int -> int -> state -> step_result

val handle_NEGINT : int -> state -> step_result

val handle_ADDINT : int -> state -> step_result

val handle_SUBINT : int -> state -> step_result

val handle_MULINT : int -> state -> step_result

val handle_DIVINT : int -> state -> step_result

val handle_MODINT : int -> state -> step_result

val handle_ANDINT : int -> state -> step_result

val handle_ORINT : int -> state -> step_result

val handle_XORINT : int -> state -> step_result

val handle_LSLINT : int -> state -> step_result

val handle_LSRINT : int -> state -> step_result

val handle_ASRINT : int -> state -> step_result

val handle_EQ : int -> state -> step_result

val handle_NEQ : int -> state -> step_result

val handle_LTINT : int -> state -> step_result

val handle_LEINT : int -> state -> step_result

val handle_GTINT : int -> state -> step_result

val handle_GEINT : int -> state -> step_result

val handle_OFFSETINT : int -> int -> state -> step_result

val handle_OFFSETREF : int -> int -> state -> step_result

val handle_ISINT : int -> state -> step_result

val handle_GETMETHOD : int -> state -> step_result

val handle_GETPUBMET : int -> int -> state -> step_result

val handle_GETDYNMET : int -> state -> step_result

val handle_BEQ : int -> int -> int -> state -> step_result

val handle_BNEQ : int -> int -> int -> state -> step_result

val handle_BLTINT : int -> int -> int -> state -> step_result

val handle_BLEINT : int -> int -> int -> state -> step_result

val handle_BGTINT : int -> int -> int -> state -> step_result

val handle_BGEINT : int -> int -> int -> state -> step_result

val handle_ULTINT : int -> state -> step_result

val handle_UGEINT : int -> state -> step_result

val handle_BULTINT : int -> int -> int -> state -> step_result

val handle_BUGEINT : int -> int -> int -> state -> step_result

val handle_STOP : state -> step_result

val handle_instr : instruction -> int -> state -> step_result

module type HandleInstrSpec =
 sig
  val handle_instr : instruction -> int -> state -> step_result
 end

type 'a array = 'a Code_arr.t

val make : int -> 'a1 -> 'a1 array

val get : 'a1 array -> int -> 'a1

val set0 : 'a1 array -> int -> 'a1 -> 'a1 array

val length1 : 'a1 array -> int

val fetch_instr : instruction array -> int -> instruction option

val list_to_code_array : instruction list -> instruction array

module Coq_Make :
 functor (H:HandleInstrSpec) ->
 sig
  val step : instruction array -> state -> step_result

  val run_micro : int -> instruction array -> state -> bcmicro

  val handle_bcmicro :
    int -> bcmicro -> (int -> value list -> value option) -> run_result

  val run :
    int -> instruction array -> state -> (int -> value list -> value option)
    -> run_result

  val run_pure : int -> instruction array -> value list -> run_result
 end

module Check :
 sig
  val handle_instr : instruction -> int -> state -> step_result
 end

module Interp :
 sig
  val step : instruction array -> state -> step_result

  val run_micro : int -> instruction array -> state -> bcmicro

  val handle_bcmicro :
    int -> bcmicro -> (int -> value list -> value option) -> run_result

  val run :
    int -> instruction array -> state -> (int -> value list -> value option)
    -> run_result

  val run_pure : int -> instruction array -> value list -> run_result
 end

val step0 : instruction array -> state -> step_result

val run_micro0 : int -> instruction array -> state -> bcmicro

val handle_bcmicro0 :
  int -> bcmicro -> (int -> value list -> value option) -> run_result

val run0 :
  int -> instruction array -> state -> (int -> value list -> value option) ->
  run_result

val run_pure0 : int -> instruction array -> value list -> run_result

val fetch_instr0 : instruction array -> int -> instruction option

val list_to_code_array0 : instruction list -> instruction array

type byte_string = bytes

val read_file : int list -> byte_string

val byte_string_to_list : byte_string -> int list

val byte_string_length : byte_string -> int

val print_string_io : int list -> int

val sys_argv : int list list

val unmarshal_globals : byte_string -> int -> int -> int list list

val load_primitives : byte_string -> int -> int -> int list list

type section = { sec_name : int; sec_offset : int; sec_length : int }

module type DecoderSpec =
 sig
  val load_code_section : int list -> int -> instruction list option

  val parse_sections : int list -> int -> section list

  val find_section : section list -> int -> section option
 end

val decode_value_aux : int list -> int -> value * int list

val decode_value : int list -> value

val decode_globals : int list list -> value list

val dATA_name : int

val pRIM_name : int

val list_z_eqb : int list -> int list -> bool

val str_to_codes : char list -> int list

val z_to_string_aux : int -> int -> int list -> int list

val z_to_string_codes : int -> int list

val mk_zeros : int -> value list

val repeat_value : int -> value -> value list

val print_io : int list -> int -> int

val handle_output_char : value list -> value option

val handle_output_bytes : value list -> value option

val handle_format_int : value list -> value option

val handle_open_descriptor : value list -> value option

val handle_obj_tag : value list -> value option

val handle_string_length : value list -> value option

val handle_create_bytes : value list -> value option

val handle_string_equal : value list -> value option

val handle_int_compare : value list -> value option

val handle_string_concat : value list -> value option

val handle_blit_string : value list -> value option

val handle_identity : value list -> value option

val handle_string_get : value list -> value option

val handle_make_vect : value list -> value option

val string_value : char list -> value

val replace_first_value : value -> value -> value list -> value list

val is_blit_primitive : int list -> bool

val resume_after_ccall : int list -> value list -> state -> value -> state

val make_ccall_handler : int list list -> int -> value list -> value option

val run_effectful :
  int -> instruction array -> state -> int list list -> run_result

module Pipeline :
 functor (D:DecoderSpec) ->
 sig
  val main : int
 end

type event = int
  (* singleton inductive, whose constructor was Out_char *)

type termination =
| Term_normal of value
| Term_error of char list
| Term_timeout

type behavior = { trace : event list; result : termination }

val nat_to_events_aux : int -> int -> event list -> event list

val z_to_events : int -> event list

type ident = char list

type binop =
| Op_add
| Op_sub
| Op_mul
| Op_div
| Op_mod
| Op_eq
| Op_neq
| Op_lt
| Op_le
| Op_gt
| Op_ge
| Op_and
| Op_or

type unop =
| Op_neg
| Op_not

type pattern =
| Pat_var of ident
| Pat_int of int
| Pat_bool of bool
| Pat_unit
| Pat_tuple of pattern list
| Pat_constr of ident * pattern option
| Pat_wild
| Pat_or of pattern * pattern
| Pat_record of (ident * pattern) list
| Pat_nil
| Pat_cons of pattern * pattern

type type_expr =
| Ty_int
| Ty_bool
| Ty_unit
| Ty_arrow of type_expr * type_expr
| Ty_tuple of type_expr list
| Ty_constr of ident * type_expr list

type expr =
| Exp_int of int
| Exp_bool of bool
| Exp_unit
| Exp_var of ident
| Exp_binop of binop * expr * expr
| Exp_unop of unop * expr
| Exp_if of expr * expr * expr
| Exp_let of ident * expr * expr
| Exp_letrec of ident * expr * expr
| Exp_fun of ident * expr
| Exp_app of expr * expr
| Exp_tuple of expr list
| Exp_constr of ident * expr option
| Exp_match of expr * (pattern * expr) list
| Exp_seq of expr * expr
| Exp_record of (ident * expr) list
| Exp_field of expr * ident
| Exp_string of char list
| Exp_function of (pattern * expr) list
| Exp_nil
| Exp_cons of expr * expr

type decl =
| Decl_let of ident * expr
| Decl_letrec of ident * expr
| Decl_type of ident * ident list * type_def
| Decl_expr of expr
| Decl_module of ident * decl list
| Decl_open of ident
| Decl_exception of ident * type_expr option
and type_def =
| Td_variant of (ident * type_expr option) list
| Td_alias of type_expr
| Td_record of (ident * type_expr) list

type program = decl list

val nat_to_string_aux : int -> int -> char list -> char list

val nat_to_string : int -> char list

val z_to_string : int -> char list

val intercalate : char list -> char list list -> char list

val pp_binop : binop -> char list

val pp_pattern : pattern -> char list

val pp_type_expr : type_expr -> char list

val pp_expr : expr -> char list

val newline_char : char

val newline_str : char list

val pp_type_def : type_def -> char list

val pp_decl : decl -> char list

val pp_program : program -> char list

val constint_in_range : int -> bool

val constint_malformed_msg : char list

val constr_tag_hash : ident -> int -> int

val constr_tag : ident -> int

type builtin =
| Bi_print_int
| Bi_print_string
| Bi_print_newline
| Bi_print_char
| Bi_compare
| Bi_fst
| Bi_snd
| Bi_succ
| Bi_pred
| Bi_max

type svalue =
| SVal_int of int
| SVal_bool of bool
| SVal_unit
| SVal_tuple of svalue list
| SVal_constr of ident * svalue option
| SVal_closure of ident * expr * env0
| SVal_recclosure of ident * ident * expr * env0
| SVal_builtin of builtin
| SVal_record of (ident * svalue) list
| SVal_string of char list
and env0 =
| Env_nil
| Env_cons of ident * svalue * env0

val env_lookup : env0 -> ident -> svalue option

val env_extend : env0 -> ident -> svalue -> env0

val env_append : env0 -> env0 -> env0

val record_lookup : (ident * svalue) list -> ident -> svalue option

val match_pattern : pattern -> svalue -> env0 option

val try_cases : (pattern * expr) list -> svalue -> (expr * env0) option

type eval_result =
| Eval_ok of svalue * event list
| Eval_err of char list * event list
| Eval_timeout of event list

val eval_binop : binop -> svalue -> svalue -> svalue option

val eval_structural_binop : binop -> svalue -> svalue -> svalue option

val eval_unop : unop -> svalue -> svalue option

val string_to_events : char list -> event list

val apply_builtin :
  builtin -> svalue -> event list -> (svalue * event list) option

val qualify_name : ident -> ident -> ident

val strip_prefix : char list -> char list -> char list option

val stdlib_env : env0

val eval : int -> expr -> env0 -> event list -> eval_result

val decl_bound_names : decl list -> ident list

val add_qualified_bindings : ident -> ident list -> env0 -> env0 -> env0

val open_module_bindings : ident -> env0 -> env0 -> env0

val eval_program : int -> program -> env0 -> event list -> env0 * eval_result

val svalue_to_value : int -> svalue -> value option

val interpret : int -> program -> behavior

type var_loc =
| Loc_stack of int
| Loc_env of int
| Loc_self

type comp_env = (ident * var_loc) list

val comp_lookup : comp_env -> ident -> var_loc option

val shift0 : comp_env -> int -> comp_env

type field_env = (ident * int) list

val field_lookup_missing : int

val field_lookup : field_env -> ident -> int

val find_field_expr : (ident * expr) list -> ident -> expr option

val all_fields_known : field_env -> (ident * expr) list -> bool

val field_name_with_index :
  field_env -> (ident * expr) list -> int -> ident option

val ordered_record_exprs_from :
  field_env -> (ident * expr) list -> int -> int -> expr list option

val build_field_env : (ident * type_expr) list -> int -> field_env

val constr_tag_hash0 : ident -> int -> int

val constr_tag0 : ident -> int

val qualify_name0 : ident -> ident -> ident

val decl_bound_names0 : decl list -> ident list

val prefix_env : ident -> ident list -> int -> comp_env

val strip_final_stop : instruction list -> instruction list

val strip_prefix_string : char list -> char list -> char list option

val open_module_ce : ident -> comp_env -> comp_env

val is_builtin : ident -> int option

val is_inline_builtin : ident -> instruction list option

val mem_ident : ident -> ident list -> bool

val remove_ident : ident -> ident list -> ident list

val dedup_acc : ident list -> ident list -> ident list

val dedup : ident list -> ident list

val pat_vars : pattern -> ident list

val remove_many : ident list -> ident list -> ident list

val free_vars : expr -> ident list

val closure_vars : ident list -> expr -> comp_env -> ident list

val make_fv_env : int -> ident list -> comp_env

val make_body_env : ident -> ident list -> comp_env

val make_rec_body_env : ident -> ident -> ident list -> comp_env

val compile_push_fvs : ident list -> comp_env -> int -> instruction list

val compile_expr :
  int -> expr -> comp_env -> field_env -> int -> instruction list

val compile_decls :
  int -> decl list -> comp_env -> field_env -> int -> instruction list

val expr_node_count : expr -> int

val decl_node_count : decl -> int

val program_node_count : program -> int

val compile_fuel : program -> int

val compile_program : program -> instruction list

val byte_at : int list -> int -> int

val read_u32_le : int list -> int -> int

val read_i32_le : int list -> int -> int

val read_u32_be : int list -> int -> int

val sum_section_lengths : int list -> int -> int -> int

val build_sections : int list -> int -> int -> int -> int -> section list

val parse_sections0 : int list -> int -> section list

val cODE_name : int

val find_section0 : section list -> int -> section option

type raw_instr = { ri_word_offset : int; ri_opcode : int;
                   ri_operands : int list }

val operand_count : int -> int option

val read_operands : int list -> int -> int -> int -> int list * int

val decode_raw_aux : int list -> int -> int -> int -> int -> raw_instr list

val decode_raw : int list -> int -> int -> raw_instr list

val build_offset_map_aux : raw_instr list -> int -> (int * int) list

val build_offset_map : raw_instr list -> (int * int) list

val lookup_offset0 : (int * int) list -> int -> int

val resolve_branch : (int * int) list -> int -> int -> int

val nat_of_z : int -> int

val znth : int -> int list -> int

val resolve_one : (int * int) list -> raw_instr -> instruction

val resolve_all : raw_instr list -> instruction list

val decode_bytecode : int list -> int -> int -> instruction list

val load_code_section0 : int list -> int -> instruction list option

val is_digit : char -> bool

val is_lower : char -> bool

val is_upper : char -> bool

val is_alpha : char -> bool

val is_ident_char : char -> bool

val is_ident_start : char -> bool

val strip_prefix0 : char list -> char list -> char list option

val read_digits : char list -> int -> int * char list

val parse_nat : char list -> (int * char list) option

val try_neg_int : char list -> (int * char list) option

val read_ident_chars : char list -> char list * char list

val parse_ident : char list -> (char list * char list) option

val try_binop : char list -> (binop * char list) option

val parse_pattern : int -> char list -> (pattern * char list) option

val parse_type_expr : int -> char list -> (type_expr * char list) option

val read_string_contents :
  int -> char list -> char list -> (char list * char list) option

val parse_expr : int -> char list -> (expr * char list) option

val parse_variant :
  int -> char list -> ((ident * type_expr option) list * char list) option

val parse_td_record_fields :
  int -> char list -> ((ident * type_expr) list * char list) option

val parse_type_def : int -> char list -> (type_def * char list) option

val newline_char0 : char

val newline_str0 : char list

val parse_type_params : char list -> (ident list * char list) option

val parse_decl : int -> char list -> (decl * char list) option

val parse_program_aux :
  int -> int -> char list -> (decl list * char list) option

val lex_parse : char list -> program option

module ConcreteDecoder :
 sig
  val load_code_section : int list -> int -> instruction list option

  val parse_sections : int list -> int -> section list

  val find_section : section list -> int -> section option
 end

module App :
 sig
  val main : int
 end

val main0 : int
