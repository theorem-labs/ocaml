(* ExternalCallSpecs.v -- Shared specifications for external function calls.

   This file defines reusable specifications for the external C functions
   called by OCaml bytecode instruction handlers:
   - heap_alloc: allocates a heap block (used by MAKEBLOCK*, CLOSURE, etc.)
   - caml_modify: writes to a heap cell with GC tracking (used by SETGLOBAL,
     SETFIELD*, SETVECTITEM, etc.)

   These are DEFINITIONS ONLY.  Handler step_pre predicates include these
   specs as preconditions; no proofs are given here.

   Convention: Specs are parameterized over the Clight global environment
   (ge) so they can be used with any instantiation. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
Require Import instruct_handlers.
Require Import InstructSpec.

(* ================================================================== *)
(* External function definitions                                       *)
(* ================================================================== *)

Definition heap_alloc_ef : external_function :=
  EF_external "heap_alloc"
    (mksignature (Xptr :: Xlong :: Xlong :: nil) Xlong cc_default).

Definition caml_modify_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (Xptr :: Xlong :: nil) Xvoid cc_default).

(* ================================================================== *)
(* ext_func_findable: a named external function is in the Genv          *)
(* ================================================================== *)

Definition ext_func_findable
    (ge : genv) (e : Clight.env) (id : ident)
    (fd : Ctypes.fundef function) : Prop :=
  exists b,
    Genv.find_symbol (genv_genv ge) id = Some b /\
    Genv.find_funct (genv_genv ge) (Vptr b Ptrofs.zero) = Some fd /\
    e ! id = None.

(* Concrete fundef for heap_alloc *)
Definition heap_alloc_fundef : Ctypes.fundef function :=
  Ctypes.External heap_alloc_ef
    ((tptr (Tstruct _interp_state noattr)) :: tlong :: tlong :: nil)
    tlong cc_default.

(* Concrete fundef for caml_modify *)
Definition caml_modify_fundef : Ctypes.fundef function :=
  Ctypes.External caml_modify_ef
    ((tptr tlong) :: tlong :: nil)
    tvoid cc_default.

(* ================================================================== *)
(* heap_alloc_spec                                                     *)
(*                                                                     *)
(* Specification of heap_alloc's effect on CompCert memory.            *)
(* Given the current memory m with abs_rel fields, calling             *)
(* heap_alloc(s_ptr, sz, tag) produces:                                *)
(* - A post-memory m_alloc and return value Vptr new_b new_ofs         *)
(* - Freshness: new_b is distinct from sb, sp_b, gb, cb               *)
(* - Load preservation: existing loads on other blocks survive         *)
(* - Permission preservation: Writable perms survive                   *)
(* - The new block is storable at field offsets                        *)
(* - Stores to the new block preserve loads on other blocks            *)
(* ================================================================== *)

Definition heap_alloc_spec
    (ge : genv) (m : mem)
    (sb : block) (so : ptrofs)
    (sp_b : block) (sp_ofs : ptrofs) (stk : list Value.value)
    (gb cb : block) (tag_z sz_z : Z) : Prop :=
  0 <= tag_z <= 255 -> 0 <= sz_z ->
  exists m_alloc new_b new_ofs,
    external_call heap_alloc_ef
      (Genv.to_senv (genv_genv ge))
      (Vptr sb so :: Vlong (Int64.repr sz_z) :: Vlong (Int64.repr tag_z) :: nil)
      m E0 (Vptr new_b new_ofs) m_alloc /\
    (* Freshness: new block is distinct from all known blocks *)
    new_b <> sb /\ new_b <> sp_b /\ new_b <> gb /\ new_b <> cb /\
    (* Load preservation on existing blocks *)
    (forall b ofs chunk v,
       Mem.load chunk m b ofs = Some v -> b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v) /\
    (* Permission preservation on existing blocks *)
    (forall b ofs k p,
       Mem.valid_block m b -> Mem.perm m b ofs k p ->
       Mem.perm m_alloc b ofs k p) /\
    (* New block storable at field offsets *)
    (forall field_ofs cv,
       0 <= field_ofs -> field_ofs + 8 <= sz_z * 8 ->
       (8 | Ptrofs.unsigned new_ofs + field_ofs) ->
       exists m_store,
         Mem.store Mint64 m_alloc new_b
           (Ptrofs.unsigned new_ofs + field_ofs) cv = Some m_store) /\
    (* Stores to new block preserve loads on existing blocks *)
    (forall m_store new_v field_ofs,
       Mem.store Mint64 m_alloc new_b
         (Ptrofs.unsigned new_ofs + field_ofs) new_v = Some m_store ->
       forall b ofs chunk v, b <> new_b ->
         Mem.load chunk m_alloc b ofs = Some v ->
         Mem.load chunk m_store b ofs = Some v).

(* ================================================================== *)
(* caml_modify_spec                                                    *)
(*                                                                     *)
(* Specification of caml_modify's effect on CompCert memory.           *)
(* caml_modify(ptr, new_val) writes new_val to *ptr with GC tracking. *)
(* The spec says:                                                      *)
(* - The write happens: load at ptr returns new_val                    *)
(* - Other loads are preserved                                         *)
(* - Permissions are preserved                                         *)
(* ================================================================== *)

Definition caml_modify_spec
    (ge : genv) (m : mem)
    (ptr_b : block) (ptr_ofs : ptrofs)
    (new_val : val)
    (sb : block) (so : ptrofs)
    (sp_b gb cb : block) : Prop :=
  exists m_cm,
    external_call caml_modify_ef
      (Genv.to_senv (genv_genv ge))
      (Vptr ptr_b ptr_ofs :: new_val :: nil)
      m E0 Vundef m_cm /\
    (* The write happened *)
    Mem.load Mint64 m_cm ptr_b (Ptrofs.unsigned ptr_ofs) = Some new_val /\
    (* Other loads preserved *)
    (forall b ofs chunk v,
       Mem.load chunk m b ofs = Some v ->
       (b <> ptr_b \/ ofs <> Ptrofs.unsigned ptr_ofs) ->
       Mem.load chunk m_cm b ofs = Some v) /\
    (* Permissions preserved *)
    (forall b ofs k p,
       Mem.valid_block m b -> Mem.perm m b ofs k p ->
       Mem.perm m_cm b ofs k p).
