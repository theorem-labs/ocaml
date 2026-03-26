(* WellFormed.v - [TRUSTED] Character classification and AST well-formedness. *)

From Stdlib Require Import ZArith Strings.String Strings.Ascii.
From Stdlib Require Import List Bool Nat. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax.
Open Scope string_scope.

(* ========== Character Classification ========== *)

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 48 n && Nat.leb n 57.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 97 n && Nat.leb n 122.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 65 n && Nat.leb n 90.

Definition is_alpha (c : ascii) : bool := is_lower c || is_upper c.

Definition is_ident_char (c : ascii) : bool :=
  is_alpha c || is_digit c || Ascii.eqb c "_"%char || Ascii.eqb c "'"%char.

Definition is_ident_start (c : ascii) : bool :=
  is_alpha c || Ascii.eqb c "_"%char.

(* ========== String Predicates ========== *)

Fixpoint all_ident_chars (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => is_ident_char c && all_ident_chars rest
  end.

Definition is_keyword (s : string) : bool :=
  String.eqb s "if" || String.eqb s "then" || String.eqb s "else" ||
  String.eqb s "let" || String.eqb s "rec" || String.eqb s "in" ||
  String.eqb s "fun" || String.eqb s "match" || String.eqb s "with" ||
  String.eqb s "type" || String.eqb s "of" ||
  String.eqb s "true" || String.eqb s "false" ||
  String.eqb s "not" || String.eqb s "mod" ||
  String.eqb s "function" || String.eqb s "module" ||
  String.eqb s "open" || String.eqb s "exception" ||
  String.eqb s "struct" || String.eqb s "end".

(* ========== Name Validity ========== *)

Definition valid_var_name (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
    (is_lower c || Ascii.eqb c "_"%char) && all_ident_chars rest &&
    negb (is_keyword s) && negb (String.eqb s "_")
  end.

Definition valid_constr_name (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest => is_upper c && all_ident_chars rest
  end.

Definition valid_type_name (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
    (is_lower c || Ascii.eqb c "_"%char) && all_ident_chars rest &&
    negb (is_keyword s)
  end.

(* Integer representability: nat_to_string uses fuel 20, so n < 10^20 *)
Definition wf_int (z : Z) : bool :=
  match z with
  | Z0 => true
  | Zpos p => Pos.leb p 99999999999999999999
  | Zneg p => Pos.leb p 99999999999999999999
  end.

(* ========== Recursive Well-Formedness ========== *)

Fixpoint wf_pattern (p : pattern) : bool :=
  match p with
  | Pat_var x => valid_var_name x
  | Pat_int z => wf_int z
  | Pat_bool _ | Pat_unit | Pat_wild => true
  | Pat_tuple ps => (Nat.leb 2 (length ps)) && forallb wf_pattern ps
  | Pat_constr c None => valid_constr_name c
  | Pat_constr c (Some p') => valid_constr_name c && wf_pattern p'
  | Pat_or p1 p2 => wf_pattern p1 && wf_pattern p2
  | Pat_record fields => forallb (fun f => valid_var_name (fst f) && wf_pattern (snd f)) fields
  | Pat_nil => true
  | Pat_cons ph pt => wf_pattern ph && wf_pattern pt
  end.

Fixpoint wf_type_expr (t : type_expr) : bool :=
  match t with
  | Ty_int | Ty_bool | Ty_unit => true
  | Ty_arrow t1 t2 => wf_type_expr t1 && wf_type_expr t2
  | Ty_tuple ts => (Nat.leb 2 (length ts)) && forallb wf_type_expr ts
  | Ty_constr name [] =>
    valid_type_name name &&
    negb (String.eqb name "int") &&
    negb (String.eqb name "bool") &&
    negb (String.eqb name "unit")
  | Ty_constr name args =>
    valid_type_name name && forallb wf_type_expr args
  end.

Fixpoint wf_expr (e : expr) : bool :=
  match e with
  | Exp_int z => wf_int z
  | Exp_bool _ | Exp_unit => true
  | Exp_var x => valid_var_name x
  | Exp_binop _ e1 e2 => wf_expr e1 && wf_expr e2
  | Exp_unop _ e' => wf_expr e'
  | Exp_if e1 e2 e3 => wf_expr e1 && wf_expr e2 && wf_expr e3
  | Exp_let x e1 e2 => valid_var_name x && wf_expr e1 && wf_expr e2
  | Exp_letrec f e1 e2 => valid_var_name f && wf_expr e1 && wf_expr e2
  | Exp_fun x body => valid_var_name x && wf_expr body
  | Exp_app e1 e2 =>
    wf_expr e1 && wf_expr e2 &&
    match e1 with Exp_constr _ None => false | _ => true end
  | Exp_tuple es => (Nat.leb 2 (length es)) && forallb wf_expr es
  | Exp_constr c None => valid_constr_name c
  | Exp_constr c (Some e') => valid_constr_name c && wf_expr e'
  | Exp_match e' cases =>
    wf_expr e' && (Nat.leb 1 (length cases)) &&
    forallb (fun c => wf_pattern (fst c) && wf_expr (snd c)) cases
  | Exp_seq e1 e2 => wf_expr e1 && wf_expr e2
  | Exp_record fields => forallb (fun f => valid_var_name (fst f) && wf_expr (snd f)) fields
  | Exp_field e' name => wf_expr e' && valid_var_name name
  | Exp_string _ => true
  | Exp_function cases =>
    (Nat.leb 1 (length cases)) &&
    forallb (fun c => wf_pattern (fst c) && wf_expr (snd c)) cases
  | Exp_nil => true
  | Exp_cons e1 e2 => wf_expr e1 && wf_expr e2
  end.

Definition wf_type_def (td : type_def) : bool :=
  match td with
  | Td_variant constrs =>
    (Nat.leb 1 (length constrs)) &&
    forallb (fun c =>
      valid_constr_name (fst c) &&
      match snd c with None => true | Some t => wf_type_expr t end) constrs
  | Td_alias t => wf_type_expr t
  | Td_record fields =>
    forallb (fun f => valid_var_name (fst f) && wf_type_expr (snd f)) fields
  end.

Fixpoint wf_decl (d : decl) : bool :=
  match d with
  | Decl_let x e => valid_var_name x && wf_expr e
  | Decl_letrec f e => valid_var_name f && wf_expr e
  | Decl_type name params td =>
    valid_type_name name &&
    forallb valid_var_name params &&
    wf_type_def td
  | Decl_expr e => wf_expr e
  | Decl_module name decls => valid_constr_name name && forallb wf_decl decls
  | Decl_open name => valid_constr_name name
  | Decl_exception name None => valid_constr_name name
  | Decl_exception name (Some t) => valid_constr_name name && wf_type_expr t
  end.

Definition wf_program (prog : program) : bool :=
  forallb wf_decl prog.
