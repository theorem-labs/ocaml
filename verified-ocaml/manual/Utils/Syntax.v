(* Syntax.v - [TRUSTED] OCaml AST for a core subset. *)

From Stdlib Require Import ZArith Strings.String.
From Stdlib Require Import List. Import ListNotations.
Open Scope string_scope.

Definition ident := string.

Inductive binop : Type :=
  | Op_add | Op_sub | Op_mul | Op_div | Op_mod
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
  | Op_and | Op_or.

Inductive unop : Type := | Op_neg | Op_not.

Inductive pattern : Type :=
  | Pat_var   : ident -> pattern
  | Pat_int   : Z -> pattern
  | Pat_bool  : bool -> pattern
  | Pat_unit  : pattern
  | Pat_tuple : list pattern -> pattern
  | Pat_constr : ident -> option pattern -> pattern
  | Pat_wild  : pattern.

Inductive type_expr : Type :=
  | Ty_int | Ty_bool | Ty_unit
  | Ty_arrow : type_expr -> type_expr -> type_expr
  | Ty_tuple : list type_expr -> type_expr
  | Ty_constr : ident -> list type_expr -> type_expr.

Inductive expr : Type :=
  | Exp_int    : Z -> expr
  | Exp_bool   : bool -> expr
  | Exp_unit   : expr
  | Exp_var    : ident -> expr
  | Exp_binop  : binop -> expr -> expr -> expr
  | Exp_unop   : unop -> expr -> expr
  | Exp_if     : expr -> expr -> expr -> expr
  | Exp_let    : ident -> expr -> expr -> expr
  | Exp_letrec : ident -> expr -> expr -> expr
  | Exp_fun    : ident -> expr -> expr
  | Exp_app    : expr -> expr -> expr
  | Exp_tuple  : list expr -> expr
  | Exp_constr : ident -> option expr -> expr
  | Exp_match  : expr -> list (pattern * expr) -> expr
  | Exp_seq    : expr -> expr -> expr.

Inductive decl : Type :=
  | Decl_let    : ident -> expr -> decl
  | Decl_letrec : ident -> expr -> decl
  | Decl_type   : ident -> list ident -> type_def -> decl
  | Decl_expr   : expr -> decl
with type_def : Type :=
  | Td_variant : list (ident * option type_expr) -> type_def
  | Td_alias   : type_expr -> type_def.

Definition program := list decl.
