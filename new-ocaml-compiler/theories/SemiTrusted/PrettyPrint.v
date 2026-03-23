(* PrettyPrint.v - [TRUSTED] Fully parenthesized OCaml pretty-printer. *)

From Stdlib Require Import ZArith Strings.String Strings.Ascii.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.SemiTrusted Require Import Syntax.
Open Scope string_scope.

Fixpoint nat_to_string_aux (fuel n : nat) (acc : string) : string :=
  match fuel with
  | O => acc
  | S fuel' =>
    let digit := String (Ascii.ascii_of_nat (48 + Nat.modulo n 10)) EmptyString in
    let rest := Nat.div n 10 in
    if Nat.eqb rest 0 then String.append digit acc
    else nat_to_string_aux fuel' rest (String.append digit acc)
  end.

Definition nat_to_string (n : nat) : string :=
  if Nat.eqb n 0 then "0" else nat_to_string_aux 20 n "".

Definition Z_to_string (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => nat_to_string (Pos.to_nat p)
  | Zneg p => String.append "(-" (String.append (nat_to_string (Pos.to_nat p)) ")")
  end.

Fixpoint intercalate (sep : string) (l : list string) : string :=
  match l with
  | [] => ""
  | [x] => x
  | x :: rest => String.append x (String.append sep (intercalate sep rest))
  end.

Definition pp_binop (op : binop) : string :=
  match op with
  | Op_add => " + " | Op_sub => " - " | Op_mul => " * "
  | Op_div => " / " | Op_mod => " mod "
  | Op_eq => " = " | Op_neq => " <> "
  | Op_lt => " < " | Op_le => " <= " | Op_gt => " > " | Op_ge => " >= "
  | Op_and => " && " | Op_or => " || "
  end.

Fixpoint pp_pattern (p : pattern) : string :=
  match p with
  | Pat_var x => x
  | Pat_int n => Z_to_string n
  | Pat_bool true => "true" | Pat_bool false => "false"
  | Pat_unit => "()"
  | Pat_tuple ps => String.append "(" (String.append (intercalate ", " (List.map pp_pattern ps)) ")")
  | Pat_constr c None => c
  | Pat_constr c (Some p) => String.append "(" (String.append c (String.append " " (String.append (pp_pattern p) ")")))
  | Pat_wild => "_"
  end.

Fixpoint pp_type_expr (t : type_expr) : string :=
  match t with
  | Ty_int => "int" | Ty_bool => "bool" | Ty_unit => "unit"
  | Ty_arrow t1 t2 => String.append "(" (String.append (pp_type_expr t1) (String.append " -> " (String.append (pp_type_expr t2) ")")))
  | Ty_tuple ts => String.append "(" (String.append (intercalate " * " (List.map pp_type_expr ts)) ")")
  | Ty_constr name [] => name
  | Ty_constr name [t] => String.append "(" (String.append (pp_type_expr t) (String.append " " (String.append name ")")))
  | Ty_constr name args => String.append "((" (String.append (intercalate ", " (List.map pp_type_expr args)) (String.append ") " (String.append name ")")))
  end.

Fixpoint pp_expr (e : expr) : string :=
  match e with
  | Exp_int n => Z_to_string n
  | Exp_bool true => "true" | Exp_bool false => "false"
  | Exp_unit => "()"
  | Exp_var x => x
  | Exp_binop op e1 e2 => String.append "(" (String.append (pp_expr e1) (String.append (pp_binop op) (String.append (pp_expr e2) ")")))
  | Exp_unop Op_neg e => String.append "(- " (String.append (pp_expr e) ")")
  | Exp_unop Op_not e => String.append "(not " (String.append (pp_expr e) ")")
  | Exp_if e1 e2 e3 => String.append "(if " (String.append (pp_expr e1) (String.append " then " (String.append (pp_expr e2) (String.append " else " (String.append (pp_expr e3) ")")))))
  | Exp_let x e1 e2 => String.append "(let " (String.append x (String.append " = " (String.append (pp_expr e1) (String.append " in " (String.append (pp_expr e2) ")")))))
  | Exp_letrec f e1 e2 => String.append "(let rec " (String.append f (String.append " = " (String.append (pp_expr e1) (String.append " in " (String.append (pp_expr e2) ")")))))
  | Exp_fun x body => String.append "(fun " (String.append x (String.append " -> " (String.append (pp_expr body) ")")))
  | Exp_app f arg => String.append "(" (String.append (pp_expr f) (String.append " " (String.append (pp_expr arg) ")")))
  | Exp_tuple es => String.append "(" (String.append (intercalate ", " (List.map pp_expr es)) ")")
  | Exp_constr c None => c
  | Exp_constr c (Some e) => String.append "(" (String.append c (String.append " " (String.append (pp_expr e) ")")))
  | Exp_match e cases =>
    let pp_case := fun (c : pattern * expr) => let (p, body) := c in
      String.append "| " (String.append (pp_pattern p) (String.append " -> " (pp_expr body))) in
    String.append "(match " (String.append (pp_expr e) (String.append " with " (String.append (intercalate " " (List.map pp_case cases)) ")")))
  | Exp_seq e1 e2 => String.append "(" (String.append (pp_expr e1) (String.append "; " (String.append (pp_expr e2) ")")))
  end.

Definition pp_type_def (td : type_def) : string :=
  match td with
  | Td_variant constrs => intercalate " | " (List.map (fun cd => match cd with (name, None) => name | (name, Some t) => String.append name (String.append " of " (pp_type_expr t)) end) constrs)
  | Td_alias t => pp_type_expr t
  end.

Definition pp_decl (d : decl) : string :=
  match d with
  | Decl_let x e => String.append "let " (String.append x (String.append " = " (pp_expr e)))
  | Decl_letrec f e => String.append "let rec " (String.append f (String.append " = " (pp_expr e)))
  | Decl_type name params td =>
    let params_str := match params with [] => "" | [p] => String.append "'" (String.append p " ") | _ => String.append "(" (String.append (intercalate ", " (List.map (fun p => String.append "'" p) params)) ") ") end in
    String.append "type " (String.append params_str (String.append name (String.append " = " (pp_type_def td))))
  | Decl_expr e => pp_expr e
  end.

Definition pp_program (prog : program) : string :=
  intercalate "
" (List.map (fun d => String.append (pp_decl d) ";;") prog).
