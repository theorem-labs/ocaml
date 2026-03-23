(* Compile.v - [UNTRUSTED] Compiler from OCaml AST to bytecode.
   Transforms Syntax.v AST into Bytecode.v instruction lists.
   Validated by PBT: compile + bytecode_interp vs ocamlrun. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From OCamlInterp.Trusted.Bytecode Require Import Value AST.
From OCamlInterp.SemiTrusted Require Import Syntax.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Local Notation len := Datatypes.length (only parsing).

(* === Compilation environment === *)

Inductive var_loc : Type :=
  | Loc_stack : nat -> var_loc
  | Loc_env   : nat -> var_loc
  | Loc_self  : var_loc.

Definition comp_env := list (ident * var_loc).

Fixpoint comp_lookup (ce : comp_env) (x : ident) : option var_loc :=
  match ce with
  | [] => None
  | (y, loc) :: rest =>
    if String.eqb x y then Some loc else comp_lookup rest x
  end.

Fixpoint shift (ce : comp_env) (n : nat) : comp_env :=
  match ce with
  | [] => []
  | (x, Loc_stack pos) :: rest => (x, Loc_stack (pos + n)) :: shift rest n
  | entry :: rest => entry :: shift rest n
  end.

(* === Builtins === *)

Definition is_builtin (x : ident) : option nat :=
  if String.eqb x "print_int" then Some 0%nat
  else if String.eqb x "print_newline" then Some 1%nat
  else if String.eqb x "print_string" then Some 2%nat
  else None.

Definition is_inline_builtin (x : ident) : option (list instruction) :=
  if String.eqb x "fst" then Some [GETFIELD 0]
  else if String.eqb x "snd" then Some [GETFIELD 1]
  else None.

(* === Free variable analysis === *)

Fixpoint mem_ident (x : ident) (l : list ident) : bool :=
  match l with
  | [] => false
  | y :: r => if String.eqb x y then true else mem_ident x r
  end.

Fixpoint remove_ident (x : ident) (l : list ident) : list ident :=
  match l with
  | [] => []
  | y :: r => if String.eqb x y then remove_ident x r else y :: remove_ident x r
  end.

Fixpoint dedup_acc (seen : list ident) (l : list ident) : list ident :=
  match l with
  | [] => []
  | x :: r =>
    if mem_ident x seen then dedup_acc seen r
    else x :: dedup_acc (x :: seen) r
  end.

Definition dedup (l : list ident) : list ident := dedup_acc [] l.

Fixpoint pat_vars (p : pattern) : list ident :=
  match p with
  | Pat_var x => [x]
  | Pat_tuple ps =>
    (fix pv_list l := match l with [] => [] | p1 :: r => pat_vars p1 ++ pv_list r end) ps
  | Pat_constr _ (Some p') => pat_vars p'
  | _ => []
  end.

Definition remove_many (xs : list ident) (l : list ident) : list ident :=
  fold_left (fun acc x => remove_ident x acc) xs l.

Fixpoint free_vars (e : expr) : list ident :=
  match e with
  | Exp_int _ | Exp_bool _ | Exp_unit => []
  | Exp_var x => [x]
  | Exp_binop _ e1 e2 => free_vars e1 ++ free_vars e2
  | Exp_unop _ e1 => free_vars e1
  | Exp_if c t e => free_vars c ++ free_vars t ++ free_vars e
  | Exp_let x e1 e2 => free_vars e1 ++ remove_ident x (free_vars e2)
  | Exp_letrec f e1 e2 =>
    remove_ident f (free_vars e1) ++ remove_ident f (free_vars e2)
  | Exp_fun x body => remove_ident x (free_vars body)
  | Exp_app e1 e2 => free_vars e1 ++ free_vars e2
  | Exp_tuple es =>
    (fix fv_list l := match l with [] => [] | e1 :: r => free_vars e1 ++ fv_list r end) es
  | Exp_constr _ None => []
  | Exp_constr _ (Some e1) => free_vars e1
  | Exp_match scrut cases =>
    free_vars scrut ++
    (fix fv_cases l :=
      match l with
      | [] => []
      | (p, b) :: r => remove_many (pat_vars p) (free_vars b) ++ fv_cases r
      end) cases
  | Exp_seq e1 e2 => free_vars e1 ++ free_vars e2
  end.

(* Compute free vars that need closure capture *)
Definition closure_vars (params : list ident) (body : expr) (ce : comp_env)
    : list ident :=
  let fvs := remove_many params (free_vars body) in
  let fvs' := dedup fvs in
  filter (fun x => match comp_lookup ce x with Some _ => true | None => false end) fvs'.

(* === Closure helpers === *)

Fixpoint make_fv_env (i : nat) (fvs : list ident) : comp_env :=
  match fvs with
  | [] => []
  | x :: rest => (x, Loc_env (2 + i)) :: make_fv_env (S i) rest
  end.

Definition make_body_env (param : ident) (fvs : list ident) : comp_env :=
  (param, Loc_stack 0) :: make_fv_env 0 fvs.

Definition make_rec_body_env (param fname : ident) (fvs : list ident) : comp_env :=
  (param, Loc_stack 0) :: (fname, Loc_self) :: make_fv_env 0 fvs.

(* Push free vars for closure creation.
   Input: fvs in REVERSE order so ENVACC 2 = fvs[0], ENVACC 3 = fvs[1], etc.
   Last var ends up in accu; earlier ones pushed to stack. *)
Fixpoint compile_push_fvs (fvs : list ident) (ce : comp_env) (pushed : nat)
    : list instruction :=
  match fvs with
  | [] => []
  | [x] =>
    let ce' := shift ce pushed in
    match comp_lookup ce' x with
    | Some (Loc_stack n) => [ACC n]
    | Some (Loc_env n) => [ENVACC n]
    | Some Loc_self => [OFFSETCLOSURE 0]
    | None => [CONSTINT 0]
    end
  | x :: rest =>
    let ce' := shift ce pushed in
    let load := match comp_lookup ce' x with
                | Some (Loc_stack n) => [ACC n]
                | Some (Loc_env n) => [ENVACC n]
                | Some Loc_self => [OFFSETCLOSURE 0]
                | None => [CONSTINT 0]
                end in
    load ++ [PUSH] ++ compile_push_fvs rest ce (S pushed)
  end.

(* === Main compilation function === *)

(* base = absolute instruction index where this expression's code starts.
   All branch targets are absolute instruction indices. *)
Fixpoint compile_expr (fuel : nat) (e : expr) (ce : comp_env) (base : nat)
    : list instruction :=
  match fuel with O => [STOP] | S fuel' =>
  match e with
  | Exp_int n => [CONSTINT n]
  | Exp_bool true => [CONSTINT 1]
  | Exp_bool false => [CONSTINT 0]
  | Exp_unit => [CONSTINT 0]

  | Exp_var x =>
    match comp_lookup ce x with
    | Some (Loc_stack n) => [ACC n]
    | Some (Loc_env n) => [ENVACC n]
    | Some Loc_self => [OFFSETCLOSURE 0]
    | None => [CONSTINT 0]
    end

  | Exp_binop op e1 e2 =>
    let c2 := compile_expr fuel' e2 ce base in
    let c1 := compile_expr fuel' e1 (shift ce 1) (base + len c2 + 1) in
    let op_instr := match op with
      | Op_add => ADDINT | Op_sub => SUBINT | Op_mul => MULINT
      | Op_div => DIVINT | Op_mod => MODINT
      | Op_eq => EQ | Op_neq => NEQ
      | Op_lt => LTINT | Op_le => LEINT | Op_gt => GTINT | Op_ge => GEINT
      | Op_and => ANDINT | Op_or => ORINT
      end in
    c2 ++ [PUSH] ++ c1 ++ [op_instr]

  | Exp_unop Op_neg e1 => compile_expr fuel' e1 ce base ++ [NEGINT]
  | Exp_unop Op_not e1 => compile_expr fuel' e1 ce base ++ [BOOLNOT]

  | Exp_if cond then_e else_e =>
    let cc := compile_expr fuel' cond ce base in
    let cc_len := len cc in
    let ct := compile_expr fuel' then_e ce (base + cc_len + 1) in
    let ct_len := len ct in
    let else_base := (base + cc_len + 1 + ct_len + 1)%nat in
    let ce_code := compile_expr fuel' else_e ce else_base in
    let ce_len := len ce_code in
    cc ++ [BRANCHIFNOT (Z.of_nat else_base)] ++
    ct ++ [BRANCH (Z.of_nat (else_base + ce_len))] ++ ce_code

  | Exp_let x e1 e2 =>
    let c1 := compile_expr fuel' e1 ce base in
    let c1_len := len c1 in
    let c2 := compile_expr fuel' e2
                ((x, Loc_stack 0) :: shift ce 1)
                (base + c1_len + 1) in
    c1 ++ [PUSH] ++ c2 ++ [POP 1]

  | Exp_letrec f e1 e2 =>
    match e1 with
    | Exp_fun param body =>
      let fvs := closure_vars [f; param] body ce in
      let nvars := len fvs in
      let body_env := make_rec_body_env param f fvs in
      let body_code := compile_expr fuel' body body_env (base + 1) in
      let body_instrs := body_code ++ [RETURN 1] in
      let body_len := len body_instrs in
      let push_code := compile_push_fvs (rev fvs) ce 0 in
      let body_start := Z.of_nat (base + 1) in
      let branch_target := Z.of_nat (base + 1 + body_len) in
      let cr_pos := (base + 1 + body_len + len push_code)%nat in
      let c2 := compile_expr fuel' e2
                  ((f, Loc_stack 0) :: shift ce 1)
                  (cr_pos + 1) in
      [BRANCH branch_target] ++ body_instrs ++ push_code ++
      [CLOSUREREC 1 nvars [body_start]] ++ c2 ++ [POP 1]
    | _ =>
      let c1 := compile_expr fuel' e1 ce base in
      let c1_len := len c1 in
      let c2 := compile_expr fuel' e2
                  ((f, Loc_stack 0) :: shift ce 1)
                  (base + c1_len + 1) in
      c1 ++ [PUSH] ++ c2 ++ [POP 1]
    end

  | Exp_fun param body =>
    let fvs := closure_vars [param] body ce in
    let nvars := len fvs in
    let body_env := make_body_env param fvs in
    let body_code := compile_expr fuel' body body_env (base + 1) in
    let body_instrs := body_code ++ [RETURN 1] in
    let body_len := len body_instrs in
    let push_code := compile_push_fvs (rev fvs) ce 0 in
    let body_start := Z.of_nat (base + 1) in
    let branch_target := Z.of_nat (base + 1 + body_len) in
    [BRANCH branch_target] ++ body_instrs ++ push_code ++
    [CLOSURE nvars body_start]

  | Exp_app func arg =>
    match func with
    | Exp_var fname =>
      match is_builtin fname with
      | Some prim_idx =>
        compile_expr fuel' arg ce base ++ [C_CALL 1 prim_idx]
      | None =>
        match is_inline_builtin fname with
        | Some instrs =>
          compile_expr fuel' arg ce base ++ instrs
        | None =>
          let ca := compile_expr fuel' arg ce base in
          let ca_len := len ca in
          let cf := compile_expr fuel' func (shift ce 1) (base + ca_len + 1) in
          ca ++ [PUSH] ++ cf ++ [APPLY1]
        end
      end
    | _ =>
      let ca := compile_expr fuel' arg ce base in
      let ca_len := len ca in
      let cf := compile_expr fuel' func (shift ce 1) (base + ca_len + 1) in
      ca ++ [PUSH] ++ cf ++ [APPLY1]
    end

  | Exp_tuple es =>
    (* Evaluate right-to-left: field 0 = first element *)
    match es with
    | [] => [ATOM 0]
    | [e1] => compile_expr fuel' e1 ce base ++ [MAKEBLOCK1 0]
    | [e1; e2] =>
      let c2 := compile_expr fuel' e2 ce base in
      let c1 := compile_expr fuel' e1 (shift ce 1) (base + len c2 + 1) in
      c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK2 0]
    | [e1; e2; e3] =>
      let c3 := compile_expr fuel' e3 ce base in
      let c3_len := len c3 in
      let c2 := compile_expr fuel' e2 (shift ce 1) (base + c3_len + 1) in
      let c2_len := len c2 in
      let c1 := compile_expr fuel' e1 (shift ce 2)
                  (base + c3_len + 1 + c2_len + 1) in
      c3 ++ [PUSH] ++ c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK3 0]
    | _ => [CONSTINT 0]
    end

  | Exp_constr _ None => [CONSTINT 0]
  | Exp_constr _ (Some e1) =>
    compile_expr fuel' e1 ce base ++ [MAKEBLOCK1 0]

  | Exp_match scrut cases =>
    let cs := compile_expr fuel' scrut ce base in
    let cs_len := len cs in
    let scrut_ce := shift ce 1 in  (* scrutinee pushed onto stack *)
    let cases_base := (base + cs_len + 1)%nat in
    let cases_code :=
      (fix compile_cases (cl : list (pattern * expr)) (b : nat)
           : list instruction :=
        match cl with
        | [] => []
        | (pat, body) :: rest =>
          let body_ce := match pat with
                         | Pat_var x => (x, Loc_stack 0) :: scrut_ce
                         | _ => scrut_ce
                         end in
          let irrefutable := match pat with
                             | Pat_wild | Pat_var _ | Pat_unit => true
                             | _ => false
                             end in
          if irrefutable then
            compile_expr fuel' body body_ce b
          else
            match rest with
            | [] => compile_expr fuel' body body_ce b
            | _ =>
              let test := match pat with
                | Pat_int n => [ACC 0; PUSH; CONSTINT n; EQ]
                | Pat_bool true => [ACC 0; PUSH; CONSTINT 1; EQ]
                | Pat_bool false => [ACC 0; PUSH; CONSTINT 0; EQ]
                | _ => []
                end in
              let tl := len test in
              let bs := (b + tl + 1)%nat in  (* +1 for BRANCHIFNOT *)
              let bc := compile_expr fuel' body body_ce bs in
              let bl := len bc in
              let ns := (bs + bl + 1)%nat in  (* +1 for BRANCH end *)
              let rc := compile_cases rest ns in
              let rl := len rc in
              let ep := (ns + rl)%nat in
              test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
              bc ++ [BRANCH (Z.of_nat ep)] ++ rc
            end
        end) cases cases_base in
    cs ++ [PUSH] ++ cases_code ++ [POP 1]

  | Exp_seq e1 e2 =>
    let c1 := compile_expr fuel' e1 ce base in
    let c2 := compile_expr fuel' e2 ce (base + len c1) in
    c1 ++ c2

  end
  end.

(* === Top-level program compilation === *)

Fixpoint compile_decls (fuel : nat) (decls : list decl) (ce : comp_env) (base : nat)
    : list instruction :=
  match fuel with O => [STOP] | S fuel' =>
  match decls with
  | [] => [STOP]
  | Decl_expr e :: rest =>
    let c := compile_expr fuel' e ce base in
    c ++ compile_decls fuel' rest ce (base + len c)
  | Decl_let x e :: rest =>
    let c := compile_expr fuel' e ce base in
    let c_len := len c in
    c ++ [PUSH] ++
    compile_decls fuel' rest ((x, Loc_stack 0) :: shift ce 1) (base + c_len + 1)
  | Decl_letrec f e :: rest =>
    match e with
    | Exp_fun param body =>
      (* Mirror Exp_letrec: use CLOSUREREC for recursive closures *)
      let fvs := closure_vars [f; param] body ce in
      let nvars := len fvs in
      let body_env := make_rec_body_env param f fvs in
      let body_code := compile_expr fuel' body body_env (base + 1) in
      let body_instrs := body_code ++ [RETURN 1] in
      let body_len := len body_instrs in
      let push_code := compile_push_fvs (rev fvs) ce 0 in
      let body_start := Z.of_nat (base + 1) in
      let branch_target := Z.of_nat (base + 1 + body_len) in
      let cr_pos := (base + 1 + body_len + len push_code)%nat in
      let rest_code := compile_decls fuel' rest
                         ((f, Loc_stack 0) :: shift ce 1)
                         (cr_pos + 1) in
      [BRANCH branch_target] ++ body_instrs ++ push_code ++
      [CLOSUREREC 1 nvars [body_start]] ++ rest_code
    | _ =>
      (* Non-function let rec: treat as let *)
      compile_decls fuel' (Decl_let f e :: rest) ce base
    end
  | Decl_type _ _ _ :: rest =>
    compile_decls fuel' rest ce base
  end
  end.

Definition compile_program (prog : program) : list instruction :=
  compile_decls 1000 prog [] 0.
