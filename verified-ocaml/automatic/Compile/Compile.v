(* Compile.v - [UNTRUSTED] Compiler from OCaml AST to bytecode.
   Transforms Syntax.v AST into Bytecode.v instruction lists.
   Validated by PBT: compile + bytecode_interp vs ocamlrun. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Utils Require Import Syntax.
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

(* === Field environment === *)

Definition field_env := list (ident * nat).  (* field_name -> index *)

Fixpoint field_lookup (fe : field_env) (f : ident) : nat :=
  match fe with
  | [] => 0  (* default to 0 if not found *)
  | (name, idx) :: rest =>
    if String.eqb f name then idx else field_lookup rest f
  end.

Fixpoint build_field_env (fields : list (ident * type_expr)) (idx : nat) : field_env :=
  match fields with
  | [] => []
  | (name, _) :: rest => (name, idx) :: build_field_env rest (S idx)
  end.

(* === Qualified name helpers === *)

Definition qualify_name (prefix : ident) (name : ident) : ident :=
  String.append prefix (String.append "." name).

(* Extract names bound by a list of declarations (in order of binding).
   Only Decl_let and Decl_letrec introduce bindings. *)
Fixpoint decl_bound_names (ds : list decl) : list ident :=
  match ds with
  | [] => []
  | Decl_let x _ :: rest => x :: decl_bound_names rest
  | Decl_letrec f _ :: rest => f :: decl_bound_names rest
  | _ :: rest => decl_bound_names rest
  end.

(* Given names [x_0; x_1; ...; x_n] (in binding order), produce qualified-name
   aliases. After all inner decls are compiled, x_n is at stack 0, x_{n-1} at
   stack 1, etc. So we reverse the list first and assign positions 0..n. *)
Fixpoint prefix_env (prefix : ident) (names_rev : list ident) (pos : nat) : comp_env :=
  match names_rev with
  | [] => []
  | x :: rest =>
    (qualify_name prefix x, Loc_stack pos) :: prefix_env prefix rest (S pos)
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
  else if String.eqb x "succ" then Some [OFFSETINT 1]
  else if String.eqb x "Stdlib.Int.succ" then Some [OFFSETINT 1]
  else if String.eqb x "pred" then Some [OFFSETINT (-1)]
  else if String.eqb x "Stdlib.Int.pred" then Some [OFFSETINT (-1)]
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
  | Pat_or p1 _ => pat_vars p1  (* treat first pattern only *)
  | Pat_record _ => []  (* treat as wildcard *)
  | Pat_nil => []
  | Pat_cons ph pt => pat_vars ph ++ pat_vars pt
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
  | Exp_record fields =>
    (fix fv_fields l := match l with [] => [] | (_, e1) :: r => free_vars e1 ++ fv_fields r end) fields
  | Exp_field e1 _ => free_vars e1
  | Exp_string _ => []
  | Exp_function cases =>
    (* Desugar: function cases = fun $arg -> match $arg with cases *)
    let arg := "$arg"%string in
    remove_ident arg
      (arg ::
       (fix fv_cases l :=
         match l with
         | [] => []
         | (p, b) :: r => remove_many (pat_vars p) (free_vars b) ++ fv_cases r
         end) cases)
  | Exp_nil => []
  | Exp_cons e1 e2 => free_vars e1 ++ free_vars e2
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
Fixpoint compile_expr (fuel : nat) (e : expr) (ce : comp_env) (fe : field_env) (base : nat)
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
    let c2 := compile_expr fuel' e2 ce fe base in
    let c1 := compile_expr fuel' e1 (shift ce 1) fe (base + len c2 + 1) in
    let op_instr := match op with
      | Op_add => ADDINT | Op_sub => SUBINT | Op_mul => MULINT
      | Op_div => DIVINT | Op_mod => MODINT
      | Op_eq => EQ | Op_neq => NEQ
      | Op_lt => LTINT | Op_le => LEINT | Op_gt => GTINT | Op_ge => GEINT
      | Op_and => ANDINT | Op_or => ORINT
      end in
    c2 ++ [PUSH] ++ c1 ++ [op_instr]

  | Exp_unop Op_neg e1 => compile_expr fuel' e1 ce fe base ++ [NEGINT]
  | Exp_unop Op_not e1 => compile_expr fuel' e1 ce fe base ++ [BOOLNOT]

  | Exp_if cond then_e else_e =>
    let cc := compile_expr fuel' cond ce fe base in
    let cc_len := len cc in
    let ct := compile_expr fuel' then_e ce fe (base + cc_len + 1) in
    let ct_len := len ct in
    let else_base := (base + cc_len + 1 + ct_len + 1)%nat in
    let ce_code := compile_expr fuel' else_e ce fe else_base in
    let ce_len := len ce_code in
    cc ++ [BRANCHIFNOT (Z.of_nat else_base)] ++
    ct ++ [BRANCH (Z.of_nat (else_base + ce_len))] ++ ce_code

  | Exp_let x e1 e2 =>
    let c1 := compile_expr fuel' e1 ce fe base in
    let c1_len := len c1 in
    let c2 := compile_expr fuel' e2
                ((x, Loc_stack 0) :: shift ce 1)
                fe (base + c1_len + 1) in
    c1 ++ [PUSH] ++ c2 ++ [POP 1]

  | Exp_letrec f e1 e2 =>
    match e1 with
    | Exp_fun param body =>
      let fvs := closure_vars [f; param] body ce in
      let nvars := len fvs in
      let body_env := make_rec_body_env param f fvs in
      let body_code := compile_expr fuel' body body_env fe (base + 1) in
      let body_instrs := body_code ++ [RETURN 1] in
      let body_len := len body_instrs in
      let push_code := compile_push_fvs (rev fvs) ce 0 in
      let body_start := Z.of_nat (base + 1) in
      let branch_target := Z.of_nat (base + 1 + body_len) in
      let cr_pos := (base + 1 + body_len + len push_code)%nat in
      let c2 := compile_expr fuel' e2
                  ((f, Loc_stack 0) :: shift ce 1)
                  fe (cr_pos + 1) in
      [BRANCH branch_target] ++ body_instrs ++ push_code ++
      [CLOSUREREC 1 nvars [body_start]] ++ c2 ++ [POP 1]
    | _ =>
      let c1 := compile_expr fuel' e1 ce fe base in
      let c1_len := len c1 in
      let c2 := compile_expr fuel' e2
                  ((f, Loc_stack 0) :: shift ce 1)
                  fe (base + c1_len + 1) in
      c1 ++ [PUSH] ++ c2 ++ [POP 1]
    end

  | Exp_fun param body =>
    let fvs := closure_vars [param] body ce in
    let nvars := len fvs in
    let body_env := make_body_env param fvs in
    let body_code := compile_expr fuel' body body_env fe (base + 1) in
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
        compile_expr fuel' arg ce fe base ++ [C_CALL 1 prim_idx]
      | None =>
        match is_inline_builtin fname with
        | Some instrs =>
          compile_expr fuel' arg ce fe base ++ instrs
        | None =>
          let ca := compile_expr fuel' arg ce fe base in
          let ca_len := len ca in
          let cf := compile_expr fuel' func (shift ce 1) fe (base + ca_len + 1) in
          ca ++ [PUSH] ++ cf ++ [APPLY1]
        end
      end
    | _ =>
      let ca := compile_expr fuel' arg ce fe base in
      let ca_len := len ca in
      let cf := compile_expr fuel' func (shift ce 1) fe (base + ca_len + 1) in
      ca ++ [PUSH] ++ cf ++ [APPLY1]
    end

  | Exp_tuple es =>
    (* Evaluate right-to-left: field 0 = first element.
       Uses MAKEBLOCK1/2/3 for small sizes, general MAKEBLOCK for larger. *)
    let n := len es in
    match es with
    | [] => [ATOM 0]
    | [e1] => compile_expr fuel' e1 ce fe base ++ [MAKEBLOCK1 0]
    | [e1; e2] =>
      let c2 := compile_expr fuel' e2 ce fe base in
      let c1 := compile_expr fuel' e1 (shift ce 1) fe (base + len c2 + 1) in
      c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK2 0]
    | [e1; e2; e3] =>
      let c3 := compile_expr fuel' e3 ce fe base in
      let c3_len := len c3 in
      let c2 := compile_expr fuel' e2 (shift ce 1) fe (base + c3_len + 1) in
      let c2_len := len c2 in
      let c1 := compile_expr fuel' e1 (shift ce 2) fe
                  (base + c3_len + 1 + c2_len + 1) in
      c3 ++ [PUSH] ++ c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK3 0]
    | _ =>
      (* General case for N > 3 elements: evaluate right-to-left,
         PUSH all but the leftmost, then MAKEBLOCK 0 N *)
      let rev_es := rev es in
      let fix compile_elems (elems : list expr) (ce_acc : comp_env)
              (b : nat) (pushed : nat) : list instruction :=
        match elems with
        | [] => []
        | [last] =>
          (* Last element to evaluate (= first in original order):
             leave result in accu, no PUSH *)
          compile_expr fuel' last ce_acc fe b
        | e_i :: rest =>
          let ci := compile_expr fuel' e_i ce_acc fe b in
          let ci_len := len ci in
          ci ++ [PUSH] ++
          compile_elems rest (shift ce_acc 1) (b + ci_len + 1)%nat (S pushed)
        end in
      compile_elems rev_es ce base 0%nat ++ [MAKEBLOCK 0 n]
    end

  | Exp_constr _ None => [CONSTINT 0]
  | Exp_constr _ (Some e1) =>
    compile_expr fuel' e1 ce fe base ++ [MAKEBLOCK1 0]

  | Exp_match scrut cases =>
    let cs := compile_expr fuel' scrut ce fe base in
    let cs_len := len cs in
    let scrut_ce := shift ce 1 in  (* scrutinee pushed onto stack *)
    let cases_base := (base + cs_len + 1)%nat in
    (* Extract variables from a Pat_tuple of Pat_var elements.
       Returns (Some var_list) for pure Pat_var tuples, None otherwise. *)
    let fix tuple_vars (ps : list pattern) : option (list ident) :=
      match ps with
      | [] => Some []
      | Pat_var x :: rest =>
        match tuple_vars rest with
        | Some xs => Some (x :: xs)
        | None => None
        end
      | Pat_wild :: rest =>
        match tuple_vars rest with
        | Some xs => Some ("_" :: xs)
        | None => None
        end
      | _ => None
      end in
    (* Generate code to extract tuple fields and push onto stack.
       Fields are extracted in reverse order so that field 0 ends up
       on top of the stack. Stack layout after: [x0, x1, ..., xn, scrut, ...] *)
    let fix extract_fields (n : nat) (total : nat) (scrut_depth : nat)
        : list instruction :=
      match n with
      | O => []
      | S n' =>
        let field_idx := Nat.sub total n in
        let rest := extract_fields n' total (S scrut_depth) in
        [ACC scrut_depth; GETFIELD field_idx; PUSH] ++ rest
      end in
    (* Build comp_env for tuple-destructured variables.
       vars = [x0, x1, ...], positioned at stack[0..n-1],
       with scrut at stack[n] and the original env shifted by (n+1). *)
    let fix make_tuple_env (vars : list ident) (idx : nat) : comp_env :=
      match vars with
      | [] => []
      | x :: rest => (x, Loc_stack idx) :: make_tuple_env rest (S idx)
      end in
    let cases_code :=
      (fix compile_cases (cl : list (pattern * expr)) (b : nat)
           : list instruction :=
        match cl with
        | [] => []
        | (pat, body) :: rest =>
          let irrefutable := match pat with
                             | Pat_wild | Pat_var _ | Pat_unit => true
                             | Pat_tuple ps =>
                               match tuple_vars ps with
                               | Some _ => true | None => false
                               end
                             | _ => false
                             end in
          let body_ce := match pat with
                         | Pat_var x => (x, Loc_stack 0) :: scrut_ce
                         | _ => scrut_ce
                         end in
          if irrefutable then
            match pat with
            | Pat_tuple ps =>
              match tuple_vars ps with
              | Some vars =>
                let nv := len vars in
                let extr := extract_fields nv nv 0%nat in
                let el := len extr in
                let tup_ce := make_tuple_env (rev vars) 0%nat ++ shift scrut_ce nv in
                let bc := compile_expr fuel' body tup_ce fe (b + el) in
                extr ++ bc ++ [POP nv]
              | None => compile_expr fuel' body body_ce fe b
              end
            | Pat_cons ph pt =>
              match tuple_vars [ph; pt] with
              | Some vars =>
                let nv := 2%nat in
                let extr := extract_fields nv nv 0%nat in
                let el := len extr in
                let cons_ce := make_tuple_env (rev vars) 0%nat ++ shift scrut_ce nv in
                let bc := compile_expr fuel' body cons_ce fe (b + el) in
                extr ++ bc ++ [POP nv]
              | None => compile_expr fuel' body body_ce fe b
              end
            | _ => compile_expr fuel' body body_ce fe b
            end
          else
            match rest with
            | [] =>
              match pat with
              | Pat_tuple ps =>
                match tuple_vars ps with
                | Some vars =>
                  let nv := len vars in
                  let extr := extract_fields nv nv 0%nat in
                  let el := len extr in
                  let tup_ce := make_tuple_env (rev vars) 0%nat ++ shift scrut_ce nv in
                  let bc := compile_expr fuel' body tup_ce fe (b + el) in
                  extr ++ bc ++ [POP nv]
                | None => compile_expr fuel' body body_ce fe b
                end
              | Pat_cons ph pt =>
                match tuple_vars [ph; pt] with
                | Some vars =>
                  let nv := 2%nat in
                  let extr := extract_fields nv nv 0%nat in
                  let el := len extr in
                  let cons_ce := make_tuple_env (rev vars) 0%nat ++ shift scrut_ce nv in
                  let bc := compile_expr fuel' body cons_ce fe (b + el) in
                  extr ++ bc ++ [POP nv]
                | None => compile_expr fuel' body body_ce fe b
                end
              | Pat_constr _ (Some cpat) =>
                (* Last case: constructor with argument, extract field 0 *)
                match cpat with
                | Pat_var x =>
                  let extr := [ACC 0; GETFIELD 0; PUSH] in
                  let el := len extr in
                  let constr_ce := (x, Loc_stack 0) :: shift scrut_ce 1 in
                  let bc := compile_expr fuel' body constr_ce fe (b + el) in
                  extr ++ bc ++ [POP 1]
                | Pat_wild =>
                  compile_expr fuel' body body_ce fe b
                | _ =>
                  compile_expr fuel' body body_ce fe b
                end
              | _ => compile_expr fuel' body body_ce fe b
              end
            | _ =>
              match pat with
              | Pat_cons ph pt =>
                (* Pat_cons with remaining cases: test ISINT (nil=int, cons=block),
                   then extract fields if test passes. *)
                let test := [ACC 0; ISINT; BOOLNOT] in
                let tl := len test in
                let bs := (b + tl + 1)%nat in  (* +1 for BRANCHIFNOT *)
                (* After test passes, extract cons fields *)
                match tuple_vars [ph; pt] with
                | Some vars =>
                  let nv := 2%nat in
                  let extr := extract_fields nv nv 0%nat in
                  let el := len extr in
                  let cons_ce := make_tuple_env (rev vars) 0%nat ++ shift scrut_ce nv in
                  let bc := compile_expr fuel' body cons_ce fe (bs + el) in
                  let bl := len bc in
                  let pop_len := 1%nat in  (* POP nv *)
                  let ns := (bs + el + bl + pop_len + 1)%nat in  (* +1 for BRANCH end *)
                  let rc := compile_cases rest ns in
                  let rl := len rc in
                  let ep := (ns + rl)%nat in
                  test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                  extr ++ bc ++ [POP nv] ++ [BRANCH (Z.of_nat ep)] ++ rc
                | None =>
                  let bc := compile_expr fuel' body body_ce fe bs in
                  let bl := len bc in
                  let ns := (bs + bl + 1)%nat in  (* +1 for BRANCH end *)
                  let rc := compile_cases rest ns in
                  let rl := len rc in
                  let ep := (ns + rl)%nat in
                  test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                  bc ++ [BRANCH (Z.of_nat ep)] ++ rc
                end
              | Pat_constr _ (Some cpat) =>
                (* Constructor with argument: test ISINT; BOOLNOT
                   (true if block = has arg), then extract field 0. *)
                let test := [ACC 0; ISINT; BOOLNOT] in
                let tl := len test in
                let bs := (b + tl + 1)%nat in  (* +1 for BRANCHIFNOT *)
                match cpat with
                | Pat_var x =>
                  let extr := [ACC 0; GETFIELD 0; PUSH] in
                  let el := len extr in
                  let constr_ce := (x, Loc_stack 0) :: shift scrut_ce 1 in
                  let bc := compile_expr fuel' body constr_ce fe (bs + el) in
                  let bl := len bc in
                  let pop_len := 1%nat in  (* POP 1 *)
                  let ns := (bs + el + bl + pop_len + 1)%nat in
                  let rc := compile_cases rest ns in
                  let rl := len rc in
                  let ep := (ns + rl)%nat in
                  test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                  extr ++ bc ++ [POP 1] ++ [BRANCH (Z.of_nat ep)] ++ rc
                | Pat_wild =>
                  let bc := compile_expr fuel' body body_ce fe bs in
                  let bl := len bc in
                  let ns := (bs + bl + 1)%nat in
                  let rc := compile_cases rest ns in
                  let rl := len rc in
                  let ep := (ns + rl)%nat in
                  test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                  bc ++ [BRANCH (Z.of_nat ep)] ++ rc
                | Pat_constr _ (Some inner_pat) =>
                  (* Nested constructor: Some (Some x) -- extract outer field,
                     then test if inner is also a block. *)
                  match inner_pat with
                  | Pat_var x =>
                    (* E.g. Some (Some x): extract field 0 of outer,
                       test ISINT of inner, extract field 0 of inner. *)
                    let extr_outer := [ACC 0; GETFIELD 0] in
                    let test_inner := [PUSH; ACC 0; ISINT; BOOLNOT] in
                    let extr_inner := [ACC 0; GETFIELD 0; PUSH] in
                    let setup := extr_outer ++ test_inner in
                    let setup_len := len setup in
                    let bs2 := (bs + setup_len + 1)%nat in
                    let inner_extr_len := len extr_inner in
                    let inner_ce := (x, Loc_stack 0) :: shift scrut_ce 2 in
                    let bc := compile_expr fuel' body inner_ce fe (bs2 + inner_extr_len) in
                    let bl := len bc in
                    let ns := (bs2 + inner_extr_len + bl + 1 + 1)%nat in
                    let rc := compile_cases rest ns in
                    let rl := len rc in
                    let ep := (ns + rl)%nat in
                    test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                    setup ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                    extr_inner ++ bc ++ [POP 2] ++ [BRANCH (Z.of_nat ep)] ++ rc
                  | _ =>
                    let bc := compile_expr fuel' body body_ce fe bs in
                    let bl := len bc in
                    let ns := (bs + bl + 1)%nat in
                    let rc := compile_cases rest ns in
                    let rl := len rc in
                    let ep := (ns + rl)%nat in
                    test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                    bc ++ [BRANCH (Z.of_nat ep)] ++ rc
                  end
                | _ =>
                  let bc := compile_expr fuel' body body_ce fe bs in
                  let bl := len bc in
                  let ns := (bs + bl + 1)%nat in
                  let rc := compile_cases rest ns in
                  let rl := len rc in
                  let ep := (ns + rl)%nat in
                  test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                  bc ++ [BRANCH (Z.of_nat ep)] ++ rc
                end
              | Pat_constr _ None =>
                (* Nullary constructor (e.g. None): test ISINT
                   (true if int = nullary constr) *)
                let test := [ACC 0; ISINT] in
                let tl := len test in
                let bs := (b + tl + 1)%nat in
                let bc := compile_expr fuel' body body_ce fe bs in
                let bl := len bc in
                let ns := (bs + bl + 1)%nat in
                let rc := compile_cases rest ns in
                let rl := len rc in
                let ep := (ns + rl)%nat in
                test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                bc ++ [BRANCH (Z.of_nat ep)] ++ rc
              | _ =>
                let test := match pat with
                  | Pat_int n => [ACC 0; PUSH; CONSTINT n; EQ]
                  | Pat_bool true => [ACC 0; PUSH; CONSTINT 1; EQ]
                  | Pat_bool false => [ACC 0; PUSH; CONSTINT 0; EQ]
                  | Pat_nil => [ACC 0; PUSH; CONSTINT 0; EQ]
                  | _ => []
                  end in
                let tl := len test in
                let bs := (b + tl + 1)%nat in  (* +1 for BRANCHIFNOT *)
                let bc := compile_expr fuel' body body_ce fe bs in
                let bl := len bc in
                let ns := (bs + bl + 1)%nat in  (* +1 for BRANCH end *)
                let rc := compile_cases rest ns in
                let rl := len rc in
                let ep := (ns + rl)%nat in
                test ++ [BRANCHIFNOT (Z.of_nat ns)] ++
                bc ++ [BRANCH (Z.of_nat ep)] ++ rc
              end
            end
        end) cases cases_base in
    cs ++ [PUSH] ++ cases_code ++ [POP 1]

  | Exp_record fields =>
    (* Compile as tuple: MAKEBLOCK with tag 0, fields in order.
       Extract expressions from (name, expr) pairs, compile right-to-left. *)
    let es := map snd fields in
    let n := len es in
    match es with
    | [] => [ATOM 0]
    | [e1] => compile_expr fuel' e1 ce fe base ++ [MAKEBLOCK1 0]
    | [e1; e2] =>
      let c2 := compile_expr fuel' e2 ce fe base in
      let c1 := compile_expr fuel' e1 (shift ce 1) fe (base + len c2 + 1) in
      c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK2 0]
    | [e1; e2; e3] =>
      let c3 := compile_expr fuel' e3 ce fe base in
      let c3_len := len c3 in
      let c2 := compile_expr fuel' e2 (shift ce 1) fe (base + c3_len + 1) in
      let c2_len := len c2 in
      let c1 := compile_expr fuel' e1 (shift ce 2) fe
                  (base + c3_len + 1 + c2_len + 1) in
      c3 ++ [PUSH] ++ c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK3 0]
    | _ =>
      (* General case for N > 3 fields: evaluate right-to-left,
         PUSH all but the leftmost, then MAKEBLOCK 0 N *)
      let rev_es := rev es in
      let fix compile_elems (elems : list expr) (ce_acc : comp_env)
              (b : nat) (pushed : nat) : list instruction :=
        match elems with
        | [] => []
        | [last] =>
          compile_expr fuel' last ce_acc fe b
        | e_i :: rest =>
          let ci := compile_expr fuel' e_i ce_acc fe b in
          let ci_len := len ci in
          ci ++ [PUSH] ++
          compile_elems rest (shift ce_acc 1) (b + ci_len + 1)%nat (S pushed)
        end in
      compile_elems rev_es ce base 0%nat ++ [MAKEBLOCK 0 n]
    end

  | Exp_field e1 f =>
    let idx := field_lookup fe f in
    compile_expr fuel' e1 ce fe base ++ [GETFIELD idx]

  | Exp_string _ =>
    (* String literal placeholder *)
    [CONSTINT 0]

  | Exp_function cases =>
    (* Desugar: function cases = fun "$arg" -> match "$arg" with cases *)
    compile_expr fuel' (Exp_fun "$arg" (Exp_match (Exp_var "$arg") cases)) ce fe base

  | Exp_seq e1 e2 =>
    let c1 := compile_expr fuel' e1 ce fe base in
    let c2 := compile_expr fuel' e2 ce fe (base + len c1) in
    c1 ++ c2

  | Exp_nil => [CONSTINT 0]

  | Exp_cons e1 e2 =>
    let c2 := compile_expr fuel' e2 ce fe base in
    let c1 := compile_expr fuel' e1 (shift ce 1) fe (base + len c2 + 1) in
    c2 ++ [PUSH] ++ c1 ++ [MAKEBLOCK2 0]

  end
  end.

(* === Top-level program compilation === *)

Fixpoint compile_decls (fuel : nat) (decls : list decl) (ce : comp_env) (fe : field_env) (base : nat)
    : list instruction :=
  match fuel with O => [STOP] | S fuel' =>
  match decls with
  | [] => [STOP]
  | Decl_expr e :: rest =>
    let c := compile_expr fuel' e ce fe base in
    c ++ compile_decls fuel' rest ce fe (base + len c)
  | Decl_let x e :: rest =>
    let c := compile_expr fuel' e ce fe base in
    let c_len := len c in
    c ++ [PUSH] ++
    compile_decls fuel' rest ((x, Loc_stack 0) :: shift ce 1) fe (base + c_len + 1)
  | Decl_letrec f e :: rest =>
    match e with
    | Exp_fun param body =>
      (* Mirror Exp_letrec: use CLOSUREREC for recursive closures *)
      let fvs := closure_vars [f; param] body ce in
      let nvars := len fvs in
      let body_env := make_rec_body_env param f fvs in
      let body_code := compile_expr fuel' body body_env fe (base + 1) in
      let body_instrs := body_code ++ [RETURN 1] in
      let body_len := len body_instrs in
      let push_code := compile_push_fvs (rev fvs) ce 0 in
      let body_start := Z.of_nat (base + 1) in
      let branch_target := Z.of_nat (base + 1 + body_len) in
      let cr_pos := (base + 1 + body_len + len push_code)%nat in
      let rest_code := compile_decls fuel' rest
                         ((f, Loc_stack 0) :: shift ce 1)
                         fe (cr_pos + 1) in
      [BRANCH branch_target] ++ body_instrs ++ push_code ++
      [CLOSUREREC 1 nvars [body_start]] ++ rest_code
    | _ =>
      (* Non-function let rec: treat as let *)
      compile_decls fuel' (Decl_let f e :: rest) ce fe base
    end
  | Decl_type _ _ td :: rest =>
    let fe' := match td with
               | Td_record fields => build_field_env fields 0 ++ fe
               | _ => fe
               end in
    compile_decls fuel' rest ce fe' base
  | Decl_module mod_name inner :: rest =>
    (* Compile inner declarations, then continue with rest.
       Also add qualified-name aliases (e.g. "M.x") for each binding. *)
    let ci := compile_decls fuel' inner ce fe base in
    let ci_len := len ci in
    let names := decl_bound_names inner in
    let n := len names in
    (* After inner decls, stack has n new entries.
       names_rev = [x_n; ...; x_1] where x_n is at stack 0. *)
    let names_rev := rev names in
    (* Build ce with both unqualified and qualified names *)
    let inner_ce :=
      (fix build_inner_ce (ns : list ident) (pos : nat) : comp_env :=
        match ns with
        | [] => []
        | x :: r => (x, Loc_stack pos) :: build_inner_ce r (S pos)
        end) names_rev 0%nat in
    let qualified_ce := prefix_env mod_name names_rev 0%nat in
    let new_ce := qualified_ce ++ inner_ce ++ shift ce n in
    ci ++ compile_decls fuel' rest new_ce fe (base + ci_len)
  | Decl_open _ :: rest =>
    (* Skip: name resolution happens at parse time *)
    compile_decls fuel' rest ce fe base
  | Decl_exception _ _ :: rest =>
    (* Skip for now *)
    compile_decls fuel' rest ce fe base
  end
  end.

Definition compile_program (prog : program) : list instruction :=
  compile_decls 1000 prog [] [] 0.
