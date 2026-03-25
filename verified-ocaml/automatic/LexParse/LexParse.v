(* LexParse.v - OCaml source string to AST parser. *)

From Stdlib Require Import ZArith Strings.String Strings.Ascii.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Syntax.
Open Scope string_scope.

(* TODO: Implement string-to-AST parser *)
Definition lex_parse (s : string) : option program :=
  None.
