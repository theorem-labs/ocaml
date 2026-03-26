(* uint63.ml - Shim module for Rocq extraction of Uint63 primitives.
   Maps Uint63 kernel primitives to native OCaml int operations. *)
let of_int (x : int) : int = x
