(* IO.v - [TRUSTED] Opaque axioms for OS interaction.

   Two OS boundaries:
   1. Disk to bytes: read_file, byte_string_to_list, byte_string_length, sys_argv
   2. Syscalls to real world: print_string_io
   Plus data loading: unmarshal_globals, load_primitives

   Extract Constant directives are in Extract.v (they must be in the
   same compilation unit as the Extraction command). *)

From Stdlib Require Import ZArith List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Opaque types and axioms                                             *)
(* ------------------------------------------------------------------ *)

(* Opaque byte-string type, backed by OCaml [bytes]. *)
Axiom byte_string : Type.

(* Read an entire file. Filename given as a list of char codes (Z). *)
Axiom read_file : list Z -> byte_string.

(* Convert an opaque byte_string to a list of byte values (Z, 0..255). *)
Axiom byte_string_to_list : byte_string -> list Z.

(* Length of an opaque byte_string. *)
Axiom byte_string_length : byte_string -> Z.

(* Print a list of char codes to stdout. Returns 0.
   Return type is Z (not unit) so extraction preserves the call. *)
Axiom print_string_io : list Z -> Z.

(* Command-line arguments as list of (list of char codes). *)
Axiom sys_argv : list (list Z).

(* Marshal a byte_string starting at offset, returning an opaque Obj.t
   that we immediately convert to a value array via a second axiom. *)
Axiom marshal_from_bytes : byte_string -> Z -> list Z.

(* Unmarshal globals: takes raw file bytes and offset+length of DATA section,
   returns a list of (tag, fields) or int encodings suitable for building
   the global table as a list of value. We represent each global as a
   list Z encoding using a simple convention:
     - Integers: [0; n]
     - Blocks: [1; tag; size; field0; field1; ...] (fields are recursive)
     - String blocks: [2; len; c0; c1; ...] *)
Axiom unmarshal_globals : byte_string -> Z -> Z -> list (list Z).

(* Load PRIM section: takes raw file bytes, offset, length -> list of
   primitive name strings (each as list Z of char codes). *)
Axiom load_primitives : byte_string -> Z -> Z -> list (list Z).
