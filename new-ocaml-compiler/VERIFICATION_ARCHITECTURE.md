# Verification Architecture

```
  LEGEND
  =====>  Trusted
  ----->  Untrusted
  d['a] := 'a PathMap.t


                                 ocamlrun
                          +--------------------+
                          |       disk         |
                          |        |           |
                          |        | os        |
                          |        V           |
                          |     d[bytes]       |
                          |        |           |
                          |  lexing/  ^        |
                          | parsing   | pretty-|
                          |   |       | printer|
  ocamlc                  |   V       |        |
+-------------------------+---+-------+--------+-----------------------+
|          compile        |   | interpret      |    pretty-printer     |
|         lexing/parsing  |   | -bytecode      |                       |
| disk ======> d[bytes]   |   |                |                       |
|   |            |        |   |                |                       |
|   | os         |        |   |                |                       |
|   V            V        |   V                |                       |
| d[bytes] ---> d[OCaml  ---> d[bytecode  =====================> d[bytes] =====> disk
|          <===  AST]         AST]         |   |                       |    os
|       pretty-  |            |            |   |                       |
|       printer  |            |            |   |                       |
+----------------+-----+------+-----------+---+-----------------------+
                       |      |           |
                       |       \          |
                  interpret     \         |
                       |         \        |
                       V          V       V
                 +--------------------------+
                 |      interaction         |
                 |      tree[syscall]       |
                 +--------------------------+
                            |
                            | os
                            V
                 +--------------------------+
                 |       real world         |
                 +--------------------------+
```

## Data Flow

1. **ocamlc path** (left): `disk =os=> d[bytes] --lexing/parsing--> d[OCaml AST] --compile--> d[bytecode AST]`
2. **ocamlrun path** (top): `disk =os=> d[bytes] --lexing/parsing--> d[bytecode AST]` and `d[bytecode AST] =pretty-printer=> d[bytes]`
3. **Interpretation**: `d[bytecode AST] =interpret-bytecode=> interaction tree[syscall] =os=> real world`
4. **Source interpretation**: `d[OCaml AST] --interpret--> interaction tree[syscall]`
5. **Serialization** (right): `d[bytecode AST] =pretty-printer=> d[bytes] =os=> disk`

## Trust Model

- **Trusted (=====>, green in diagram)**: pretty-printers, `interpret-bytecode`, `os` interfaces. Must be correct; kept simple.
- **Untrusted (----->)**: parsers/lexers, `compile`, `interpret`. Validated by PBT and proofs; can be complex.

The correctness theorem: `forall source, interpret(source) = (interpret-bytecode . compile)(source)`

Pretty-printers are trusted because they are simple injections. Parsers are untrusted because they are complex inversions validated by roundtrip proofs: `parse(pretty-print(x)) = x`.
