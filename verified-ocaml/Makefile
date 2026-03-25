.PHONY: all build extract test testsuite clean

all: build extract test

build:
	@rm -f Extract.glob Extract.vo .Extract.aux
	dune build

COQC_FLAGS = \
  -R _build/default/manual/Utils OCamlInterp.Manual.Utils \
  -R _build/default/manual/InterpBytecode OCamlInterp.Manual.InterpBytecode \
  -R _build/default/manual/Correctness OCamlInterp.Manual.Correctness \
  -R _build/default/manual/Checker OCamlInterp.Manual.Checker \
  -R _build/default/semi-auto/Compile/LexParse OCamlInterp.SemiAutomatic.Compile.LexParse \
  -R _build/default/semi-auto/Interpret OCamlInterp.SemiAutomatic.Interpret \
  -R _build/default/automatic/theories/Compile OCamlInterp.Automatic.Compile \
  -R _build/default/automatic/theories/Correctness OCamlInterp.Automatic.Correctness \
  -R _build/default/automatic/theories/InterpBytecode OCamlInterp.Automatic.InterpBytecode

extract: build
	coqc $(COQC_FLAGS) Extract.v -output-directory /tmp
	cp /tmp/Interp_extracted.ml automatic/test/common/interp_extracted.ml
	rm -f /tmp/Interp_extracted.ml /tmp/Interp_extracted.mli

test: extract
	dune build \
		automatic/test/interpret-bytecode-pbt/harness.exe \
		automatic/test/interpret-bytecode-pbt/manual_test.exe \
		automatic/test/compile-pbt/roundtrip_test.exe \
		automatic/test/interpret-pbt/source_interp_test.exe \
		automatic/test/compile-pbt/compile_test.exe \
		automatic/test/compile-pbt/bytecode_equiv_test.exe
	dune exec automatic/test/interpret-bytecode-pbt/manual_test.exe
	@echo "--- Bytecode PBT (QCheck) ---"
	dune exec automatic/test/interpret-bytecode-pbt/harness.exe
	@echo "--- Parser Round-trip PBT (QCheck) ---"
	dune exec automatic/test/compile-pbt/roundtrip_test.exe
	@echo "--- Source Interpreter PBT (QCheck) ---"
	dune exec automatic/test/interpret-pbt/source_interp_test.exe
	@echo "--- Compiler PBT (QCheck) ---"
	dune exec automatic/test/compile-pbt/compile_test.exe
	@echo "--- Bytecode Equivalence PBT (QCheck) ---"
	dune exec automatic/test/compile-pbt/bytecode_equiv_test.exe

testsuite: extract
	dune build automatic/test/interpret-bytecode-pbt/ocaml_testsuite_runner.exe
	dune exec automatic/test/interpret-bytecode-pbt/ocaml_testsuite_runner.exe -- automatic/test/ocaml-testsuite/basic

testsuite-all: extract
	dune build automatic/test/interpret-bytecode-pbt/ocaml_testsuite_runner.exe
	dune exec automatic/test/interpret-bytecode-pbt/ocaml_testsuite_runner.exe -- \
		automatic/test/ocaml-testsuite/basic \
		automatic/test/ocaml-testsuite/basic-more \
		automatic/test/ocaml-testsuite/basic-modules \
		automatic/test/ocaml-testsuite/basic-multdef \
		automatic/test/ocaml-testsuite/basic-private \
		automatic/test/ocaml-testsuite/basic-float \
		automatic/test/ocaml-testsuite/basic-io \
		automatic/test/ocaml-testsuite/basic-io-2 \
		automatic/test/ocaml-testsuite/basic-manyargs

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f Extract.glob Extract.vo .Extract.aux
