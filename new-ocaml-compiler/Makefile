.PHONY: all build extract test testsuite clean

all: build extract test

build:
	@rm -f theories/Extract.glob theories/Extract.vo theories/.Extract.aux
	dune build

extract: build
	coqc -R _build/default/theories OCamlInterp theories/Extract.v -output-directory /tmp
	cp /tmp/Interp_extracted.ml test/harness/interp_extracted.ml
	rm -f /tmp/Interp_extracted.ml /tmp/Interp_extracted.mli

test: extract
	dune build test/harness/harness.exe test/harness/manual_test.exe test/harness/roundtrip_test.exe test/harness/source_interp_test.exe test/harness/compile_test.exe test/harness/bytecode_equiv_test.exe
	dune exec test/harness/manual_test.exe
	@echo "--- Bytecode PBT (QCheck) ---"
	dune exec test/harness/harness.exe
	@echo "--- Parser Round-trip PBT (QCheck) ---"
	dune exec test/harness/roundtrip_test.exe
	@echo "--- Source Interpreter PBT (QCheck) ---"
	dune exec test/harness/source_interp_test.exe
	@echo "--- Compiler PBT (QCheck) ---"
	dune exec test/harness/compile_test.exe
	@echo "--- Bytecode Equivalence PBT (QCheck) ---"
	dune exec test/harness/bytecode_equiv_test.exe

testsuite: extract
	dune build test/harness/ocaml_testsuite_runner.exe
	dune exec test/harness/ocaml_testsuite_runner.exe -- test/ocaml-testsuite/basic

testsuite-all: extract
	dune build test/harness/ocaml_testsuite_runner.exe
	dune exec test/harness/ocaml_testsuite_runner.exe -- \
		test/ocaml-testsuite/basic \
		test/ocaml-testsuite/basic-more \
		test/ocaml-testsuite/basic-modules \
		test/ocaml-testsuite/basic-multdef \
		test/ocaml-testsuite/basic-private \
		test/ocaml-testsuite/basic-float \
		test/ocaml-testsuite/basic-io \
		test/ocaml-testsuite/basic-io-2 \
		test/ocaml-testsuite/basic-manyargs

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f theories/Extract.glob theories/Extract.vo theories/.Extract.aux
