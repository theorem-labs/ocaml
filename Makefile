.PHONY: all build extract test clean

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
	@echo "--- Bytecode PBT ---"
	dune exec test/harness/harness.exe -- 200 42
	@echo "--- Parser Round-trip PBT ---"
	dune exec test/harness/roundtrip_test.exe -- 500 42 4
	@echo "--- Source Interpreter PBT ---"
	dune exec test/harness/source_interp_test.exe -- 100 42
	@echo "--- Compiler PBT ---"
	dune exec test/harness/compile_test.exe -- 200 42
	@echo "--- Bytecode Equivalence PBT (Part 5) ---"
	dune exec test/harness/bytecode_equiv_test.exe -- 100 42

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f theories/Extract.glob theories/Extract.vo theories/.Extract.aux
