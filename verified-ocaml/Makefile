.PHONY: all build extract test clean

all: build extract test

build:
	@rm -f Extract.glob Extract.vo .Extract.aux
	dune build

COQC_FLAGS = \
  -R _build/default/manual/Utils OCamlInterp.Manual.Utils \
  -R _build/default/manual/Bytecode OCamlInterp.Manual.Bytecode \
  -R _build/default/manual/Checker OCamlInterp.Manual.Checker \
  -R _build/default/semi-auto/LexParse OCamlInterp.SemiAutomatic.LexParse \
  -R _build/default/semi-auto/Interpret OCamlInterp.SemiAutomatic.Interpret \
  -R _build/default/automatic/Compile OCamlInterp.Automatic.Compile \
  -R _build/default/automatic/theories/Bytecode OCamlInterp.Automatic.Bytecode \
  -R _build/default/automatic/LexParse OCamlInterp.Automatic.LexParse \
  -R _build/default/manual/theories/LexParse OCamlInterp.Manual.LexParse \
  -R _build/default/manual/theories/Compile OCamlInterp.Manual.Compile

extract: build
	coqc $(COQC_FLAGS) Extract.v -output-directory /tmp
	cp /tmp/Interp_extracted.ml manual/test/common/interp_extracted.ml
	rm -f /tmp/Interp_extracted.ml /tmp/Interp_extracted.mli

test: extract
	dune build \
		manual/test/bytecode-pbt/harness.exe \
		manual/test/bytecode-pbt/runner.exe \
		manual/test/compile-pbt/roundtrip_test.exe \
		manual/test/interpret-pbt/source_interp_test.exe \
		manual/test/compile-pbt/compile_test.exe \
		manual/test/compile-pbt/bytecode_equiv_test.exe \
		manual/test/Compile/harness.exe
	@echo "--- Bytecode PBT: Main.v pipeline vs ocamlrun (QCheck) ---"
	dune exec manual/test/bytecode-pbt/harness.exe
	@echo "--- Parser Round-trip PBT (QCheck) ---"
	dune exec manual/test/compile-pbt/roundtrip_test.exe
	@echo "--- Source Interpreter PBT (QCheck) ---"
	dune exec manual/test/interpret-pbt/source_interp_test.exe
	@echo "--- Compiler PBT (QCheck) ---"
	dune exec manual/test/compile-pbt/compile_test.exe
	@echo "--- Bytecode Equivalence PBT (QCheck) ---"
	dune exec manual/test/compile-pbt/bytecode_equiv_test.exe
	@echo "--- Compile vs ocamlc PBT (QCheck) ---"
	dune exec manual/test/Compile/harness.exe

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f Extract.glob Extract.vo .Extract.aux
