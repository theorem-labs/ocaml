.PHONY: all build extract test testsuite testsuite-all clean

all: build extract test

build:
	@rm -f Extract.glob Extract.vo .Extract.aux
	dune build

COQC_FLAGS = \
  -R _build/default/manual/theories/Utils OCamlInterp.Manual.Utils \
  -R _build/default/manual/theories/Bytecode OCamlInterp.Manual.Bytecode \
  -R _build/default/semi-auto/LexParse OCamlInterp.SemiAutomatic.LexParse \
  -R _build/default/semi-auto/Interpret OCamlInterp.SemiAutomatic.Interpret \
  -R _build/default/automatic/Compile OCamlInterp.Automatic.Compile \
  -R _build/default/automatic/Bytecode OCamlInterp.Automatic.Bytecode \
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
		manual/test/compile-pbt/harness.exe
	@echo "--- Bytecode PBT: Main.v pipeline vs ocamlrun (QCheck) ---"
	dune exec manual/test/bytecode-pbt/harness.exe
	@echo "--- Compile vs ocamlc PBT (QCheck) ---"
	dune exec manual/test/compile-pbt/harness.exe

TESTSUITE_DIR = manual/test/ocaml-testsuite

TESTSUITE_BASIC = \
	$(TESTSUITE_DIR)/basic \
	$(TESTSUITE_DIR)/basic-more \
	$(TESTSUITE_DIR)/basic-modules \
	$(TESTSUITE_DIR)/basic-private \
	$(TESTSUITE_DIR)/basic-float \
	$(TESTSUITE_DIR)/basic-io \
	$(TESTSUITE_DIR)/basic-io-2 \
	$(TESTSUITE_DIR)/basic-manyargs

TESTSUITE_PHASE1 = \
	$(TESTSUITE_DIR)/misc \
	$(TESTSUITE_DIR)/letrec-compilation \
	$(TESTSUITE_DIR)/match-exception \
	$(TESTSUITE_DIR)/array-functions \
	$(TESTSUITE_DIR)/local-functions \
	$(TESTSUITE_DIR)/lib-list \
	$(TESTSUITE_DIR)/lib-string \
	$(TESTSUITE_DIR)/lib-hashtbl \
	$(TESTSUITE_DIR)/lib-int \
	$(TESTSUITE_DIR)/lib-int64 \
	$(TESTSUITE_DIR)/lib-float \
	$(TESTSUITE_DIR)/lib-option \
	$(TESTSUITE_DIR)/lib-result \
	$(TESTSUITE_DIR)/lib-set \
	$(TESTSUITE_DIR)/lib-queue \
	$(TESTSUITE_DIR)/lib-stack \
	$(TESTSUITE_DIR)/lib-seq \
	$(TESTSUITE_DIR)/lib-buffer \
	$(TESTSUITE_DIR)/lib-fun \
	$(TESTSUITE_DIR)/lib-bool \
	$(TESTSUITE_DIR)/lib-random \
	$(TESTSUITE_DIR)/lib-atomic \
	$(TESTSUITE_DIR)/lib-uchar \
	$(TESTSUITE_DIR)/lib-filename \
	$(TESTSUITE_DIR)/lib-obj \
	$(TESTSUITE_DIR)/misc-kb \
	$(TESTSUITE_DIR)/misc-unsafe \
	$(TESTSUITE_DIR)/lazy \
	$(TESTSUITE_DIR)/functors \
	$(TESTSUITE_DIR)/exotic-syntax \
	$(TESTSUITE_DIR)/let-syntax \
	$(TESTSUITE_DIR)/extension-constructor \
	$(TESTSUITE_DIR)/generalized-open \
	$(TESTSUITE_DIR)/letrec-check \
	$(TESTSUITE_DIR)/match-exception-warnings \
	$(TESTSUITE_DIR)/raise-counts \
	$(TESTSUITE_DIR)/prim-revapply \
	$(TESTSUITE_DIR)/prim-bswap \
	$(TESTSUITE_DIR)/float-unboxing \
	$(TESTSUITE_DIR)/fma \
	$(TESTSUITE_DIR)/int64-unboxing \
	$(TESTSUITE_DIR)/basic-multdef

RUNNER = _build/default/manual/test/bytecode-pbt/ocaml_testsuite_runner.exe

testsuite: extract
	dune build manual/test/bytecode-pbt/ocaml_testsuite_runner.exe
	ulimit -s unlimited && $(RUNNER) $(TESTSUITE_BASIC)

testsuite-all: extract
	dune build manual/test/bytecode-pbt/ocaml_testsuite_runner.exe
	ulimit -s unlimited && $(RUNNER) $(TESTSUITE_BASIC) $(TESTSUITE_PHASE1)

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f Extract.glob Extract.vo .Extract.aux
