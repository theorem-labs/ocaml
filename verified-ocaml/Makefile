SHELL := /bin/bash

.PHONY: all build extract extract-full test test-manual test-full \
        testsuite testsuite-all clean

# ---- Build ----

all: build extract test

build:
	@rm -f checker/Extract.glob checker/Extract.vo checker/.Extract.aux
	dune build manual/ semi-auto/ automatic/ checker/

# ---- Extraction ----

COQC_FLAGS = \
  -R _build/default/manual/Utils OCamlInterp.Manual.Utils \
  -R _build/default/manual/Bytecode OCamlInterp.Manual.Bytecode \
  -R _build/default/manual/LexParse OCamlInterp.Manual.LexParse \
  -R _build/default/manual/Compile OCamlInterp.Manual.Compile \
  -R _build/default/semi-auto/LexParse OCamlInterp.SemiAutomatic.LexParse \
  -R _build/default/semi-auto/Interpret OCamlInterp.SemiAutomatic.Interpret \
  -R _build/default/automatic/Compile OCamlInterp.Automatic.Compile \
  -R _build/default/automatic/Bytecode OCamlInterp.Automatic.Bytecode \
  -R _build/default/automatic/LexParse OCamlInterp.Automatic.LexParse \
  -R _build/default/checker/Bytecode OCamlInterp.Checker.Bytecode \
  -R _build/default/checker/Compile OCamlInterp.Checker.Compile \
  -R _build/default/checker/LexParse OCamlInterp.Checker.LexParse

# Full extraction (compiler, decoder, source interp, pretty-printer).
# We always re-extract to avoid stale binaries.
extract: build
	coqc $(COQC_FLAGS) checker/Extract.v -output-directory /tmp
	@if ! diff -q /tmp/Interp_extracted.ml checker/common/interp_extracted.ml >/dev/null 2>&1; then \
	  echo "Extraction changed — updating interp_extracted.ml"; \
	  cp /tmp/Interp_extracted.ml checker/common/interp_extracted.ml; \
	fi
	rm -f /tmp/Interp_extracted.ml /tmp/Interp_extracted.mli
	@# Wrap eager module instantiation so it doesn't run at load time.
	@# Pipeline(ConcreteDecoder) reads Sys.argv and would crash all test exes.
	sed -i 's/^module App = Pipeline(ConcreteDecoder)/module App() = Pipeline(ConcreteDecoder)/' \
	  checker/common/interp_extracted.ml
	sed -i 's/^let main0 =$$/let main0 () =/' \
	  checker/common/interp_extracted.ml
	sed -i 's/^  App\.main$$/  let module M = App() in M.main/' \
	  checker/common/interp_extracted.ml

# ---- Tests ----

# Bytecode interpreter PBT
test-manual: extract
	dune build \
		checker/Bytecode/tests/harness.exe \
		checker/Bytecode/tests/manual_test.exe
	@echo "--- Manual bytecode tests ---"
	dune exec checker/Bytecode/tests/manual_test.exe
	@echo "--- Bytecode PBT: interpret-bytecode vs ocamlrun (QCheck) ---"
	dune exec checker/Bytecode/tests/harness.exe

test: test-manual

# Full tests: includes compiler PBT
test-full: extract
	dune build \
		checker/Bytecode/tests/harness.exe \
		checker/Bytecode/tests/manual_test.exe \
		checker/Compile/compile-pbt/harness.exe
	@echo "--- Manual bytecode tests ---"
	dune exec checker/Bytecode/tests/manual_test.exe
	@echo "--- Bytecode PBT: interpret-bytecode vs ocamlrun (QCheck) ---"
	dune exec checker/Bytecode/tests/harness.exe
	@echo "--- Compile vs ocamlc PBT (QCheck) ---"
	dune exec checker/Compile/compile-pbt/harness.exe

# ---- Testsuite ----

TESTSUITE_DIR = checker/Bytecode/tests/ocaml-testsuite

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

RUNNER = _build/default/checker/Bytecode/tests/ocaml_testsuite_runner.exe

testsuite: extract
	dune build checker/Bytecode/tests/ocaml_testsuite_runner.exe
	ulimit -s unlimited && $(RUNNER) --skip-conf testsuite.conf $(TESTSUITE_BASIC)

testsuite-all: extract
	dune build checker/Bytecode/tests/ocaml_testsuite_runner.exe
	ulimit -s unlimited && $(RUNNER) --skip-conf testsuite.conf $(TESTSUITE_BASIC) $(TESTSUITE_PHASE1)

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f checker/Extract.glob checker/Extract.vo checker/.Extract.aux
