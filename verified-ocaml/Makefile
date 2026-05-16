SHELL := /bin/bash

.PHONY: all build build-instruct extract extract-full test test-manual test-full \
        testsuite testsuite-all clean

# ---- Build ----

all: build extract test

build:
	@rm -f checker/Extract.glob checker/Extract.vo checker/.Extract.aux
	dune build manual/ semi-auto/ automatic/ checker/

# Build instruct-verification theories (InstructSpec.v + Clight AST).
# Delegates to instruct-verification/Makefile for C code generation, then
# builds the Rocq theories via dune.
build-instruct:
	$(MAKE) -C instruct-verification gen/instruct_handlers.c
	dune build instruct-verification/theories/

SUBPROJECTS = manual semi-auto automatic checker

Makefile.coq $(addprefix Makefile.coq., $(SUBPROJECTS)): Makefile.coq% : _CoqProject%
	$(COQBIN)coq_makefile -f $< -o $@

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
	@# Rewrite cyclic [type int = int] inside extracted Compcert Int module
	@# to a [nonrec] alias so OCaml accepts it.
	sed -i 's/^  type int = int$$/  type nonrec int = int/' \
	  checker/common/interp_extracted.ml
	@# Coq's extraction now produces [step0], [run0], [run_pure0] aliases
	@# when these names appear inside a functor. test_common.ml expects the
	@# unsuffixed names, so re-export them at top level.
	@if ! grep -q '^let step = step0' checker/common/interp_extracted.ml; then \
	  printf '\n(* Backwards-compatible top-level aliases used by test_common.ml. *)\n' \
	    >> checker/common/interp_extracted.ml; \
	  printf 'let step = step0\nlet run = run0\nlet run_pure = run_pure0\n' \
	    >> checker/common/interp_extracted.ml; \
	fi

# ---- Tests ----

# Bytecode interpreter PBT
test: extract
	dune build \
		checker/Bytecode/test/pbt.exe \
		checker/Bytecode/test/pipeline_runner.exe
	@echo "--- Bytecode PBT: interpret-bytecode vs ocamlrun (QCheck) ---"
	dune exec checker/Bytecode/test/pbt.exe

# Full tests: includes compiler PBT
test-full: extract
	dune build \
		checker/Bytecode/test/pbt.exe \
		checker/Bytecode/test/pipeline_runner.exe \
		checker/Compile/test/pbt.exe
	@echo "--- Bytecode PBT: interpret-bytecode vs ocamlrun (QCheck) ---"
	dune exec checker/Bytecode/test/pbt.exe
	@echo "--- Compile vs ocamlc PBT (QCheck) ---"
	dune exec checker/Compile/test/pbt.exe

# ---- Testsuite ----

TESTSUITE_DIR = checker/Bytecode/test/ocaml-testsuite

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

RUNNER = _build/default/checker/Bytecode/test/ocaml_testsuite_runner.exe

testsuite: extract
	dune build checker/Bytecode/test/ocaml_testsuite_runner.exe
	ulimit -s unlimited && $(RUNNER) --skip-conf testsuite.conf $(TESTSUITE_BASIC)

testsuite-all: extract
	dune build checker/Bytecode/test/ocaml_testsuite_runner.exe
	ulimit -s unlimited && $(RUNNER) --skip-conf testsuite.conf $(TESTSUITE_BASIC) $(TESTSUITE_PHASE1)

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f checker/Extract.glob checker/Extract.vo checker/.Extract.aux
	$(MAKE) -C instruct-verification clean
