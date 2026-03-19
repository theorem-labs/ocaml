.PHONY: all build extract test clean

all: build extract test

build:
	dune build

extract: build
	coqc -R _build/default/theories OCamlInterp theories/Extract.v -output-directory /tmp
	cp /tmp/Interp_extracted.ml test/harness/interp_extracted.ml
	rm -f /tmp/Interp_extracted.ml /tmp/Interp_extracted.mli

test: extract
	dune build test/harness/harness.exe test/harness/manual_test.exe
	dune exec test/harness/manual_test.exe
	@echo "---"
	dune exec test/harness/harness.exe -- 100 42

clean:
	dune clean
	rm -f Interp_extracted.ml Interp_extracted.mli
	rm -f theories/Extract.glob theories/Extract.vo theories/.Extract.aux
