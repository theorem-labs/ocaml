.PHONY: all clean snippets

# Paths -- adjust if the Rocq source tree is elsewhere.
# The script auto-discovers Interp.v if the default path doesn't exist.
INTERP_V ?= $(wildcard ../../theories/Trusted/Bytecode/Interp.v)
INTERP_C ?= interp.c

all: audit.pdf

# If INTERP_V is empty (file not found), let the script auto-discover
snippets: extract_snippets.py $(INTERP_C)
	python3 extract_snippets.py $(INTERP_V) $(INTERP_C)

audit.pdf: audit.tex snippets
	pdflatex -interaction=nonstopmode audit.tex || true
	pdflatex -interaction=nonstopmode audit.tex || true

clean:
	rm -rf snippets/ *.aux *.log *.out *.toc *.pdf *.lof *.lot
