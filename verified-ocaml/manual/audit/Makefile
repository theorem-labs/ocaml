.PHONY: all audit internal-audit clean snippets

# Paths -- adjust if the Rocq source tree is elsewhere.
INTERP_V ?= $(wildcard ../theories/Bytecode/Interpret.v)
INTERP_C ?= interp.c

all: audit

# Re-extract code snippets from Interp.v and interp.c
snippets: extract_snippets.py $(INTERP_C)
	python3 extract_snippets.py $(INTERP_V) $(INTERP_C)

# External audit: neutral document for external auditors.
# PDF spec + C snippet + Rocq snippet. No internal commentary.
audit: audit.tex snippets
	pdflatex -interaction=nonstopmode audit.tex || true
	pdflatex -interaction=nonstopmode audit.tex || true

# Internal audit: same content plus analysis, status, risk, action items.
internal-audit: internal_audit.tex audit.tex snippets
	pdflatex -interaction=nonstopmode internal_audit.tex || true
	pdflatex -interaction=nonstopmode internal_audit.tex || true

clean:
	rm -rf snippets/ *.aux *.log *.out *.toc *.pdf *.lof *.lot
