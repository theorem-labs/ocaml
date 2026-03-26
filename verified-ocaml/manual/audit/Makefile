.PHONY: all audit internal-audit clean snippets fetch-pdf

# Paths -- adjust if the Rocq source tree is elsewhere.
INTERP_V ?= $(wildcard ../theories/Bytecode/Interpret.v)
INTERP_C ?= interp.c
PDF_SPEC ?= caml-instructions.pdf
PDF_URL  ?= https://cadmium.x9c.fr/distrib/caml-instructions.pdf

all: audit

# Download the Clerc bytecode instruction PDF if not already present.
fetch-pdf: $(PDF_SPEC)
$(PDF_SPEC):
	curl -fSL -o $@ "$(PDF_URL)"

# Re-extract code snippets from Interp.v, interp.c, and caml-instructions.pdf
snippets: extract_snippets.py $(INTERP_C) $(PDF_SPEC)
	python3 extract_snippets.py $(INTERP_V) $(INTERP_C) $(PDF_SPEC)

# External audit: neutral document for external auditors.
# PDF spec images + C snippet + Rocq snippet. No internal commentary.
audit: audit.tex snippets
	pdflatex -interaction=nonstopmode audit.tex || true
	pdflatex -interaction=nonstopmode audit.tex || true

# Internal audit: same content plus analysis, status, risk, action items.
internal-audit: internal_audit.tex audit.tex snippets
	pdflatex -interaction=nonstopmode internal_audit.tex || true
	pdflatex -interaction=nonstopmode internal_audit.tex || true

clean:
	rm -rf snippets/ *.aux *.log *.out *.toc *.lof *.lot audit.pdf internal_audit.pdf
