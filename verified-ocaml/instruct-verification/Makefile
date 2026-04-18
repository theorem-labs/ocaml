SUBMODULE := ../../system-ocaml
INTERP_C = $(SUBMODULE)/runtime/interp.c

.PHONY: all clean

all: gen/instruct_handlers.c

$(INTERP_C):
	if [ ! -d $(SUBMODULE) ]; then git submodule update --init $(SUBMODULE); fi

gen/instruct_handlers.c: $(INTERP_C) extract_handlers.sh
	mkdir -p gen
	./extract_handlers.sh $(INTERP_C) > gen/instruct_handlers.c

# Generate Clight AST (requires clightgen from CompCert)
gen/instruct_handlers.v: gen/instruct_handlers.c
	clightgen -normalize gen/instruct_handlers.c -o gen/instruct_handlers.v

# Copy into theories/ so dune can build it
theories/instruct_handlers.v: gen/instruct_handlers.v
	cp gen/instruct_handlers.v theories/instruct_handlers.v

clean:
	rm -rf gen/
