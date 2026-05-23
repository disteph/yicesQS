.PHONY: default build static install install-deps opam-pins debug uninstall test NRA LRA BV oldBV clean

export OCAMLRUNPARAM = b

OPAM ?= opam
OPAM_PIN_FLAGS ?= --yes --no-action
OPAM_INSTALL_FLAGS ?= --yes

TRACING_PIN ?= https://github.com/disteph/tracing/archive/refs/heads/main.zip
TIMER_PIN ?= https://github.com/disteph/timer/archive/refs/heads/main.zip
LIBPOLY_BINDINGS_PIN ?= https://github.com/SRI-CSL/libpoly_ocaml_bindings/archive/refs/heads/main.zip
YICES2_BINDINGS_PIN ?= https://github.com/SRI-CSL/yices2_ocaml_bindings/archive/49f9c9eabddfe27b5f965e6e0913da8c5450578c.zip

default: build

install: install-deps

install-deps: opam-pins
	$(OPAM) install . --deps-only $(OPAM_INSTALL_FLAGS)

opam-pins:
	$(OPAM) pin add tracing $(TRACING_PIN) $(OPAM_PIN_FLAGS)
	$(OPAM) pin add timer $(TIMER_PIN) $(OPAM_PIN_FLAGS)
	$(OPAM) pin add libpoly_bindings $(LIBPOLY_BINDINGS_PIN) $(OPAM_PIN_FLAGS)
	$(OPAM) pin add yices2_bindings $(YICES2_BINDINGS_PIN) $(OPAM_PIN_FLAGS)

debug:
	dune build --profile debug

build:
	dune build

static:
	@if [ "$$(uname -s)" = "Darwin" ]; then \
		echo "make static is not supported on macOS (ld lacks -Bstatic/-Bdynamic)"; \
		exit 1; \
	fi
	dune build --profile static

clean:
	dune clean

test: build
	time find regress -follow -name "*.smt2" -print0 | xargs -I{} -0 sh -c "echo {} && timeout 5 ./main.exe {}"

NRA:
	time find ../SMTLib/NRA -follow -name "*.smt2" -print0 | xargs -I{} -0 sh -c "echo {} && timeout 5 ./main.exe {}"

LRA:
	time find ../SMTLib/LRA -follow -name "*.smt2" -print0 | xargs -I{} -0 sh -c "echo {} && timeout 5 ./main.exe {}"

BV:
	time find ../SMTLib/BV/2018-Preiner-cav18 -follow -name "*.smt2" -print0 | xargs -I{} -0 sh -c "echo {} && timeout 5 ./main.exe {}"

oldBV:
	time find ../SMTLib/BV/2018-Preiner-cav18 -follow -name "*.smt2" -print0 | xargs -I{} -0 sh -c "echo {} && timeout 5 ./main-old.exe {}"
