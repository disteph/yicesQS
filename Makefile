.PHONY: default build static install install-deps opam-pins debug uninstall test NRA LRA BV oldBV clean

export OCAMLRUNPARAM = b

OPAM ?= opam
OPAM_PIN_FLAGS ?= --yes --no-action
OPAM_INSTALL_FLAGS ?= --yes

OPAM_LIBDIR ?= $(shell $(OPAM) var lib 2>/dev/null)
OPAM_STUBLIBS ?= $(shell $(OPAM) var stublibs 2>/dev/null)
RUNTIME_LIBRARY_PATHS ?= $(OPAM_LIBDIR):$(OPAM_STUBLIBS):/usr/local/lib
RUN_WITH_LIBPATH = LD_LIBRARY_PATH="$(RUNTIME_LIBRARY_PATHS)$${LD_LIBRARY_PATH:+:$$LD_LIBRARY_PATH}" DYLD_LIBRARY_PATH="$(RUNTIME_LIBRARY_PATHS)$${DYLD_LIBRARY_PATH:+:$$DYLD_LIBRARY_PATH}"
RUN_MAIN_EXE = sh -c 'status=0; for file do echo "$$file"; $(RUN_WITH_LIBPATH) timeout 5 ./main.exe "$$file" || status=1; done; exit $$status' sh
RUN_MAIN_OLD_EXE = sh -c 'status=0; for file do echo "$$file"; $(RUN_WITH_LIBPATH) timeout 5 ./main-old.exe "$$file" || status=1; done; exit $$status' sh

TRACING_PACKAGE ?= tracing.v0.17.0
TRACING_PIN ?= https://github.com/disteph/tracing/archive/refs/heads/main.zip
TIMER_PACKAGE ?= timer.~dev
TIMER_PIN ?= https://github.com/disteph/timer/archive/refs/heads/main.zip

default: install-deps build

install: install-deps

install-deps: opam-pins
	$(OPAM) install . --deps-only $(OPAM_INSTALL_FLAGS)

opam-pins:
	$(OPAM) pin add $(TRACING_PACKAGE) $(TRACING_PIN) $(OPAM_PIN_FLAGS)
	$(OPAM) pin add $(TIMER_PACKAGE) $(TIMER_PIN) $(OPAM_PIN_FLAGS)

debug:
	dune build --profile debug

build:
	dune build

static:
	@if [ "$$(uname -s)" = "Darwin" ]; then \
		echo "make static is not supported on macOS (ld does not support fully static executables)"; \
		exit 1; \
	fi
	dune build --profile static
	@if command -v ldd >/dev/null 2>&1 && ldd main.exe 2>/dev/null | grep -q '=>'; then \
		ldd main.exe; \
		echo "make static did not produce a fully static executable"; \
		exit 1; \
	fi

clean:
	dune clean

test: build
	time find regress -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

NRA:
	time find ../SMTLib/NRA -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

LRA:
	time find ../SMTLib/LRA -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

BV:
	time find ../SMTLib/BV/2018-Preiner-cav18 -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

oldBV:
	time find ../SMTLib/BV/2018-Preiner-cav18 -follow -name "*.smt2" -exec $(RUN_MAIN_OLD_EXE) {} +
