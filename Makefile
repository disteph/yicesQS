.PHONY: default build install install-deps opam-pins uninstall test run-test run-bv-delegate-test run-all-tests NRA LRA BV oldBV clean

export OCAMLRUNPARAM = b

-include config.mk

DUNE_PROFILE ?=
YICESQS_STATIC ?= 0
DUNE_PROFILE_FLAG = $(if $(DUNE_PROFILE),--profile $(DUNE_PROFILE),)

OPAM ?= opam
OPAM_PIN_FLAGS ?= --yes --no-action
OPAM_INSTALL_FLAGS ?= --yes

OPAM_LIBDIR ?= $(shell $(OPAM) var lib 2>/dev/null)
OPAM_STUBLIBS ?= $(shell $(OPAM) var stublibs 2>/dev/null)
RUNTIME_LIBRARY_PATHS ?= $(OPAM_LIBDIR):$(OPAM_STUBLIBS):/usr/local/lib
BV_DELEGATES ?= cadical cryptominisat
REGRESS_SMT2 ?= $(shell git ls-files 'regress/**/*.smt2' 'regress/*.smt2')
RUN_WITH_LIBPATH = LD_LIBRARY_PATH="$(RUNTIME_LIBRARY_PATHS)$${LD_LIBRARY_PATH:+:$$LD_LIBRARY_PATH}" DYLD_LIBRARY_PATH="$(RUNTIME_LIBRARY_PATHS)$${DYLD_LIBRARY_PATH:+:$$DYLD_LIBRARY_PATH}"
RUN_MAIN_EXE = sh -c 'status=0; for file do echo "$$file"; $(RUN_WITH_LIBPATH) timeout 5 ./main.exe "$$file" || status=1; done; exit $$status' sh
RUN_MAIN_OLD_EXE = sh -c 'status=0; for file do echo "$$file"; $(RUN_WITH_LIBPATH) timeout 5 ./main-old.exe "$$file" || status=1; done; exit $$status' sh
RUN_BV_DELEGATES = sh -c 'status=0; supported="$$( $(RUN_WITH_LIBPATH) ./main.exe -delegates 2>/dev/null || true )"; enabled=""; for delegate in $(BV_DELEGATES); do case " $$supported " in *" $$delegate "*) enabled="$${enabled:+$$enabled }$$delegate" ;; *) echo "Skipping unsupported delegate: $$delegate" ;; esac; done; echo "Supported QF_BV delegates: $${enabled:-<none>}"; for delegate in $$enabled; do echo "QF_BV delegate: $$delegate"; for file do if grep -Eq "\(set-logic (QF_)?BV\)" "$$file"; then echo "$$file [delegate=$$delegate]"; $(RUN_WITH_LIBPATH) timeout 5 ./main.exe -delegate "$$delegate" "$$file" || status=1; fi; done; done; exit $$status' sh

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

build:
	@if [ "$(YICESQS_STATIC)" = "1" ] && [ "$$(uname -s)" = "Darwin" ]; then \
		echo "static builds are not supported on macOS (ld does not support fully static executables)"; \
		exit 1; \
	fi
	dune build $(DUNE_PROFILE_FLAG)
	@if [ "$(YICESQS_STATIC)" = "1" ] && command -v ldd >/dev/null 2>&1 && ldd main.exe 2>/dev/null | grep -q '=>'; then \
		ldd main.exe; \
		echo "configured static build did not produce a fully static executable"; \
		exit 1; \
	fi

clean:
	dune clean

test: build run-all-tests

run-all-tests:
	time sh -c 'status=0; for file do echo "$$file"; $(RUN_WITH_LIBPATH) timeout 5 ./main.exe "$$file" || status=1; done; if [ $$status -ne 0 ]; then exit $$status; fi; supported="$$( $(RUN_WITH_LIBPATH) ./main.exe -delegates 2>/dev/null || true )"; enabled=""; for delegate in $(BV_DELEGATES); do case " $$supported " in *" $$delegate "*) enabled="$${enabled:+$$enabled }$$delegate" ;; *) echo "Skipping unsupported delegate: $$delegate" ;; esac; done; echo "Supported QF_BV delegates: $${enabled:-<none>}"; for delegate in $$enabled; do echo "QF_BV delegate: $$delegate"; for file do if grep -Eq "\(set-logic (QF_)?BV\)" "$$file"; then echo "$$file [delegate=$$delegate]"; $(RUN_WITH_LIBPATH) timeout 5 ./main.exe -delegate "$$delegate" "$$file" || status=1; fi; done; done; exit $$status' sh $(REGRESS_SMT2)

run-test: build
	time $(RUN_MAIN_EXE) $(REGRESS_SMT2)

run-bv-delegate-test: build
	time $(RUN_BV_DELEGATES) $(REGRESS_SMT2)

NRA:
	time find ../SMTLib/NRA -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

LRA:
	time find ../SMTLib/LRA -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

BV:
	time find ../SMTLib/BV/2018-Preiner-cav18 -follow -name "*.smt2" -exec $(RUN_MAIN_EXE) {} +

oldBV:
	time find ../SMTLib/BV/2018-Preiner-cav18 -follow -name "*.smt2" -exec $(RUN_MAIN_OLD_EXE) {} +
