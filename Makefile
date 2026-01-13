.PHONY: default build static install debug uninstall test NRA LRA BV oldBV clean

export OCAMLRUNPARAM = b

default: build

debug:
	dune build

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
