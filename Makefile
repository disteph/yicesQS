.PHONY: default build install debug uninstall test NRA LRA BV oldBV clean

export OCAMLRUNPARAM = b

default: build

debug:
	dune build

build:
	dune build

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
