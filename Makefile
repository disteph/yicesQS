.PHONY: default build install debug uninstall test clean

export OCAMLRUNPARAM = b

default: build

debug:
	dune build

build:
	dune build

clean:
	dune clean

test: build
	time find regress -follow -name "*.smt2" -print0 | xargs -I{} -0 sh -c "echo {} && ./main.exe {}"
