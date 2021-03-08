.PHONY: default build install debug uninstall test clean

export OCAMLRUNPARAM = b

default: build

debug:
	dune build

build:
	dune build

clean:
	dune clean
