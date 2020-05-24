.PHONY: default build install debug uninstall test clean

export OCAMLRUNPARAM = b

default: build

debug:
	ocamlbuild -use-ocamlfind src/main.native -plugin-option -debug-mode

build:
	ocamlbuild -use-ocamlfind src/main.native

clean:
	ocamlbuild -clean
	git clean -dfXq
