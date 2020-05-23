.PHONY: default build install uninstall test clean

default: build

build:
	ocamlbuild -use-ocamlfind src/main.native

clean:
	rm -rf _build
	git clean -dfXq
