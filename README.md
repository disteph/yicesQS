[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

# yicesQS
Quantified Satisfiability in Yices

This repository contains a solver for quantified satisfiability, calling Yices2 for ground satisfiability queries. It currently only supports the following two logics of SMTLib:

- NRA (non-linear real arithmetic)
- BV (bitvector)

The solver entered the SMT'2021 competition in those logics (single query track), and won NRA:

- [https://smt-comp.github.io/2021/results/nra-single-query](https://smt-comp.github.io/2021/results/nra-single-query)
- [https://smt-comp.github.io/2021/results/bitvec-single-query](https://smt-comp.github.io/2021/results/bitvec-single-query)

A description of the solver can be found on the SMT-comp website:

[https://smt-comp.github.io/2021/system-descriptions/Yices2-QS.pdf](https://smt-comp.github.io/2021/system-descriptions/Yices2-QS.pdf)

## Building and Running

#### Installing dependencies with opam (needs 2.0 or higher, needs gmp)

Besides Yices and its dependencies, YicesQS needs some OCaml dependencies and the Yices2 bindings. Assuming that the yices library (and the libraries it depends on) are present in the conventional directories (like `/usr/local/lib`), the OCaml libraries can all be installed by the following opam commands. 
If for some reason this is not the case, follow the instructions for "Installing dependencies without opam".

First, run:

```
opam pin yices2_bindings https://github.com/SRI-CSL/yices2_ocaml_bindings/archive/refs/heads/yices-2.6.4.zip
```
Note that this URL is the correct version of the Yices2 bindings that YicesQS requires. Opam may have a `yices2_bindings` package, but it's probably outdated.

Then, in the directory of this `README.md`, install (in findlib) the remaining OCaml dependencies with the following command:

```
opam install . --deps-only
```

#### Installing dependencies without opam (or with the Yices library being located in an unconventional directory)

You should start by installing the Yices2 bindings, in the yices-2.6.3 branch,
following the instructions given there:

[https://github.com/SRI-CSL/yices2\_ocaml\_bindings/tree/yices-2.6.3](https://github.com/SRI-CSL/yices2_ocaml_bindings/tree/yices-2.6.3)

Then inspect `yicesQS.opam` to see if there are further OCaml dependencies listed there; if there are not installed (in findlib), install them with opam from source.

#### Building

To build, run the following command:

```
make
```
in the directory of this `README.md`.

This should create an executable `main.exe` in the directory; it is statically linked with the OCaml dependencies (you can execute it on a similar machine that doesn't have opam or findlib), but it is dynamically linked with Yices and its dependencies (libpoly, cudd, gmp, etc).

You can also use `make clean`.

If for some reason the yices library (or the libraries it depends on) are not in the conventional directories, then you can specify the correct directory paths by setting the environment variables `LDFLAGS` (for the yices library) and `LD_LIBRARY_PATH` (for its dependencies, like libpoly or cudd), e.g.:

```
export LD_LIBRARY_PATH=[UNCONVENTIONAL_PATHS]:/usr/local/lib
export LDFLAGS="-L[UNCONVENTIONAL_PATH]"
```


#### Quick Testing

Simply execute `main.exe` on any of the files in the `regress` directory.
For each file, you should get an answer `sat` or `unsat` on standard out.
