[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

# yicesQS

YicesQS is an extension of Yices2 for quantified satisfiability. It currently supports the following logics of SMTLib:

- NRA (non-linear real arithmetic). Winner in
[2021](https://smt-comp.github.io/2021/results/nra-single-query)
[2022](https://smt-comp.github.io/2022/results/nra-single-query)
[2023](https://smt-comp.github.io/2023/results/nra-single-query).
- NIA (non-linear integer arithmetic)
[2022](https://smt-comp.github.io/2022/results/nia-single-query)
[2023](https://smt-comp.github.io/2023/results/nia-single-query)
- LRA (linear real arithmetic). Winner in
[2022](https://smt-comp.github.io/2022/results/lra-single-query)
[2023](https://smt-comp.github.io/2023/results/lra-single-query).
- LIA (linear integer arithmetic)
[2022](https://smt-comp.github.io/2022/results/lia-single-query)
[2023](https://smt-comp.github.io/2023/results/lia-single-query)
- BV (bitvector)
[2021](https://smt-comp.github.io/2021/results/bitvec-single-query)
[2022](https://smt-comp.github.io/2022/results/bitvec-single-query)
[2023](https://smt-comp.github.io/2023/results/bitvec-single-query)

A description of the solver can be found on the [2021](https://smt-comp.github.io/2021/system-descriptions/Yices2-QS.pdf) and [2022](https://smt-comp.github.io/2022/system-descriptions/YicesQS.pdf) SMT-comp websites.




## Building and Running

#### Yices2 and dependencies

Install [Yices version 2.6.4](https://yices.csl.sri.com/) and its dependencies [libpoly](https://github.com/SRI-CSL/libpoly) and [cudd](https://github.com/ivmai/cudd).

#### Installing OCaml dependencies with opam (needs 2.0 or higher)

Besides Yices and its dependencies, YicesQS needs some OCaml dependencies and the Yices2 bindings. Assuming that the yices library (and the libraries it depends on) are present in the conventional directories (like `/usr/local/lib`), the OCaml libraries can all be installed by the following opam commands. 
If for some reason this is not the case, follow the instructions for "Installing dependencies without opam".

First, run:

```
opam pin tracing https://github.com/disteph/tracing/archive/refs/heads/main.zip
opam pin libpoly_bindings https://github.com/SRI-CSL/libpoly_ocaml_bindings/archive/refs/heads/main.zip
opam pin yices2 https://github.com/SRI-CSL/yices2_ocaml_bindings/archive/49f9c9eabddfe27b5f965e6e0913da8c5450578c.zip
```
Note that this URL is the correct version of the Yices2 bindings that YicesQS requires. Opam may have a `yices2_bindings` package, but it's probably outdated.

Then, in the directory of this `README.md`, install (in findlib) the remaining OCaml dependencies with the following command:

```
opam install . --deps-only
```

#### Installing OCaml dependencies without opam (or with the Yices library being located in an unconventional directory)

You should start by installing the 
[Yices2 bindings (in the dev branch)
following these instructions](https://github.com/SRI-CSL/yices2_ocaml_bindings/tree/49f9c9eabddfe27b5f965e6e0913da8c5450578c).

Then inspect `yicesQS.opam` to see if there are further OCaml dependencies listed there; if there are not installed (in findlib), install them with opam or from source.

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
