[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

# yicesQS

`yicesQS` is an extension of Yices 2 for quantified satisfiability. It accepts SMT-LIB inputs with quantifiers, builds quantifier-free obligations internally, and checks these obligations with Yices.

Supported SMT-LIB families include:

- NRA: non-linear real arithmetic
- NIA: non-linear integer arithmetic
- LRA: linear real arithmetic
- LIA: linear integer arithmetic
- BV: bit-vectors

System descriptions are available from SMT-COMP:

- [2021 Yices2-QS](https://smt-comp.github.io/2021/system-descriptions/Yices2-QS.pdf)
- [2022 YicesQS](https://smt-comp.github.io/2022/system-descriptions/YicesQS.pdf)

## Dependencies

You need:

- OCaml and Dune
- opam, unless you install OCaml libraries manually
- Yices 2 and its C dependencies
- The Yices 2 OCaml bindings installed in the active opam switch

The OCaml package dependencies are listed in `yicesQS.opam`. The Yices OCaml bindings are not installed automatically by this package, because current development often depends on local or vendored Yices builds.

The usual local setup is:

```sh
opam pin add tracing.v0.17.0 https://github.com/disteph/tracing/archive/refs/heads/main.zip
opam pin add timer.~dev https://github.com/disteph/timer/archive/refs/heads/main.zip
opam install . --deps-only
```

The Makefile can do the same dependency installation:

```sh
make install
```

or as part of the default target:

```sh
make
```

If Yices or its dependencies are installed outside the usual linker/search paths, set the relevant environment variables before building or running. For test targets, `RUNTIME_LIBRARY_PATHS` controls the runtime library path prefix:

```sh
make test RUNTIME_LIBRARY_PATHS="/path/to/lib:/usr/local/lib"
```

## Configure

Build mode is selected with `./configure`. `make` does not take build-mode options directly; it reads the generated `config.mk`.

Default build:

```sh
./configure
make build
```

Debug build:

```sh
./configure --debug
make build
```

This uses Dune profile `debug`, which enables the `debug_mode` conditional code in `src/debug.mlh`.

Static build:

```sh
./configure --static
make build
```

This uses Dune profile `static` and checks that `main.exe` is not dynamically linked. Static builds are not supported on macOS because the system linker does not support fully static executables there.

The generated `config.mk` is local build state and is ignored by git.

## Build Targets

Common targets:

```sh
make build
make test
make clean
```

The default target installs opam dependencies and builds:

```sh
make
```

Regression/benchmark targets:

```sh
make test
make NRA
make LRA
make BV
make oldBV
```

`make test` first runs the checked-in `regress/*.smt2` tests normally. It then reruns BV/QF_BV regressions with supported delegate SAT solvers, displaying the delegate used for each run.

## Running

After building, run:

```sh
./main.exe path/to/file.smt2
```

The solver prints `sat` or `unsat` on standard output.

Useful options:

```text
-under N          Desired number of underapproximations in SAT answers
-no_bv_invert    Disable BV invertibility conditions
-mcsat           Force MCSAT
-cdclT           Force CDCL(T)
-auto_portfolio S
                 Sequential auto-portfolio anticipating timeout S
-delegate S      For BV/CDCL(T): use delegate S
-delegates       Print supported delegates
```

Trace/debug options are also available:

```text
-trace PATTERN
-step
-filedump PREFIX
```

Run the executable with `-help` for the full option list:

```sh
./main.exe -help
```

## Delegate SAT Solvers

For BV, `yicesQS` transforms quantified problems into quantifier-free checks. These QF_BV checks can use Yices delegate SAT solvers.

Only delegates that support the operations needed by `yicesQS` are exposed:

- `cadical`
- `cryptominisat`

`y2sat` and `kissat` are not accepted by `yicesQS` because they do not support the assumption/unsat-core operations used by the solver.

Show delegates supported by the linked Yices library and accepted by `yicesQS`:

```sh
./main.exe -delegates
```

Run with a delegate:

```sh
./main.exe -delegate cadical regress/035.smt2
./main.exe -delegate cryptominisat regress/035.smt2
```

`-delegate none` is accepted as an explicit way to clear delegate selection; it follows the same solver path as omitting `-delegate`.

For BV, `-auto_portfolio S` starts with CaDiCaL when it is available, then switches to native Yices SAT, then to CryptoMiniSat when it is available, then to MCSAT. With all delegates available, the intended split is 40% CaDiCaL, 20% native Yices SAT, 20% CryptoMiniSat, and the remaining 20% MCSAT.

## Static Linking

Static builds are configured by:

```sh
./configure --static
make build
```

On Linux, the build uses the Dune `static` profile. The current profile links Yices and the delegate/archive dependencies explicitly, including CaDiCaL, CryptoMiniSat, Kissat, CUDD, libpoly, GMP, zlib, pthread, and the C++ runtime.

Check the result with:

```sh
ldd ./main.exe
```

For a fully static executable, `ldd` should report that it is not a dynamic executable.

## Repository Notes

Generated files and local environment folders are ignored, including:

- `_build/`
- `_opam/`
- `config.mk`
- `.vscode/`
- `.codex/`
- `.agents/`

Untracked local benchmark collections can live alongside the checked-in regression suite, but `make test` uses the checked-in regression files so local scratch directories do not change the standard test set.
