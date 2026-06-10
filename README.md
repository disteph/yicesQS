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

Command-line options:

```text
-under N
    Desired number of underapproximations in SAT answers. Default: 20.
-no_bv_invert
    Disable BV invertibility conditions. By default, BV invertibility
    conditions are computed.
-wide-projection N
    Use wide arithmetic model projection with cube budget N. Use 0 for an
    unbounded cube budget.
-auto_portfolio S
    Enable the built-in sequential portfolio for the input logic, anticipating
    an external timeout of S seconds.
-mcsat
    Force MCSAT.
-cdclT
    Force CDCL(T) with inequality assumptions.
-cdclT-assumptions Eq|Ineq
    Force CDCL(T) and choose equality or inequality assumptions.
-seed S
    Set the Yices random seed to S.
-switch T
    Run the current solver configuration for T seconds, then switch to the
    configuration described by subsequent options, up to the next switch
    delimiter or the end of the command line.
-switch_seeds T N
    Add N switch segments for the current solver configuration, each T seconds
    long, using seeds 1 through N.
-delegate none|cadical|cryptominisat
    For BV/CDCL(T), use a Yices SAT delegate. `none` clears delegate selection.
-delegates
    Print supported SAT delegates and exit.
-trace PATTERN
    Enable tracing according to PATTERN.
-step
    Step through the last trace.
-filedump PREFIX
    Dump input and trace files under PREFIX on selected errors.
-help, --help
    Display the full option list and exit.
```

Portfolio options are order-sensitive. For example, this runs MCSAT for 10
seconds, then CDCL(T) with equality assumptions for 20 seconds, then continues
with the final configuration:

```sh
./main.exe -mcsat -switch 10 -cdclT-assumptions Eq -switch 20 file.smt2
```

Run the executable with `-help` to print the option list from the binary:

```sh
./main.exe -help
```

## Auto Portfolio

`-auto_portfolio S` enables a built-in sequential portfolio for the input
logic, with slice lengths scaled to an expected external timeout of `S`
seconds. It only takes effect when no explicit switch portfolio was already
specified.

For `NRA` and `NIA`, the portfolio uses MCSAT throughout. It enables unbounded
wide projection, runs MCSAT seed 0 for `24.5 / 1200 * S` seconds, then tries 20
short MCSAT seed slices of `5 / 1200 * S` seconds each.

For `LRA`, the portfolio uses MCSAT throughout. After the initial seed-0 run,
it tries seeds 1 through 3, with each timed slice using `S / 4` seconds.

For `LIA`, the portfolio uses CDCL(T) with inequality assumptions throughout.
After the initial seed-0 run, it tries seeds 1 through 5, with each timed slice
using `S / 6` seconds.

For `BV`, the portfolio starts with native CDCL(T) with equality assumptions,
then tries 10 short native CDCL(T) seed slices, then switches to MCSAT followed
by 10 short MCSAT seed slices. For `S = 1200`, the intended split is 24.5
seconds of native CDCL(T), 10 five-second native CDCL(T) seed slices, 700
seconds of MCSAT, and 10 five-second MCSAT seed slices.

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

## Static Linking

Static builds are configured by:

```sh
./configure --static
make build
```

On Linux, the build uses the Dune `static` profile. The current profile links Yices and the delegate/archive dependencies explicitly, including CaDiCaL, CryptoMiniSat, CUDD, libpoly, GMP, zlib, pthread, and the C++ runtime.

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
