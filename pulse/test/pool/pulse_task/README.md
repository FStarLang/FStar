# Parallel quicksort extracted to Pulse's own task pool

This directory contains the build infrastructure to extract the
Pulse.Lib.Task module into OCaml, and the Quicksort.Task implementation,
and build it with OCaml 5. This does not use domainslib in any way.

The extraction goes through Custard (`--codegen OCaml`), whole-program
from `Quicksort.Task.quicksort`, so one `.ml` file comes out and
`fstar.exe --ocamlopt` links it against the realizations in `ml/` and
`Pulse_Lib_SpinLock.ml`, which must never be compiled from its F* source.
See `doc/ref/custard.md` section 128.

`make run-cherry` (part of `make test` unless `NOCHERRY=1`) builds the
same program with Cherry (`--codegen Cherry`, see `doc/ref/cherry.md`),
the reference-counted C backend: `c/` has the C realizations of
`fork_core` (a detached pthread) and `sleep_ms` and the
driver, and the spin lock is the C realization in
`share/pulse/examples/dice/external/c/hacl`.
