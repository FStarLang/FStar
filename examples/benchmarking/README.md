Benchmarking FStar
==================

There are hooks within the FStar makefiles to make it easy to run a benchmarks of examples/micro-benchmarks, ulib and OCaml extraction of the FStar compiler itself.

To get started, you can run the micro-benchmarks using GNU time to measure execution with:
```
 $ make -C examples/micro-benchmarks BENCHMARK_CMD=time
```
This will output .bench files for each of the benchmarks.


Example of full benchmarks
--------------------------

The `make_bench_results.sh` script is an example which:
 - places all the results into the directory `./bench_results/YYYY_HHMMSS`
 - cleans the fstar tree to start from a known state
 - builds the fstar compiler
 - builds a fresh ulib
 - executes the benchmarks for micro-benchmarks, ulib and OCaml extraction
 - collates the JSON results into a CSV file and also timing summaries in the results directory

To run this script you may need to install:
 - orun which to collect OCaml profiling information including GC stats and is part of the sandmark OCaml benchmarking suite (https://github.com/ocaml-bench/sandmark). To install a local pinned copy of orun do the following:
```
 $ git clone https://github.com/ocaml-bench/sandmark.git sandmark
 $ cd sandmark/orun
 $ opam install .
```
 - jq which collates JSON into CSV (https://stedolan.github.io/jq/)

To run the script execute (from the fstar root directory)
```
 $ examples/benchmarking/make_bench_results.sh
```

The script has options to set wrappers for tasksetting and/or setting FStar OTHERFLAGS, for example:
```
 $ BENCH_WRAP='taskset --cpu-list 3' BENCH_OTHERFLAGS='--admit_smt_queries true' examples/benchmarking/make_bench_results.sh
```

