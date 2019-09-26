HINTS_ENABLED?=--use_hints
# 271: theory symbols in smt patters
WARN_ERROR=--warn_error -271
OTHERFLAGS+=$(WARN_ERROR)

ifdef Z3
OTHERFLAGS+=--smt $(Z3)
endif

ifdef FSTAR_HOME
FSTAR_ALWAYS=$(shell cd $(FSTAR_HOME) && pwd)/bin/fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED) $(CACHE_DIR)
FSTAR=$(FSTAR_ALWAYS)
else
# FSTAR_HOME not defined, assume fstar.exe reachable from PATH
FSTAR=fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED) $(CACHE_DIR)
endif

# Benchmarking wrappers are enabled by setting BENCHMARK_CMD, for example:
#  make -C examples/micro-benchmarks BENCHMARK_CMD=time
#  make -C ulib benchmark BENCHMARK_CMD='perf stat -x,'
#
# This will utilize the BENCHMARK_CMD to collect data on the executed commands
#
# BENCHMARK_CMD can be set to a wrapper command that works when called as follows:
#  $BENCHMARK_CMD -o <output-file> -- <program-to-benchmark> <arguments-to-program>
#
# For example Linux perf stat or strace:
#  BENCHMARK_CMD=perf stat -x,
#  BENCHMARK_CMD=strace
#
# or GNU time:
#  BENCHMARK_CMD=time
#
# or the orun OCaml benchmarking program which will include GC stats and available at:
#  https://github.com/ocaml-bench/sandmark/tree/master/orun
#  BENCHMARK_CMD=orun
#
BENCHMARK_CMD?=

ifeq ($(BENCHMARK_CMD),)
BENCHMARK_PRE=
else
# substitution allows targets of the form %.fst.bench to still produce single .bench suffix
BENCHMARK_PRE=-$(BENCHMARK_CMD) -o $(subst .bench,,$@).bench --
endif
