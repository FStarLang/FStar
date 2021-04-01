HINTS_ENABLED?=--use_hints
WARN_ERROR=
OTHERFLAGS+=$(WARN_ERROR)

ifdef Z3
OTHERFLAGS+=--smt $(Z3)
endif

# Set ADMIT=1 to admit queries
ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

ifdef FSTAR_HOME
  FSTAR_HOME := $(realpath $(FSTAR_HOME))
  ifeq ($(OS),Windows_NT)
    FSTAR_HOME := $(shell cygpath -m $(FSTAR_HOME))
  endif
  FSTAR_EXE?=$(FSTAR_HOME)/bin/fstar.exe
else
# FSTAR_HOME not defined, assume fstar.exe reachable from PATH
FSTAR_EXE?=fstar.exe
endif
FSTAR=$(FSTAR_EXE) $(OTHERFLAGS) $(MAYBE_ADMIT) $(HINTS_ENABLED) $(WITH_CACHE_DIR)

# Benchmarking wrappers are enabled by setting BENCHMARK_CMD, for example:
#  make -C tests/micro-benchmarks BENCHMARK_CMD=time
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
