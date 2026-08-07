FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# These modules are benchmarks, but they are also differential tests: every
# assert_norm here must succeed with --no_smt, so it is checking that the
# selected engine computes the right answer, not just that it is fast.
#
# `make bench` runs the timing harness. It is not part of `all` because it
# checks every module several times under two configurations.
bench:
	./run.sh $(FSTAR_EXE) $(REPS)

.PHONY: bench
