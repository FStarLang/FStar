STEEL_SHARE = ../../
# ^ This must point to /steel/share. But we cannot rely on going via
# the root (../../../..) since the OPAM package will detach the share
# directory from the rest of the repo.

INCLUDE_DIRS=bug-reports lib dice/common dice/dpe dice/engine dice/l0 parallel .
CACHE_DIR=.cache
SRC_DIRS=$(addprefix $(STEEL_SHARE)/examples/pulse/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard $(addsuffix /*.fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*.fsti, $(SRC_DIRS)))

all: verify


include Makefile.pulse.common
