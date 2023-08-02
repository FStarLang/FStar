STEEL_HOME=../../../..
INCLUDE_DIRS=bug-reports lib dice/common dice/dpe dice/engine dice/l0
CACHE_DIR=.cache
SRC_DIRS=$(addprefix $(STEEL_HOME)/share/steel/examples/pulse/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard $(addsuffix /*fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*fsti, $(SRC_DIRS)))

all: verify


include Makefile.pulse.common
