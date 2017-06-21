.PHONY: indent

FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/fstar.mk

FLAKY=FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst

ALL=$(filter-out $(FLAKY) ,$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL))

indent: $(addsuffix -indent, $(ALL))

%.fst-indent: %.fst
	$(FSTAR) --indent $^ > $^.indent.fst

%.fsti-indent: %.fsti
	$(FSTAR) --indent $^ > $^.indent.fsti

verify-indent: $(addsuffix -verindent, $(wildcard *.indent.fst))

%-verindent: %
	$(FSTAR) $^

%-ver: %
	$(FSTAR) $^

wc:	
	wc -l prims.fst $(ALL)
