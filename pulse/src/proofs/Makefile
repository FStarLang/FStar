TARGETS :=

ifneq (,$(STEEL_NIGHTLY_CI))
TARGETS += steelc
endif

all: $(TARGETS)

$(TARGETS): %:
	+$(MAKE) -C $@

.PHONY: all $(TARGETS)
