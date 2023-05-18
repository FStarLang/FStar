all: verify krml

.PHONY: krml

ifneq (,$(KRML_HOME))
krml:
	+$(MAKE) -C $@
else
krml:
	echo "No krml found, gracefully skipping"
endif

# Assuming share/steel/tests
STEEL_HOME ?= ../../..

# This consumes too much memory (8GB), so disable it for now.
EXCLUDE_FILES=SteelIntroExists.fst

include $(STEEL_HOME)/share/steel/Makefile.include
