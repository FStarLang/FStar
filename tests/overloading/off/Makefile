FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

# 'off' restores the pre-overloading behaviour: names resolve
# first-match-wins in scope order and no candidates are ever collected.
# Now that 'compat' is the default, this is the escape hatch, so keep it
# tested.
FSTAR_ARGS += --ext fstar:overload=off
