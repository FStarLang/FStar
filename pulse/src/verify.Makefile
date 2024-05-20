all: verify

PULSE_HOME ?= ..

PULSE_LIB_SUBDIRS = \
	c \
	core \
	lib \
	lib/class \
	lib/pledge \
	.
PULSE_DICE_SUBDIRS = \
	external \
  external/hacl \
  external/l0 \
	dpe \
	engine \
	l0 \
	cbor \
	.
PULSE_EXAMPLES_SUBDIRS = \
	bug-reports \
	by-example \
	c \
	$(addprefix dice/,$(PULSE_DICE_SUBDIRS)) \
	parallel \
	parix \
	.

SRC_DIRS := $(PULSE_HOME)/src/checker $(addprefix $(PULSE_HOME)/lib/pulse/,$(PULSE_LIB_SUBDIRS)) $(addprefix $(PULSE_HOME)/share/pulse/examples/,$(PULSE_EXAMPLES_SUBDIRS))
FSTAR_OPTIONS += --already_cached 'Prims,FStar' --load_cmxs pulse

include $(PULSE_HOME)/share/pulse/Makefile.include-base
