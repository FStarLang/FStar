SUBDIRS += bug-reports
SUBDIRS += error_messages
SUBDIRS += nolib
SUBDIRS += pool

PULSE_ROOT ?= ..
include $(PULSE_ROOT)/mk/test.mk

# Extraction here goes through Custard: see $(PULSE_ROOT)/mk/custard-test.mk,
# which replaces test.mk's OCaml, krml and C rules.  The .expected files record
# what Custard currently emits, so that a change to the compiler shows up as a
# diff; they are not a specification of the only correct output.
#
# There is no dependency graph to hand to karamel any more, and no -bundle:
# Custard is whole-program, so the extra .krml prerequisites that Example.Slice
# and Example.Hashtable used to need are gone with the rules that needed them.
CUSTARD_KRML_C += ANF
CUSTARD_KRML_C += Null

include $(PULSE_ROOT)/mk/custard-test.mk

# Pulse compiles [goto], [break] and [return] into a flag that the code after
# the jump tests, and the last write to that flag is by construction never
# read -- as is the write to a local the jump skips over.  A C compiler is
# right to point at both, and neither is Custard's doing, so the warning is
# not an error here.  This is the same accommodation the karamel pipeline
# needed, which is what the KRML_FLAGS line below is for.
CUSTARD_CFLAGS += -Wno-error=unused-but-set-variable

KRML_FLAGS = -ccopt -Wno-error=unused-but-set-variable
