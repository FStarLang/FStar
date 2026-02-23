FSTAR_ROOT ?= ../../../../../
FSTAR_CONTRIB := $(FSTAR_ROOT)/contrib
OTHERFLAGS += --include $(FSTAR_CONTRIB)/Platform/fst --include $(FSTAR_CONTRIB)/CoreCrypto/fst

# exercises have val without definitions, by design
OTHERFLAGS += --warn_error -240

FSTAR_FILES := Ex01a.fst \
Ex02a.fst \
Ex03a.fst \
Ex03b.fst \
Ex03c.fst \
Ex04a.fst \
Ex04b.fst \
Ex04c.fst \
Ex04e.fst \
Ex04f.fst \
Ex04g.fst \
Ex04h.fst \
Ex05a.fst \
Ex05b.fst \
Ex06a.fst \
Ex06b.fst \
Ex06e.fst \
Ex07a.fst \
Ex07b.fst \
Ex07c.fst \
Ex07d.fst \
Ex10a.fst \
Ex10b.fst \
Ex12a1.Cap.fst \
Ex12b1.Format.fst \
Ex12b2.Format.fst \
Ex12c.Format.fst \
Ex12d.Pad.fst \
Ex12e.Pad.fst \
Ex12f.TMAC.fst \
Ex12g.TMAC2.fst

include $(FSTAR_ROOT)/mk/test.mk

Ex01a-ocaml: $(OUTPUT_DIR)/Ex01a.exe
	-./$(OUTPUT_DIR)/Ex01a.exe
