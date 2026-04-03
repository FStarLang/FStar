FSTAR_ROOT ?= ../..

SUBDIRS += cmi

RUN += Eta_expand.fst

# The Div test is based on testing a non-terminating program and
# sending it a signal to interrupt it, which is not well-supported on
# Windows.
ifneq ($(OS),Windows_NT)
RUN += Div.fst
endif

RUN += ExtractAs.fst
RUN += ParseTest.fst

include $(FSTAR_ROOT)/mk/test.mk

# Overriding the default rule for this one. We need to wrap this in a timeout.
$(OUTPUT_DIR)/Div.out: $(OUTPUT_DIR)/Div.exe
	$(call msg,TIMEOUT,$<)
	$(Q)timeout 1 $(OUTPUT_DIR)/Div.exe ; \
	  RC=$$? ;\
	  if ! [ $$RC -eq 124 ]; then echo "ERROR: Div.exe terminated!?!?!"; false; fi
	$(Q)touch $@

# all: inline_let all_cmi Eta_expand.test Div.test ExtractAs.test

# %.exe: %.fst
#         $(FSTAR) --codegen OCaml $<
#         $(OCAMLOPT) -package fstar.lib -linkpkg $(OUTPUT_DIR)/$(patsubst %.fst,%.ml,$<) -o $@

# %.test: %.exe
#         $(call msg,RUN,$<)
#         $(Q)./$<
#         $(Q)touch $@

# Div.test: Div.exe
#         $(call msg,TIMEOUT,$<)
#         $(Q)timeout 1 ./Div.exe ; \
#           RC=$$? ;\
#           if ! [ $$RC -eq 124 ]; then echo "ERROR: Div.exe terminated!?!?!"; false; fi
#         $(Q)touch $@

# inline_let: InlineLet.fst
#         $(FSTAR) --codegen OCaml InlineLet.fst
#         egrep -A 10 test $(OUTPUT_DIR)/InlineLet.ml | grep -qs "17"
#         @touch $@

# all_cmi:
#         +$(MAKE) -C cmi all

# clean:
#         rm -rf out
#         rm -f *.exe
#         rm -f *~
#         rm -f *.exe *.test
#         rm -f inline_let
