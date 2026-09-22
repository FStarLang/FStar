FSTAR_ROOT ?= ../../..

# Section 34 and section 64: a Custard *rule* is registered by a plugin and
# then fires during a later extraction, so the only way to test one is to
# build a plugin, load it, and extract something with it loaded.
#
# This used to be `make custard-plugin', forty lines of mk/custard.mk driving
# a second compiler in stagec/.  It does not need one any more: the compiler
# running this suite is itself Custard-extracted, --codegen Plugin is a
# Custard extraction linked against its .cui (section 13.6), and the .checked
# files here are written by the same binary that loads the plugin -- which is
# what mk/custard-rule.mk existed to arrange by hand.
#
# CustardPluginTest.fst is deliberately not in FSTAR_FILES: it asserts that
# irreducible definitions reduce, which is true only with the plugin loaded,
# so the default __verify must not pick it up.  It is checked by the
# plugin.test rule below instead.
FSTAR_FILES := CustardPlugin.fst CustardPluginAux.fst CustardRulePlugin.fst \
               CustardRuleTest.fst CustardRuleArity.fst CustardRuleBare.fst \
               CustardRuleOverArity.fst

# CustardRulePlugin registers a rule, so its *source* names FStarC.Custard's
# own types: unlike an ordinary plugin, this one has to be checked with the
# compiler's modules in scope and not only extracted with them.  --with_fstarc
# also puts the compiler's prelude on the path, whose bundle hashes are not
# the ones ulib's checked files were written against, so ulib's come last and
# win (the same pair pulse/mk/checker.mk needs, for the same reason).
FSTAR_LIBDIR = $(abspath $(dir $(FSTAR_EXE))../lib/fstar)
FSTAR_ARGS += --with_fstarc --include $(FSTAR_LIBDIR)/ulib.checked
# --already_cached keeps only its last setting, so this repeats test.mk's
# Prims,FStar rather than adding to it: the compiler's own modules arrive
# through --with_fstarc with checked files beside them and must not be
# rechecked (they do not verify outside the compiler's own build flags).
FSTAR_ARGS += --already_cached Prims,FStar,FStarC
# 272: a plugin module exists for its top-level registration call, which is
# exactly the "top-level let-binding may have effects" this warns about.
FSTAR_ARGS += --warn_error -272-274

include $(FSTAR_ROOT)/mk/test.mk

CC ?= cc

# The three roots of the plugin.  Section 13.4: a registration is generated
# only for a module named as an entry, so every module carrying [@@plugin]
# has to be one -- CustardPluginAux is reached from nothing else, and
# CustardRulePlugin exists purely for its initializer.
PLUGIN_ROOTS := CustardPlugin.fst CustardPluginAux.fst CustardRulePlugin.fst

# --ext fly_deps=false: fly_deps allows only one file on the command line,
# and a plugin with three roots has three.
$(OUTPUT_DIR)/CustardPlugin.ml: $(PLUGIN_ROOTS) | $(ALL_CHECKED_FILES)
	$(call msg, "EXTRACT PLUGIN", CustardPlugin)
	$(FSTAR) --codegen Plugin --ext fly_deps=false $(PLUGIN_ROOTS)

$(OUTPUT_DIR)/CustardPlugin.cmxs: $(OUTPUT_DIR)/CustardPlugin.ml
	$(call msg, "OCAMLOPT", $(notdir $<))
	$(FSTAR_EXE) --ocamlopt_plugin -o $@ $<

PLUGIN := $(abspath $(OUTPUT_DIR))/CustardPlugin

# The definitions the test reduces are irreducible, so this fails unless the
# native steps the plugin registered are the ones answering.
$(OUTPUT_DIR)/plugin.test: $(OUTPUT_DIR)/CustardPlugin.cmxs CustardPluginTest.fst
	$(call msg, "CHECK NATIVE", CustardPluginTest)
	$(FSTAR) --load_cmxs $(PLUGIN) CustardPluginTest.fst
	touch $@

all: $(OUTPUT_DIR)/plugin.test

# ------------------------------------------------------------------ the rule

# Section 34.  Without the rule the extraction fails with error 368 -- the
# descriptor stores a type -- so reaching the C at all is already the test;
# running it checks that the rule read the descriptor correctly rather than
# merely having been consulted.
$(OUTPUT_DIR)/CustardRuleTest.c: $(OUTPUT_DIR)/CustardPlugin.cmxs \
                                 $(CACHE_DIR)/CustardRuleTest.fst.checked
	$(call msg, "EXTRACT C", CustardRuleTest)
	$(FSTAR) --load_cmxs $(PLUGIN) \
	  --codegen Custard --custard_backend C \
	  --custard_monomorphize_types true \
	  --custard_main CustardRuleTest.main \
	  CustardRuleTest.fst -o $@

$(OUTPUT_DIR)/CustardRuleTest.ran: $(OUTPUT_DIR)/CustardRuleTest.c CustardRuleMain.c
	$(call msg, "RULE", CustardRuleTest)
	# The descriptor is compile-time input to code generation and must not
	# survive into the output in any form: the rule consumed it, and
	# dead-code elimination then removed the types it mentioned.
	$(Q)grep -q 'CustardRuleTest_desc\|CustardRuleTest_sized\|CustardRuleTest_kdesc' \
	  $(OUTPUT_DIR)/CustardRuleTest.c $(OUTPUT_DIR)/CustardRuleTest.h \
	  && { echo "ERROR: the descriptor reached the C output"; exit 1; } || true
	# 40 + 2, added up by the plugin while the extraction was running.
	$(Q)grep -qF '(uint32_t)42U' $< \
	  || { echo "ERROR: the rule did not fold the descriptor"; exit 1; }
	# Section 36.3: the kernel body was lifted under the name the *descriptor*
	# gave it, not a generated one, and carries the flags the rule asked for.
	$(Q)grep -q 'static uint32_t kernel(uint32_t c, uint32_t tid) {' $< \
	  || { echo "ERROR: the kernel was not lifted under its own name"; exit 1; }
	$(Q)grep -qF '__attribute__((noinline))' $< \
	  || { echo "ERROR: the rule's Prologue flag did not reach the C"; exit 1; }
	$(Q)grep -qF '/* kernel kernel, 42 bytes shared */' $< \
	  || { echo "ERROR: the rule's Comment flag did not reach the C"; exit 1; }
	# Section 36.2: the runtime entry point nothing in the source calls
	# survived, under the name [@@custard_extern] gave it rather than the
	# mangled one -- which is what a deleted declaration used to produce.
	$(Q)grep -qF 'kpr_kcall' $< \
	  || { echo "ERROR: the rule's registered root was dropped"; exit 1; }
	$(Q)grep -q 'CustardRuleTest_kcall' $< \
	  && { echo "ERROR: the extern's target name was not read"; exit 1; } || true
	# Section 36.4: a rule's call is direct, not through a temporary holding
	# the function.  A name is not a computation and ANF must not hoist one.
	$(Q)grep -q '= kpr_kcall;' $< \
	  && { echo "ERROR: the rule's call went through a function pointer"; \
	       exit 1; } || true
	# Section 64: a polymorphic external reached only through a rule.  The
	# extractor never sees a call to [sink], so the instantiations exist
	# only as type arguments on the [EQual] the rule built; one declaration
	# per distinct type vector is what says they were read.  Both greps
	# together are the assertion -- either name alone would still be here
	# if the two had collapsed into one symbol at [any].
	$(Q)grep -q 'CustardRuleTest_sink__uint32(uint32_t)' $< \
	  || { echo "ERROR: the u32 instantiation of the rule's polymorphic \
	             external is missing"; exit 1; }
	$(Q)grep -q 'CustardRuleTest_sink__uint64(uint64_t)' $< \
	  || { echo "ERROR: the u64 instantiation of the rule's polymorphic \
	             external is missing"; exit 1; }
	# And nothing left at [any], which is what it used to come out as.
	$(Q)grep -q 'CustardRuleTest_sink(' $< \
	  && { echo "ERROR: the polymorphic external survived unspecialized"; \
	       exit 1; } || true
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror -I$(abspath $(OUTPUT_DIR)) \
	  -x c $< CustardRuleMain.c -o $(OUTPUT_DIR)/CustardRuleTest.exe
	$(Q)$(OUTPUT_DIR)/CustardRuleTest.exe
	touch $@

all: $(OUTPUT_DIR)/CustardRuleTest.ran

# ---------------------------------------------------- rule-authoring mistakes

# Section 64.2: the arity mistake in the direction that used to get all the
# way to the C compiler.  The rule for CustardRuleArity.thrice is registered
# at arity 1 against three retained arguments, so its result is applied to
# the two left over.  Extracted for the diagnostic; the C is expected not to
# compile and is not compiled.
$(OUTPUT_DIR)/CustardRuleArity.diag: $(OUTPUT_DIR)/CustardPlugin.cmxs \
                                     $(CACHE_DIR)/CustardRuleArity.fst.checked
	$(call msg, "RULE DIAG", CustardRuleArity)
	$(Q)$(FSTAR) --load_cmxs $(PLUGIN) \
	  --codegen Custard --custard_backend C \
	  --custard_monomorphize_types true \
	  --custard_main CustardRuleArity.main \
	  CustardRuleArity.fst -o $(OUTPUT_DIR)/CustardRuleArity.c \
	  > $(OUTPUT_DIR)/arity.log 2>&1 || true
	$(Q)grep -q 'Warning 381' $(OUTPUT_DIR)/arity.log \
	  || { echo "ERROR: an under-declared rule arity was not reported"; \
	       cat $(OUTPUT_DIR)/arity.log; exit 1; }
	$(Q)grep -qF 'the rule'"'"'s result is not a function' $(OUTPUT_DIR)/arity.log \
	  || { echo "ERROR: 381 fired, but not for the under-arity reason"; \
	       cat $(OUTPUT_DIR)/arity.log; exit 1; }
	touch $@

# Section 64: the other rule-authoring mistake a polymorphic entry point makes
# possible -- an EQual built without the argument's type.  Nothing else records
# the instantiation, so the reference would name a symbol that does not exist;
# 388 says so here instead of the linker saying it about generated code.
$(OUTPUT_DIR)/CustardRuleBare.diag: $(OUTPUT_DIR)/CustardPlugin.cmxs \
                                    $(CACHE_DIR)/CustardRuleBare.fst.checked
	$(call msg, "RULE DIAG", CustardRuleBare)
	$(Q)$(FSTAR) --load_cmxs $(PLUGIN) \
	  --codegen Custard --custard_backend C \
	  --custard_monomorphize_types true \
	  --custard_main CustardRuleBare.main \
	  CustardRuleBare.fst -o $(OUTPUT_DIR)/CustardRuleBare.c \
	  > $(OUTPUT_DIR)/bare.log 2>&1 || true
	$(Q)grep -q 'Error 388' $(OUTPUT_DIR)/bare.log \
	  || { echo "ERROR: a rule that dropped the type argument was not \
	             reported"; cat $(OUTPUT_DIR)/bare.log; exit 1; }
	touch $@

# Issue 4565: the arity mistake in the direction that used to delete the call.
# The rule for CustardRuleOverArity.store is registered at arity 3 against two
# retained arguments, and the declaration's codomain is not a function, so this
# is an error and not warning 381.
$(OUTPUT_DIR)/CustardRuleOverArity.diag: $(OUTPUT_DIR)/CustardPlugin.cmxs \
                                         $(CACHE_DIR)/CustardRuleOverArity.fst.checked
	$(call msg, "RULE DIAG", CustardRuleOverArity)
	$(Q)$(FSTAR) --load_cmxs $(PLUGIN) \
	  --codegen Custard --custard_backend C \
	  --custard_monomorphize_types true \
	  --custard_main CustardRuleOverArity.main \
	  CustardRuleOverArity.fst -o $(OUTPUT_DIR)/CustardRuleOverArity.c \
	  > $(OUTPUT_DIR)/overarity.log 2>&1 \
	  && { echo "ERROR: an over-declared rule arity did not fail extraction"; \
	       cat $(OUTPUT_DIR)/overarity.log; exit 1; } || true
	$(Q)grep -q 'Error 396' $(OUTPUT_DIR)/overarity.log \
	  || { echo "ERROR: an over-declared rule arity was not reported as 396"; \
	       cat $(OUTPUT_DIR)/overarity.log; exit 1; }
	touch $@

all: $(OUTPUT_DIR)/CustardRuleArity.diag
all: $(OUTPUT_DIR)/CustardRuleBare.diag
all: $(OUTPUT_DIR)/CustardRuleOverArity.diag
