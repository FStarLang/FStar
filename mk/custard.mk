# Build an F* compiler with Custard instead of the ML extraction.
#
# See doc/ref/custard.md, section 12.10.  The pipeline is:
#
#   1. --custard_split the whole compiler, from FStarC.Main.main plus the
#      entry points in src/custard/entrypoints.txt, into one .ml per F*
#      module;
#   2. drop the hand-written realizations of src/ml in beside them;
#   3. build the result with dune, in a project laid out like stage1's and
#      stage2's.  That is what generates the two menhir parsers against
#      *these* interfaces, not the ones the ML extraction produced -- the two
#      extractions lay the same F* types out differently, so a parser
#      inferred against the wrong ones is at best accidentally well-typed --
#      and what makes the build parallel (section 12.14).
#
# The result is a working fstar.exe -- ulib's plugins included, so tactics
# like FStar.Tactics.Typeclasses.mk_class run natively -- with one known
# limitation, recorded in section 12.10: it cannot read .checked files
# written by a dune-built compiler, because those are Marshal dumps of
# differently laid out types.
#
# The `plugin' target is the other half of section 12.8: a plugin that is
# itself compiled by Custard, against this compiler's .cui, and loaded into
# it with --load_cmxs.

include mk/common.mk

$(call need_exe, FSTAR_EXE, the compiler that runs the extraction)
$(call need_dir, ULIB_CHECKED, checked files for ulib)
$(call need_dir, FSTARC_CHECKED, checked files for src)

OUT     ?= stagec
CACHE   := $(OUT)/cache
SPLIT   := $(OUT)/split
BUILD   := $(OUT)/dune
BIN     := $(OUT)/out/bin/fstar.exe

# Where dune leaves the library's artifacts.  Two directories, because with
# `(modes native)' the .cmi files are still under byte/ and only the .cmx and
# .o are under native/.  A plugin compiles against both (section 12.11).
OBJS    := $(BUILD)/_build/default/fstar-guts/.fstarcompiler.objs
INCS    := -I $(abspath $(OBJS))/byte -I $(abspath $(OBJS))/native

# The compiler's own roots, and the roots a *plugin's* hand-written OCaml
# needs: a realization calls the compiler by OCaml name, through no request
# Custard can see, so the symbol has to be named in the build of the binary
# the plugin is loaded into.  Pulse is built by this repo, so its list is
# here; another plugin adds its file to CUSTARD_ENTRYFILES.
ENTRYFILES := src/custard/entrypoints.txt pulse/src/custard-entrypoints.txt \
              $(CUSTARD_ENTRYFILES)
ENTRIES    := $(patsubst %,--custard_entrypoints %,$(ENTRYFILES))

# The realizations, the two grammars and the two sedlex lexers.
# The version stamp is a script that assigns to FStarC.Options' `_version'
# and friends.  Custard mangles a leading underscore to `u__' (section 5.2),
# so the script's output has to be renamed; the dune build's copy is not
# usable as it stands.
VERSION_SH := .scripts/make_fstar_version.sh

# ulib/ml/plugin holds the realizations of the modules ulib declares for
# metaprograms -- FStar.Sealed, FStar.Issue, and the two Stubs modules that
# are really the compiler's own tactic engine.  The dune build compiles them
# into the plugin library rather than the compiler; a whole-program build has
# only one link unit, so they go in beside the rest.
REALIZATIONS := $(wildcard src/ml/*.ml) $(wildcard ulib/ml/plugin/*.ml)
GRAMMARS     := FStarC_Parser_Parse FStarC_Parser_WarnError

OCAMLPKGS := fstar.lib,sedlex,sedlex.ppx,zarith,batteries,menhirLib,pprint,ppxlib,ppx_deriving_yojson.runtime,memtrace,mtime.clock.os,process,stdint,yojson,dynlink
export OCAMLPATH := $(abspath out/lib)

# -w -a: the generated code is not meant to be read, and every warning it can
# raise is one this build cannot act on.
OCAMLFIND := ocamlfind
OCAMLOPT  := $(OCAMLFIND) ocamlopt -package $(OCAMLPKGS) -w -a
OCAMLC    := $(OCAMLFIND) ocamlc   -package $(OCAMLPKGS) -w -a

# Quieten findlib's deprecation chatter, which is about our *dependencies*.
FILTER := 2>&1 | grep -v '^findlib\|Deprecated, use\|^Alert' || true

.PHONY: all split build clean smoke plugin pulse-plugin

all: $(BIN)

# ---------------------------------------------------------------- extraction

# The cache is a *copy*, so it has to be refreshed whenever the checked files
# it was copied from change -- otherwise an edit to the compiler is verified,
# extracted and linked against a stale cache, and the failure is a link error
# in generated code rather than anything that names the edit.  This makefile is
# only read after `2.full' has run, so the wildcard sees the finished set.
CHECKED_FILES := $(wildcard $(ULIB_CHECKED)/*.checked $(FSTARC_CHECKED)/*.checked)

$(CACHE)/.touch: mk/custard.mk $(CHECKED_FILES)
	$(call bold_msg, "CUSTARD", "CACHE")
	$(Q)rm -rf $(CACHE) && mkdir -p $(CACHE)
	$(Q)cp $(ULIB_CHECKED)/* $(CACHE)/
	$(Q)cp -f $(FSTARC_CHECKED)/* $(CACHE)/
	$(Q)touch $@

$(SPLIT)/.touch: mk/custard.mk $(CACHE)/.touch $(ENTRYFILES)
	$(call bold_msg, "CUSTARD", "SPLIT")
	$(Q)rm -rf $(SPLIT) && mkdir -p $(SPLIT)
	$(Q)env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  --lax --codegen Custard --custard_split --custard_unit fstarc \
	  --custard_entry FStarC.Main.main $(ENTRIES) \
	  --cache_dir $(CACHE) --include src/ --already_cached ',*' \
	  --warn_error -321-274-272-241 \
	  src/fstar/FStarC.Main.fst --odir $(SPLIT)
	$(Q)touch $@

split: $(SPLIT)/.touch

# ------------------------------------------------------------------ assembly

# A dune project laid out like stage1's and stage2's: one `wrapped false'
# library out of the generated modules and the realizations, and one
# executable that calls FStarC_Main.main.  Section 12.14.
#
# Doing it this way rather than by hand buys three things.  Dune runs the
# menhir `--infer' pre-pass itself, and against *this* library, which is the
# whole point of not borrowing the stage2 parser; it compiles in parallel,
# which the hand-rolled `ocamldep -sort' pipeline could not; and it is the
# same recipe the rest of the repo already uses, so there is one build to
# understand rather than two.
#
# The pieces are symlinked rather than copied, so an edit to a realization is
# picked up without re-running the extraction.  Nothing overlaps: a realized
# module's F* definitions are a model (section 8.2, M10j) and Custard does not
# emit them, so `$(SPLIT)' and `src/ml' are disjoint.
#
# `fstar.lib' supplies Prims and the rest of the app-side realizations, and
# its FStar_Order collides with the one Custard emits.  `-linkall' therefore
# goes on the *library* rather than on the executable: an archive module that
# something already defines is then simply not pulled in, which is what the
# hand-rolled link relied on too.

DUNE_LIBS := batteries zarith stdint yojson ppxlib dynlink menhirLib pprint \
             process sedlex mtime.clock fstar.lib

$(BUILD)/.touch: mk/custard.mk $(SPLIT)/.touch
	$(call bold_msg, "CUSTARD", "ASSEMBLE")
	$(Q)rm -rf $(BUILD) && mkdir -p $(BUILD)/fstar-guts $(BUILD)/fstar-exe
	$(Q)printf '(lang dune 3.15)\n(name fstarc-custard)\n(using menhir 2.1)\n' \
	   > $(BUILD)/dune-project
	$(Q)printf '(env (_ (bin_annot false) (flags (:standard -w -A))))\n' \
	   > $(BUILD)/dune
	$(Q)ln -sfT $(abspath $(SPLIT))        $(BUILD)/fstar-guts/split
	$(Q)ln -sfT $(abspath src/ml)          $(BUILD)/fstar-guts/ml
	$(Q)ln -sfT $(abspath ulib/ml/plugin)  $(BUILD)/fstar-guts/plugin
	$(Q)ln -sf  $(abspath $(VERSION_SH))   $(BUILD)/fstar-guts/
	$(Q)ln -sf  $(abspath version.txt)     $(BUILD)/fstar-guts/
	$(Q)for g in $(GRAMMARS); do \
	   ln -sf $(abspath src/ml)/$$g.mly $(BUILD)/fstar-guts/; done
	$(Q){ \
	   echo '(include_subdirs unqualified)'; \
	   echo '(library'; \
	   echo ' (name fstarcompiler)'; \
	   echo ' (wrapped false)'; \
	   echo ' (modes native)'; \
	   echo ' (library_flags (-linkall))'; \
	   echo ' (libraries $(DUNE_LIBS))'; \
	   echo ' (preprocess (pps ppx_deriving.show ppx_deriving_yojson sedlex.ppx)))'; \
	   for g in $(GRAMMARS); do echo "(menhir (modules $$g))"; done; \
	   echo '(rule'; \
	   echo '  (target FStarC_Version.ml)'; \
	   echo '  (deps (:script $(notdir $(VERSION_SH))) version.txt)'; \
	   echo '  (action (with-stdout-to FStarC_Version.ml'; \
	   echo "    (system \"bash %{script} | sed s/FStarC_Options[.]_/FStarC_Options.u__/\"))))"; \
	 } > $(BUILD)/fstar-guts/dune
	$(Q){ \
	   echo '(executable'; \
	   echo ' (name zzMain)'; \
	   echo ' (modes (native exe))'; \
	   echo ' (libraries fstarcompiler memtrace))'; \
	 } > $(BUILD)/fstar-exe/dune
	$(Q)printf 'let () = FStarC_Main.main ()\n' > $(BUILD)/fstar-exe/zzMain.ml
	$(Q)touch $@

# ------------------------------------------------------------------- compile

# No file list: dune reads the symlinked directories itself, so this rule runs
# on every `make' and does nothing when nothing changed.
$(BIN): mk/custard.mk $(BUILD)/.touch $(REALIZATIONS) \
        $(addprefix src/ml/,$(addsuffix .mly,$(GRAMMARS))) \
        $(VERSION_SH) version.txt
	$(call bold_msg, "CUSTARD", "COMPILE")
	$(Q)cd $(BUILD) && dune build --display=quiet fstar-exe/zzMain.exe
	$(Q)mkdir -p $(dir $(BIN))
	$(Q)cp -f $(BUILD)/_build/default/fstar-exe/zzMain.exe $(BIN)

build: $(BIN)

# --------------------------------------------------------------------- smoke

# The Custard-built compiler cannot read a dune-built compiler's .checked
# files, so the test starts from an empty cache and rechecks ulib from source.
smoke: $(BIN)
	$(call bold_msg, "CUSTARD", "SMOKE")
	$(Q)rm -rf $(OUT)/smoke && mkdir -p $(OUT)/smoke
	$(Q)env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) \
	   --cache_checked_modules --cache_dir $(OUT)/smoke \
	   ulib/FStar.List.Tot.Properties.fst

# ------------------------------------------------------------------- plugin

# Section 12.8: a plugin compiled by Custard, loaded into the compiler
# compiled by Custard.  The two runs are separate whole-program extractions
# and agree only through $(SPLIT)/fstarc.cui, which records for every
# compiler declaration the name Custard gave it *and* the file it landed in.
#
# The extraction runs with the dune-built compiler (the .checked files are
# its), the load runs with the Custard-built one; nothing else would test
# anything.  The plugin's own module is checked into $(CACHE) first because
# --custard_link needs a checked file for it like any other.
PLUGIN_SRC  := tests/custard/plugin
PLUGIN_DIR  := $(OUT)/plugin
PLUGIN_MOD  := CustardPlugin
# Section 13.4: a registration is generated only for a module named by
# --custard_entry, so every module of a plugin that carries [@@plugin] has to
# be a root.  CustardPluginAux is a second one, reached from nothing.
PLUGIN_AUX  := CustardPluginAux
# Section 34: a third root, which registers a Custard *rule* rather than a
# normalization step.  It is a root for the same reason -- a module that
# exists for its initializer has to be named, or nothing reaches it.
PLUGIN_RULE := CustardRulePlugin

plugin: $(BIN)
	$(call bold_msg, "CUSTARD", "PLUGIN")
	$(Q)rm -rf $(PLUGIN_DIR) && mkdir -p $(PLUGIN_DIR)
	$(Q)env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  --cache_checked_modules --cache_dir $(CACHE) \
	  --include src/ --include $(PLUGIN_SRC) --already_cached ',*' \
	  --ext fly_deps=false \
	  --warn_error -321-274-272-241 \
	  $(PLUGIN_SRC)/$(PLUGIN_MOD).fst $(PLUGIN_SRC)/$(PLUGIN_AUX).fst \
	  $(PLUGIN_SRC)/$(PLUGIN_RULE).fst
	# --ext fly_deps=false: fly_deps allows only one file on the command
	# line, and a plugin with two roots has two.
	$(Q)env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  --lax --codegen Custard --custard_unit $(PLUGIN_MOD) \
	  --custard_link $(SPLIT)/fstarc.cui \
	  --custard_entry $(PLUGIN_MOD) --custard_entry $(PLUGIN_AUX) \
	  --custard_entry $(PLUGIN_RULE) \
	  --ext fly_deps=false \
	  --cache_dir $(CACHE) --include src/ --include $(PLUGIN_SRC) \
	  --already_cached ',*' --warn_error -321-274-272-241 \
	  $(PLUGIN_SRC)/$(PLUGIN_MOD).fst $(PLUGIN_SRC)/$(PLUGIN_AUX).fst \
	  $(PLUGIN_SRC)/$(PLUGIN_RULE).fst \
	  --odir $(PLUGIN_DIR)
	$(Q)cd $(PLUGIN_DIR) && $(OCAMLOPT) -shared \
	  $(INCS) -o $(PLUGIN_MOD).cmxs \
	  $$($(OCAMLFIND) ocamldep -sort *.ml) $(FILTER)
	# The definitions the test reduces are irreducible, so this fails
	# unless the native steps the plugin registered are the ones answering.
	$(Q)env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) \
	  --load_cmxs $(abspath $(PLUGIN_DIR))/$(PLUGIN_MOD) \
	  --cache_dir $(PLUGIN_DIR)/cache \
	  --include $(PLUGIN_SRC) $(PLUGIN_SRC)/$(PLUGIN_MOD)Test.fst
	# Section 34: the rule.  CustardRuleTest is checked and then extracted to
	# C by the compiler the plugin is loaded into.  Without the rule the
	# extraction fails with error 368 -- the descriptor stores a type -- so
	# reaching the C at all is the test; running it checks that the rule read
	# the descriptor correctly rather than merely being consulted.
	$(Q)env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) --dep full \
	  --cache_dir $(abspath $(PLUGIN_DIR))/cache --include $(PLUGIN_SRC) \
	  $(PLUGIN_SRC)/CustardRuleTest.fst -o $(PLUGIN_DIR)/rule.depend
	+$(Q)$(MAKE) -f mk/custard-rule.mk all \
	  RULE_DEPEND=$(abspath $(PLUGIN_DIR))/rule.depend \
	  RULE_FSTAR="env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) --lax \
	    --cache_checked_modules --cache_dir $(abspath $(PLUGIN_DIR))/cache \
	    --include $(PLUGIN_SRC)"
	$(Q)env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) \
	  --load_cmxs $(abspath $(PLUGIN_DIR))/$(PLUGIN_MOD) \
	  --codegen Custard --custard_backend C \
	  --custard_monomorphize_types true \
	  --custard_main CustardRuleTest.main \
	  --cache_dir $(PLUGIN_DIR)/cache --include $(PLUGIN_SRC) \
	  $(PLUGIN_SRC)/CustardRuleTest.fst -o $(PLUGIN_DIR)/CustardRuleTest.c
	# The descriptor is compile-time input to code generation and must not
	# survive into the output in any form: the rule consumed it, and
	# dead-code elimination then removed the types it mentioned.
	$(Q)grep -q 'CustardRuleTest_desc\|CustardRuleTest_sized\|CustardRuleTest_kdesc' \
	  $(PLUGIN_DIR)/CustardRuleTest.c $(PLUGIN_DIR)/CustardRuleTest.h \
	  && { echo "ERROR: the descriptor reached the C output"; exit 1; } || true
	# 40 + 2, added up by the plugin while the extraction was running.
	$(Q)grep -qF '(uint32_t)42U' $(PLUGIN_DIR)/CustardRuleTest.c \
	  || { echo "ERROR: the rule did not fold the descriptor"; exit 1; }
	# Section 36.3: the kernel body was lifted under the name the *descriptor*
	# gave it, not a generated one, and carries the flags the rule asked for.
	$(Q)grep -q 'static uint32_t kernel(uint32_t c, uint32_t tid) {' $(PLUGIN_DIR)/CustardRuleTest.c \
	  || { echo "ERROR: the kernel was not lifted under its own name"; exit 1; }
	$(Q)grep -qF '__attribute__((noinline))' $(PLUGIN_DIR)/CustardRuleTest.c \
	  || { echo "ERROR: the rule's Prologue flag did not reach the C"; exit 1; }
	$(Q)grep -qF '/* kernel kernel, 42 bytes shared */' \
	  $(PLUGIN_DIR)/CustardRuleTest.c \
	  || { echo "ERROR: the rule's Comment flag did not reach the C"; exit 1; }
	# Section 36.2: the runtime entry point nothing in the source calls
	# survived, under the name [@@custard_extern] gave it rather than the
	# mangled one -- which is what a deleted declaration used to produce.
	$(Q)grep -qF 'kpr_kcall' $(PLUGIN_DIR)/CustardRuleTest.c \
	  || { echo "ERROR: the rule's registered root was dropped"; exit 1; }
	$(Q)grep -q 'CustardRuleTest_kcall' $(PLUGIN_DIR)/CustardRuleTest.c \
	  && { echo "ERROR: the extern's target name was not read"; exit 1; } || true
	# Section 36.4: a rule's call is direct, not through a temporary holding
	# the function.  A name is not a computation and ANF must not hoist one.
	$(Q)grep -q '= kpr_kcall;' $(PLUGIN_DIR)/CustardRuleTest.c \
	  && { echo "ERROR: the rule's call went through a function pointer"; \
	       exit 1; } || true
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror \
	  -I$(abspath $(PLUGIN_DIR)) -x c $(PLUGIN_DIR)/CustardRuleTest.c \
	  $(PLUGIN_SRC)/CustardRuleMain.c \
	  -o $(PLUGIN_DIR)/CustardRuleTest.exe
	$(Q)$(PLUGIN_DIR)/CustardRuleTest.exe

# -------------------------------------------------------------- pulse plugin

# Section 12.13: the real thing.  Pulse is 126 F* files in three units, three
# [@@plugin] declarations, four hand-written OCaml realizations and two menhir
# grammars; the three units link into one .cmxs that this compiler loads.
#
# The units are extracted in dependency order and each links against the ones
# before it, so `checker' sees only the compiler, `syntax_extension' sees the
# compiler and `checker', and `extraction' sees only the compiler again --
# it depends on the krml backend and on nothing of Pulse's.
#
# Every module carrying [@@plugin] has to be a --custard_entry of its own
# (section 13.4); pulse/mk/checker.mk's ROOTS line is the authority on which
# those are, and Pulse.Lib.Tactics is the one that is not a unit root already.
#
# --ext fly_deps=false: fly_deps allows only one file on the command line, and
# every one of these units has more than one root.

PULSE       := pulse
PULSE_OUT   := $(OUT)/pulse
PULSE_LIBS  := lib.common lib.core lib.pulse

# One cache per unit, and never one shared between two: Pulse.Main.fsti and
# PulseSyntaxExtension.ASTBuilder.fsti exist in *two* units' trees with
# different contents, so a shared directory silently gives one unit the
# other's interface (section 12.13).
#
# $(1) is the unit, $(2) the extra checked directories it needs.
define pulse_cache
$(PULSE_OUT)/cache.$(1)/.touch:
	$$(Q)rm -rf $$(dir $$@) && mkdir -p $$(dir $$@)
	$$(Q)cp $(ULIB_CHECKED)/* $$(dir $$@)
	$$(Q)cp -f $(FSTARC_CHECKED)/* $$(dir $$@)
	$$(Q)for d in $(2); do cp -f $(PULSE)/build/$$$$d.checked/* $$(dir $$@); done
	$$(Q)touch $$@
endef

$(eval $(call pulse_cache,checker,$(PULSE_LIBS) checker))
$(eval $(call pulse_cache,syntax_extension,$(PULSE_LIBS) checker syntax_extension))
$(eval $(call pulse_cache,extraction,$(PULSE_LIBS) extraction))

# --already_cached '*,' is what makes the cache authoritative: everything is
# taken from a checked file and nothing is rechecked here.  It has to come
# last, since F* keeps only the final setting of the option.
PULSE_FLAGS := --lax --codegen Custard --custard_split \
               --warn_error -321-242-250 \
               --with_fstarc --ext fly_deps=false --already_cached '*,'

pulse-plugin: $(BIN) $(PULSE_OUT)/x.cmxs
	$(call bold_msg, "CUSTARD", "PULSE SMOKE")
	$(Q)rm -rf $(PULSE_OUT)/smoke && mkdir -p $(PULSE_OUT)/smoke
	$(Q)cd $(PULSE) && env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) \
	  --load_cmxs $(abspath $(PULSE_OUT))/x \
	  --cache_checked_modules --cache_dir $(abspath $(PULSE_OUT))/smoke \
	  --include lib/pulse --include lib/core --include lib/common \
	  --include test test/CalcInPulse.fst

# --include $(ULIB_CHECKED): the prelude has to come from stage2 and not from
# the *installed* fstarc/src.checked, which is where --with_fstarc otherwise
# finds Prims and FStar.Pervasives.  Those are the fstarc flavour, and their
# `fstar.prelude'/`fstar.reflection.typing' bundle hashes are not the ones
# Pulse.Main.fsti.checked was written against; the failure is Error 317 with
# no mention of a prelude anywhere.  A copy in the cache does not help: the
# cache is searched *first* and the last hit wins (section 12.13).
$(PULSE_OUT)/checker/.touch: mk/custard.mk $(SPLIT)/.touch \
                             $(PULSE_OUT)/cache.checker/.touch
	$(call bold_msg, "CUSTARD", "PULSE CHECKER")
	$(Q)rm -rf $(dir $@) && mkdir -p $(dir $@)
	$(Q)cd $(PULSE) && env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  $(PULSE_FLAGS) \
	  --include lib/common --include src/checker \
	  --include $(ULIB_CHECKED) \
	  --smtencoding.elim_box true --z3smtopt '(set-option :smt.arith.nl false)' \
	  --cache_dir $(abspath $(PULSE_OUT))/cache.checker \
	  --custard_unit PulseChecker \
	  --custard_link $(abspath $(SPLIT))/fstarc.cui \
	  --custard_entry Pulse.Main --custard_entry Pulse.Lib.Tactics \
	  src/checker/Pulse.Main.fst lib/common/Pulse.Lib.Tactics.fsti \
	  --odir $(abspath $(dir $@))
	$(Q)touch $@

$(PULSE_OUT)/syntax_extension/.touch: mk/custard.mk $(PULSE_OUT)/checker/.touch \
                             $(PULSE_OUT)/cache.syntax_extension/.touch \
                             $(PULSE)/src/syntax_extension/custard-entrypoints.txt
	$(call bold_msg, "CUSTARD", "PULSE SYNTAX")
	$(Q)rm -rf $(dir $@) && mkdir -p $(dir $@)
	$(Q)cd $(PULSE) && env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  $(PULSE_FLAGS) --ext optimize_let_vc \
	  --include lib/common --include src/checker \
	  --include src/syntax_extension --include ../src \
	  --cache_dir $(abspath $(PULSE_OUT))/cache.syntax_extension \
	  --custard_unit PulseSyntaxExtension \
	  --custard_link $(abspath $(SPLIT))/fstarc.cui \
	  --custard_link $(abspath $(PULSE_OUT))/checker/PulseChecker.cui \
	  --custard_entry PulseSyntaxExtension.ASTBuilder \
	  --custard_entry PulseSyntaxExtension.Printing \
	  --custard_entrypoints src/syntax_extension/custard-entrypoints.txt \
	  src/syntax_extension/PulseSyntaxExtension.ASTBuilder.fst \
	  src/syntax_extension/PulseSyntaxExtension.Printing.fst \
	  --odir $(abspath $(dir $@))
	$(Q)touch $@

$(PULSE_OUT)/extraction/.touch: mk/custard.mk $(SPLIT)/.touch \
                             $(PULSE_OUT)/cache.extraction/.touch
	$(call bold_msg, "CUSTARD", "PULSE EXTRACTION")
	$(Q)rm -rf $(dir $@) && mkdir -p $(dir $@)
	$(Q)cd $(PULSE) && env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  $(PULSE_FLAGS) --ext optimize_let_vc \
	  --include src/extraction \
	  --cache_dir $(abspath $(PULSE_OUT))/cache.extraction \
	  --custard_unit PulseExtraction \
	  --custard_link $(abspath $(SPLIT))/fstarc.cui \
	  --custard_entry ExtractPulse --custard_entry ExtractPulseC \
	  --custard_entry ExtractPulseOCaml \
	  src/extraction/ExtractPulse.fst src/extraction/ExtractPulseC.fst \
	  src/extraction/ExtractPulseOCaml.fst \
	  --odir $(abspath $(dir $@))
	$(Q)touch $@

# The three units, the four realizations and the two grammars, in one flat
# directory and one link.  Not a dune project like the compiler's own build:
# this is a .cmxs against an already built library, which is the one shape
# dune has no stanza for.  src/ml-custard overlays src/ml: see the header of the one file it
# holds.  The grammars are inferred against *these* interfaces, exactly as
# the compiler's own are.
PULSE_UNITDIRS := $(PULSE_OUT)/checker $(PULSE_OUT)/syntax_extension \
                  $(PULSE_OUT)/extraction

$(PULSE_OUT)/x.cmxs: mk/custard.mk $(BIN) \
                     $(addsuffix /.touch,$(PULSE_UNITDIRS)) \
                     $(wildcard $(PULSE)/src/ml/*.ml $(PULSE)/src/ml/*.mly) \
                     $(wildcard $(PULSE)/src/ml-custard/*.ml)
	$(call bold_msg, "CUSTARD", "PULSE LINK")
	$(Q)rm -rf $(PULSE_OUT)/link && mkdir -p $(PULSE_OUT)/link
	$(Q)cp $(addsuffix /*.ml,$(PULSE_UNITDIRS)) $(PULSE_OUT)/link/
	$(Q)cp -f --no-preserve=mode $(PULSE)/src/ml/*.ml $(PULSE)/src/ml/*.mly \
	   $(PULSE_OUT)/link/
	$(Q)cp -f --no-preserve=mode $(PULSE)/src/ml-custard/*.ml $(PULSE_OUT)/link/
	$(Q)cd $(PULSE_OUT)/link && for f in \
	     $$($(OCAMLFIND) ocamldep -package $(OCAMLPKGS) -sort *.ml 2>/dev/null); do \
	   $(OCAMLC) -I . $(INCS) -c $$f >/dev/null 2>&1 || true; \
	 done
	# One parser out of two grammars: pulseparser.mly is an extension of
	# the compiler's own, and menhir builds them together.
	$(Q)cd $(PULSE_OUT)/link && \
	   menhir --base Pulse_FStar_Parser --infer-write-query mock.ml \
	     pulseparser.mly FStarC_Parser_Parse.mly 2>/dev/null && \
	   $(OCAMLC) -I . $(INCS) -i mock.ml > reply 2>/dev/null && \
	   menhir --explain --base Pulse_FStar_Parser --infer-read-reply reply \
	     pulseparser.mly FStarC_Parser_Parse.mly 2>/dev/null
	$(Q)cd $(PULSE_OUT)/link && rm -f Pulse_FStar_Parser.mli mock.ml reply *.cm* *.o
	$(Q)cd $(PULSE_OUT)/link && $(OCAMLOPT) -shared -I . $(INCS) \
	   -o x.cmxs $$($(OCAMLFIND) ocamldep -package $(OCAMLPKGS) -sort *.ml) $(FILTER)
	$(Q)cp -f $(PULSE_OUT)/link/x.cmxs $@

clean:
	rm -rf $(OUT)
