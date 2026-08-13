# Build an F* compiler with Custard instead of the ML extraction.
#
# See doc/ref/custard.md, section 12.10.  The pipeline is:
#
#   1. --custard_split the whole compiler, from FStarC.Main.main plus the
#      entry points in src/custard/entrypoints.txt, into one .ml per F*
#      module;
#   2. drop the hand-written realizations of src/ml in beside them;
#   3. generate the two menhir parsers against *these* interfaces, not the
#      ones the ML extraction produced -- the two extractions lay the same F*
#      types out differently, so a parser inferred against the wrong ones is
#      at best accidentally well-typed;
#   4. compile and link, in `ocamldep -sort' order.
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
BUILD   := $(OUT)/build
BIN     := $(OUT)/out/bin/fstar.exe

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

# The generated modules and the realizations sit in one flat directory, which
# is what makes a realization able to call compiled code and vice versa
# (section 12.9).  The realizations win where both exist: a realized module's
# F* definitions are a model (section 8.2, M10j) and Custard does not emit
# them, but FStarC_Version.ml and the like have no F* side at all.
$(BUILD)/.touch: mk/custard.mk $(SPLIT)/.touch $(REALIZATIONS) $(addprefix src/ml/,$(addsuffix .mly,$(GRAMMARS))) $(VERSION_SH) version.txt
	$(call bold_msg, "CUSTARD", "ASSEMBLE")
	$(Q)rm -rf $(BUILD) && mkdir -p $(BUILD)
	$(Q)cp $(SPLIT)/*.ml $(BUILD)/
	$(Q)cp -f --no-preserve=mode src/ml/*.ml src/ml/*.mly $(BUILD)/
	$(Q)cp -f --no-preserve=mode ulib/ml/plugin/*.ml $(BUILD)/
	$(Q)bash $(VERSION_SH) | sed 's/FStarC_Options\._/FStarC_Options.u__/' \
	   > $(BUILD)/FStarC_Version.ml
	$(Q)printf 'let () = FStarC_Main.main ()\n' > $(BUILD)/zzMain.ml
	$(Q)touch $@

# --------------------------------------------------------------- the parsers
#
# menhir infers the types of the grammar's semantic values by compiling a mock
# module against the surrounding code, which is the dune `menhir' stanza's
# --infer.  Doing it here rather than borrowing dune's answer is the whole
# point: the mock has to see *Custard's* FStarC_Parser_AST.
#
# Compiling the mock needs the interfaces of everything the grammar's header
# opens, so there is a first, best-effort pass that compiles as much as it can
# to bytecode -- fast, and .cmi is all that is wanted.  The modules that fail
# are exactly those downstream of the parser, and the final pass compiles
# everything again in order.

$(BUILD)/.parsers: mk/custard.mk $(BUILD)/.touch
	$(call bold_msg, "CUSTARD", "MENHIR")
	$(Q)cd $(BUILD) && for f in $$($(OCAMLFIND) ocamldep -package $(OCAMLPKGS) -sort *.ml 2>/dev/null); do \
	   $(OCAMLC) -I . -c $$f >/dev/null 2>&1 || true; \
	 done
	$(Q)cd $(BUILD) && for g in $(GRAMMARS); do \
	   menhir --infer-write-query $$g.mock.ml $$g.mly 2>/dev/null && \
	   $(OCAMLC) -I . -i $$g.mock.ml > $$g.reply 2>/dev/null && \
	   menhir --explain --infer-read-reply $$g.reply $$g.mly 2>/dev/null; \
	 done
	$(Q)cd $(BUILD) && rm -f *.mock.ml *.reply *.cm* *.o
	# The generated .mli would have to be compiled before its dependencies,
	# which `ocamldep -sort' over .ml files alone cannot arrange.  Nothing
	# here needs the parsers' interfaces narrowed.
	$(Q)cd $(BUILD) && rm -f $(addsuffix .mli, $(GRAMMARS))
	$(Q)touch $@

# ------------------------------------------------------------------- compile

$(BIN): mk/custard.mk $(BUILD)/.parsers
	$(call bold_msg, "CUSTARD", "COMPILE")
	$(Q)mkdir -p $(dir $(BIN))
	$(Q)cd $(BUILD) && $(OCAMLFIND) ocamldep -package $(OCAMLPKGS) -sort *.ml 2>/dev/null \
	   | head -1 > .order
	$(Q)cd $(BUILD) && $(OCAMLOPT) -g -linkpkg -I . -o fstar.exe $$(cat .order) $(FILTER)
	$(Q)cp -f $(BUILD)/fstar.exe $(BIN)

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

plugin: $(BIN)
	$(call bold_msg, "CUSTARD", "PLUGIN")
	$(Q)rm -rf $(PLUGIN_DIR) && mkdir -p $(PLUGIN_DIR)
	$(Q)env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  --cache_checked_modules --cache_dir $(CACHE) \
	  --include src/ --include $(PLUGIN_SRC) --already_cached ',*' \
	  --ext fly_deps=false \
	  --warn_error -321-274-272-241 \
	  $(PLUGIN_SRC)/$(PLUGIN_MOD).fst $(PLUGIN_SRC)/$(PLUGIN_AUX).fst
	# --ext fly_deps=false: fly_deps allows only one file on the command
	# line, and a plugin with two roots has two.
	$(Q)env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  --lax --codegen Custard --custard_unit $(PLUGIN_MOD) \
	  --custard_link $(SPLIT)/fstarc.cui \
	  --custard_entry $(PLUGIN_MOD) --custard_entry $(PLUGIN_AUX) \
	  --ext fly_deps=false \
	  --cache_dir $(CACHE) --include src/ --include $(PLUGIN_SRC) \
	  --already_cached ',*' --warn_error -321-274-272-241 \
	  $(PLUGIN_SRC)/$(PLUGIN_MOD).fst $(PLUGIN_SRC)/$(PLUGIN_AUX).fst \
	  --odir $(PLUGIN_DIR)
	$(Q)cd $(PLUGIN_DIR) && $(OCAMLOPT) -shared \
	  -I $(abspath $(BUILD)) -o $(PLUGIN_MOD).cmxs \
	  $$($(OCAMLFIND) ocamldep -sort *.ml) $(FILTER)
	# The definitions the test reduces are irreducible, so this fails
	# unless the native steps the plugin registered are the ones answering.
	$(Q)env FSTAR_LIB=$(abspath ulib) $(abspath $(BIN)) \
	  --load_cmxs $(abspath $(PLUGIN_DIR))/$(PLUGIN_MOD) \
	  --cache_dir $(PLUGIN_DIR)/cache \
	  --include $(PLUGIN_SRC) $(PLUGIN_SRC)/$(PLUGIN_MOD)Test.fst

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
# directory and one link -- the same shape as $(BUILD), and for the same
# reason.  src/ml-custard overlays src/ml: see the header of the one file it
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
	   $(OCAMLC) -I . -I $(abspath $(BUILD)) -c $$f >/dev/null 2>&1 || true; \
	 done
	# One parser out of two grammars: pulseparser.mly is an extension of
	# the compiler's own, and menhir builds them together.
	$(Q)cd $(PULSE_OUT)/link && \
	   menhir --base Pulse_FStar_Parser --infer-write-query mock.ml \
	     pulseparser.mly FStarC_Parser_Parse.mly 2>/dev/null && \
	   $(OCAMLC) -I . -I $(abspath $(BUILD)) -i mock.ml > reply 2>/dev/null && \
	   menhir --explain --base Pulse_FStar_Parser --infer-read-reply reply \
	     pulseparser.mly FStarC_Parser_Parse.mly 2>/dev/null
	$(Q)cd $(PULSE_OUT)/link && rm -f Pulse_FStar_Parser.mli mock.ml reply *.cm* *.o
	$(Q)cd $(PULSE_OUT)/link && $(OCAMLOPT) -shared -I . -I $(abspath $(BUILD)) \
	   -o x.cmxs $$($(OCAMLFIND) ocamldep -package $(OCAMLPKGS) -sort *.ml) $(FILTER)
	$(Q)cp -f $(PULSE_OUT)/link/x.cmxs $@

clean:
	rm -rf $(OUT)
