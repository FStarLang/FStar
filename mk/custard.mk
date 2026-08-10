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
# The result is a working fstar.exe with two known limitations, both recorded
# in section 12.10: it cannot read .checked files written by a dune-built
# compiler (they are Marshal dumps of differently laid out types), and the
# ulib plugins are still the ML-extracted ones, so anything that needs
# FStar.Tactics.Typeclasses.mk_class fails with "tactic got stuck".

include mk/common.mk

$(call need_exe, FSTAR_EXE, the compiler that runs the extraction)
$(call need_dir, ULIB_CHECKED, checked files for ulib)
$(call need_dir, FSTARC_CHECKED, checked files for src)

OUT     ?= stagec
CACHE   := $(OUT)/cache
SPLIT   := $(OUT)/split
BUILD   := $(OUT)/build
BIN     := $(OUT)/out/bin/fstar.exe

ENTRYFILE := src/custard/entrypoints.txt
# NB: [#] rather than # in the regex; make would take a bare # for a comment.
# The names are double-quoted because some of them end in a prime.
ENTRIES   := $(shell sed -e 's/[#].*//' -e '/^[[:space:]]*$$/d' $(ENTRYFILE) | sed 's/.*/--custard_entry "&"/')

# The realizations, the two grammars and the two sedlex lexers.
# The version stamp is a script that assigns to FStarC.Options' `_version'
# and friends.  Custard mangles a leading underscore to `u__' (section 5.2),
# so the script's output has to be renamed; the dune build's copy is not
# usable as it stands.
VERSION_SH := .scripts/make_fstar_version.sh

REALIZATIONS := $(wildcard src/ml/*.ml)
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

.PHONY: all split build clean smoke

all: $(BIN)

# ---------------------------------------------------------------- extraction

$(CACHE)/.touch: mk/custard.mk
	$(call bold_msg, "CUSTARD", "CACHE")
	$(Q)rm -rf $(CACHE) && mkdir -p $(CACHE)
	$(Q)cp $(ULIB_CHECKED)/* $(CACHE)/
	$(Q)cp -f $(FSTARC_CHECKED)/* $(CACHE)/
	$(Q)touch $@

$(SPLIT)/.touch: mk/custard.mk $(CACHE)/.touch $(ENTRYFILE)
	$(call bold_msg, "CUSTARD", "SPLIT")
	$(Q)rm -rf $(SPLIT) && mkdir -p $(SPLIT)
	$(Q)env FSTAR_LIB=$(abspath ulib) $(FSTAR_EXE) \
	  --lax --codegen Custard --custard_split \
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

clean:
	rm -rf $(OUT)
