# -*- Makefile -*-
include Makefile.config
export FSTAR_HOME # because of the recursive calls to `make`

FSLYDIR := VS/packages/FsLexYacc.6.1.0
FSYACC  := $(RUNTIME) $(FSLYDIR)/build/fsyacc.exe
FSLEX   := $(RUNTIME) $(FSLYDIR)/build/fslex.exe

# --------------------------------------------------------------------
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

.PHONY: fstar-in-fsharp clean boot ocaml nuget-restore nuget-clean

# --------------------------------------------------------------------
# An artefact of the build process is that parse.fsi is auto-generated
fstar-in-fsharp: nuget-restore
	+$(MAKE) -C VS install-packages
	$(MSBUILD) VS/FStar.sln
	$(DOS2UNIX) parser/parse.fsi
	chmod a+x $(BIN)/tests.exe
	chmod a+x $(BIN)/fstar.exe
	chmod a-x $(BIN)/*.dll
	cp $(BIN)/fstar.exe $(BIN)/fstar.fsharp

# SAD! Can't make clean if fslex and fsyacc haven't be restored... what...
clean: clean-ocaml nuget-restore
	$(MSBUILD) /t:clean VS/FStar.sln

# --------------------------------------------------------------------
nuget-restore:
	$(RUNTIME) VS/.nuget/NuGet.exe restore VS/FStar.sln

nuget-clean:
	rm -r VS/packages

$(FSYACC) $(FSLEX): nuget-restore

# --------------------------------------------------------------------
# Bootstrapping in OCaml: The main logic is in Makefile.boot. Here, we
# mainly prepare for bootstrapping by copying and sed'ing a few F#
# files.
# --------------------------------------------------------------------

# All the files that need to be pre-processed

ALL_BOOT=$(addprefix boot/FStar., Util.fsti List.fsti			\
			          Compiler.Bytes.fsti String.fsti	\
			          BigInt.fsti Pprint.fsti		\
			          Parser.Parse.fsti			\
			          Tests.Test.fst \
			          StringBuffer.fsti)

define from_boot_file
	@echo "[BOOT      $(notdir $@)]"
	$(Q)cp $^ $@
	$(Q)$(SED) -i.bak '/\/\/ *JUST *FSHARP */d' $@
	$(Q)$(SED) -i.bak 's,^ *// *IN *F\* *:,,g' $@
	$(Q)rm -f $@.bak
endef

boot/%.fst: basic/boot/%.fs | boot_dir
	$(call from_boot_file)

boot/%.fsti: basic/boot/%.fsi | boot_dir
	$(call from_boot_file)

boot/%.fsti: prettyprint/boot/%.fsi | boot_dir
	$(call from_boot_file)


boot/FStar.Tests.Test.fst: tests/boot/FStar.Tests.Test.fs | boot_dir
	$(call from_boot_file)

# GM: What's going on here?
boot/FStar.Parser.Parse.fsti: parser/parse.fsi | boot_dir
	@echo "[BOOT      $(notdir $@)]"
	$(Q)echo "#light \"off\"" > $@
	$(Q)$(HEAD) -n12 $^ >> $@

boot/FStar.Parser.Parse.fst: parser/parse.fs | boot_dir
	$(call from_boot_file)

boot_dir:
	mkdir -p boot

boot: $(ALL_BOOT)

clean_boot:
	rm -rf .cache.boot
	rm -f .depend
	rm -rf boot

# --------------------------------------------------------------------------------
# Now we have some make targets wrap calls to other makefiles,
# Notably, Makefile.boot, to extract ocaml from the compiler sources
# And ocaml-output/Makefile, to actually build the compiler in OCaml
# --------------------------------------------------------------------------------
ocaml: boot
	$(Q)+$(MAKE) -f Makefile.boot all-ml

boot-ocaml:
	+$(MAKE) -C ocaml-output all

fstar-ocaml: ocaml
	+$(MAKE) boot-ocaml

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml: boot-ocaml
	+$(MAKE) ocaml
	+$(MAKE) boot-ocaml

clean-ocaml: clean_boot
	+$(MAKE) -C ocaml-output clean

# Very aggressive cleaning: remove all extracted files
clean_extracted:
	rm -f ocaml-output/FStar_*.ml

rebuild:
	+$(MAKE) ocaml
	+$(MAKE) -C ../ulib clean_ocaml
	+$(MAKE) -C ocaml-output
	+$(MAKE) -C ../ulib rebuild
# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------

# The regressions to be run with a working F# build of F*
fsharp-unit-tests:
ifeq ($(OS),Windows_NT)
	$(RUNTIME) $(BIN)/tests.exe
else
	@# On Linux, we need to increase the maximum stack size, or we overflow
	ulimit -s unlimited; $(RUNTIME) $(BIN)/tests.exe
endif

fsharp-build-and-test:
	+$(MAKE) fstar-in-fsharp
	+$(MAKE) fsharp-unit-tests

utest:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions

# The first tests have to be performed sequentially (but each one may use some parallelism)
# Adding the F# build and F# tests also here
#   since in the uregressions target it may not be a good idea to override the fstar.exe binary?
utest-prelude: fsharp-build-and-test
	+$(MAKE) boot-ocaml        #build the ocaml-snapshot
	+$(MAKE) clean_extracted   #ensures that there is no leftover from previous extraction
	+$(MAKE) fstar-ocaml       #extract the compiler again and build the result
	+$(MAKE) ocaml-unit-tests  #run the unit tests
	+$(MAKE) .fstarlib

ocaml-unit-tests:
	$(BIN)/tests.exe

# Getting parallelism from this target
uregressions: ulib-extra tutorial utests uexamples

# Getting parallelism from this target as well
# This is a hook for nightly builds (on Linux)
# But, at the moment, it tests the same files as get tested on every push
# We may add more nightly tests here in the future
uregressions-ulong: uregressions

# This is not optimal, since if some dependencies
# of fstarlib change we will not rebuild. However
# simply calling the install-fstar-tactics rule
# will unconditionally reinstall everything,
# which is also not good.
.fstarlib: $(FSTARLIB_DIR)/fstarlib.cmxs
	touch $@

$(FSTARLIB_DIR)/fstarlib.cmxs:
	+$(MAKE) -C ../ulib/ml
	+$(MAKE) -C ../ulib install-fstar-tactics
	+$(MAKE) -C ../ulib

ulib-extra:
	+$(MAKE) -C ../ulib extra

tutorial: .fstarlib
	+$(MAKE) -C ../doc/tutorial regressions

utests: .fstarlib
	+$(MAKE) -C ../tests all

uexamples: .fstarlib
	+$(MAKE) -C ../examples all
	+$(MAKE) -C ../examples native_tactics.all
	+$(MAKE) -C ../examples semiring.all

ulong:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions-ulong

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .

