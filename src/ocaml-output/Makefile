
# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX=$(shell pwd)/fstar
# The string "Madoko" if madoko is installed, something else otherwise.
MADOKO = $(shell madoko --version 2>/dev/null | cut -c -6)

# Detect the GNU utilities
INSTALL_EXEC := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
FIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)
ifdef INSTALL_EXEC
   INSTALL_EXEC := ginstall
else
   INSTALL_EXEC := install
endif

ifeq ($(OS),Windows_NT)
  SCONS = scons.bat
else
  SCONS = scons
endif

# parse MAKEFLAGS to extract out the '-jN' switch, and pass it to scons
SCONSFLAGS=$(filter -j%,$(MAKEFLAGS))

.PHONY: make_fstar
make_fstar:
	$(SCONS) -u $(SCONSFLAGS) --target=ocaml-output

.PHONY: install-compiler-lib
install-compiler-lib: make_fstar
	mkdir -p ../../bin/fstar-compiler-lib/
	$(FIND) -name "*.cmi" -exec cp {} ../../bin/fstar-compiler-lib/ \;
    
all:  install-compiler-lib
    
# always bump version for a release; always bump it when recompiling so that one
# can easily help debugging
VERSION=$(shell head -n 1 ../../version.txt)
ifeq ($(OS),Windows_NT)
  ifeq ($(PROCESSOR_ARCHITECTURE),AMD64)
     PLATFORM=Windows_x64
  else
     PLATFORM=Windows_x86
  endif
else
     PLATFORM=$(shell echo `uname`_`uname -m`)
endif
# ------------------------------------------------------------------------------
# Preparing a release... these targets are not optimized and the Makefile is
# actually used for scripting a bunch of stuff.
# ------------------------------------------------------------------------------

# Copy the contents of $(1) into $(PREFIX)/$(2) while setting the right file
# permissions and creating directories on the fly as needed.
# (JP: the package version of this command is based on git but for OPAM
#  installs we cannot assume the user has git installed.)
install_dir = cd ../../$(1) && find . -type f -exec $(INSTALL_EXEC) -m 644 -D {} $(PREFIX)/$(2)/{} \;

# Install FStar into $(PREFIX) using the standard Unix directory structure.
install: all
        # Install the binary
	$(INSTALL_EXEC) -m 755 -D _build/src/fstar/ml/main.native $(PREFIX)/bin/fstar.exe
        # Then the rest of the static files.
	$(call install_dir,ulib,lib/fstar)
	$(call install_dir,examples,share/fstar/examples)
	$(call install_dir,ucontrib,share/fstar/contrib)
ifeq ($(MADOKO),Madoko)
        # Build the tutorial first
	$(MAKE) -C ../../doc/tutorial
endif
	$(call install_dir,doc/tutorial,share/fstar/tutorial)

NAME=fstar_$(VERSION)_$(PLATFORM)

# the `fexport` function takes a path relative to the top of the F* repo
# and exports the contents of that directory to the $(PREFIX) dir
fexport = cd ../.. && git archive "--format=tar" "--prefix=$(1)/" HEAD:$(1)/ |\
          tar -x -C $(PREFIX)

# Similar, but exports every file instead of only those in version control.
fexport-all = cp -a ../../$(1) $(PREFIX)/$(1)

ifeq ($(OS),Windows_NT)
  Z3_NAME=z3.exe
else
  Z3_NAME=z3
endif
Z3_DIR=$(shell dirname $$(which $(Z3_NAME)))
Z3_LICENSE=$(shell dirname $(Z3_DIR))/LICENSE.txt

.PHONY: ulib
ulib:
	make -C ../../ulib/ml

# Create a zip / tar.gz package of FStar that contains a Z3 binary and
# proper license files.
package: all
	$(MAKE) ulib
        # Clean previous packages.
	rm -f $(NAME).zip $(NAME).tar.gz
	if [ -d "$(PREFIX)" ]; then rm -dfr fstar; fi
        # Install the F* binary
	mkdir -p $(PREFIX)/bin/
	$(INSTALL_EXEC) -m 755 _build/src/fstar/ml/main.native $(PREFIX)/bin/fstar.exe
        # Then the standard library.
	$(call fexport,ulib)
	# Do not provide ml/fs sources, however. From ulib/ml, only
	# preserve Makefile.include
	mv $(PREFIX)/ulib/ml/Makefile.include $(PREFIX)/ulib/ml_Makefile.include
	rm -rf $(PREFIX)/ulib/ml $(PREFIX)/ulib/fs
	mkdir -p $(PREFIX)/ulib/ml
	mv $(PREFIX)/ulib/ml_Makefile.include $(PREFIX)/ulib/ml/Makefile.include
	# Only provide the Makefile suited for verification
	rm -f $(PREFIX)/ulib/Makefile
	mv $(PREFIX)/ulib/Makefile.verify $(PREFIX)/ulib/Makefile
	# Then the rest of the static files.
	$(call fexport,examples)
	$(call fexport,ucontrib)
	$(call fexport,doc/tutorial)
	$(call fexport-all,bin/fstarlib)

ifeq ($(MADOKO),Madoko)
        # Build the tutorial
	$(MAKE) -C fstar/doc/tutorial
else
	@echo " ********** You don't have Madoko installed. Binary package will not include tutorial in html form."
	false
endif
        # Documentation and licenses
	cp ../../README.md ../../INSTALL.md ../../LICENSE ../../LICENSE-fsharp.txt $(PREFIX)
	cp $(Z3_LICENSE) $(PREFIX)/LICENSE-z3.txt

        # Some new things used by examples/Makefile
	mkdir -p $(PREFIX)/src/gmake/
	cp ../../src/gmake/*.mk $(PREFIX)/src/gmake/

	# Z3
ifeq ($(OS),Windows_NT)
	cp $(shell which libgmp-10.dll) $(PREFIX)/bin
	cp $(Z3_DIR)/*.exe $(Z3_DIR)/*.dll $(Z3_DIR)/*.lib $(PREFIX)/bin
	chmod a+x $(PREFIX)/bin/z3.exe $(PREFIX)/bin/*.dll
	zip -r -9 $(NAME).zip fstar
else
	cp $(Z3_DIR)/z3 $(PREFIX)/bin
	tar czf $(NAME).tar.gz fstar
endif


.PHONY: clean
# Clean up all files generated by targets in _this_ Makefile
# Also clean up the standard library
clean:
	$(MAKE) -C ../../ulib clean
	rm -rf _build
	rm -f *.tar.gz *.zip
	rm -f ../../bin/fstar-compiler-lib/*.cm[aiox]
	rm -f ../../bin/fstar-compiler-lib/*.cmx[as]

# Purge (clean + delete *all* automatically generated files)
# if you do this you'll need to run `make ocaml` in `src` to get them back
purge: clean
	rm -f *.ml || true

-include .depend
