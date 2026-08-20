# Regression test for the checked-file *location* when no --cache_dir is given.
#
# With no --cache_dir, FStarC.Find.prepend_cache_dir is the identity, so the
# checked-file path produced by FStarC.Parser.Dep.cache_file_name is used
# verbatim as a make target. It must keep the directory of the source file:
# lib/A.fst must yield lib/A.fst.checked, not a bare A.fst.checked in the cwd.
#
# Downstream projects (e.g. EverParse) build their whole tree this way, with
# .checked files sitting next to their sources, so dropping the directory
# silently breaks every rule in their generated .depend.
#
# This test deliberately does NOT include ../Makefile.sub: that harness always
# passes --cache_dir, which is exactly the case we are not testing here.

FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe

# Warning 321 (unexpected checked file) is noise here.
FSTAR = $(FSTAR_EXE) --warn_error -321

check-pos:
	@rm -f deps.mk
	$(FSTAR) --include lib --dep full Test.fst lib/A.fst --output_deps_to deps.mk
	@grep -q '^lib/A\.fst\.checked:' deps.mk || { \
	  echo "FAIL: expected target 'lib/A.fst.checked' in deps.mk; got:"; \
	  grep -E '^[^ 	]*A\.fst\.checked:' deps.mk; \
	  exit 1; }
	@grep -q '^Test\.fst\.checked:' deps.mk || { \
	  echo "FAIL: expected target 'Test.fst.checked' in deps.mk; got:"; \
	  grep -E '^[^ 	]*Test\.fst\.checked:' deps.mk; \
	  exit 1; }
	@echo "checked-file paths keep their source directory"
	@touch $@

clean:
	@rm -f check-pos deps.mk
	@rm -f *.checked lib/*.checked
