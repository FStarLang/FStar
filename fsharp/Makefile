FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/common.mk

.PHONY: all lib test clean

all: lib test

lib:
	@test -d extracted && test -n "$$(ls extracted/ 2>/dev/null)" \
	  || { echo "ERROR: fsharp/extracted/ is empty. Run 'make lib-fsharp.src' from the top level first."; exit 1; }
	$(call msg, "BUILD", "ULIBFS")
	dotnet build ulibfs.fsproj --nologo -v q

test: lib
	+$(MAKE) -C tests all

clean:
	rm -rf bin obj
	+$(MAKE) -C tests clean
