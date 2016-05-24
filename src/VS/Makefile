# -*- Makefile -*-

# --------------------------------------------------------------------
ifeq ($(OS),Windows_NT)
RUNTIME =
else
RUNTIME = mono
endif

NUGET=$(RUNTIME) .nuget/NuGet.exe

# --------------------------------------------------------------------
.PHONY: all update-nuget install-packages clean-packages

all: update-nuget install-packages

update-nuget:
	[ -d packages ] || mkdir packages
	$(NUGET) update -self

install-packages:
	[ -d packages ] || $(MAKE) update-nuget
	$(NUGET) restore FStar.sln
	find packages -name '*.exe' -exec chmod +x '{}' ';'

clean-packages:
	rm -r VS/packages