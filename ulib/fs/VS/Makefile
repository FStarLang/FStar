# -*- Makefile -*-

# --------------------------------------------------------------------
MSBUILD = dotnet msbuild

CONFIGURATION?=Release

MSBUILD := $(MSBUILD) /verbosity:minimal /p:Configuration=$(CONFIGURATION)

# --------------------------------------------------------------------
.PHONY: all install-packages

all: install-packages
	$(MSBUILD) UlibFS.sln

install-packages:
	$(MSBUILD) /t:Restore UlibFS.sln

clean:
	$(MSBUILD) /t:clean UlibFS.sln
