# -*- Makefile -*-

# --------------------------------------------------------------------
# Configuration of some platform-specific tools; eventually we will want a configure script

ifeq ($(OS),Windows_NT)
  FSC     = fsc
  MSBUILD = ./msbuild.bat
  UNAME   = Windows_NT
  RUNTIME =
else
  FSC     = fsharpc
  # If can't find msbuild, use xbuild, but throw a warning
  MSBUILD = $(shell which msbuild || (echo '\n\n\033[0;31mWarning:\033[0m could not find "msbuild", trying (deprecated) "xbuild"\n\n'>&2; which xbuild))
  UNAME   = $(shell uname -s)
  RUNTIME = mono
endif

NUGET=$(RUNTIME) .nuget/NuGet.exe

CONFIGURATION?=Release

MSBUILD := $(MSBUILD) /verbosity:minimal /p:Configuration=$(CONFIGURATION)

# --------------------------------------------------------------------
.PHONY: all install-packages

all: install-packages
	$(MSBUILD) UlibFS.sln

install-packages:
	mkdir -p packages
	$(NUGET) restore UlibFS.sln
	find packages -name '*.exe' -exec chmod +x '{}' ';'

clean:
	$(MSBUILD) /t:clean UlibFS.sln
