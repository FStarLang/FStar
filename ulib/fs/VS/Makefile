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
  #MSBUILD = $(shell which msbuild || (echo '\n\n\033[0;31mWarning:\033[0m could not find "msbuild", trying (deprecated) "xbuild"\n\n'>&2; which xbuild))
  MSBUILD = dotnet msbuild
  UNAME   = $(shell uname -s)
  RUNTIME = mono
endif

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
