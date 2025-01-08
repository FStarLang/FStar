# -*- Makefile -*-

# --------------------------------------------------------------------
DOTNET = dotnet

CONFIGURATION?=Release

DOTNET_PARAMS = /verbosity:minimal /p:Configuration=$(CONFIGURATION)

ifndef FSTAR_HOME
  FSTAR_EXE = $(shell which fstar.exe)
  ifdef FSTAR_EXE
    # assuming some ..../bin directory
    FSTAR_HOME=$(dir $(FSTAR_EXE))/..
  else
    # assuming F* source repository
    FSTAR_HOME=../../..
  endif
endif

PREFIX?=$(FSTAR_HOME)


# --------------------------------------------------------------------
.PHONY: all install-packages build

all: build
	$(DOTNET) pack ../ulibfs.fsproj -o $(PREFIX)/nuget

# .NET convention: .dll files go to bin/ instead of lib/fstar
# TODO: in that case, we should rename ulibfs.dll into fstar_ulibfs.dll
# to avoid clashes with other .dll files in bin/ . This is one reason
# why we do not include this rule in `make install`, but only in
# `make package`
build: install-packages
	$(DOTNET) build UlibFS.sln -o $(PREFIX)/bin

install-packages:
	$(DOTNET) restore $(DOTNET_PARAMS) UlibFS.sln

clean:
	$(DOTNET) clean $(DOTNET_PARAMS) UlibFS.sln
