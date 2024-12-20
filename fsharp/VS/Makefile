FSTAR_ROOT ?= ../..

# -*- Makefile -*-

# --------------------------------------------------------------------
DOTNET = dotnet

CONFIGURATION?=Release

DOTNET_PARAMS = /verbosity:minimal /p:Configuration=$(CONFIGURATION)

PREFIX?=$(FSTAR_ROOT)

# --------------------------------------------------------------------
.PHONY: all install-packages build

all: build
	$(DOTNET) pack ../ulibfs.fsproj -o $(PREFIX)/fsharp/nuget

# .NET convention: .dll files go to bin/ instead of lib/fstar
# TODO: in that case, we should rename ulibfs.dll into fstar_ulibfs.dll
# to avoid clashes with other .dll files in bin/ . This is one reason
# why we do not include this rule in `make install`, but only in
# `make package`
build: install-packages
	$(DOTNET) build UlibFS.sln -o $(PREFIX)/fsharp/bin

install-packages:
	$(DOTNET) restore $(DOTNET_PARAMS) UlibFS.sln

clean:
	$(DOTNET) clean $(DOTNET_PARAMS) UlibFS.sln
