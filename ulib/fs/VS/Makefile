# -*- Makefile -*-

# --------------------------------------------------------------------
DOTNET = dotnet

CONFIGURATION?=Release

DOTNET_PARAMS = /verbosity:minimal /p:Configuration=$(CONFIGURATION)

# --------------------------------------------------------------------
.PHONY: all install-packages

all: install-packages
	$(DOTNET) build UlibFS.sln
	$(DOTNET) pack ../ulibfs.fsproj -o ../../../nuget/

install-packages:
	$(DOTNET) restore $(DOTNET_PARAMS) UlibFS.sln

clean:
	$(DOTNET) clean $(DOTNET_PARAMS) UlibFS.sln
