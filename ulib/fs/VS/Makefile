# -*- Makefile -*-

# --------------------------------------------------------------------
DOTNET = dotnet

CONFIGURATION?=Release

DOTNET_PARAMS = /verbosity:minimal /p:Configuration=$(CONFIGURATION)

ifndef FSTAR_ULIB_VS_DEST
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
  FSTAR_ULIB_VS_DEST=$(FSTAR_HOME)/nuget
endif

# --------------------------------------------------------------------
.PHONY: all install-packages

all: install-packages
	$(DOTNET) build UlibFS.sln
	$(DOTNET) pack ../ulibfs.fsproj -o $(FSTAR_ULIB_VS_DEST)

install-packages:
	$(DOTNET) restore $(DOTNET_PARAMS) UlibFS.sln

clean:
	$(DOTNET) clean $(DOTNET_PARAMS) UlibFS.sln
