# -*- Makefile -*-

# --------------------------------------------------------------------
ifeq ($(OS),Windows_NT)
RUNTIME =
else
RUNTIME = mono
endif

# --------------------------------------------------------------------
.PHONY: all dotnet-restore

all: dotnet-restore

dotnet-restore:
	dotnet tool restore
	dotnet paket install
	dotnet restore fstar.sln
