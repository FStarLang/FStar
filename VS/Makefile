ifeq ($(OS),Windows_NT)
MONO=./
else
MONO=mono 
endif

NUGET=$(MONO).nuget/NuGet.exe
.PHONY: all update-nuget

all: packages/FsLexYacc.6.0.3/bin/fslex.exe

packages:
	mkdir packages

update-nuget: packages
	$(NUGET) update -self
	$(NUGET) restore FStar.sln

packages/FsLexYacc.6.0.3/bin/fslex.exe: update-nuget
	
