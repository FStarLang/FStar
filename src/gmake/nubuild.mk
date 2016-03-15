ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

ifeq ($(OS),Windows_NT)
   NUBUILD_DIR=$(shell readlink -e $(FSTAR_HOME)/.nubuild)
   NUBUILD=$(NUBUILD_DIR)/bin/NuBuild.exe
else
   ifdef USE_NUBUILD
      $(error "NuBuild currently only supports Windows platforms.")
   endif
endif

ifdef USE_NUBUILD
   FSTAR=$(NUBUILD) --quiet FStarVerify $(OTHERFLAGS)
endif
