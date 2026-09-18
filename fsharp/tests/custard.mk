# Section 126.8.  The F# run tests, through Custard.
#
# These used to go through --codegen FSharp and a hand-written .fsproj that
# named one source and referenced ulibfs.fsproj.  Custard's F# backend emits
# its own support library and its own project (section 122), so there is
# nothing left for a hand-written project to say, and the two .fsproj files
# are gone.
#
# Static pattern rules, not implicit ones: mk/test.mk is included first and
# owns $(OUTPUT_DIR)/%.fs, so an implicit rule here would lose to it however
# specific it was.  .fsran has no rule there at all, but the same discipline
# applies to it for the next reader.
#
# A test listed in CUSTARD_FS_RUN must define its own [main]: Custard compiles
# standalone programs, and an entry point is what makes the generated project
# an Exe rather than a Library.  A module initializer is not enough --- .NET
# has no load-time execution for an assembly nobody runs.

DOTNET ?= dotnet
DOTNET10 := $(shell $(DOTNET) --list-sdks 2>/dev/null | grep -c "^1[0-9]\.")

$(patsubst %,$(OUTPUT_DIR)/%.fsout,$(CUSTARD_FS_RUN)): \
  $(OUTPUT_DIR)/%.fsout: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "EXTRACT FS", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)/fs/$*
	$(FSTAR) --codegen Custard --custard_backend FSharp \
	  --custard_main $*.main $*.fst -o $(OUTPUT_DIR)/fs/$*/$*.fs
	@touch $@

$(patsubst %,$(OUTPUT_DIR)/%.fsran,$(CUSTARD_FS_RUN)): \
  $(OUTPUT_DIR)/%.fsran: $(OUTPUT_DIR)/%.fsout
	$(call msg, "RUN (F#)", $(basename $(notdir $@)))
	cd $(OUTPUT_DIR)/fs/$* && \
	  DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_NOLOGO=1 \
	  $(DOTNET) build -c Release -v quiet --nologo >build.log 2>&1 \
	    || { echo "ERROR: $* does not compile as F#"; cat build.log; exit 1; }
	cd $(OUTPUT_DIR)/fs/$* && DOTNET_NOLOGO=1 \
	  $(DOTNET) bin/Release/net10.0/$*.dll
	@touch $@

ifneq ($(DOTNET10),0)
all: $(patsubst %,$(OUTPUT_DIR)/%.fsran,$(CUSTARD_FS_RUN))
else
$(warning no .NET 10 SDK found: skipping the F# run tests)
all: $(patsubst %,$(OUTPUT_DIR)/%.fsout,$(CUSTARD_FS_RUN))
endif
