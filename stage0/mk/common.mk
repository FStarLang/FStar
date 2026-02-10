# This makefile is included from several other makefiles in the tree.

# In some places, we need to compute absolute paths, and in a Cygwin
# enviroment we need Windows-style paths (forward slashes ok, but no
# /cygdrive/).
ifeq ($(OS),Windows_NT)
cygpath=$(shell cygpath -m "$(abspath $(1))")
else
cygpath=$(abspath $(1))
endif

FSTAR_OPTIONS += --ext fly_deps
FSTAR_ARGS += --ext fly_deps
MAKEFLAGS += --no-builtin-rules
Q?=@
SIL?=--silent
RUNLIM=
ifneq ($(V),)
	Q=
	SIL=
else
	MAKEFLAGS += -s
endif

define NO_RUNLIM_ERR
runlim not found:
  To use RESOURCEMONITOR=1, the `runlim` tool must be installed and in your $$PATH.
  It must also be a recent version supporting the `-p` option.
  You can get it from: [https://github.com/arminbiere/runlim]
endef

define msg =
@printf "   %-14s  %s\n" $(1) $(2)
endef
# Must be one line so it can be commented out easily
#-tput bold 2>/dev/null
#-tput sgr0 2>/dev/null
define bold_msg =
printf -- "  %-15s  %s\n" $(1) $(2)
endef

# Passing RESOURCEMONITOR=1 will create .runlim files through the source tree with
# information about the time and space taken by each F* invocation.
ifneq ($(RESOURCEMONITOR),)
	ifeq ($(shell which runlim),)
		_ := $(error $(NO_RUNLIM_ERR))
	endif
	ifneq ($(MONID),)
		MONPREFIX=$(MONID).
	endif
	RUNLIM=runlim -p -o $@.$(MONPREFIX)runlim
endif

# Ensure that any failing rule will not create its target file.
# In other words, make `make` less insane.
.DELETE_ON_ERROR:

.DEFAULT_GOAL:=__undef
.PHONY: __undef
__undef:
	$(error "This makefile does not have a default goal")

# Check that a variable is defined. If not, abort with an (optional) error message.
need =												\
  $(if $(value $(strip $1)),,									\
    $(error Need a value for $(strip $1)$(if $2, ("$(strip $2)"))))

# Check that a variable is defined and pointing to an executable.
# Is there no negation in make...?
# Wew! this was interesting to write. Especially the override part.
need_exe =											\
  $(if $(value $(strip $1)),									\
    $(if $(wildcard $(value $(strip $1))),							\
      $(if $(shell test -x $(value $(strip $1)) && echo 1),					\
        $(eval override $(strip $1):=$(call cygpath,$(value $(strip $1)))),				\
        $(error $(strip $1) ("$(value $(strip $1))") is not executable)),			\
      $(error $(strip $1) ("$(value $(strip $1))") does not exist (cwd = $(CURDIR)))),		\
    $(error Need an executable for $(strip $1)$(if $2, ("$(strip $2)"))))			\

need_file =											\
  $(if $(value $(strip $1)),									\
    $(if $(wildcard $(value $(strip $1))),							\
      $(if $(shell test -f $(value $(strip $1)) && echo 1),					\
        $(eval override $(strip $1):=$(call cygpath,$(value $(strip $1)))),				\
        $(error $(strip $1) ("$(value $(strip $1))") is not executable)),			\
      $(error $(strip $1) ("$(value $(strip $1))") does not exist (cwd = $(CURDIR)))),		\
    $(error Need a file path for $(strip $1)$(if $2, ("$(strip $2)"))))				\

need_dir =											\
  $(if $(value $(strip $1)),									\
    $(if $(wildcard $(value $(strip $1))),							\
      $(if $(shell test -d $(value $(strip $1)) && echo 1),					\
        $(eval override $(strip $1):=$(call cygpath,$(value $(strip $1)))),				\
        $(error $(strip $1) ("$(value $(strip $1))") is not executable)),			\
      $(error $(strip $1) ("$(value $(strip $1))") is not a directory (cwd = $(CURDIR)))),	\
    $(error Need an *existing* directory path for $(strip $1)$(if $2, ("$(strip $2)"))))	\

need_dir_mk =											\
  $(if $(value $(strip $1)),									\
    $(if $(shell mkdir -p $(value $(strip $1)) && echo 1),					\
      $(eval override $(strip $1):=$(call cygpath,$(value $(strip $1)))),				\
      $(error $(strip $1) ("$(value $(strip $1))") is not a directory (mkdir failed, cwd = $(CURDIR)))),	\
    $(error Need a directory path for $(strip $1)$(if $2, ("$(strip $2)"))))			\
