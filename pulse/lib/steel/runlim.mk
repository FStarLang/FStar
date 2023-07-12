# Passing RESOURCEMONITOR=1 will create .runlim files through the source tree with
# information about the time and space taken by each F* invocation.
ifneq ($(RESOURCEMONITOR),)
	ifeq ($(shell which runlim),)
		_ := $(error $(NO_RUNLIM_ERR)))
	endif
	ifneq ($(MONID),)
		MONPREFIX=$(MONID).
	endif
	RUNLIM=runlim -p -o $@.$(MONPREFIX)runlim
endif