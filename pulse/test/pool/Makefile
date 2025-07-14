PULSE_ROOT ?= ../..

SUBDIRS += pulse_task
ifeq ($(PULSE_NO_DOMAINSLIB),)
SUBDIRS += domainslib
endif

include $(PULSE_ROOT)/mk/test.mk
