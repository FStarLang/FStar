# Examples for the Pulse protocol libraries in pulse/lib/pulse/lib/protocol:
#   calc  -- verified calculator server: state machine, wire format,
#            Implementation/Endpoint/Driver, temporal properties
#   echo  -- length-prefixed echo server: BufferedTCP (buffering, compaction
#            via Memmove), BufferedStream Layer 1 classifier and Layer 2
#            buffered_stream_endpoint + drive_until_conclusive
#   tftp  -- verified TFTP sender/receiver loops over FileTransfer
SUBDIRS += calc
SUBDIRS += echo
SUBDIRS += tftp

PULSE_ROOT ?= ../../../..
include $(PULSE_ROOT)/mk/test.mk
