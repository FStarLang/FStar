/* C runtime for the extern Pulse.Lib.Memmove interface: an in-place,
   possibly overlapping, byte move within one array. */
#ifndef PULSE_LIB_MEMMOVE_RUNTIME_H
#define PULSE_LIB_MEMMOVE_RUNTIME_H

#include <stddef.h>
#include <stdint.h>

void Pulse_Lib_Memmove_memmove(
    uint8_t *buffer,
    size_t dst_offset,
    size_t src_offset,
    size_t len);

#endif
