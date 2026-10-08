#include "Pulse_Lib_Memmove_runtime.h"

#include <string.h>

void Pulse_Lib_Memmove_memmove(
    uint8_t *buffer,
    size_t dst_offset,
    size_t src_offset,
    size_t len) {
  memmove(buffer + dst_offset, buffer + src_offset, len);
}
