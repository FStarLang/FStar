/* C runtime for the extern Pulse.Lib.TCP interface.

   Pulse.Lib.TCP declares an abstract channel/listener API over byte streams.
   This file and Pulse_Lib_TCP_runtime.c implement it over POSIX sockets (see
   pulse_tcp_sockets.{c,h}).  When extracting with KaRaMeL, pass
   `-library Pulse.Lib.TCP -add-include '"Pulse_Lib_TCP_runtime.h"'` so that
   the generated Pulse_Lib_TCP.h picks up the type definitions below, and link
   Pulse_Lib_TCP_runtime.c and pulse_tcp_sockets.c. */

#ifndef PULSE_LIB_TCP_RUNTIME_H
#define PULSE_LIB_TCP_RUNTIME_H

#include <stddef.h>
#include <stdint.h>

typedef struct Pulse_Lib_TCP_channel_s *Pulse_Lib_TCP_channel;
typedef struct Pulse_Lib_TCP_listener_s *Pulse_Lib_TCP_listener;

/* A channel over a single bidirectional file descriptor (e.g. a connected
   socket, or one end of a socketpair). */
Pulse_Lib_TCP_channel Pulse_Lib_TCP_channel_of_fd(int fd);
/* A channel that reads from rfd and writes to wfd (e.g. stdin/stdout). */
Pulse_Lib_TCP_channel Pulse_Lib_TCP_channel_of_fds(int rfd, int wfd);

/* The remaining entry points, with the prototypes KaRaMeL emits for them
   (ghost arguments are erased).  Declared here too so that C harnesses can
   call them even when the verified code does not. */
size_t Pulse_Lib_TCP_read(Pulse_Lib_TCP_channel ch, uint8_t *out, size_t max_len);
size_t Pulse_Lib_TCP_read_full(Pulse_Lib_TCP_channel ch, uint8_t *out, size_t len);
size_t Pulse_Lib_TCP_write(Pulse_Lib_TCP_channel ch, uint8_t *buf, size_t len);
void Pulse_Lib_TCP_close(Pulse_Lib_TCP_channel ch);
void Pulse_Lib_TCP_close_listener(Pulse_Lib_TCP_listener l);

#endif
