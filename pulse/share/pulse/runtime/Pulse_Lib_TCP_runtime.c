#include "Pulse_Lib_TCP_runtime.h"

#include "pulse_tcp_sockets.h"

#include <stdlib.h>
#include <string.h>

struct Pulse_Lib_TCP_channel_s {
  int rfd;
  int wfd;
};

struct Pulse_Lib_TCP_listener_s {
  int fd;
};

/* connect_tcp, listen_tcp and accept_tcp return an option.  Only its layout
   crosses the boundary with the extracted code, and that layout depends on the
   C backend:
   - KaRaMeL (the default): a uint8_t tag followed by the payload `v`;
   - Custard's direct-to-C backend (--codegen C; compile this file with
     -DPULSE_RUNTIME_CUSTARD_C): an enum tag followed by a union holding the
     payload `Some`.
   In both, None is 0 and Some is 1. */
#define PULSE_OPTION_NONE 0
#define PULSE_OPTION_SOME 1

#ifdef PULSE_RUNTIME_CUSTARD_C
#define PULSE_OPTION_TYPE(name, T)                                          \
  typedef struct name##_s {                                                 \
    enum name##_tags { name##_none = PULSE_OPTION_NONE,                     \
                       name##_some = PULSE_OPTION_SOME } tag;               \
    union {                                                                 \
      T Some;                                                               \
    } val;                                                                  \
  } name
#define PULSE_SOME(name, x) ((name){.tag = PULSE_OPTION_SOME, .val.Some = (x)})
#else
#define PULSE_OPTION_TYPE(name, T)                                          \
  typedef struct name##_s {                                                 \
    uint8_t tag;                                                            \
    T v;                                                                    \
  } name
#define PULSE_SOME(name, x) ((name){.tag = PULSE_OPTION_SOME, .v = (x)})
#endif
#define PULSE_NONE(name) ((name){.tag = PULSE_OPTION_NONE})

PULSE_OPTION_TYPE(option_channel, Pulse_Lib_TCP_channel);
PULSE_OPTION_TYPE(option_listener, Pulse_Lib_TCP_listener);

static Pulse_Lib_TCP_channel pulse_tcp_channel_from_fd(int fd) {
  Pulse_Lib_TCP_channel ch = malloc(sizeof *ch);
  if (ch == NULL) {
    return NULL;
  }
  ch->rfd = fd;
  ch->wfd = fd;
  return ch;
}

Pulse_Lib_TCP_channel Pulse_Lib_TCP_channel_of_fd(int fd) {
  return pulse_tcp_channel_from_fd(fd);
}

/* A channel that reads from one fd and writes to another (e.g. stdin/stdout).
   The single-fd constructors above set rfd == wfd (a bidirectional socket), so
   existing callers are unaffected. */
Pulse_Lib_TCP_channel Pulse_Lib_TCP_channel_of_fds(int rfd, int wfd) {
  Pulse_Lib_TCP_channel ch = malloc(sizeof *ch);
  if (ch == NULL) {
    return NULL;
  }
  ch->rfd = rfd;
  ch->wfd = wfd;
  return ch;
}

static Pulse_Lib_TCP_listener pulse_tcp_listener_from_fd(int fd) {
  Pulse_Lib_TCP_listener l = malloc(sizeof *l);
  if (l == NULL) {
    return NULL;
  }
  l->fd = fd;
  return l;
}

option_channel Pulse_Lib_TCP_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port) {
  if (hostname == NULL || hostname_len == SIZE_MAX) {
    return PULSE_NONE(option_channel);
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return PULSE_NONE(option_channel);
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  int fd = pulse_tcp_connect(host, port);
  free(host);
  if (fd < 0) {
    return PULSE_NONE(option_channel);
  }
  Pulse_Lib_TCP_channel ch = pulse_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)pulse_tcp_close_fd(fd);
    return PULSE_NONE(option_channel);
  }
  return PULSE_SOME(option_channel, ch);
}

option_listener Pulse_Lib_TCP_listen_tcp(
    uint8_t *bind_host,
    size_t bind_host_len,
    uint16_t port) {
  if (bind_host == NULL || bind_host_len == SIZE_MAX) {
    return PULSE_NONE(option_listener);
  }
  char *host = malloc(bind_host_len + 1u);
  if (host == NULL) {
    return PULSE_NONE(option_listener);
  }
  memcpy(host, bind_host, bind_host_len);
  host[bind_host_len] = '\0';
  int fd = pulse_tcp_listen(host, port);
  free(host);
  if (fd < 0) {
    return PULSE_NONE(option_listener);
  }
  Pulse_Lib_TCP_listener l = pulse_tcp_listener_from_fd(fd);
  if (l == NULL) {
    (void)pulse_tcp_close_fd(fd);
    return PULSE_NONE(option_listener);
  }
  return PULSE_SOME(option_listener, l);
}

option_channel Pulse_Lib_TCP_accept_tcp(
    Pulse_Lib_TCP_listener l) {
  if (l == NULL) {
    return PULSE_NONE(option_channel);
  }
  int fd = pulse_tcp_accept(l->fd);
  if (fd < 0) {
    return PULSE_NONE(option_channel);
  }
  Pulse_Lib_TCP_channel ch = pulse_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)pulse_tcp_close_fd(fd);
    return PULSE_NONE(option_channel);
  }
  return PULSE_SOME(option_channel, ch);
}

void Pulse_Lib_TCP_close_listener(Pulse_Lib_TCP_listener l) {
  if (l == NULL) {
    return;
  }
  if (l->fd >= 0) {
    (void)pulse_tcp_close_fd(l->fd);
  }
  free(l);
}

size_t Pulse_Lib_TCP_read(
    Pulse_Lib_TCP_channel ch,
    uint8_t *out,
    size_t max_len) {
  if (ch == NULL) {
    return 0;
  }
  ssize_t n = pulse_tcp_read_fd(ch->rfd, out, max_len);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

size_t Pulse_Lib_TCP_read_full(
    Pulse_Lib_TCP_channel ch,
    uint8_t *out,
    size_t len) {
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = pulse_tcp_read_fd(ch->rfd, out + off, len - off);
    if (n <= 0) {
      return off;
    }
    off += (size_t)n;
  }
  return off;
}

size_t Pulse_Lib_TCP_write(
    Pulse_Lib_TCP_channel ch,
    uint8_t *buf,
    size_t len) {
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = pulse_tcp_write_fd(ch->wfd, buf + off, len - off);
    if (n <= 0) {
      return off;
    }
    off += (size_t)n;
  }
  return off;
}

void Pulse_Lib_TCP_close(Pulse_Lib_TCP_channel ch) {
  if (ch == NULL) {
    return;
  }
  if (ch->rfd >= 0) {
    (void)pulse_tcp_close_fd(ch->rfd);
  }
  if (ch->wfd >= 0 && ch->wfd != ch->rfd) {
    (void)pulse_tcp_close_fd(ch->wfd);
  }
  free(ch);
}
