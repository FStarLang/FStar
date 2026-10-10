#include "Pulse_Lib_TCP_runtime.h"

#include "pulse_tcp_sockets.h"

#include <stdlib.h>
#include <string.h>

#ifndef FStar_Pervasives_Native_None
#define FStar_Pervasives_Native_None 0
#endif

#ifndef FStar_Pervasives_Native_Some
#define FStar_Pervasives_Native_Some 1
#endif

struct Pulse_Lib_TCP_channel_s {
  int rfd;
  int wfd;
};

struct Pulse_Lib_TCP_listener_s {
  int fd;
};

typedef struct FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel_s {
  uint8_t tag;
  Pulse_Lib_TCP_channel v;
} FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel;

typedef struct FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener_s {
  uint8_t tag;
  Pulse_Lib_TCP_listener v;
} FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener;

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

FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel Pulse_Lib_TCP_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port) {
  if (hostname == NULL || hostname_len == SIZE_MAX) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  int fd = pulse_tcp_connect(host, port);
  free(host);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  Pulse_Lib_TCP_channel ch = pulse_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)pulse_tcp_close_fd(fd);
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
}

FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener Pulse_Lib_TCP_listen_tcp(
    uint8_t *bind_host,
    size_t bind_host_len,
    uint16_t port) {
  if (bind_host == NULL || bind_host_len == SIZE_MAX) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(bind_host_len + 1u);
  if (host == NULL) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, bind_host, bind_host_len);
  host[bind_host_len] = '\0';
  int fd = pulse_tcp_listen(host, port);
  free(host);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  Pulse_Lib_TCP_listener l = pulse_tcp_listener_from_fd(fd);
  if (l == NULL) {
    (void)pulse_tcp_close_fd(fd);
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_listener){
      .tag = FStar_Pervasives_Native_Some,
      .v = l,
  };
}

FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel Pulse_Lib_TCP_accept_tcp(
    Pulse_Lib_TCP_listener l) {
  if (l == NULL) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  int fd = pulse_tcp_accept(l->fd);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  Pulse_Lib_TCP_channel ch = pulse_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)pulse_tcp_close_fd(fd);
    return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__Pulse_Lib_TCP_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
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
