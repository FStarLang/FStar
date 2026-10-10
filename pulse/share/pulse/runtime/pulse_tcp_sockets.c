#include "pulse_tcp_sockets.h"

#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>
#include <sys/socket.h>
#include <unistd.h>

int pulse_tcp_connect(const char *hostname, uint16_t port) {
  if (hostname == NULL) {
    errno = EINVAL;
    return -1;
  }

  char port_string[6];
  int n = snprintf(port_string, sizeof port_string, "%u", (unsigned)port);
  if (n < 0 || (size_t)n >= sizeof port_string) {
    errno = EINVAL;
    return -1;
  }

  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;

  struct addrinfo *result = NULL;
  int gai = getaddrinfo(hostname, port_string, &hints, &result);
  if (gai != 0) {
    errno = EHOSTUNREACH;
    return -1;
  }

  int fd = -1;
  for (struct addrinfo *rp = result; rp != NULL; rp = rp->ai_next) {
    fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
    if (fd < 0) {
      continue;
    }
    if (connect(fd, rp->ai_addr, rp->ai_addrlen) == 0) {
      break;
    }
    close(fd);
    fd = -1;
  }
  freeaddrinfo(result);
  return fd;
}

int pulse_tcp_listen(const char *bind_host, uint16_t port) {
  if (bind_host == NULL) {
    errno = EINVAL;
    return -1;
  }

  char port_string[6];
  int n = snprintf(port_string, sizeof port_string, "%u", (unsigned)port);
  if (n < 0 || (size_t)n >= sizeof port_string) {
    errno = EINVAL;
    return -1;
  }

  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  struct addrinfo *result = NULL;
  int gai = getaddrinfo(bind_host[0] == '\0' ? NULL : bind_host, port_string, &hints, &result);
  if (gai != 0) {
    errno = EADDRNOTAVAIL;
    return -1;
  }

  int fd = -1;
  for (struct addrinfo *rp = result; rp != NULL; rp = rp->ai_next) {
    fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
    if (fd < 0) {
      continue;
    }
    int one = 1;
    (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    if (bind(fd, rp->ai_addr, rp->ai_addrlen) == 0 && listen(fd, 1) == 0) {
      break;
    }
    close(fd);
    fd = -1;
  }
  freeaddrinfo(result);
  return fd;
}

/* Default per-socket receive timeout armed on accepted connections.  Without
   one, a client that opens a connection and then goes quiet -- a browser
   pre-connect, or an HTTP/1.1 keep-alive connection parked between requests --
   pins the accepting process inside read() forever.  Override with
   COMMON_TCP_ACCEPT_TIMEOUT_SECS (0 disables the timeout). */
#define COMMON_TCP_ACCEPT_TIMEOUT_SECS 15

static void pulse_tcp_arm_accept_timeout(int fd) {
  long secs = COMMON_TCP_ACCEPT_TIMEOUT_SECS;
  const char *env = getenv("COMMON_TCP_ACCEPT_TIMEOUT_SECS");
  if (env != NULL && *env != '\0') {
    long v = atol(env);
    if (v >= 0) secs = v;
  }
  if (secs <= 0) return;
  struct timeval tv;
  tv.tv_sec = (time_t)secs;
  tv.tv_usec = 0;
  (void)setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
  (void)setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
}

int pulse_tcp_accept(int listener_fd) {
  int fd;
  do {
    fd = accept(listener_fd, NULL, NULL);
  } while (fd < 0 && errno == EINTR);
  if (fd >= 0) pulse_tcp_arm_accept_timeout(fd);
  return fd;
}

ssize_t pulse_tcp_read_fd(int fd, uint8_t *out, size_t max_len) {
  if (max_len != 0 && out == NULL) {
    errno = EINVAL;
    return -1;
  }

  ssize_t n;
  do {
    n = read(fd, out, max_len);
  } while (n < 0 && errno == EINTR);
  /* A receive timeout (armed by pulse_tcp_accept) means the peer has gone
     quiet.  Callers above translate a short read into "no data yet" and retry
     on a fuel budget, so make the timeout TERMINAL: half-close the socket so
     every subsequent read reports a clean end-of-stream immediately and the
     connection is torn down instead of being retried for fuel x timeout. */
  if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
    (void)shutdown(fd, SHUT_RDWR);
  }
  return n;
}

int pulse_tcp_close_fd(int fd) {
  int r;
  do {
    r = close(fd);
  } while (r < 0 && errno == EINTR);
  return r;
}

ssize_t pulse_tcp_write_fd(int fd, const uint8_t *buf, size_t len) {
  if (len != 0 && buf == NULL) {
    errno = EINVAL;
    return -1;
  }

  ssize_t n;
  do {
    n = write(fd, buf, len);
  } while (n < 0 && errno == EINTR);
  return n;
}
