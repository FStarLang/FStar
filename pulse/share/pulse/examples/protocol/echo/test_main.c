/* Self-checking test for the verified echo servers (see impl/Echo.Server.fst).
 *
 * Each scenario creates a fresh AF_UNIX socketpair (no ports are bound),
 * hands one end to a verified server running in a thread, and plays the
 * client on the other end in plain C.  The client sends length-prefixed
 * frames (2-byte big-endian length L, 1 <= L <= 256, then L bytes) and checks
 * the echoes byte for byte, as well as the server's final report.
 *
 * Frames are deliberately split across writes, and several frames (including
 * more than the 300-byte receive buffer) are packed into single writes, so
 * the server exercises append-reads, buffer-full reads and compaction.
 * Every scenario is run against both servers:
 *   - echo_session_direct   (Layer-1 classifier, hand-written loop)
 *   - echo_session_endpoint (Layer-2 buffered_stream_endpoint + driver)
 */
#include "Echo_Verified.h"

#include <errno.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#define MAX_PAYLOAD 256
#define ENDPOINT_FUEL ((size_t)1000000)
#define BUF_CAP 65536

/* ------------------------------------------------------------------ */
/* Server thread                                                      */
/* ------------------------------------------------------------------ */

enum server_kind { SERVER_DIRECT = 0, SERVER_ENDPOINT = 1 };

struct server_args {
  int fd;
  enum server_kind kind;
  echo_report report;
  bool ok;
};

static void *server_thread(void *arg) {
  struct server_args *args = (struct server_args *)arg;
  Pulse_Lib_TCP_channel ch = Pulse_Lib_TCP_channel_of_fd(args->fd);
  if (ch == NULL) {
    close(args->fd);
    return NULL;
  }
  /* The session closes the channel (and its fd) when it returns. */
  if (args->kind == SERVER_DIRECT) {
    args->report = echo_session_direct(ch);
  } else {
    args->report = echo_session_endpoint(ch, ENDPOINT_FUEL);
  }
  args->ok = true;
  return NULL;
}

/* ------------------------------------------------------------------ */
/* Client helpers                                                     */
/* ------------------------------------------------------------------ */

static bool write_all(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, buf + off, len - off);
    if (n < 0 && errno == EINTR) {
      continue;
    }
    if (n <= 0) {
      return false;
    }
    off += (size_t)n;
  }
  return true;
}

static bool read_exact(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = read(fd, buf + off, len - off);
    if (n < 0 && errno == EINTR) {
      continue;
    }
    if (n <= 0) {
      return false;
    }
    off += (size_t)n;
  }
  return true;
}

/* True iff the peer has closed and there are no further bytes. */
static bool expect_eof(int fd) {
  uint8_t b;
  for (;;) {
    ssize_t n = read(fd, &b, 1);
    if (n < 0 && errno == EINTR) {
      continue;
    }
    return n == 0;
  }
}

/* A growable byte string. */
struct bytes {
  uint8_t data[BUF_CAP];
  size_t len;
};

/* Append a well-formed frame with a deterministic payload; returns its size. */
static size_t add_frame(struct bytes *b, size_t payload_len, uint8_t seed) {
  b->data[b->len++] = (uint8_t)(payload_len >> 8);
  b->data[b->len++] = (uint8_t)payload_len;
  for (size_t i = 0; i < payload_len; i++) {
    b->data[b->len++] = (uint8_t)(seed + 7 * i);
  }
  return payload_len + 2;
}

static void add_raw(struct bytes *b, const uint8_t *raw, size_t len) {
  memcpy(b->data + b->len, raw, len);
  b->len += len;
}

/* Send b[from, to), optionally pausing so the server sees a partial read. */
static bool send_range(int fd, const struct bytes *b, size_t from, size_t to,
                       bool pause) {
  if (!write_all(fd, b->data + from, to - from)) {
    return false;
  }
  if (pause) {
    usleep(20000);
  }
  return true;
}

/* Read [len] echoed bytes and compare them with b[from, from+len). */
static bool check_echo(int fd, const struct bytes *b, size_t from, size_t len,
                       const char *what) {
  static uint8_t got[BUF_CAP];
  if (!read_exact(fd, got, len)) {
    fprintf(stderr, "  %s: short echo\n", what);
    return false;
  }
  if (memcmp(got, b->data + from, len) != 0) {
    fprintf(stderr, "  %s: echo mismatch\n", what);
    return false;
  }
  return true;
}

/* ------------------------------------------------------------------ */
/* Scenarios                                                          */
/* ------------------------------------------------------------------ */

/* A session that ends with the client closing its write side. */
static bool scenario_normal(int fd, uint64_t *frames) {
  static struct bytes out;
  out.len = 0;
  size_t start, mid;
  bool ok = true;
  *frames = 0;

  /* 1. one frame, one write */
  start = out.len;
  add_frame(&out, 5, 'h');
  (*frames)++;
  ok = ok && send_range(fd, &out, start, out.len, false);
  ok = ok && check_echo(fd, &out, start, out.len - start, "single frame");

  /* 2. one frame split inside the header and inside the payload */
  start = out.len;
  add_frame(&out, 40, 1);
  (*frames)++;
  ok = ok && send_range(fd, &out, start, start + 1, true);
  ok = ok && send_range(fd, &out, start + 1, start + 12, true);
  ok = ok && send_range(fd, &out, start + 12, out.len, false);
  ok = ok && check_echo(fd, &out, start, out.len - start, "split frame");

  /* 3. several frames plus half a frame in one write, then the rest */
  start = out.len;
  add_frame(&out, 3, 2);
  add_frame(&out, 1, 3);
  add_frame(&out, 100, 4);
  mid = out.len + 50;
  add_frame(&out, 200, 5);
  *frames += 4;
  ok = ok && send_range(fd, &out, start, mid, true);
  ok = ok && send_range(fd, &out, mid, out.len, false);
  ok = ok && check_echo(fd, &out, start, out.len - start, "packed frames");

  /* 4. more than the 300-byte receive buffer in one write, including a
        maximal (256-byte payload) frame */
  start = out.len;
  add_frame(&out, 100, 6);
  add_frame(&out, MAX_PAYLOAD, 7);
  add_frame(&out, MAX_PAYLOAD, 8);
  *frames += 3;
  ok = ok && send_range(fd, &out, start, out.len, false);
  ok = ok && check_echo(fd, &out, start, out.len - start, "buffer-sized write");

  /* 5. a burst of many frames of varied sizes in one write */
  start = out.len;
  for (size_t i = 0; i < 60; i++) {
    add_frame(&out, 1 + (i * 37) % MAX_PAYLOAD, (uint8_t)(9 + i));
  }
  *frames += 60;
  ok = ok && send_range(fd, &out, start, out.len, false);
  ok = ok && check_echo(fd, &out, start, out.len - start, "burst");

  /* Close our write side: the server sees EOF between frames. */
  shutdown(fd, SHUT_WR);
  ok = ok && expect_eof(fd);
  return ok;
}

/* Two good frames followed by a malformed header (length [bad_len]). */
static bool scenario_malformed(int fd, uint16_t bad_len) {
  static struct bytes out;
  out.len = 0;
  bool ok = true;
  add_frame(&out, 10, 20);
  add_frame(&out, 20, 21);
  size_t good = out.len;
  uint8_t bad[4] = {(uint8_t)(bad_len >> 8), (uint8_t)bad_len, 0xAA, 0xBB};
  add_raw(&out, bad, sizeof bad);
  ok = ok && send_range(fd, &out, 0, out.len, false);
  /* Exactly the good frames come back, then the server hangs up. */
  ok = ok && check_echo(fd, &out, 0, good, "frames before malformed");
  ok = ok && expect_eof(fd);
  return ok;
}

/* One good frame, then EOF in the middle of the next frame. */
static bool scenario_eof_mid_frame(int fd) {
  static struct bytes out;
  out.len = 0;
  bool ok = true;
  add_frame(&out, 10, 30);
  size_t good = out.len;
  add_frame(&out, 50, 31);
  ok = ok && send_range(fd, &out, 0, good + 20, false);
  ok = ok && check_echo(fd, &out, 0, good, "frame before EOF");
  shutdown(fd, SHUT_WR);
  ok = ok && expect_eof(fd);
  return ok;
}

enum scenario { NORMAL, MALFORMED_ZERO, MALFORMED_LONG, EOF_MID_FRAME };

static const char *scenario_name(enum scenario s) {
  switch (s) {
  case NORMAL: return "normal";
  case MALFORMED_ZERO: return "malformed (L=0)";
  case MALFORMED_LONG: return "malformed (L=257)";
  default: return "EOF mid-frame";
  }
}

static bool run(enum server_kind kind, enum scenario s) {
  int fds[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, fds) != 0) {
    perror("socketpair");
    return false;
  }
  struct server_args args = {.fd = fds[1], .kind = kind, .ok = false};
  pthread_t thread;
  if (pthread_create(&thread, NULL, server_thread, &args) != 0) {
    fprintf(stderr, "failed to start server thread\n");
    close(fds[0]);
    close(fds[1]);
    return false;
  }

  int fd = fds[0];
  bool ok;
  uint64_t expected_frames;
  echo_status expected_status;
  switch (s) {
  case NORMAL:
    ok = scenario_normal(fd, &expected_frames);
    expected_status = EchoClosed;
    break;
  case MALFORMED_ZERO:
    ok = scenario_malformed(fd, 0);
    expected_frames = 2;
    expected_status = EchoMalformed;
    break;
  case MALFORMED_LONG:
    ok = scenario_malformed(fd, MAX_PAYLOAD + 1);
    expected_frames = 2;
    expected_status = EchoMalformed;
    break;
  default:
    ok = scenario_eof_mid_frame(fd);
    expected_frames = 1;
    expected_status = EchoClosed;
    break;
  }
  /* Make sure the server terminates even if a check failed early. */
  shutdown(fd, SHUT_RDWR);
  pthread_join(thread, NULL);
  close(fd);

  const char *server = kind == SERVER_DIRECT ? "direct" : "endpoint";
  if (!args.ok) {
    fprintf(stderr, "[%s] %s: server did not finish\n", server, scenario_name(s));
    return false;
  }
  if (args.report.frames != expected_frames ||
      args.report.status != expected_status) {
    fprintf(stderr,
            "[%s] %s: report frames=%llu status=%u, expected frames=%llu status=%u\n",
            server, scenario_name(s),
            (unsigned long long)args.report.frames, (unsigned)args.report.status,
            (unsigned long long)expected_frames, (unsigned)expected_status);
    ok = false;
  }
  printf("[%s] %-18s frames=%llu %s\n", server, scenario_name(s),
         (unsigned long long)args.report.frames, ok ? "ok" : "FAILED");
  return ok;
}

int main(void) {
  alarm(60); /* never hang a CI job */
  bool ok = true;
  enum server_kind kinds[] = {SERVER_DIRECT, SERVER_ENDPOINT};
  enum scenario scenarios[] = {NORMAL, MALFORMED_ZERO, MALFORMED_LONG, EOF_MID_FRAME};
  for (size_t k = 0; k < 2; k++) {
    for (size_t s = 0; s < 4; s++) {
      ok = run(kinds[k], scenarios[s]) && ok;
    }
  }
  if (!ok) {
    fprintf(stderr, "echo socket test failed\n");
    return 1;
  }
  printf("echo socket test passed\n");
  return 0;
}
