#include "Calc_Server.h"

#include <errno.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#define CALC_FRAME_LEN 5
#define CALC_TEST_STEPS 9

struct server_args {
  int fd;
  size_t steps;
  bool ok;
};

static void make_push_request(uint8_t *buf, int32_t value) {
  buf[0] = 0x00;
  buf[1] = (uint8_t)((uint32_t)value >> 24);
  buf[2] = (uint8_t)((uint32_t)value >> 16);
  buf[3] = (uint8_t)((uint32_t)value >> 8);
  buf[4] = (uint8_t)value;
}

static void make_op_request(uint8_t *buf, uint8_t opcode) {
  buf[0] = opcode;
  buf[1] = 0;
  buf[2] = 0;
  buf[3] = 0;
  buf[4] = 0;
}

static int32_t get_int32_be(const uint8_t *buf) {
  return (int32_t)(((uint32_t)buf[1] << 24) |
                   ((uint32_t)buf[2] << 16) |
                   ((uint32_t)buf[3] << 8) |
                   (uint32_t)buf[4]);
}

static bool write_full(int fd, const uint8_t *buf, size_t len) {
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

static bool read_full(int fd, uint8_t *buf, size_t len) {
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

static void *server_thread(void *arg) {
  struct server_args *args = (struct server_args *)arg;
  Pulse_Lib_TCP_channel ch = Pulse_Lib_TCP_channel_of_fd(args->fd);
  if (ch == NULL) {
    close(args->fd);
    return NULL;
  }

  run_channel_endpoint(ch, args->steps);
  args->ok = true;
  return NULL;
}

static bool send_expect_tag(int fd, const uint8_t *request, uint8_t expected_tag) {
  uint8_t response[CALC_FRAME_LEN];
  if (!write_full(fd, request, CALC_FRAME_LEN) ||
      !read_full(fd, response, CALC_FRAME_LEN)) {
    return false;
  }
  return response[0] == expected_tag;
}

static bool send_expect_result(int fd, const uint8_t *request, int32_t expected) {
  uint8_t response[CALC_FRAME_LEN];
  if (!write_full(fd, request, CALC_FRAME_LEN) ||
      !read_full(fd, response, CALC_FRAME_LEN)) {
    return false;
  }
  return response[0] == 0x01 && get_int32_be(response) == expected;
}

int main(void) {
  /* The server end of a connected socket pair is handed to the verified
   * endpoint; the test plays the client on the other end.  No ports are
   * bound, so the test is safe to run in parallel CI jobs. */
  int fds[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, fds) != 0) {
    perror("socketpair");
    return 1;
  }
  int fd = fds[0];
  struct server_args args = {.fd = fds[1], .steps = CALC_TEST_STEPS, .ok = false};

  pthread_t thread;
  if (pthread_create(&thread, NULL, server_thread, &args) != 0) {
    fprintf(stderr, "failed to start server thread\n");
    return 1;
  }

  uint8_t req[CALC_FRAME_LEN];
  bool ok = true;

  make_push_request(req, 42);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_push_request(req, 10);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_op_request(req, 0x02);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_op_request(req, 0x01);
  ok = ok && send_expect_result(fd, req, 52);
  make_push_request(req, 5);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_op_request(req, 0x04);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_push_request(req, 20);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_op_request(req, 0x05);
  ok = ok && send_expect_tag(fd, req, 0x00);
  make_op_request(req, 0x02);
  ok = ok && send_expect_tag(fd, req, 0x02);

  close(fd);
  pthread_join(thread, NULL);

  if (!ok || !args.ok) {
    fprintf(stderr, "calc socket test failed\n");
    return 1;
  }

  printf("calc socket test passed\n");
  return 0;
}
