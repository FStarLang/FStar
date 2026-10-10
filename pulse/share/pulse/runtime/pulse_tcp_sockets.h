#ifndef PULSE_TCP_SOCKETS_H
#define PULSE_TCP_SOCKETS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>

int pulse_tcp_connect(const char *hostname, uint16_t port);

int pulse_tcp_listen(const char *bind_host, uint16_t port);

int pulse_tcp_accept(int listener_fd);

ssize_t pulse_tcp_read_fd(int fd, uint8_t *out, size_t max_len);

ssize_t pulse_tcp_write_fd(int fd, const uint8_t *buf, size_t len);

int pulse_tcp_close_fd(int fd);

#endif
