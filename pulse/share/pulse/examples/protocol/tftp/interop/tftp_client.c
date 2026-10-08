/*
 * tftp_client.c — a TFTP (RFC 1350) read-request CLIENT (receiver) whose
 * data-transfer loop is the VERIFIED, extracted Pulse driver loop
 * `tftp_client_run`.
 *
 * The core receive loop — reading each DATA datagram, extracting its
 * variable-length payload, acknowledging it by block number, reassembling the
 * file, and completing on the short final block — is the verified FStar/Pulse loop
 * extracted to C in TFTP_Verified.c.  This program is the thin, UNVERIFIED glue
 * around it:
 *
 *   1. create a UDP socket (its ephemeral port is the client TID) and send a
 *      Read Request (RRQ) for the file, in octet mode, to the server port (the
 *      RRQ is out-of-model glue — the modeled transfer starts from the local
 *      Client_start event, already fired via tftp_client_start);
 *   2. learn the server's TID by MSG_PEEK'ing the first reply datagram's source
 *      port, then `connect()` the socket to it, so each `Pulse_Lib_TCP_read` is
 *      exactly one datagram from that fixed peer (the one-datagram-per-read
 *      discipline the verified loop was checked against) — the peeked DATA #1
 *      stays queued for the loop to consume;
 *   3. hand the connected channel to `tftp_client_run`, which reassembles the
 *      file, then write the reconstructed bytes out.
 *
 * We request `octet` mode (byte-exact reconstruction) and send no RFC 2347
 * options, so the server replies with DATA #1 directly.
 *
 * Usage:  tftp_client <server_ip> <server_port> <remote_filename> <out_file>
 */

#include "TFTP_Verified.h"
#include "Pulse_Lib_TCP_runtime.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#define TFTP_BLOCK 512
#define TFTP_PKT   516
#define FUEL       1000000
/* Max TFTP transfer: 65535 blocks * 512 bytes.  We do not know the file size in
 * advance (a read request learns it only as DATA arrives), so we size the
 * reconstruction buffer to the protocol maximum. */
#define OUTCAP     (65535u * 512u)

int main(int argc, char **argv) {
  if (argc != 5) {
    fprintf(stderr, "usage: tftp_client <server_ip> <server_port> <remote_filename> <out_file>\n");
    return 2;
  }
  const char *server_ip = argv[1];
  uint16_t port = (uint16_t)atoi(argv[2]);
  const char *remote = argv[3];
  const char *outpath = argv[4];

  /* 1. Create the UDP socket (its port is the client TID) and send the RRQ. */
  int fd = socket(AF_INET, SOCK_DGRAM, 0);
  if (fd < 0) { perror("socket"); return 1; }
  struct sockaddr_in srv;
  memset(&srv, 0, sizeof srv);
  srv.sin_family = AF_INET;
  srv.sin_port = htons(port);
  if (inet_pton(AF_INET, server_ip, &srv.sin_addr) != 1) { fprintf(stderr, "bad server ip\n"); return 1; }

  /* RRQ = 00 01 | filename | 00 | "octet" | 00 */
  uint8_t rrq[1024];
  size_t p = 0;
  rrq[p++] = 0x00; rrq[p++] = 0x01;
  size_t rl = strlen(remote);
  if (p + rl + 1 + 5 + 1 > sizeof rrq) { fprintf(stderr, "filename too long\n"); return 1; }
  memcpy(rrq + p, remote, rl); p += rl; rrq[p++] = 0x00;
  memcpy(rrq + p, "octet", 5);  p += 5;  rrq[p++] = 0x00;
  if (sendto(fd, rrq, p, 0, (struct sockaddr *)&srv, sizeof srv) != (ssize_t)p) {
    perror("sendto RRQ"); return 1;
  }

  /* 2. Learn the server TID from the first reply's source port (peek, don't
     consume), then connect the socket to it. */
  uint8_t peek[TFTP_PKT];
  struct sockaddr_in from;
  socklen_t fl = sizeof from;
  ssize_t pn = recvfrom(fd, peek, sizeof peek, MSG_PEEK, (struct sockaddr *)&from, &fl);
  if (pn < 0) { perror("recvfrom (server reply)"); return 1; }
  /* If the server replied with an ERROR, surface it and stop. */
  if (pn >= 4 && peek[0] == 0x00 && peek[1] == 0x05) {
    fprintf(stderr, "tftp_client: server returned ERROR (code %u)\n", peek[3]);
    return 1;
  }
  if (connect(fd, (struct sockaddr *)&from, fl) != 0) { perror("connect"); return 1; }

  /* 3. Drive the VERIFIED receiver loop over the connected datagram channel. */
  Pulse_Lib_TCP_channel ch = Pulse_Lib_TCP_channel_of_fd(fd);
  uint8_t *cli = new_tftp_client();
  tftp_client_start(cli);
  uint8_t *inbuf   = malloc(TFTP_PKT);
  uint8_t *scratch = malloc(TFTP_BLOCK);
  uint8_t *ackout  = malloc(4);
  size_t   outcap  = OUTCAP;
  uint8_t *outbuf  = malloc(outcap);
  if (!inbuf || !scratch || !ackout || !outbuf) { fprintf(stderr, "oom\n"); return 1; }
  size_t nbytes = tftp_client_run(cli, ch, inbuf, scratch, ackout, outbuf, outcap, (size_t)FUEL);
  Pulse_Lib_TCP_close(ch);

  /* Write the reconstructed file. */
  FILE *of = fopen(outpath, "wb");
  if (!of) { perror("fopen out"); return 1; }
  if (nbytes > 0 && fwrite(outbuf, 1, nbytes, of) != nbytes) { perror("fwrite"); fclose(of); return 1; }
  fclose(of);

  fprintf(stderr, "tftp_client: received %s -> %s (%zu bytes)\n", remote, outpath, nbytes);
  free(inbuf); free(scratch); free(ackout); free(outbuf);
  return 0;
}
