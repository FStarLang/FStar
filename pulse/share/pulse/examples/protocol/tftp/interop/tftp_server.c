/*
 * tftp_server.c — a TFTP (RFC 1350) read-request SERVER whose data-transfer loop
 * is the VERIFIED, extracted Pulse driver loop `tftp_server_run`.
 *
 * The core send loop — framing each variable-length DATA block through the
 * verified codec with the correct incrementing 16-bit block number, awaiting
 * each ACK, and terminating with the short final block — is the verified
 * FStar/Pulse loop extracted to C in TFTP_Verified.c.  This program is the thin,
 * UNVERIFIED glue around it:
 *
 *   1. bind a UDP socket to the server port and receive the client's Read
 *      Request (RRQ), parsing the requested filename (the RRQ is out-of-model
 *      glue — the modeled transfer starts from the local Server_start event);
 *   2. open that file under the served root and read it into memory;
 *   3. perform the TFTP TID (transfer-ID) dance: reply from a FRESH ephemeral
 *      UDP port (the server TID), `connect()`ed to the client's source port
 *      (the client TID), so each `Pulse_Lib_TCP_read`/`write` is exactly one
 *      datagram to/from that fixed peer — the one-datagram-per-read discipline
 *      the verified loop was checked against;
 *   4. hand the connected channel to `tftp_server_run`, which serves the file.
 *
 * We serve `octet` mode only (byte-exact, so the receiver reconstructs the file
 * exactly); the RRQ mode field is parsed but not honoured (netascii/mail are not
 * supported).  RFC 2347 options, if present, are ignored: we send DATA #1
 * directly (no OACK), so an options-requesting client falls back to defaults.
 *
 * Usage:  tftp_server <bind_port> <served_root_dir>
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
#include <sys/stat.h>
#include <unistd.h>

#define TFTP_BLOCK 512
#define TFTP_PKT   516
#define FUEL       1000000
#define RRQ_MAX    2048

/* Read a whole file into a freshly malloc'd buffer; sets *out_len. */
static uint8_t *read_file(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  rewind(f);
  if (n < 0) { fclose(f); return NULL; }
  uint8_t *buf = malloc((size_t)n ? (size_t)n : 1);
  if (!buf) { fclose(f); return NULL; }
  if (n > 0 && fread(buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(buf); return NULL; }
  fclose(f);
  *out_len = (size_t)n;
  return buf;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: tftp_server <bind_port> <served_root_dir>\n");
    return 2;
  }
  uint16_t port = (uint16_t)atoi(argv[1]);
  const char *root = argv[2];

  /* 1. Bind a UDP socket on the well-known server port and receive the RRQ. */
  int lfd = socket(AF_INET, SOCK_DGRAM, 0);
  if (lfd < 0) { perror("socket"); return 1; }
  int one = 1;
  setsockopt(lfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in bind_addr;
  memset(&bind_addr, 0, sizeof bind_addr);
  bind_addr.sin_family = AF_INET;
  bind_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  bind_addr.sin_port = htons(port);
  if (bind(lfd, (struct sockaddr *)&bind_addr, sizeof bind_addr) != 0) { perror("bind"); return 1; }

  uint8_t rrq[RRQ_MAX];
  struct sockaddr_in client;
  socklen_t clen = sizeof client;
  ssize_t rn = recvfrom(lfd, rrq, sizeof rrq, 0, (struct sockaddr *)&client, &clen);
  if (rn < 4) { fprintf(stderr, "short/absent RRQ\n"); return 1; }
  /* opcode 1 == RRQ; filename is the first NUL-terminated string after it. */
  if (!(rrq[0] == 0x00 && rrq[1] == 0x01)) { fprintf(stderr, "not an RRQ (opcode %u%u)\n", rrq[0], rrq[1]); return 1; }
  size_t fi = 2;
  while (fi < (size_t)rn && rrq[fi] != 0x00) fi++;
  if (fi >= (size_t)rn) { fprintf(stderr, "malformed RRQ filename\n"); return 1; }
  char fname[1024];
  size_t flen_name = fi - 2;
  if (flen_name >= sizeof fname) { fprintf(stderr, "filename too long\n"); return 1; }
  memcpy(fname, rrq + 2, flen_name);
  fname[flen_name] = '\0';

  /* 2. Open the requested file under the served root and read it in. */
  char path[2048];
  snprintf(path, sizeof path, "%s/%s", root, fname);
  size_t filelen = 0;
  uint8_t *infile = read_file(path, &filelen);
  if (!infile) {
    /* File not found: send a minimal ERROR (code 1) and exit. */
    uint8_t err[] = {0x00, 0x05, 0x00, 0x01, 0x00};
    (void)sendto(lfd, err, sizeof err, 0, (struct sockaddr *)&client, clen);
    fprintf(stderr, "cannot open %s: %s\n", path, strerror(errno));
    return 1;
  }
  size_t nblocks = filelen / TFTP_BLOCK + 1;
  if (nblocks > 65534) { fprintf(stderr, "file too large for TFTP\n"); free(infile); return 1; }

  /* 3. TID dance: reply from a FRESH ephemeral port, connected to the client. */
  close(lfd);
  int fd = socket(AF_INET, SOCK_DGRAM, 0);
  if (fd < 0) { perror("socket"); free(infile); return 1; }
  if (connect(fd, (struct sockaddr *)&client, clen) != 0) { perror("connect"); free(infile); return 1; }

  /* 4. Drive the VERIFIED sender loop over the connected datagram channel. */
  Pulse_Lib_TCP_channel ch = Pulse_Lib_TCP_channel_of_fd(fd);
  tftp_server_impl srv = new_tftp_server();
  uint8_t *blk    = malloc(TFTP_BLOCK);
  uint8_t *out    = malloc(TFTP_PKT);
  uint8_t *ackbuf = malloc(4);
  uint8_t *tsnf   = malloc(TFTP_PKT);
  size_t nsent = tftp_server_run(srv, ch, infile, nblocks, filelen, blk, out, ackbuf, tsnf, (size_t)FUEL);
  Pulse_Lib_TCP_close(ch);

  fprintf(stderr, "tftp_server: served %s (%zu bytes, %zu block(s))\n", fname, filelen, nsent);
  free(blk); free(out); free(ackbuf); free(tsnf); free(infile);
  return 0;
}
