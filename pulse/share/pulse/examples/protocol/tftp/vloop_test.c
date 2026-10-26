/*
 * vloop_test.c — end-to-end test of the *verified* TFTP driver loops.
 *
 * Exercises the extracted, verified FStar/Pulse driver loops `tftp_server_run`
 * (sender) and `tftp_client_run` (receiver) from TFTP_Verified.c — NOT the
 * unverified interop wrappers.  It connects the verified sender to the verified
 * receiver over a SOCK_DGRAM socketpair, transfers a file through the verified
 * stop-and-wait ARQ (indexed DATA blocks + per-block ACKs, terminated by a short
 * final block), and checks that the receiver reconstructed the original bytes.
 *
 * WHY SOCK_DGRAM (vs YMODEM's SOCK_STREAM): TFTP DATA is datagram-delimited (no
 * length field on the wire — its payload length is the enclosing datagram's
 * length).  The verified loops therefore read ONE datagram per `Pulse_Lib_TCP_read`
 * and use the returned length as the frame length.  A SOCK_DGRAM socketpair
 * preserves those message boundaries (one send = one datagram = one recv),
 * realizing the one-datagram-per-read discipline the loops were verified against.
 *
 * The whole data path — framing, the recv/emit codecs, the ACK handshake, the
 * state-machine transitions — is the verified, extracted code in TFTP_Verified.c.
 * The RRQ (filename negotiation) is impl glue outside the modeled state machine,
 * so this our-sender <-> our-receiver test skips it: only the DATA blocks
 * (blocks 1..N) and their ACKs flow through the verified loops, and the file is
 * split into 512-byte blocks with a short final block (nblocks = len/512 + 1).
 */

#include "TFTP_Verified.h"
#include "Pulse_Lib_TCP_runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>

#define TFTP_BLOCK 512
#define TFTP_PKT   516   /* 4-byte header + up to 512 payload */
#define FUEL       100000

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: vloop_test <file>\n");
    return 2;
  }

  /* Read the whole input file (UNPADDED — TFTP blocks are variable length). */
  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror("fopen"); return 1; }
  fseek(in, 0, SEEK_END);
  long flen_l = ftell(in);
  rewind(in);
  if (flen_l < 0) { fclose(in); return 1; }
  size_t flen = (size_t)flen_l;
  uint8_t *infile = malloc(flen ? flen : 1);
  if (!infile) { fclose(in); return 1; }
  if (flen > 0 && fread(infile, 1, flen, in) != flen) { fclose(in); free(infile); return 1; }
  fclose(in);

  /* nblocks = len/512 + 1: blocks 0..nblocks-2 are 512 bytes, block nblocks-1 is
     the short final block (len%512 bytes, possibly 0) that terminates the
     transfer.  Matches the F* server loop's precondition. */
  size_t nblocks = flen / TFTP_BLOCK + 1;
  if (nblocks > 65534) { fprintf(stderr, "file too large for TFTP (>%d blocks)\n", 65534); free(infile); return 1; }

  /* A late final ACK/DATA to an already-closed peer must not raise SIGPIPE. */
  signal(SIGPIPE, SIG_IGN);

  /* SOCK_DGRAM: one send == one datagram == one recv (message boundaries kept). */
  int sv[2];
  if (socketpair(AF_UNIX, SOCK_DGRAM, 0, sv) != 0) { perror("socketpair"); free(infile); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); free(infile); return 1; }

  if (pid == 0) {
    /* ── child: the VERIFIED sender ─────────────────────────────────────── */
    close(sv[1]);
    Pulse_Lib_TCP_channel ch = Pulse_Lib_TCP_channel_of_fd(sv[0]);
    tftp_server_impl srv = new_tftp_server();
    uint8_t *blk    = malloc(TFTP_BLOCK);
    uint8_t *out    = malloc(TFTP_PKT);
    uint8_t *ackbuf = malloc(4);
    uint8_t *tsnf   = malloc(TFTP_PKT);
    tftp_server_run(srv, ch, infile, nblocks, flen, blk, out, ackbuf, tsnf, (size_t)FUEL);
    Pulse_Lib_TCP_close(ch);
    free(blk); free(out); free(ackbuf); free(tsnf); free(infile);
    _exit(0);
  }

  /* ── parent: the VERIFIED receiver ────────────────────────────────────── */
  close(sv[0]);
  Pulse_Lib_TCP_channel ch = Pulse_Lib_TCP_channel_of_fd(sv[1]);
  uint8_t *cli = new_tftp_client();
  tftp_client_start(cli);
  uint8_t *inbuf   = malloc(TFTP_PKT);
  uint8_t *scratch = malloc(TFTP_BLOCK);
  uint8_t *ackout  = malloc(4);
  size_t   outcap  = nblocks * TFTP_BLOCK;      /* >= flen; room for full reassembly */
  uint8_t *outbuf  = calloc(outcap ? outcap : 1, 1);
  size_t nbytes = tftp_client_run(cli, ch, inbuf, scratch, ackout, outbuf, outcap, (size_t)FUEL);
  Pulse_Lib_TCP_close(ch);

  int status = 0;
  waitpid(pid, &status, 0);

  /* Check: the receiver reconstructed the original file exactly (TFTP is
     unpadded, so the reassembly equals the file — no truncation). */
  int ok = (nbytes == flen) && (flen == 0 || memcmp(outbuf, infile, flen) == 0);
  printf("verified-loop transfer: sent %zu block(s), receiver wrote %zu byte(s); content %s\n",
         nblocks, nbytes, ok ? "MATCH" : "DIFFER");

  free(inbuf); free(scratch); free(ackout); free(outbuf); free(infile);
  return ok ? 0 : 1;
}
