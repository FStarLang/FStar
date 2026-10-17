module TFTP.Impl.Server.Plan

(**
  Pure block-plan arithmetic for the IETF TFTP (RFC 1350) *server* endpoint.

  A file `file : Seq.seq U8.t` of `nbytes` bytes is cut into `nblocks` consecutive
  data blocks of AT MOST 512 bytes each, with a SHORT final block (the RFC 1350
  end-of-transfer marker).  Unlike YMODEM (uniform, zero-padded 128-byte blocks),
  a TFTP block is variable length: `block file i` is the i-th chunk

      block file i = Seq.slice file (i*512) (min ((i+1)*512) nbytes)   (i*512 < nbytes)
                   = Seq.empty                                          (otherwise)

  so every block has length <= 512, and choosing `nblocks = nbytes/512 + 1` makes
  the last block strictly shorter than 512 (a 0-byte block when nbytes%512 == 0)
  — exactly what makes the receiver complete on the short final block.

  `blocks_of file lo hi` is the list `[block file lo; …; block file (hi-1)]`.  The
  loop's coupling invariant `loop_coupling` says the ghost ARQ state's
  `tss_sent == blocks_of file 0 cursor` and `tss_pending == blocks_of file cursor
  nblocks`.  This module proves the list/seq facts the loop needs:

    * `block_len`         : every block is <= 512 bytes (an SMTPat), so the plan
      is well-formed (`TP.plan_wf`);
    * `block_slice`       : in range, `block file i` is the concrete file slice
      `file[i*512 .. i*512 + len i]` (the coupling discharge for the copy);
    * `blocks_of_unfold`  : cons at the low end (head/tail);
    * `blocks_of_snoc`    : append at the high end (the send-shift step);
    * `blocks_of_plan_wf` : `TP.plan_wf (blocks_of …)`;
    * `blocks_of_length`  : the list length is the size of the index range;
    * `lemma_send_shift`  : the combined shift the loop discharges after each ACK.

  Everything is ordinary total F*; the Pulse loop calls these lemmas explicitly
  (never relying on SMT to instantiate their quantifiers).  Structural mirror of
  `YModem.Impl.Server.Plan`, adapted from uniform 128-byte blocks to TFTP's
  variable-length (<= 512) blocks with a short final block.
**)

module Seq = FStar.Seq
module L = FStar.List.Tot
module U8 = FStar.UInt8
module TCP = Pulse.Lib.TCP
module Math = FStar.Math.Lemmas

module TP = TFTP.Protocol

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* The i-th (variable-length, <= 512) block of a file: the concrete slice in
   range, otherwise the empty sequence (total).  `lo + 512` (not `(i+1)*512`)
   keeps the slice bounds LINEAR so the definition typechecks without any
   nonlinear-arithmetic help. *)
let block (file:Seq.seq U8.t) (i:nat) : TCP.bytes =
  let lo = i * 512 in
  let n = Seq.length file in
  if lo < n
  then Seq.slice file lo (if lo + 512 <= n then lo + 512 else n)
  else Seq.empty

(* Every block is at most 512 bytes, so `TP.plan_wf` holds unconditionally. *)
let block_len (file:Seq.seq U8.t) (i:nat)
  : Lemma (Seq.length (block file i) <= 512)
          [SMTPat (Seq.length (block file i))]
  = ()

(* The concrete length of the i-th block: `min 512 (len - i*512)`, i.e. exactly
   512 for a full block and the short remainder for the final one (0 when
   `i*512 == len`).  The loop computes `block_len_c` this way at runtime, then
   uses this lemma to identify it with `Seq.length (block …)`. *)
let block_len_eq (file:Seq.seq U8.t) (i:nat)
  : Lemma (requires i * 512 <= Seq.length file)
          (ensures
            Seq.length (block file i) ==
            (let r = Seq.length file - i * 512 in if r < 512 then r else 512))
  = ()

(* With `nblocks == len/512 + 1`, every block index `i < nblocks` starts within
   the file (`i*512 <= len`).  Isolates the (Euclidean-division) nonlinear step
   the loop needs before it can slice out block `i`. *)
let block_offset_le (file:Seq.seq U8.t) (nblocks i:nat)
  : Lemma (requires nblocks == Seq.length file / 512 + 1 /\ i < nblocks)
          (ensures i * 512 <= Seq.length file)
  = let n = Seq.length file in
    Math.lemma_div_mod n 512;                  (* n == 512 * (n/512) + n%512 *)
    Math.swap_mul 512 (n / 512);               (* 512 * (n/512) == (n/512) * 512 *)
    Math.lemma_mult_le_right 512 i (n / 512)   (* i*512 <= (n/512)*512 *)


(* In range, the block is the concrete file slice `file[i*512 .. i*512+len]`
   (Seq.equal, matching the `local_pre_ok` payload obligation).  Holds up to and
   including the boundary `i*512 == length file` (the 0-byte final block). *)
let block_slice (file:Seq.seq U8.t) (i:nat)
  : Lemma (requires i * 512 <= Seq.length file)
          (ensures
            i * 512 + Seq.length (block file i) <= Seq.length file /\
            Seq.equal (block file i)
              (Seq.slice file (i * 512) (i * 512 + Seq.length (block file i))))
  = ()

(* The blocks with indices [lo, hi), consed at the low end. *)
let rec blocks_of (file:Seq.seq U8.t) (lo:nat) (hi:nat)
  : Tot (list TCP.bytes) (decreases (hi - lo)) =
  if lo >= hi then []
  else block file lo :: blocks_of file (lo + 1) hi

(* Empty range. *)
let blocks_of_empty (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (requires hi <= lo) (ensures blocks_of file lo hi == [])
  = ()

(* L1 — cons-unfold at the low end: exposes head and tail. *)
let blocks_of_unfold (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (requires lo < hi)
          (ensures
            blocks_of file lo hi == block file lo :: blocks_of file (lo + 1) hi /\
            Cons? (blocks_of file lo hi) /\
            L.hd (blocks_of file lo hi) == block file lo /\
            L.tl (blocks_of file lo hi) == blocks_of file (lo + 1) hi)
  = ()

(* L2 — snoc at the high end (the send-shift step), by induction on hi - lo. *)
let rec blocks_of_snoc (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (requires lo <= hi)
          (ensures
            blocks_of file lo (hi + 1) ==
            L.append (blocks_of file lo hi) [block file hi])
          (decreases (hi - lo))
  = if lo = hi then begin
      blocks_of_unfold file lo (hi + 1);
      blocks_of_empty file (lo + 1) (hi + 1);
      blocks_of_empty file lo hi
    end
    else begin
      blocks_of_unfold file lo (hi + 1);
      blocks_of_unfold file lo hi;
      blocks_of_snoc file (lo + 1) hi
    end

(* L3 — every block is <= 512 bytes, so the plan is well-formed. *)
let rec blocks_of_plan_wf (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (ensures TP.plan_wf (blocks_of file lo hi))
          (decreases (hi - lo))
  = if lo >= hi then ()
    else blocks_of_plan_wf file (lo + 1) hi

(* L4 — the list length is exactly the size of the index range.  The loop uses
   this to turn the coupling `sent == blocks_of file 0 cursor` into the concrete
   fact `L.length sent == cursor`. *)
let rec blocks_of_length (file:Seq.seq U8.t) (lo hi:nat)
  : Lemma (ensures L.length (blocks_of file lo hi) == (if lo >= hi then 0 else hi - lo))
          (decreases (hi - lo))
  = if lo >= hi then () else blocks_of_length file (lo + 1) hi

(* ── the combined fact the loop discharges at each scheduling point ────────── *)

(* Send-shift: moving the head of `pending` onto the tail of `sent` shifts the
   cursor by one while preserving the `blocks_of` split.  Used after each ACK to
   re-establish the coupling at cursor+1 (the port of YMODEM's `lemma_send_shift`). *)
let lemma_send_shift (file:Seq.seq U8.t) (c nblocks:nat)
  : Lemma (requires c < nblocks)
          (ensures
            Cons? (blocks_of file c nblocks) /\
            L.hd (blocks_of file c nblocks) == block file c /\
            L.tl (blocks_of file c nblocks) == blocks_of file (c + 1) nblocks /\
            L.append (blocks_of file 0 c) [block file c] == blocks_of file 0 (c + 1))
  = blocks_of_unfold file c nblocks;
    blocks_of_snoc file 0 c

(* The whole plan is exactly `blocks_of file 0 nblocks`. *)
let plan_of_file (file:Seq.seq U8.t) (nblocks:nat) : list TCP.bytes =
  blocks_of file 0 nblocks
