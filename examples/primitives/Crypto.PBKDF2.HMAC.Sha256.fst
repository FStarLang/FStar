module Crypto.PBKDF2.HMAC.Sha256

open FStar.SBytes
open SBuffer
open FStar.Heap
open FStar.UInt8
open Crypto.HMAC.Sha256


#set-options "--lax"


let mac = hmac_sha256
let hl = 32


val pbkdf2_inner_F : (f        :sbytes) ->
                     (ti       :sbytes { length ti = hl /\ Disjoint f ti }) ->
                     (i        :ref nat) ->
                     (password :sbytes { Disjoint password f /\ Disjoint password ti }) ->
                     (passwdlen :nat { length password = passwdlen }) ->
                     (salt     :sbytes { Disjoint salt f /\ Disjoint salt ti /\ Disjoint salt password }) ->
                     (saltlen  :nat { length salt = saltlen }) ->
                     (c        :nat) ->
                     (ghost_hl :nat { length ti = ghost_hl /\ length f = ghost_hl })
                     -> ST unit
                          (requires (fun h -> Live h f /\ Live h ti /\ Live h password /\ Live h salt))
                          (ensures  (fun h0 r h1 -> Live h1 f /\ Live h1 ti /\ Live h1 password /\ Live h1 salt))
let rec pbkdf2_inner_F f ti i password passwdlen salt saltlen c hl =
  if !i = 1 then begin
    let _pos = !i in
    let _wlen = saltlen + (hl/8) in
    let _i = create #8 FStar.UInt8.zero 4 in
    FStar.SBytes.sbytes_of_uint32 _i (FStar.UInt32.of_int _pos);
    let _w = create #8 FStar.UInt8.zero _wlen in
    FStar.SBytes.blit salt 0 _w 0 saltlen;
    FStar.SBytes.blit _i 0 _w saltlen 4;
    mac ti _w _wlen password passwdlen;
    FStar.SBytes.blit ti 0 f _pos hl;
    i := !i + 1;
    pbkdf2_inner_F f ti i password passwdlen salt saltlen c hl end
  else if !i < c then begin
    let _tmp = create #8 FStar.UInt8.zero hl in
    FStar.SBytes.blit ti 0 _tmp 0 hl;
    mac ti _tmp hl password passwdlen;
    FStar.SBytes.xor_bytes f _tmp ti hl;
    i := !i + 1;
    pbkdf2_inner_F f ti i password passwdlen salt saltlen c hl end
  else ()

val pbkdf2_inner_T : (dk        :sbytes) ->
                     (f         :sbytes { length f = hl /\ Disjoint f dk }) ->
                     (ti        :sbytes { length ti = hl /\ Disjoint ti dk /\ Disjoint ti f }) ->
                     (i         :ref nat) ->
                     (l         :nat) ->
                     (password  :sbytes { Disjoint password dk /\ Disjoint password f /\ Disjoint password ti }) ->
                     (passwdlen :nat      { length password = passwdlen } ) ->
                     (salt      :sbytes { Disjoint salt dk /\ Disjoint salt f /\ Disjoint salt ti /\ Disjoint salt password }) ->
                     (saltlen   :nat      { length salt = saltlen }) ->
                     (c         :nat)
                     -> ST unit
                          (requires (fun h -> Live h dk /\ Live h f /\ Live h ti /\ Live h password /\ Live h salt))
                          (ensures  (fun h0 r h1 -> Live h1 dk /\ Live h1 f /\ Live h1 ti /\ Live h1 password /\ Live h1 salt))
let rec pbkdf2_inner_T dk f ti i l password passwdlen salt saltlen c =
  if !i <= l then begin
    let pos = (!i - 1) * hl in
    pbkdf2_inner_F f ti i password passwdlen salt saltlen c hl;
    FStar.SBytes.blit f 0 dk pos hl;
    i := !i + 1;
    pbkdf2_inner_T dk f ti i l password passwdlen salt saltlen c end
  else ()


let pbkdf2 dk dklen password passwdlen salt saltlen c =
  (* Step 1: check for length of the derived key *)
  if dklen > 4294967295 then
    exit 1
  else

  (* Step 2: compute l and r parameters *)
  let l =
    let rest = dklen % hl in
    if rest <> 0 then (dklen - rest)/hl + 1 else (dklen - rest)/hl
  in
  let r = dklen - (l - 1) * hl in

  (* Step 3 & 4: define function F and apply it; concatenate ti blocks into dk *)
  let i = ref 0 in
  let f = create #8 FStar.UInt8.zero hl in
  let ti = create #8 FStar.UInt8.zero hl in
  pbkdf2_inner_T dk f ti i l password passwdlen salt saltlen c
