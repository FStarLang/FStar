module Crypto.HKDF.HMAC.Sha384

open FStar.SBytes
open SBuffer
open FStar.Heap
open Crypto.HMAC.Sha384



(* Define the hash length used *)
let hl = 48
let hmac = hmac_sha384

(* Define HKDF Extraction function *)
val hkdf_extract : (prk     :sbytes { length prk = hl }) ->
                   (salt    :sbytes { Disjoint prk salt }) ->
                   (saltlen :nat { length salt = saltlen } ) ->
                   (ikm     :sbytes { Disjoint prk ikm /\ Disjoint salt ikm }) ->
                   (ikmlen  :nat { length ikm = ikmlen })
                   -> ST unit
                        (requires (fun h -> Live h prk /\ Live h salt /\ Live h ikm))
                        (ensures  (fun h0 r h1 -> Live h1 prk /\ Live h1 salt /\ Live h1 ikm))

let hkdf_extract prk salt saltlen ikm ikmlen = hmac prk salt saltlen ikm ikmlen


val hkdf_expand_inner : (t       :sbytes) ->
                        (prk     :sbytes { length prk >= hl /\ Disjoint t prk }) ->
                        (prklen  :nat      { length prk = prklen }) ->
                        (info    :sbytes { Disjoint t info /\ Disjoint prk info }) ->
                        (infolen :nat      { length info = infolen }) ->
                        (n       :nat ) ->
                        (i       :ref nat ) ->
                        (ti      :sbytes { length ti = hl + infolen + 1
                                           /\ Disjoint ti t /\ Disjoint ti prk /\ Disjoint ti info }) ->
                        (til     :sbytes { length til = hl
                                           /\ Disjoint til t /\ Disjoint til prk
                                           /\ Disjoint til info /\ Disjoint til ti})
                        -> ST unit
                             (requires (fun h -> Live h t /\ Live h prk /\ Live h info /\ Live h ti /\ Live h til))
                             (ensures  (fun h0 r h1 -> Live h1 t /\ Live h1 prk /\ Live h1 info /\ Live h1 ti /\ Live h1 til))

let rec hkdf_expand_inner t prk prklen info infolen n i ti til =
  let _i = create #8 (FStar.UInt8.of_int !i) 1 in
  if !i = 1 then begin
    let _til = create #8 FStar.UInt8.zero (infolen + 1) in
    FStar.SBytes.blit info 0 _til 0 infolen;
    FStar.SBytes.blit _i 0 _til infolen 1;
    hmac ti prk prklen _til (infolen + 1);
    FStar.SBytes.blit ti 0 t 0 hl;
    i := !i + 1;
    hkdf_expand_inner t prk prklen info infolen n i ti til end
  else if !i <= n then begin
    FStar.SBytes.blit ti 0 til 0 hl;
    FStar.SBytes.blit info 0 til hl infolen;
    FStar.SBytes.blit _i 0 til (hl + infolen) 1;
    hmac ti prk prklen til (hl + infolen + 1);
    let pos = (!i - 1) * hl in
    FStar.SBytes.blit ti 0 t pos hl;
    i := !i + 1;
    hkdf_expand_inner t prk prklen info infolen n i ti til end
  else ()

(* Define HKDF Expand function *)
val hkdf_expand : (okm     :sbytes) ->
                  (prk     :sbytes { length prk >= hl }) ->
                  (prklen  :nat { length prk = prklen }) ->
                  (info    :sbytes) ->
                  (infolen :nat { length info = infolen }) ->
                  (l       :nat { length okm = l })
                  -> ST unit
                       (requires (fun h -> Live h okm /\ Live h prk /\ Live h info))
                       (ensures  (fun h0 r h1 -> Live h1 okm /\ Live h1 prk /\ Live h1 info))

let hkdf_expand okm prk prklen info infolen l =
  let n =
    let r = l % hl in
    (l - r)/hl + 1
  in
  let i = ref 1 in
  let _Til = create #8 FStar.UInt8.zero (hl + infolen + 1) in
  let _Ti = create #8 FStar.UInt8.zero hl in
  let _T = create #8 FStar.UInt8.zero (n * hl) in
  hkdf_expand_inner _T prk prklen info infolen n i _Ti _Til;
  FStar.SBytes.blit _T 0 okm 0 l
