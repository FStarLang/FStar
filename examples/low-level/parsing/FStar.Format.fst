(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Format

open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
open FStar.Seq
open ImmBuffer

type lsize = n:int{n = 1 \/ n = 2 \/ n = 3}
type csize = n:t{v n = 1 \/ v n = 2 \/ v n = 3}

#reset-options "--initial_fuel 2 --max_fuel 2"

assume val aux_lemma_1: a:t -> b:t -> Lemma
  (requires (v a < pow2 8 /\ v b < pow2 8))
  (ensures  (v a + (FStar.Mul (v b * pow2 8) % pow2 32) < pow2 16))

assume val aux_lemma_2: a:t -> b:t -> c:t -> Lemma
  (requires (v a < pow2 8 /\ v b < pow2 8))
  (ensures  (v a + (FStar.Mul (v b * pow2 8) % pow2 32) 
	         + (FStar.Mul (v c * pow2 16) % pow2 32) < pow2 24))

val read_length: b:buffer u8 -> n:csize{v n <= length b} -> Tot (l:UInt32.t{v l < pow2 24})
let read_length b n =
  if n = 1ul then (
    let b0 = read b 0ul in
    Math.Lib.pow2_increases_lemma 24 8;
    uint8_to_uint32 b0
  ) else if n = 2ul then (
    let b1 = read b 0ul in
    let b0 = read b 1ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    aux_lemma_1 b0 b1;
    Math.Lib.pow2_increases_lemma 24 16;
    Math.Lib.pow2_increases_lemma 32 24;
    b0 +^ (b1 <<^ 8ul)
  ) else (
    let b2 = read b 0ul in
    let b1 = read b 1ul in
    let b0 = read b 2ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    let b2 = uint8_to_uint32 b2 in
    aux_lemma_2 b0 b1 b2;
    Math.Lib.pow2_increases_lemma 32 24;
    b0 +^ (b1 <<^ 8ul) +^ (b2 <<^ 16ul)
  )

type lserializer (t:Type0) = f:(t -> Tot  lbytes)
// The parser return the number of bytes read
type lparser (#t:Type0) ($f:lserializer t) = 
  f:(lbytes -> Tot (result (t * UInt32.t))){forall (b:lbytes). Correct? (f b) ==> (v (snd (correct (f b))) <= v (lb_length b) /\ v (snd (correct (f b))) > 0)}

type inverse (#t:Type0) ($f:lserializer t  ) ($g:lparser f) =
  (forall (x:t). g (f x) == Correct (x, lb_length (f x)))
    /\ (forall (y:lbytes). Correct? (g y) ==>  (f (fst (Correct._0 (g y))) == y))

noeq type lserializable (t:Type0) : Type0 =
  | VLSerializable: $f:lserializer t   -> $g:lparser f{inverse f g} -> lserializable t

// Type of buffer prefixes by their length (on 1, 2 or 3 bytes)
let vlbytes (n:lsize) = b:buffer u8{length b >= n /\ length b = n + v (read_length b (uint_to_t n))}

assume HasSizeVLBytes: forall (n:lsize).
  hasSize (vlbytes n) /\ sizeof (vlbytes n) = sizeof (buffer u8)

val vlb_length: n:csize -> b:vlbytes (v n) -> Tot UInt32.t
let vlb_length n b = read_length (sub b 0ul n) n

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val read_length_lemma: #n:csize -> b:vlbytes (v n) -> j:UInt32.t{v j <= length b /\ v j >= v n} -> 
  Lemma (requires True)
	(ensures  (read_length (sub b 0ul j) n = read_length b n))
	[SMTPat (read_length (sub b 0ul j) n)]
let read_length_lemma #n b j = ()	

(*** WIP ***)

let vlb_content (n:csize) (b:vlbytes (v n)) : Tot (buffer u8) =
  let len = vlb_length n b in
  sub b n len

val vlserialize: n:csize -> Tot (lserializer (vlbytes (v n)))
let vlserialize n = fun b -> (| read_length b n, b |)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

let vlparse n : lparser (vlserialize n) = 
  fun (b:lbytes) ->
    let len = lb_length b in
    let bytes = lb_bytes b in
    if n >^ len then Error "Too short"
    else (
      let l = read_length bytes n in
      assume(v n < pow2 2);
      Math.Lib.pow2_exp_lemma 2 24;
      Math.Lib.pow2_increases_lemma 32 26;
      if len <^ n +^ l then Error "Wrong vlbytes format"
      else Correct (sub bytes 0ul (n +^ l), n +^ l)
    )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

let rec valid_seq (#t:Type0) (ty:lserializable t) (b:lbytes) : Tot bool (decreases (v (lb_length b))) =  
  let len = lb_length b in
  let bytes = lb_bytes b in
  if len =^ 0ul then true
  else (
    let blob  = ty.g b in
    match blob with
    | Correct (blob, blob_len) -> valid_seq ty (lb_offset b blob_len)
    | Error z -> false
  )

type vlbuffer (#t:Type0) (n:lsize) (ty:lserializable t) = b:buffer u8{
  length b >= n
  /\ length b >= n + v (read_length b (uint_to_t n))
  /\ valid_seq ty (mk_lbytes (sub b (uint_to_t n) (read_length b (uint_to_t n))) (read_length b (uint_to_t n))) }

val vlbuffer_serialize: #t:Type0 -> ty:lserializable t -> n:csize -> Tot (lserializer (vlbuffer (v n) ty))
let vlbuffer_serialize #t ty n = fun b -> (| read_length b n, b |)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

let vlbuffer_parse (#t:Type0) (ty:lserializable t) (n:csize) : lparser (vlbuffer_serialize ty n) 
  = fun b ->
    let len = lb_length b in
    let bytes = lb_bytes b in
    if len <^ n then Error "Too short"
    else (
      let l = read_length bytes n in
      assume (v n < pow2 2);
      Math.Lib.pow2_exp_lemma 2 24;
      Math.Lib.pow2_increases_lemma 32 26;
      if l +^ n >^ len then Error "Too short"
      else (
	let b' = mk_lbytes (sub bytes n l) l in
	if valid_seq ty b' then Correct (bytes, n+^ l)
	else Error "Ill-formated data"
      )
    )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

noeq type key_share : Type0 = {
  ks_group_name: UInt16.t;
  ks_public_key: vlbytes 2
}

assume KeyShareHasSize: 
  hasSize key_share /\ sizeof key_share = sizeof UInt16.t + sizeof (vlbytes 2)

assume val concat_buf: #t:sizeof_t -> #ty:serializable t -> 
  #t':sizeof_t -> #ty':serializable t -> a:buffer ty -> b:buffer ty' -> Tot (buffer u8)

assume val u16_to_buf: UInt16.t -> Tot (buffer u8)

// Cannot really write it since the whole point of immutable buffers is that they are not writable
// This is an ugly dummy
let vlserialize_key_share: lserializer key_share =
  admit();
  fun ks -> (| 2ul +^ read_length ks.ks_public_key 2ul, 
    concat_buf #byte #u8 #byte #u8 (u16_to_buf ks.ks_group_name) (ks.ks_public_key) |)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val vlparse_key_share: p:lparser (vlserialize_key_share){inverse vlserialize_key_share p}
let vlparse_key_share
  = 
    admit();
    let p : lparser (vlserialize_key_share) =fun (b:lbytes) ->
    let len = lb_length b in
    let bytes = lb_bytes b in
    if len <^ 4ul then Error "Too short"
    else (
      let gn:buffer u8 = sub bytes 0ul 2ul in
      // Requires to axiomatize the parsing/serialization of machine integers more precisely
      assume (Correct? (of_seq_bytes #UInt16.t #u16 (to_seq_byte gn)));
      let gn = cast u16 gn in
      let gn = read gn 0ul in
      let pk_bytes = lb_offset b 2ul in
      match vlparse 2ul pk_bytes with
      | Correct (blob,l) -> Correct ({ks_group_name = gn; ks_public_key = blob}, 2ul +^ l)
      | Error z -> Error z
    ) in
    assume (inverse vlserialize_key_share p);
    p

let key_share' : lserializable key_share = VLSerializable vlserialize_key_share vlparse_key_share

type key_shares = vlbuffer 2 key_share'

// I do not know how this will be handed out by the application
// In a buffer of key_shares ? In something already contiguous ?
assume val vlserialize_key_shares : lserializer key_shares

let vlparse_key_shares : lparser vlserialize_key_shares =
  fun b -> vlbuffer_parse key_share' 2ul b
