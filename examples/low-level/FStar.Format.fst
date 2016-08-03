module FStar.Format

open FStar.Ghost
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
open FStar.Seq
open FStar.ImmBuffer

assume val lemma_buffer_length: b:buffer u8 -> Lemma
  (requires (True))
  (ensures  (length b = Seq.length (as_seq_bytes b)))
  [SMTPat (length b)]

type lsize = n:int{n = 1 \/ n = 2 \/ n = 3}
type csize = n:t{v n = 1 \/ v n = 2 \/ v n = 3}

val read_length: b:buffer u8 -> n:csize{v n <= length b} -> Tot UInt32.t
let read_length b n =
  if n = 1ul then (
    let b0 = read b 0ul in
    uint8_to_uint32 b0
  ) else if n = 2ul then (
    let b1 = read b 0ul in
    let b0 = read b 1ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    b0 |^ (b1 <<^ 8ul)
  ) else (
    let b2 = read b 0ul in
    let b1 = read b 1ul in
    let b0 = read b 2ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    let b2 = uint8_to_uint32 b2 in
    b0 |^ (b1 <<^ 8ul) |^ (b2 <<^ 16ul)
  )

#set-options "--lax"

// Type of buffers for which a lower bound on the length is known
let lbytes = (|len:UInt32.t & b:buffer u8{length b >= v len} |)

let mk_lbytes (b:buffer u8) (len:UInt32.t{v len <= length b}) = (| len, b |)
let lb_length (b:lbytes) = dfst b
let lb_bytes  (b:lbytes) = dsnd b
let loffset   (b:lbytes) (i:UInt32.t{v i <= v (lb_length b)}) : Tot lbytes =
  (|lb_length b -^ i,  offset (lb_bytes b) i|)
let lsub   (b:lbytes) (i:UInt32.t) (j:UInt32.t{v i + v j <= v (lb_length b)}) : Tot lbytes =
  (|lb_length b -^ i -^ j,  sub (lb_bytes b) i j|)


type lserializer (t:Type0) = f:(t -> Tot  lbytes)
// The parser return the number of bytes read
type lparser (#t:Type0) ($f:lserializer t) = 
  b:lbytes -> Tot (r:result (t * UInt32.t){is_Correct r ==> v (snd (correct r)) <= v (lb_length b)})

type inverse (#t:Type0) ($f:lserializer t  ) ($g:lparser f) =
  (forall (x:t). g (f x) == Correct (x, lb_length (f x)))
    /\ (forall (y:lbytes). is_Correct (g y) ==>  (f (fst (Correct._0 (g y))) == y))

noeq type lserializable (t:Type0) : Type0 =
  | VLSerializable: $f:lserializer t   -> $g:lparser f{inverse f g} -> lserializable t

// Type of buffer prefixes by their length (on 1, 2 or 3 bytes)
let vlbytes (n:lsize) = b:buffer u8{length b >= n /\ length b = n + v (read_length b (uint_to_t n))}
let vlb_length (n:csize) (b:vlbytes (v n)) : Tot UInt32.t = read_length (sub b 0ul n) n

let vlb_content (n:csize) (b:vlbytes (v n)) : Tot (buffer u8) =
  let len = vlb_length n b in
  cut (length b >= v n + v len);
  sub b n (n +^ len)

val vlserialize: n:csize -> Tot (lserializer (vlbytes (v n)))//b:vlbytes (v n) -> Tot (seq byte)
let vlserialize n = fun b -> (| read_length b n, b |)

let vlparse n : lparser (vlserialize n) = 
  fun (b:lbytes) ->
    let len = lb_length b in
    let bytes = lb_bytes b in
    if n >^ len then Error "Too short"
    else (
      let l = read_length bytes n in
      if len <^ n +^ l then Error "Wrong vlbytes format"
      else Correct (sub bytes 0ul (n +^ l), n +^ l)
    )

let rec valid_seq (#t:Type0) (ty:lserializable t) (b:lbytes) : Tot bool =  
  let len = lb_length b in
  let bytes = lb_bytes b in
  if len =^ 0ul then true
  else (
    let blob  = ty.g b in
    match blob with
    | Correct (blob, blob_len) -> valid_seq ty (loffset b blob_len)
    | Error z -> false
  )

type vlbuffer (#t:Type0) (n:lsize) (ty:lserializable t) = b:buffer u8{
  length b >= n /\ valid_seq ty (mk_lbytes b (read_length b (uint_to_t n))) }

val vlbuffer_serialize: #t:Type0 -> ty:lserializable t -> n:csize -> Tot (lserializer (vlbuffer (v n) ty))
let vlbuffer_serialize #t ty n = fun b -> (| read_length b n, b |)

let vlbuffer_parse (#t:Type0) (ty:lserializable t) (n:csize) : lparser (vlbuffer_serialize ty n) 
  = fun b ->
    let len = lb_length b in
    let bytes = lb_bytes b in
    if len <^ n then Error "Too short"
    else (
      let l = read_length bytes n in
      if l +^ n >^ len then Error "Too short"
      else (
	let b' = mk_lbytes (sub bytes n (n+^l)) l in
	if valid_seq ty b' then Correct (bytes, n+^ l)
	else Error "Ill-formated data"
      )
    )

noeq type key_share = {
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
  fun ks -> (| 2ul +^ read_length ks.ks_public_key 2ul, 
    concat_buf #byte #u8 #byte #u8 (u16_to_buf ks.ks_group_name) (ks.ks_public_key) |)

(* val vlparse_key_share: b:lbytes -> Tot (result (key_share)) *)
let vlparse_key_share: lparser (vlserialize_key_share) =
  fun b ->
  let len = lb_length b in
  let bytes = lb_bytes b in
  if len <^ 4ul then Error "Too short"
  else (
    let gn = sub bytes 0ul 2ul in
    let gn = cast u16 gn in
    let gn = read gn 0ul in
    let pk_bytes = loffset b 2ul in
    match vlparse 2ul pk_bytes with
    | Correct (blob,l) -> Correct ({ks_group_name = gn; ks_public_key = blob}, 2ul +^ l)
    | Error z -> Error z
  )

let key_share' : lserializable key_share = VLSerializable vlserialize_key_share vlparse_key_share

type key_shares = vlbuffer 2 key_share'

// I do not know how this will be handed out by the application
// In a buffer of key_shares ? In something already contiguous ?
assume val vlserialize_key_shares : lserializer key_shares

let vlparse_key_shares : lparser vlserialize_key_shares =
  fun b -> vlbuffer_parse key_share' 2ul b
