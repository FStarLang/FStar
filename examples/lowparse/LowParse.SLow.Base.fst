module LowParse.SLow.Base
include LowParse.Spec.Base

module B32 = FStar.Bytes
module U32 = FStar.UInt32

let bytes32 = B32.bytes

let parser32_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes32)
  (res: option (t * U32.t))
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | None -> gp == None
  | Some (hres, consumed) ->
    Some? gp /\ (
      let (Some (hres' , consumed')) = gp in
      hres == hres' /\
      U32.v consumed == (consumed' <: nat)
    )

let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: bytes32) -> Tot (res: option (t * U32.t) { parser32_correct p input res } )

inline_for_extraction
let make_parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (p32: (input: bytes32) -> Pure (option (t * U32.t)) (requires True) (ensures (fun res -> parser32_correct p input res)))
: Tot (parser32 p)
= (fun (input: bytes32) -> (p32 input <: (res: option (t * U32.t) { parser32_correct p input res } )))

inline_for_extraction
let coerce_parser32
  (t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (#p: parser k t1)
  (p32: parser32 p)
  (u: unit { t2 == t1 } )
: Tot (parser32 (coerce_parser t2 p))
= p32

let validator_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes32)
  (res: option U32.t)
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | None -> gp == None
  | Some (consumed) ->
    Some? gp /\ (
      let (Some (_ , consumed')) = gp in
      U32.v consumed == (consumed' <: nat)
    )

let validator
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: bytes32) -> Tot (res: option U32.t { validator_correct p input res } )

let serializer32_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: t)
  (res: bytes32)
: GTot Type0
= B32.reveal res == s input

let serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (input: t) -> Tot (res: bytes32 { serializer32_correct s input res } )

let partial_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (input: t { Seq.length (s input) < 4294967296 } ) -> Tot (res: bytes32 { serializer32_correct s input res } )

let serializer32_then_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: t)
: Lemma
  (p32 (s32 input) == Some (input, B32.len (s32 input)))
= ()

inline_for_extraction
let b32slice
  (b: bytes32)
  (s: U32.t)
  (e: U32.t)
: Pure bytes32
  (requires (U32.v s <= U32.v e /\ U32.v e <= B32.length b))
  (ensures (fun res -> B32.reveal res == Seq.slice (B32.reveal b) (U32.v s) (U32.v e)))
= B32.slice b s e

let parser32_then_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
: Lemma
  (requires (Some? (p32 input)))
  (ensures (
    let (Some (v, consumed)) = p32 input in
    U32.v consumed <= B32.length input /\
    s32 v == b32slice input 0ul consumed
  ))
= serializer_correct_implies_complete p s

let parser32_then_serializer32'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
  (v: t)
  (consumed: U32.t)
: Lemma
  (requires (p32 input == Some (v, consumed)))
  (ensures (
    B32.length (s32 v) == U32.v consumed /\
    U32.v consumed <= B32.length input /\
    B32.reveal (s32 v) == Seq.slice (B32.reveal input) 0 (U32.v consumed)
  ))
= parser32_then_serializer32 s p32 s32 input

let parser32_injective
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input1 input2: bytes32)
: Lemma
  (requires (
    let p1 = p32 input1 in
    let p2 = p32 input2 in
    Some? p1 /\
    Some? p2 /\ (
    let (Some (v1, _)) = p1 in
    let (Some (v2, _)) = p2 in
    v1 == v2
  )))
  (ensures (
    let p1 = p32 input1 in
    let p2 = p32 input2 in
    Some? p1 /\
    Some? p2 /\ (
    let (Some (v1, consumed1)) = p1 in
    let (Some (v2, consumed2)) = p2 in
    v1 == v2 /\
    consumed1 == consumed2 /\
    U32.v consumed1 <= B32.length input1 /\
    U32.v consumed2 <= B32.length input2 /\
    b32slice input1 0ul consumed1 == b32slice input2 0ul consumed2
  )))
= assert (injective_precond p (B32.reveal input1) (B32.reveal input2));
  assert (injective_postcond p (B32.reveal input1) (B32.reveal input2))

let serializer32_injective
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (s32: serializer32 s)
  (input1 input2: t)
: Lemma
  (requires (s32 input1 == s32 input2))
  (ensures (input1 == input2))
= ()

let parse32_size
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
  (data: t)
  (consumed: U32.t)
: Lemma
  (requires (p32 input == Some (data, consumed)))
  (ensures (
    k.parser_kind_low <= U32.v consumed /\ (
    Some? k.parser_kind_high ==> (
    let (Some hi) = k.parser_kind_high in
    U32.v consumed <= hi
  ))))
= ()

let parse32_total
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_total == true /\
    k.parser_kind_low <= B32.length input
  ))
  (ensures (
    Some? (p32 input)
  ))
= ()
  
(* TODO: move to FStar.Bytes *)

let b32_index_reveal
  (b: B32.bytes)
  (i: nat { i < B32.length b })
: Lemma
  (Seq.index (B32.reveal b) i == B32.index b i)
= ()

let b32_reveal_create
  (len: U32.t)
  (v: byte)
: Lemma
  (B32.reveal (B32.create len v) == Seq.create (U32.v len) v)
  [SMTPat (B32.reveal (B32.create len v))]
= let b = B32.create len v in
  let lhs = B32.reveal b in
  let rhs = Seq.create (U32.v len) v in
  let pty = (i: nat { i < Seq.length lhs }) in
  let post
    (i: pty)
  : GTot Type0
  = Seq.index lhs (i <: nat) == Seq.index rhs (i <: nat)
  in
  let f
    (i: pty)
  : Lemma
    (post i)
  = assert (B32.get b (U32.uint_to_t i) == v)
  in
  Classical.forall_intro #pty #post f;
  Seq.lemma_eq_intro lhs rhs;
  Seq.lemma_eq_elim lhs rhs

inline_for_extraction
let b32append
  (b1: B32.bytes)
  (b2: B32.bytes)
: Pure B32.bytes
  (requires (B32.length b1 + B32.length b2 < 4294967296))
  (ensures (fun y -> B32.reveal y == Seq.append (B32.reveal b1) (B32.reveal b2)))
= B32.append b1 b2

inline_for_extraction
let lb32set
  (#n: nat)
  (b: B32.lbytes n)
  (i: U32.t)
  (x: byte)
: Pure (B32.lbytes n)
  (requires (U32.v i < n))
  (ensures (fun y ->
    U32.v i < n /\
    B32.reveal y == Seq.upd (B32.reveal b) (U32.v i) x
  ))
= B32.set_byte b i x

let u32_max : (y: U32.t { forall (x: U32.t) . U32.v x <= U32.v y } ) =
  4294967295ul

inline_for_extraction
let add_overflow
  (x y: U32.t)
: Pure U32.t
  (requires True)
  (ensures (fun z ->
    if U32.v x + U32.v y > U32.v u32_max then
    z == u32_max
    else U32.v z == U32.v x + U32.v y
  ))
= if U32.lt (U32.sub u32_max y) x
  then u32_max
  else U32.add x y

let size32_postcond
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (y: U32.t)
: GTot Type0
= let sz = Seq.length (serialize s x) in
  if sz > U32.v u32_max
  then y == u32_max
  else U32.v y == sz

let size32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (x: t) ->
  Tot (y: U32.t {
    size32_postcond s x y
  })

let size32_constant_precond
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (len32: U32.t)
: GTot Type0
= k.parser_kind_high == Some k.parser_kind_low /\
  U32.v len32 == k.parser_kind_low

inline_for_extraction
let size32_constant
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (len32: U32.t)
  (u: unit { size32_constant_precond s len32 } )
: Tot (size32 s)
= fun x -> 
  [@inline_let]
  let (z: U32.t { size32_postcond s x z } ) = len32 in
  z
