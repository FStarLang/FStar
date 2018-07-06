module MiniParse.Impl.Int
include MiniParse.Spec.Int
include MiniParse.Impl.Combinators

module U8 = FStar.UInt8
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

let parse32_u8 : parser32 parse_u8 = make_total_constant_size_parser32 1 1ul (fun x -> Seq.index x 0) () (fun x -> B.index x 0ul)

let serialize32_u8 : serializer32 serialize_u8 =
  (fun output (len: U32.t { len == B.len output } ) x ->
    let h = HST.get () in
    if len `U32.lt` 1ul
    then None
    else begin
      let output' = B.sub output 0ul 1ul in
      B.upd output' 0ul x;
      let h' = HST.get () in
      assert (B.as_seq h' output' `Seq.equal` Seq.create 1 x);
      Some 1ul
    end)

#set-options "--z3rlimit 16"

inline_for_extraction
let parse32_bounded_u8
  (b: nat)
: Tot (parser32 (parse_bounded_u8 b)) =
  if b >= 256
  then (fun input len -> parse32_synth parse32_u8 (fun x -> x <: bounded_u8 b) (fun x -> x <: bounded_u8 b) (fun x -> x) () input len)
  else
    [@inline_let]
    let b' = U8.uint_to_t b in
    parse32_synth
      (parse32_filter parse32_u8 (fun x -> U8.v x < b) (fun x -> x `U8.lt` b'))
      (fun x -> x <: bounded_u8 b)
      (fun x -> x <: bounded_u8 b)
      (fun x -> x)
      ()

#reset-options

inline_for_extraction
let serialize32_bounded_u8 (b: nat) : Tot (serializer32 (serialize_bounded_u8 b)) =
  fun output len x -> serialize32_u8 output len x
