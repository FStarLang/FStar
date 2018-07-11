module MiniParse.Impl.Int
include MiniParse.Spec.Int
include MiniParse.Impl.Combinators

module U8 = FStar.UInt8
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

inline_for_extraction
let parse_u8_impl : parser_impl parse_u8 = make_total_constant_size_parser_impl 1 1ul (fun x -> Seq.index x 0) () (fun x -> B.index x 0ul)

inline_for_extraction
let serialize_u8_impl : serializer_impl serialize_u8 =
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
let parse_bounded_u8_impl
  (b: nat)
: Tot (parser_impl (parse_bounded_u8 b)) =
  if b >= 256
  then (fun input len -> parse_synth_impl parse_u8_impl (fun x -> x <: bounded_u8 b) (fun x -> x <: bounded_u8 b) (fun x -> x) () input len)
  else
    [@inline_let]
    let b' = U8.uint_to_t b in
    parse_synth_impl
      (parse_filter_impl parse_u8_impl (fun x -> U8.v x < b) (fun x -> x `U8.lt` b'))
      (fun x -> x <: bounded_u8 b)
      (fun x -> x <: bounded_u8 b)
      (fun x -> x)
      ()

#reset-options

inline_for_extraction
let serialize_bounded_u8_impl (b: nat) : Tot (serializer_impl (serialize_bounded_u8 b)) =
  fun output len x -> serialize_u8_impl output len x
