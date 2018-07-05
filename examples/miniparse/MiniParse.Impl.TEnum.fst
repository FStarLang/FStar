module MiniParse.Impl.TEnum
include MiniParse.Spec.TEnum
include MiniParse.Impl.Combinators
include MiniParse.Impl.Int

module U8 = FStar.UInt8

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
