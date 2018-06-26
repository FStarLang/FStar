module MiniParse.Impl.Int
include MiniParse.Spec.Int
include MiniParse.Impl.Combinators

module U8 = FStar.UInt8
module B32 = MiniParse.Bytes32

let parse32_u8 : parser32 parse_u8 = make_total_constant_size_parser32 1 1ul (fun x -> Seq.index x 0) () (fun x -> B32.get x 0ul)
