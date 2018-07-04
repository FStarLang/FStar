module MiniParse.Spec.Int
include MiniParse.Spec.Combinators

module U8 = FStar.UInt8

let parse_u8 : parser U8.t = make_total_constant_size_parser 1 U8.t (fun x -> Seq.index x 0)

let serialize_u8 : serializer parse_u8 = Serializer (fun x -> Seq.create 1 x)
