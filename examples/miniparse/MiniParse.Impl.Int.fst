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
