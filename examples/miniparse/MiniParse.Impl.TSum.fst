module MiniParse.Impl.TSum
include MiniParse.Impl.Combinators
include MiniParse.Spec.TSum

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 10"
inline_for_extraction
let parse_tagged_union_impl
  (#tag_t: Type0)
  (#pt: parser_spec tag_t)
  (pt32: parser_impl pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#p: (t: tag_t) -> Tot (parser_spec (refine_with_tag tag_of_data t)))
  (p32: (t: tag_t) -> Tot (parser_impl (p t)))
: Tot (parser_impl (parse_tagged_union pt tag_of_data p))
= fun input len ->
  match pt32 input len with
  | Some (tg, consumed_tg) ->
    let len1 = len `U32.sub` consumed_tg in
    let input1 = B.sub input consumed_tg len1 in
    begin match p32 tg input1 len1 with
    | Some (d, consumed_d) ->
      Some ((d <: data_t), consumed_tg `U32.add` consumed_d)
    | _ -> None
    end
  | _ -> None

#set-options "--z3rlimit 16"

inline_for_extraction
let serialize_tagged_union_impl
  (#tag_t: Type0)
  (#pt: parser_spec tag_t)
  (#st: serializer_spec pt)
  (st32: serializer_impl st)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (tag_of_data32: ((x: data_t) -> Tot (y: tag_t { y == tag_of_data x } )))
  (#p: (t: tag_t) -> Tot (parser_spec (refine_with_tag tag_of_data t)))
  (#s: (t: tag_t) -> Tot (serializer_spec (p t)))
  (s32: (t: tag_t) -> Tot (serializer_impl (s t)))
: Tot (serializer_impl (serialize_tagged_union st tag_of_data s))
= fun (output: buffer8) (len: U32.t { len == B.len output } ) (x: data_t) ->
  let tg = tag_of_data32 x in
  match st32 output len tg with
  | Some sz1 ->
    let output1 = B.offset output sz1 in
    let len1 = len `U32.sub` sz1 in
    begin match s32 tg output1 len1 x with
    | Some sz2 ->
      let h2 = HST.get () in
      seq_append_slice (B.as_seq h2 output) (U32.v sz1) (U32.v sz2);
      Some (sz1 `U32.add` sz2)
    | _ -> None
    end
  | _ -> None

#reset-options
