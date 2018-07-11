module MiniParse.Impl.List
include MiniParse.Spec.List
include MiniParse.Impl.Base

module U8 = FStar.UInt8
module U32 = FStar.UInt32

assume val parse_nlist_impl
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser_spec t)
  (p32: parser_impl p)
: Tot (parser_impl (parse_nlist n p))

assume val serialize_nlist_impl
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser_spec t)
  (#s: serializer_spec p)
  (s32: serializer_impl s)
: Tot (serializer_impl (serialize_nlist n s))
