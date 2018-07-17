module MiniParse.Impl.List
include MiniParse.Spec.List
include MiniParse.Impl.Base

module U8 = FStar.UInt8
module U32 = FStar.UInt32

assume val parse32_nlist
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser t)
  (p32: parser32 p)
: Tot (parser32 (parse_nlist n p))

assume val serialize32_nlist
  (n: nat)
  (n' : U32.t { U32.v n' == n } )
  (#t: Type0)
  (#p: parser t)
  (#s: serializer p)
  (s32: serializer32 s)
: Tot (serializer32 (serialize_nlist n s))
