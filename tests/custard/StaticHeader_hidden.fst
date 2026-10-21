module StaticHeader_hidden

module U32 = FStar.UInt32

[@@FStar.Attributes.CInline]
let collision (x:U32.t) : U32.t = U32.add_mod x 2ul

[@@FStar.Attributes.CInline]
let api (x:U32.t) : U32.t = collision x
