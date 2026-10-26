module StaticHeaderReuse

module U32 = FStar.UInt32

[@@FStar.Attributes.rename_let "static_reuse_helper"]
let helper (x:U32.t) : U32.t = U32.add_mod (StaticHeader.helper x) 1ul

[@@FStar.Attributes.CInline]
let api (x:U32.t) : U32.t = helper x
