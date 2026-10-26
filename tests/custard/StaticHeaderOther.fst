module StaticHeaderOther

type item = { first: FStar.UInt32.t; second: FStar.UInt32.t }

[@@FStar.Attributes.CInline]
let equal (p q:item) : bool = p = q
