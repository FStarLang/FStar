module StaticHeaderCompare

[@@FStar.Attributes.CInline]
let equal (p q:StaticHeader.pair) : bool = p = q
