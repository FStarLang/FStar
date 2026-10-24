module NoUnfoldAttrType

[@@FStar.Attributes.custard_no_unfold]
noeq type pair = { first: FStar.UInt32.t; second: FStar.UInt32.t }

let sum (p:pair) : FStar.UInt32.t = FStar.UInt32.add_mod p.first p.second

let main () : FStar.UInt32.t = sum { first = 1ul; second = 2ul }
