module NoUnfoldAttrValue

[@@FStar.Attributes.custard_no_unfold]
let value = 42ul

let main () : FStar.UInt32.t = value
