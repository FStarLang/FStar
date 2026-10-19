module NoUnfoldAttrBinder

let identity ([@@@FStar.Attributes.custard_no_unfold] x:FStar.UInt32.t)
  : FStar.UInt32.t = x

let main () : FStar.UInt32.t = identity 42ul
