module DeclareInCHeaderCherry

[@@FStar.Attributes.custard_declare_in_c_header]
assume val step (x:FStar.UInt32.t) : FStar.UInt32.t

let main () : FStar.All.ML FStar.UInt32.t =
  if step 1ul = 2ul then 0ul else 1ul
