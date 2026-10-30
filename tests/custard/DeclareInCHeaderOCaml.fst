module DeclareInCHeaderOCaml

[@@FStar.Attributes.custard_declare_in_c_header]
let increment (x:FStar.UInt32.t) : FStar.UInt32.t = FStar.UInt32.add_mod x 1ul

let main () : FStar.All.ML unit =
  FStar.IO.print_string (if increment 1ul = 2ul then "ok\n" else "bad\n")
