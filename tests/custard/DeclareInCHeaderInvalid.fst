module DeclareInCHeaderInvalid

module U32 = FStar.UInt32
module A = FStar.Attributes

[@@A.custard_declare_in_c_header]
let definition (x:U32.t) : U32.t = x

[@@A.custard_declare_in_c_header]
assume val value : U32.t

[@@A.custard_declare_in_c_header]
assume val abstract_type : Type0

[@@A.custard_declare_in_c_header;
   A.custard_extern "header_owned";
   A.custard_c_header "DeclareInCHeaderInvalid_stubs.h"]
assume val supplied (x:U32.t) : U32.t

let binder ([@@@A.custard_declare_in_c_header] x:U32.t) : U32.t = x

let main () : U32.t = definition (binder (supplied value))
