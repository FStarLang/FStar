module DeclareInCHeader

open FStar.All
module U32 = FStar.UInt32
module A = FStar.Attributes
module I = DeclareInCHeaderIface
module G = FStar.Ghost

noeq type pair = { left: U32.t; right: U32.t }

[@@A.custard_declare_in_c_header]
assume val swap (p:pair) : pair

[@@A.custard_declare_in_c_header; A.custard_extern "header_named"]
assume val named (x:U32.t) : U32.t

[@@A.custard_declare_in_c_header; A.custard_extern "header_named"]
assume val same_target (x:U32.t) : U32.t

[@@A.custard_extern "header_named"]
assume val source_target (x:U32.t) : U32.t

[@@A.custard_declare_in_c_header]
assume val erased (#n:G.erased nat) (x:U32.t) : U32.t

[@@A.custard_declare_in_c_header]
assume val tick (u:unit) : ML unit

[@@A.custard_declare_in_c_header]
assume val label (x:U32.t) : string

[@@A.custard_declare_in_c_header]
assume val rooted (x:U32.t) : U32.t

[@@A.custard_declare_in_c_header]
assume val unreachable (x:U32.t) : U32.t

assume val private_hook (x:U32.t) : U32.t

let main () : ML U32.t =
  tick ();
  let p = swap ({ left = 3ul; right = 4ul }) in
  if p.left = 4ul && p.right = 3ul &&
     named 1ul = 2ul && same_target 2ul = 3ul && source_target 3ul = 4ul &&
     erased #(G.hide 0) 5ul = 5ul && I.ping 6ul = 7ul &&
     label 0ul = "header" && private_hook 8ul = 9ul
  then 0ul else 1ul
