module StaticHeader

module U32 = FStar.UInt32
module A = FStar.Attributes
module G = FStar.Ghost

type pair = { left: U32.t; right: U32.t }

[@@A.CMacro]
let limit = 17ul

assume val foreign (#n:G.erased nat) (x:U32.t) : U32.t
assume val foreign_value : U32.t

[@@A.custard_extern "static_header_hook"; A.custard_c_header "StaticHeader_stubs.h"]
assume val hook (x:U32.t) : U32.t

let helper (x:U32.t) : U32.t = U32.add_mod x 1ul

let plain (x:U32.t) : U32.t = helper x

[@@A.CInline]
let api (x:U32.t) : U32.t =
  hook (U32.add_mod (foreign #(G.hide 0) (plain x)) foreign_value)

[@@A.CInline]
let equal (p q:pair) : bool = p = q

[@@A.CInline]
let rec countdown (n:U32.t) : Tot U32.t (decreases (U32.v n)) =
  if U32.gt n 0ul then countdown (U32.sub n 1ul) else n

[@@A.CInline]
let get_nan () : FStar.Float64.t = FStar.Float64.of_literal "nan"

let unreachable (x:U32.t) : U32.t = U32.add_mod x 99ul
