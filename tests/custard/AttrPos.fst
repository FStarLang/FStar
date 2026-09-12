module AttrPos

(* Section 34.2: recognized attributes in unrecognized positions.

   None of the four below can do anything where it is written.  Each is an
   attribute Custard does read -- just never in this position -- so the author
   has configured nothing and has no way to tell. *)

module U32 = FStar.UInt32

(* [@@custard_inline_field] describes a constructor field, not a definition. *)
[@@FStar.Attributes.custard_inline_field]
let width : U32.t = 4ul

(* [@@custard_c_header] configures [@@custard_extern] and there is none. *)
[@@FStar.Attributes.custard_c_header "attrpos.h"]
let height : U32.t = 5ul

(* [@@custard_compile_time] names a definition; a parameter is not one. *)
let scale ([@@@FStar.Attributes.custard_compile_time] k : U32.t) (x : U32.t)
  : U32.t
  = U32.mul_mod k x

(* [@@custard_opaque] fixes a type's representation; a field is not a type. *)
noeq
type box =
  | Box : [@@@FStar.Attributes.custard_opaque] contents:U32.t -> box

let unbox (b:box) : U32.t = match b with | Box c -> c

let main () : U32.t =
  let b = Box (scale width height) in
  if unbox b = 20ul then 0ul else 1ul
