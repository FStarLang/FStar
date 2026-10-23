module CExternGrouping
open FStar.All
open FStar.Attributes
module U32 = FStar.UInt32

type box = { value:U32.t; other:U32.t }
type variant = | Empty | Full : value:U32.t -> variant

[@@custard_extern "CG_NUMBER"; custard_c_header "CExternGrouping_stubs.h"]
assume val number : U32.t
[@@custard_extern "CG_PLUS"; custard_c_header "CExternGrouping_stubs.h"]
assume val plus (x:U32.t) : U32.t
[@@custard_extern "CG_WIDE"; custard_c_header "CExternGrouping_stubs.h"]
assume val wide : U32.t
[@@custard_extern "CG_FALSE"; custard_c_header "CExternGrouping_stubs.h"]
assume val false_flag : bool
[@@custard_extern "CG_FLAG"; custard_c_header "CExternGrouping_stubs.h"]
assume val flag : bool
[@@custard_extern "CG_BOX"; custard_c_header "CExternGrouping_stubs.h"]
assume val selected : box
[@@custard_extern "CG_BOX_FN"; custard_c_header "CExternGrouping_stubs.h"]
assume val selected_fn (_:unit) : box
[@@custard_extern "CG_VARIANT"; custard_c_header "CExternGrouping_stubs.h"]
assume val tagged : variant
[@@custard_extern "CG_COMMA"; custard_c_header "CExternGrouping_stubs.h"]
assume val comma : U32.t
[@@custard_extern "cg_identity"; custard_c_header "CExternGrouping_stubs.h"]
assume val identity (x:U32.t) : U32.t
[@@custard_extern "cg_tick"; custard_c_header "CExternGrouping_stubs.h"]
assume val tick (_:unit) : ML U32.t
[@@custard_extern "cg_count"; custard_c_header "CExternGrouping_stubs.h"]
assume val count (_:unit) : ML U32.t

let binary () = U32.mul_mod number 3ul
let binary_call () = U32.mul_mod (plus 1ul) 3ul
let narrow () =
  FStar.Int.Cast.uint8_to_uint32 (FStar.Int.Cast.uint32_to_uint8 wide)
let logical () = false_flag && flag
let project () = selected.value
let project_call () = (selected_fn ()).value
let discriminate () = Full? tagged
let argument () = identity comma
let ignored () : ML bool =
  let _ = tick () in
  U32.eq (count ()) 1ul

let main () : ML FStar.Int32.t =
  let once = ignored () in
  if once && U32.eq (binary ()) 9ul &&
     U32.eq (binary_call ()) 9ul &&
     U32.eq (narrow ()) 0ul &&
     not (logical ()) &&
     U32.eq (project ()) 11ul &&
     U32.eq (project_call ()) 11ul &&
     discriminate () &&
     U32.eq (argument ()) 2ul
  then 0l else 1l
