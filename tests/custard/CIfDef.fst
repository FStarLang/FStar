module CIfDef

open FStar.All
module U32 = FStar.UInt32
module I32 = FStar.Int32

[@@CIfDef; custard_extern "CUSTARD_IFDEF_A"; custard_c_header "CIfDef_stubs.h"]
assume val first : bool

[@@CIfDef]
assume val second : bool

[@@custard_c_ifdef "defined(CUSTARD_IFDEF_A)"]
assume val native_first : bool

let native_selection () : U32.t =
  if native_first then 1ul else 0ul

[@@custard_c_closure_guard "defined(CUSTARD_IFDEF_A)"]
let native_payload () : U32.t = 1ul

let legacy_selection () : U32.t =
  let selected = if native_first then native_payload () else 0ul in
  if first then selected else 0ul

[@@custard_extern "cifdef_payload"; custard_c_header "CIfDef_stubs.h"]
assume val payload : Type0

[@@custard_extern "cifdef_make"; custard_c_header "CIfDef_stubs.h"]
assume val make_payload : unit -> payload

[@@custard_extern "cifdef_read"; custard_c_header "CIfDef_stubs.h"]
assume val read_payload : payload -> U32.t

[@@custard_extern "cifdef_yes"; custard_c_header "CIfDef_stubs.h"]
assume val yes : unit -> U32.t

[@@custard_extern "cifdef_no"; custard_c_header "CIfDef_stubs.h"]
assume val no : unit -> U32.t

[@@custard_extern "cifdef_tick"; custard_c_header "CIfDef_stubs.h"]
assume val tick : bool -> ML bool

[@@custard_extern "cifdef_value"; custard_c_header "CIfDef_stubs.h"]
assume val value : unit -> ML U32.t

[@@custard_extern "cifdef_bool"; custard_c_header "CIfDef_stubs.h"]
assume val bool_value : bool -> U32.t

[@@custard_extern "cifdef_reset"; custard_c_header "CIfDef_stubs.h"]
assume val reset : unit -> ML unit

[@@custard_extern "cifdef_expected"; custard_c_header "CIfDef_stubs.h"]
assume val expected : bool -> U32.t -> U32.t

[@@custard_extern "cifdef_counts_ok"; custard_c_header "CIfDef_stubs.h"]
assume val counts_ok : unit -> ML bool

let rec helper (n:U32.t) : ML U32.t =
  if U32.eq n 0ul then 7ul else helper (U32.sub_mod n 1ul)

let shared_guard (runtime:bool) : ML U32.t =
  let guard = tick runtime && first in
  let a = if guard then yes () else 0ul in
  let b = if guard then yes () else 0ul in
  U32.add_mod a b

let evaluate (runtime:bool) (x:U32.t) : ML U32.t =
  let local = value () in
  let selected = if first then read_payload (make_payload ()) else no () in
  let combination = if (first && not second) || (second && not first) then 1ul else 0ul in
  let nested = if first then (if second then 3ul else 5ul) else 7ul in
  let mixed = if first && runtime then yes () else 0ul in
  let mixed_or = if not first || runtime then 0ul else yes () in
  let alias = first && not second in
  let aliased = if alias then yes () else 0ul in
  let before = if tick runtime && first then yes () else 0ul in
  let after = if first && tick runtime then yes () else 0ul in
  let or_before = if tick runtime || first then 0ul else no () in
  let or_after = if first || tick runtime then 0ul else no () in
  let guard = tick runtime && first in
  let bound = if guard then yes () else 0ul in
  let shared = shared_guard runtime in
  let conditional = if first then U32.add_mod x local else 0ul in
  let recursive = if first then helper 2ul else 0ul in
  U32.add_mod selected (
    U32.add_mod combination (
    U32.add_mod nested (
    U32.add_mod mixed (
    U32.add_mod mixed_or (
    U32.add_mod aliased (
    U32.add_mod before (
    U32.add_mod after (
    U32.add_mod or_before (
    U32.add_mod or_after (
    U32.add_mod bound (
    U32.add_mod shared (
    U32.add_mod conditional (
    U32.add_mod recursive (bool_value first))))))))))))))

let main () : ML I32.t =
  reset ();
  let a = evaluate false 41ul in
  let b = evaluate true 41ul in
  if U32.eq a (expected false 41ul) && U32.eq b (expected true 41ul) && counts_ok () &&
     U32.eq (native_selection ()) (legacy_selection ())
  then 0l else 1l
