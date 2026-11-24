module GotoReturn

(* Ported from karamel's test/pulse/GotoReturn.fst, the test of krml's
   -goto_for_early_return, and checked by ../earlyreturn.py with
   --custard_early_return goto. As in karamel, branch values go through
   opaque calls so that the tail ifs stay statements; the externs are
   defined in GotoReturn_stubs.h so that the result can be run. *)
[@@custard_extern "gr_opaque_int32"; custard_c_header "GotoReturn_stubs.h"]
assume val opaque_int32 (x: Int32.t) : Int32.t
[@@custard_extern "gr_opaque_bool"; custard_c_header "GotoReturn_stubs.h"]
assume val opaque_bool (x: bool) : bool
[@@custard_extern "gr_opaque_uint32"; custard_c_header "GotoReturn_stubs.h"]
assume val opaque_uint32 (x: FStar.UInt32.t) : FStar.UInt32.t
[@@custard_extern "gr_opaque_uint64"; custard_c_header "GotoReturn_stubs.h"]
assume val opaque_uint64 (x: FStar.UInt64.t) : FStar.UInt64.t
[@@custard_extern "gr_opaque_int64"; custard_c_header "GotoReturn_stubs.h"]
assume val opaque_int64 (x: FStar.Int64.t) : FStar.Int64.t

(* Early return with Int32 *)
let early_return_int (x: Int32.t) : Int32.t =
  if x = 0l then opaque_int32 42l
  else if x = 1l then opaque_int32 43l
  else opaque_int32 44l

(* No early return: single return at the end *)
[@@Comment "This function has no early return.\n  It tests that line comments leave top-level comments unchanged."]
let no_early_return (x: Int32.t) : Int32.t =
  x

(* Early return with two args *)
let early_return_two_args (x: Int32.t) (y: Int32.t) : Int32.t =
  if x = 0l then opaque_int32 42l
  else y

(* Collision avoidance: local named result. Unlike karamel, Custard would
   substitute `let result = x`, so it binds an opaque call. *)
let collision_test (x: Int32.t) : Int32.t =
  let result = opaque_int32 x in
  if result = 0l then opaque_int32 42l
  else if result = 1l then opaque_int32 43l
  else opaque_int32 44l

(* Early return with bool *)
let early_return_bool (x: Int32.t) : bool =
  if x = 0l then opaque_bool true
  else if x = 1l then opaque_bool false
  else opaque_bool true

(* Early return with UInt32 *)
let early_return_uint32 (x: FStar.UInt32.t) : FStar.UInt32.t =
  let open FStar.UInt32 in
  if x = 0ul then opaque_uint32 42ul
  else if x = 1ul then opaque_uint32 43ul
  else opaque_uint32 44ul

(* Early return with UInt64 *)
let early_return_uint64 (x: FStar.UInt64.t) : FStar.UInt64.t =
  let open FStar.UInt64 in
  if x = 0UL then opaque_uint64 42UL
  else if x = 1UL then opaque_uint64 43UL
  else opaque_uint64 44UL

(* Early return with Int64 *)
let early_return_int64 (x: FStar.Int64.t) : FStar.Int64.t =
  let open FStar.Int64 in
  if x = 0L then opaque_int64 42L
  else if x = 1L then opaque_int64 43L
  else opaque_int64 44L

(* Early return with void: use assumed side-effecting function *)
[@@custard_extern "gr_side_effect"; custard_c_header "GotoReturn_stubs.h"]
assume val side_effect: Int32.t -> FStar.All.ML unit

let early_return_void (x: Int32.t) : FStar.All.ML unit =
  if x = 0l then side_effect 1l
  else if x = 1l then side_effect 2l
  else side_effect 3l

(* Struct type for testing *)
type point = { px: Int32.t; py: Int32.t }

(* Early return with struct *)
let early_return_struct (x: Int32.t) : point =
  if x = 0l then { px = opaque_int32 1l; py = opaque_int32 2l }
  else if x = 1l then { px = opaque_int32 3l; py = opaque_int32 4l }
  else { px = opaque_int32 5l; py = opaque_int32 6l }

(* Unit/void interaction: returning unit values *)
let unit_return (x: unit) : FStar.All.ML unit =
  if true then x else ()

(* Pulse function with early return *)
open Pulse
#lang-pulse
fn pulse_early_return (x: Int32.t)
  returns r: Int32.t
  ensures pure (x = 0l ==> r = 42l)
  ensures pure (x <> 0l ==> r = 99l)
{
  if (x = 0l) {
    return 42l;
  };
  99l
}

[@@custard_extern "gr_side_effects"; custard_c_header "GotoReturn_stubs.h"]
assume val side_effects : unit -> FStar.All.ML Int32.t

(* Unlike karamel's, this main checks the results. It cannot call the Pulse
   function, which is extracted as an extra entry point instead, as is
   no_early_return, which would otherwise be inlined. *)
let main () : FStar.All.ML FStar.Int32.t =
  let i0 = early_return_int 0l in
  let i1 = early_return_int 1l in
  let i2 = early_return_int 5l in
  let n = no_early_return 1l in
  let t0 = early_return_two_args 0l 1l in
  let t1 = early_return_two_args 2l 7l in
  let c0 = collision_test 0l in
  let c1 = collision_test 1l in
  let c2 = collision_test 2l in
  let b0 = early_return_bool 0l in
  let b1 = early_return_bool 1l in
  let b2 = early_return_bool 2l in
  let u0 = early_return_uint32 0ul in
  let u1 = early_return_uint32 1ul in
  let u2 = early_return_uint32 2ul in
  let w0 = early_return_uint64 0UL in
  let w1 = early_return_uint64 1UL in
  let w2 = early_return_uint64 2UL in
  let l0 = early_return_int64 0L in
  let l1 = early_return_int64 1L in
  let l2 = early_return_int64 2L in
  early_return_void 0l;
  early_return_void 1l;
  early_return_void 2l;
  let e = side_effects () in
  let p = early_return_struct 0l in
  let q = early_return_struct 1l in
  let r = early_return_struct 2l in
  unit_return ();
  if i0 = 42l && i1 = 43l && i2 = 44l && n = 1l
     && t0 = 42l && t1 = 7l && c0 = 42l && c1 = 43l && c2 = 44l
     && b0 && not b1 && b2
     && FStar.UInt32.eq u0 42ul && FStar.UInt32.eq u1 43ul && FStar.UInt32.eq u2 44ul
     && FStar.UInt64.eq w0 42UL && FStar.UInt64.eq w1 43UL && FStar.UInt64.eq w2 44UL
     && FStar.Int64.eq l0 42L && FStar.Int64.eq l1 43L && FStar.Int64.eq l2 44L
     && e = 123l
     && p.px = 1l && p.py = 2l && q.px = 3l && q.py = 4l && r.px = 5l && r.py = 6l
  then 0l else 1l
