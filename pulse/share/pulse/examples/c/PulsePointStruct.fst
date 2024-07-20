(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulsePointStruct
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.C.Types

module U32 = FStar.UInt32
// module C = C // for _zero_for_deref


fn swap (#v1 #v2: Ghost.erased U32.t) (r1 r2: ref (scalar U32.t))
requires
  ((r1 `pts_to` mk_scalar (Ghost.reveal v1)) ** (r2 `pts_to` mk_scalar (Ghost.reveal v2)))
ensures
  ((r1 `pts_to` mk_scalar (Ghost.reveal v2)) ** (r2 `pts_to` mk_scalar (Ghost.reveal v1)))
{
  let _ : squash (mk_scalar (Ghost.reveal v1) == mk_fraction (scalar U32.t) (mk_scalar (Ghost.reveal v1)) 1.0R) = (); // FIXME: WHY WHY WHY does the pattern on mk_fraction_full_scalar not trigger?
  let x1 = read r1;
  let x2 = read r2;
  write r1 x2;
  write r2 x1;
}


#set-options "--print_implicits"

inline_for_extraction noextract
let _x = norm Pulse.C.Typestring.norm_typestring (Pulse.C.Typestring.mk_string_t "x")

inline_for_extraction noextract
let _y = norm Pulse.C.Typestring.norm_typestring (Pulse.C.Typestring.mk_string_t "y")

noextract
inline_for_extraction
[@@ norm_field_attr]
let point_fields =
  field_description_cons0 _x "x" (scalar U32.t) (
  field_description_cons0 _y "y" (scalar U32.t) (
  field_description_nil))

inline_for_extraction noextract
let _point = norm Pulse.C.Typestring.norm_typestring (Pulse.C.Typestring.mk_string_t "PulsePointStruct.point")

let _ = define_struct0 _point "PulsePointStruct.point" point_fields

inline_for_extraction noextract
let point = struct0 _point "PulsePointStruct.point" point_fields

#push-options "--fuel 0"


fn swap_struct (p: ref point) (v: Ghost.erased (typeof point))
requires
    (p `pts_to` v ** pure (
      exists (vx vy: U32.t) . struct_get_field v "x" === mk_scalar vx /\ struct_get_field v "y" === mk_scalar vy
    ))
ensures
    (exists* v' . p `pts_to` v' ** pure (
      struct_get_field v' "x" === struct_get_field v "y" /\
      struct_get_field v' "y" === struct_get_field v "x"
    ))
{
  let px = struct_field0 _ p "x" (scalar U32.t);
  let py = struct_field0 _ p "y" (scalar U32.t);
  let x = read px;
  let y = read py;
  write px y;
  write py x;
  let _ = unstruct_field_and_drop p "x" px;
  let _ = unstruct_field_and_drop p "y" py;
  ()
}


#pop-options
