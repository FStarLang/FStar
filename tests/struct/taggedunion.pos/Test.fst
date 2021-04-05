(*
   Copyright 2008-2018 Microsoft Research

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
module Test

module TU = FStar.TaggedUnion
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module P = FStar.Pointer

#set-options "--initial_fuel 4"

(** Either *)

// TODO: how do I choose a name depending on the type parameters?
let either_l (a b : P.typ) : P.union_typ = {
  P.name = "either_l";
  P.fields = [("left", a); ("right", b)];
}

let either_typ (a b : P.typ) : P.typ =
  TU.typ (either_l a b)

let either_tags (a b : P.typ) : TU.tags (either_l a b) =
  [0ul; 1ul]

let either (a b : P.typ) : Type0 =
  TU.t (either_l a b) (either_tags a b)


(** Option *)

// TODO: how do I choose a name depending on the type parameters?
let option_l (a : P.typ) : P.union_typ = {
  P.name = "option_l";
  P.fields = [("none", P.(TBase TUnit)); ("some", a)];
}

let option_typ (a : P.typ) : P.typ =
  TU.typ (option_l a)

let option_tags (a : P.typ) : TU.tags (option_l a) =
  [0ul; 1ul]

let option (a : P.typ) : Type0 =
  TU.t (option_l a) (option_tags a)

(*******************)

let s_l : P.struct_typ = {
  P.name = "s_l";
  P.fields = [("x", P.(TBase TUInt8)); ("y", P.(TBase TUInt8))]
}

// FIXME?
let s_x : P.struct_field s_l = "x"
let s_y : P.struct_field s_l = "y"

let s_typ : P.typ = P.TStruct s_l

let st_typ = either_typ s_typ P.(TBase TUInt16)
let st_tags = either_tags s_typ P.(TBase TUInt16)

#set-options "--z3rlimit 20"

let step_0 (p: P.pointer st_typ) :
  HST.Stack unit
  (requires (fun h -> TU.valid h st_tags p /\ P.readable h p /\ TU.gread_tag h st_tags p == 0ul ))
  (ensures (fun h0 _ h1 ->
    TU.valid h0 st_tags p /\ P.readable h0 p /\
    TU.valid h1 st_tags p /\ P.readable h1 p /\
    TU.gread_tag h1 st_tags p == 0ul /\
    P.modifies_1 p h0 h1
  ))
=
    let h0 = HST.get () in
    let s_ptr : P.pointer (P.TStruct s_l) = TU.field st_tags p "left" in
    let x_ptr = P.field s_ptr "x" in
    let x : UInt8.t = P.read x_ptr in
    let y : UInt8.t = P.read (P.field s_ptr s_y) in
    P.write x_ptr (UInt8.logxor x y);
    let h1 = HST.get () in
    (* pattern on modifies_1 does not trigger *)
    P.modifies_1_readable_struct "x" s_ptr h0 h1

let step (p: P.pointer st_typ) :
  HST.Stack unit
  (requires (fun h -> TU.valid h st_tags p /\ P.readable h p))
  (ensures (fun h0 _ h1 ->
    TU.valid h0 st_tags p /\ P.readable h0 p /\
    TU.valid h1 st_tags p /\ P.readable h1 p /\
    TU.gread_tag h1 st_tags p == 0ul /\
    P.modifies_1 p h0 h1
  ))
=
  let t = TU.read_tag st_tags p in
  if t = 0ul then (
    step_0 p
  ) else (
    assert (t == 1ul);
    let z : UInt16.t = P.read (TU.field st_tags p "right") in
    let x : UInt8.t = FStar.Int.Cast.uint16_to_uint8 z in
    let v : P.struct s_l = P.struct_create s_l [(|"x", x|); (|"y", 0uy|)] in
    TU.write st_tags p "left" v
  )

let step_alt (p: P.pointer st_typ):
  HST.Stack unit
  (requires (fun h -> TU.valid h st_tags p /\ P.readable h p))
  (ensures (fun h0 _ h1 ->
    TU.valid h0 st_tags p /\ P.readable h0 p /\
    TU.valid h1 st_tags p /\ P.readable h1 p /\
    TU.gread_tag h1 st_tags p == 0ul /\
    P.modifies_1 p h0 h1
  ))
=
  let t = TU.read_tag st_tags p in
  if t = 0ul then (
    step_0 p
  ) else (
    assert (t == 1ul);
    let z : UInt16.t = P.read (TU.field st_tags p "right") in
    let x : UInt8.t = FStar.Int.Cast.uint16_to_uint8 z in
    TU.write_tag st_tags p "left";
    let s_ptr : P.pointer (P.TStruct s_l) = TU.field st_tags p "left" in
    P.write (P.field s_ptr "x") x;
    P.write (P.field s_ptr "y") 0uy;
    let h2 = HST.get () in
    P.readable_struct_fields_readable_struct h2 s_ptr
  )
