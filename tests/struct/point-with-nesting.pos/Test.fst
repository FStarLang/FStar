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

module S  = FStar.Pointer
module HST = FStar.HyperStack.ST

let point_struct : S.struct_typ = {
  S.name = "point";
  S.fields = [
    "X", S.TBase S.TInt;
    "Y", S.TBase S.TInt;
  ]
}

let point_t = S.TStruct point_struct

let point = S.pointer point_t

// FIXME: how to make the struct name depend on the type parameter?
let colored_object_struct (t: S.typ) : Tot S.struct_typ = {
  S.name = "colored";
  S.fields = [
    "Carrier", t;
    "Color", S.TBase S.TBool;
  ]
}

let colored_object_t (t: S.typ) : Tot S.typ =
  S.TStruct (colored_object_struct t)

let colored_object (t: S.typ) : Tot Type0 = S.pointer (colored_object_t t)

let colored_point = colored_object point_t

#set-options "--z3rlimit 10"

let write_struct_field
  (#l: S.struct_typ)
  (p: S.pointer (S.TStruct l))
  (f: S.struct_field l)
  (v: S.type_of_struct_field l f)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 ->
    S.readable h0 p /\
    S.readable h1 p /\
    // TODO: WHY WHY WHY are *both* modifies clauses below necessary? (i.e. if either is removed, then hints won't replay for flip' )
    S.modifies_1 (S.gfield p f) h0 h1 /\
    S.modifies (S.loc_pointer (S.gfield p f)) h0 h1 /\
    S.gread h1 (S.gfield p f) == v
  ))
= // Another way to make hints successfully replay with only one modifies clause is to admit this definition.
  S.write (S.field p f) v

let flip
  (p: colored_point)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 -> 
      S.readable h0 p /\
      S.readable h1 p /\
      S.modifies_1 p h0 h1 /\ (
      let q : point = S.gfield p "Carrier" in (
      S.gread h1 (S.gfield q "X") == S.gread h0 (S.gfield q "Y") /\
      S.gread h1 (S.gfield q "Y") == S.gread h0 (S.gfield q "X") /\
      S.gread h1 (S.gfield p "Color") == not (S.gread h0 (S.gfield p "Color"))
    ))))
= let pt : point = S.field p "Carrier" in
  let x = S.read (S.field pt "X") in
  let y = S.read (S.field pt "Y") in
  let color = S.read (S.field p "Color") in
  write_struct_field pt "X" y;
  write_struct_field pt "Y" x;
  write_struct_field p "Color" (not color)

let flip'
  (p: colored_point)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 -> 
      S.readable h0 p /\
      S.readable h1 p /\
      S.modifies_1 p h0 h1 /\ (
      let q : point = S.gfield p "Carrier" in (
      S.gread h1 (S.gfield q "X") == S.gread h0 (S.gfield q "Y") /\
      S.gread h1 (S.gfield q "Y") == S.gread h0 (S.gfield q "X") /\
      S.gread h1 (S.gfield p "Color") == not (S.gread h0 (S.gfield p "Color"))
    ))))
= let pt : point = S.field p "Carrier" in
  let x = S.read (S.field pt "X") in
  let y = S.read (S.field pt "Y") in
  write_struct_field pt "X" y;
  write_struct_field pt "Y" x;
  let color = S.read (S.field p "Color") in
//  assert (S.loc_disjoint (S.loc_pointer (S.gfield p "Color")) (S.loc_union (S.loc_pointer (S.gfield pt "X")) (S.loc_pointer (S.gfield pt "Y")))); // TODO: WHY WHY WHY would this be needed if we removed one modifies clause from transparent write_struct_field?
  write_struct_field p "Color" (not color)
