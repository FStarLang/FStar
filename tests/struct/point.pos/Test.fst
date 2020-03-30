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
  S.name = "point_struct";
  S.fields = [
    ("X", S.TBase S.TInt);
    ("Y", S.TBase S.TInt);
    ("Color", S.TBase S.TBool);
  ]
}

let point_struct_t = S.TStruct point_struct

let point = S.pointer point_struct_t

let flip
  (p: point)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 -> 
      S.readable h0 p
    /\ S.readable h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.gread h1 (S.gfield p "X") == S.gread h0 (S.gfield p "Y")
    /\ S.gread h1 (S.gfield p "Y") == S.gread h0 (S.gfield p "X")
    /\ S.gread h1 (S.gfield p "Color") == not (S.gread h0 (S.gfield p "Color"))
    ))
= let x = S.read (S.field p "X") in
  let y = S.read (S.field p "Y") in
  let color = S.read (S.field p "Color") in
  S.write (S.field p "X") y;
  S.write (S.field p "Y") x;
  S.write (S.field p "Color") (not color)

#set-options "--z3rlimit 16"

let flip'
  (p: point)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 -> 
      S.readable h0 p
    /\ S.readable h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.gread h1 (S.gfield p "X") == S.gread h0 (S.gfield p "Y")
    /\ S.gread h1 (S.gfield p "Y") == S.gread h0 (S.gfield p "X")
    /\ S.gread h1 (S.gfield p "Color") == not (S.gread h0 (S.gfield p "Color"))
    ))
= let x = S.read (S.field p "X") in
  let y = S.read (S.field p "Y") in
  S.write (S.field p "X") y;
  S.write (S.field p "Y") x;
  let color = S.read (S.field p "Color") in
  S.write (S.field p "Color") (not color)
