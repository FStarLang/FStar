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
open FStar.Pointer
open FStar.HyperStack.All

let s : struct_typ = {
  name = "s";
  fields = [
    "x", TBase TBool;
    "y", TBase TUnit;
  ]
}

let u : union_typ = {
  name = "u";
  fields = [
    "a", TBase TUInt32;
    "b", TStruct s;
  ]
}

let t : typ = TUnion u

#reset-options "--z3rlimit 16"

let f
  (c: bool)
  (p: pointer t)
: ST unit
  (requires (fun h -> live h p))
  (ensures (fun h _ h' ->
    modifies_1 p h h' /\
    readable h' p /\
    union_get_key #u (gread h' p) == (if c then "a" else "b")
  ))
= if c
  then begin
    write (ufield p "a") 18ul
  end else begin
    let q : pointer (TStruct s) = ufield p "b" in
    write (field q "x") true;
    write (field q "y") ();
    readable_struct_forall_mem q
  end
