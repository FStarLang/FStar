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

let struct : S.struct_typ = {
  S.name = "struc";
  S.fields = [
    ("I", S.TBase S.TInt);
    ("B", S.TBase S.TBool);
  ]
}

let struct_t = S.TStruct struct

let obj = S.pointer struct_t

let callee
   (pfrom pto: obj)
: HST.Stack int
  (requires (fun h -> S.readable h pfrom /\ S.live h pto /\ S.loc_disjoint (S.loc_pointer pfrom) (S.loc_pointer pto)))
  (ensures (fun h z h' ->
    S.live h pfrom /\ S.live h pto /\
    S.live h' pfrom /\ S.live h' pto /\
    S.modifies_1 (S.gfield pto "I") h h' /\
    S.readable h' (S.gfield pto "I") /\
    S.gread h (S.gfield pfrom "I") == z /\
    S.gread h' (S.gfield pto "I") == z + 1))
= S.write (S.field pto "I") (S.read (S.field pfrom "I") + 1);
  S.read (S.field pfrom "I")

let more_struct : S.struct_typ = {
  S.name = "more_struct";
  S.fields = [
    ("Less", struct_t);
    ("ThisMore", S.TBase S.TUnit);
  ]
}

let more_struct_t = S.TStruct more_struct

let more_obj = S.pointer more_struct_t

#reset-options "--z3rlimit 16"

(*
 * AR: 06/19: Blindly applying the #1750 fix from array.pos/Test.fst
 *)

let mk_struct_literal (x:S.struct_literal 'a) : Pure (S.struct_literal 'a)
  (requires True)
  (ensures fun _ -> True) = x

let caller
  ()
: HST.Stack int
  (requires (fun _ -> True))
  (ensures (fun _ z _ -> z == 18))
= HST.push_frame();
  let l : S.struct_literal struct = mk_struct_literal [(|"I", 18|); (| "B", true |)] in
  let ofrom : obj = S.screate _ (Some (S.struct_create struct l)) in
  let moto : more_obj = S.screate _ (Some (S.struct_create more_struct [(|"Less",S.struct_create struct [(|"I",1729|); (|"B",false|)]|); (|"ThisMore", ()|)])) in
  let pfrom : obj = ofrom in
  let pto : obj = S.field moto "Less" in
  let z = callee pfrom pto in
  HST.pop_frame ();
  z
