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

#set-options "--initial_fuel 3"

let struct : S.struct_typ = {
  S.name = "struc";
  S.fields = [
    ("I", S.TBase S.TInt);
    ("B", S.TBase S.TBool);
  ]
}

#reset-options "--initial_fuel 2"

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

#set-options "--z3rlimit 16"

let caller
  ()
: HST.Stack int
  (requires (fun _ -> True))
  (ensures (fun _ z _ -> z == 18))
= HST.push_frame();
  let dm : S.struct struct = S.struct_create struct [(|"I", 18|); (|"B", true|)] in
  let b = S.buffer_of_array_pointer (S.screate (S.TArray 2ul struct_t) (Some (Seq.create 2 dm))) in
  let pfrom : obj = S.pointer_of_buffer_cell b (UInt32.uint_to_t 0) in
  let pto : obj = S.pointer_of_buffer_cell b (UInt32.uint_to_t 1) in
  let z = callee pfrom pto in
  HST.pop_frame ();
  z
