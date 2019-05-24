(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Resource.Framing

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics
open FStar.Tactics.CanonCommMonoidSimple.Equiv

open LowStar.Resource

(*
let req : equiv resource = 
  EQ equal 
     equal_refl 
     equal_symm 
     equal_trans

let rm : cm resource req =
  CM empty_resource 
     (<*>) 
     equal_comm_monoid_left_unit 
     equal_comm_monoid_associativity 
     equal_comm_monoid_commutativity 
     equal_comm_monoid_cong

let resolve_delta (outer inner:term) : Tac unit =
  norm [delta_only [`%frame_delta]];
  refine_intro ();
  flip ();
  split ();
  norm [delta_only [`%frame_delta_pre]];
  apply_lemma (quote can_be_split_into_star);
  flip ();
  canon_monoid req rm;
  norm [delta_only [`%frame_delta_post]];
  ignore (forall_intro ());
  apply_lemma (quote can_be_split_into_star);
  canon_monoid req rm
*)

(*
let resolve_delta_simple (outer inner:term) : Tac unit =
  // dump "initial goal";
  refine_intro ();
  // dump "after refine_intro";
  flip ();
  // dump "after flip";
  canon_monoid req rm
  // dump "after canon_monoid"

let resolve_simple_test (outer inner:resource) 
         (#[resolve_delta_simple (quote outer) (quote inner)] 
             delta:resource{(inner <*> delta) `equal` outer})
  : resource = delta
  
#set-options "--use_two_phase_tc false --__temp_fast_implicits"

let test1 (r1 r2 r3 r4:resource) =
  resolve_simple_test (r1 <*> r2 <*> r3 <*> r4) (r1 <*> r2 <*> r3 <*> r4)

let test2 (r1 r2:resource) =
  resolve_simple_test (r1 <*> r2) empty_resource

let test3 (r1 r2 r3 r4 r5 r6 :resource) =  
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  let _ = resolve_simple_test (r6 <*> (r4 <*> r5) <*> r3 <*> r2 <*> r1)
                              (r1 <*> r3 <*> (r4 <*> r6)) in
  ()
*)
