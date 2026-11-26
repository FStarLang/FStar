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

module PulseTutorial.AtomicsAndInvariants
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Atomic

//owns$
let owns (x:A.atomic_ref U32.t) : timeless_slprop = exists* v. x |-> v
//end owns$

//owns_timeless$
let owns_timeless (x:A.atomic_ref U32.t)
: squash (timeless (owns x))
= ()
//end owns_timeless$

//create_invariant$
ghost
fn create_invariant (r:A.atomic_ref U32.t) (v:erased U32.t)
requires r |-> v
returns i:iname
ensures inv i (owns r)
{
    fold owns;
    new_invariant (owns r)
}
//end create_invariant$

//update_ref_atomic$
atomic
fn update_ref_atomic (r:A.atomic_ref U32.t) (i:iname) (v:U32.t)
preserves inv i (owns r)
requires later_credit 1
opens [i]
{
  with_invariants_a unit emp_inames i (owns r) emp (fun _ -> emp)
  fn _ { // owns r
     unfold owns;        //ghost step;  exists* u. r |-> u
     A.store r v;        //atomic step; r |-> v
     fold owns;          //ghost step;  owns r
  } // inv i (owns r)
}
//end update_ref_atomic$

[@@allow_ambiguous]
ghost
fn pts_to_dup_impossible (#a: Type0) (x:A.atomic_ref a)
preserves x |-> 'v
preserves x |-> 'u
ensures pure False
{
    A.gather x;
    A.pts_to_perm_bound x;
    A.share x;
}


//double_open_bad$
[@@expect_failure [19]]
fn double_open_bad (r:A.atomic_ref U32.t) (i:iname)
requires inv i (owns r)
ensures pure False
{
  later_credit_buy 1;
  with_invariants unit emp_inames i (owns r) (inv i (owns r) ** later_credit 1) (fun _ -> pure False) fn _ {
    with_invariants_a unit emp_inames i (owns r) (owns r) (fun _ -> pure False) fn _ {
      unfold owns; with v. _;
      unfold owns; with u. _;
      pts_to_dup_impossible r;
      drop_ (r |-> u);
      fold owns r;
    };
    rewrite inv i (owns r) as owns r;
  };
}
//end double_open_bad$

//update_ref$
fn update_ref (r:A.atomic_ref U32.t) (i:iname) (v:U32.t)
preserves inv i (owns r)
{                    
  later_credit_buy 1;
  update_ref_atomic r i v;
}
//end update_ref$

//update_ref_fail$
[@@expect_failure [228]]
fn update_ref_fail (r:A.atomic_ref U32.t) (i:iname) (v:U32.t)
preserves inv i (owns r)
{
  with_invariants unit emp_inames i (owns r) emp (fun _ -> emp) fn _ {
    unfold owns;
    A.store r 0ul;
    A.store r v; //two atomic steps are not atomic
    fold owns;
  }
}
//end update_ref_fail$

let readable (r:A.atomic_ref U32.t) : timeless_slprop  = exists* p v. r |-> Frac p v

ghost
fn intro_readable (r:A.atomic_ref U32.t) (p:perm) (v:U32.t)
  requires r |-> Frac p v
  ensures  readable r
{
  fold readable
}


//split_readable$
ghost
fn split_readable (r:A.atomic_ref U32.t) (i:iname)
preserves inv i (readable r)
requires later_credit 1
ensures readable r
opens [i]
{
  with_invariants_g unit emp_inames i (readable r) emp (fun _ -> readable r) fn _ {
        unfold readable;
        with p v. assert (r |-> Frac p v);
        A.share r;
        (* just folding readable would now be ambiguous, need the explicit intro. *)
        // fold readable;
        // fold readable;
        intro_readable r (p /. 2.0R) _;
        intro_readable r (p /. 2.0R) _;
    };
}
//end split_readable$