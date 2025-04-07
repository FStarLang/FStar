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
module T = FStar.Tactics
module U32 = FStar.UInt32

//owns$
let owns (x:ref U32.t) : timeless_slprop = exists* v. pts_to x v
//end owns$

//owns_timeless$
let owns_timeless (x:ref U32.t)
: squash (timeless (owns x))
by T.(norm [delta_only [`%owns; `%auto_squash]]; 
      mapply (`FStar.Squash.return_squash);
      mapply (`timeless_exists))
= ()
//end owns_timeless$

//create_invariant$
ghost
fn create_invariant (r:ref U32.t) (v:erased U32.t)
requires pts_to r v
returns i:iname
ensures inv i (owns r)
{
    fold owns;
    new_invariant (owns r)
}
//end create_invariant$

//update_ref_atomic0$
[@@expect_failure]
atomic
fn update_ref_atomic (r:ref U32.t) (i:iname) (v:U32.t)
requires inv i (owns r)
ensures inv i (owns r)
{
  with_invariants i {    //later (owns r)
     unfold owns;        //cannot prove owns; only later (owns r)
  }
}
//end update_ref_atomic0$


//update_ref_atomic$
atomic
fn update_ref_atomic (r:ref U32.t) (i:iname) (v:U32.t)
requires inv i (owns r) ** later_credit 1
ensures inv i (owns r)
opens [i]
{
  with_invariants i {    //later (owns r) ** later_credit 1
     later_elim _;       //ghost step: owns r
     unfold owns;        //ghost step;  exists* u. pts_to r u
     write_atomic r v;   //atomic step; pts_to r v
     fold owns;          //ghost step;  owns r
     later_intro (owns r) //ghost step: later (owns r)
  } // inv i (owns r)
}
//end update_ref_atomic$

//update_ref_atomic_alt$
atomic
fn update_ref_atomic_alt (r:ref U32.t) (i:iname) (v:U32.t)
requires inv i (owns r)
ensures inv i (owns r)
opens [i]
{
  with_invariants i {    //later (owns r) ** later_credit 1
     later_elim_timeless _;       //owns r
     unfold owns;        //ghost step;  exists* u. pts_to r u
     write_atomic r v;   //atomic step; pts_to r v
     fold owns;          //ghost step;  owns r
     later_intro (owns r) //later (owns r)
  } // inv i (owns r)
}
//end update_ref_atomic_alt$


ghost
fn pts_to_dup_impossible #a (x:ref a)
requires pts_to x 'v ** pts_to x 'u
ensures  pts_to x 'v ** pts_to x 'u ** pure False
{
    gather x;
    pts_to_perm_bound x;
    share x;    
}


//double_open_bad$
[@@expect_failure]
fn double_open_bad (r:ref U32.t) (i:inv (owns r))
requires emp
ensures pure False
{
    with_invariants i {
      with_invariants i {
        unfold owns;
        unfold owns;
        pts_to_dup_impossible r;
        fold owns;
        fold owns
      }
    }
}
//end double_open_bad$

//update_ref$
fn update_ref (r:ref U32.t) (i:iname) (v:U32.t)
requires inv i (owns r)
ensures inv i (owns r)
{                    
  later_credit_buy 1;
  update_ref_atomic r i v;
}
//end update_ref$

//update_ref_fail$
[@@expect_failure] 
fn update_ref_fail (r:ref U32.t) (i:iname) (v:U32.t)
requires inv i (owns r)
ensures inv i (owns r)
{
  with_invariants i {
    unfold owns;
    r := v; //not atomic
    fold owns;
  }
}
//end update_ref_fail$

let readable (r:ref U32.t) : timeless_slprop  = exists* p v. pts_to r #p v

ghost
fn intro_readable (r:ref U32.t) (p:perm) (v:U32.t)
  requires pts_to r #p v
  ensures  readable r
{
  fold readable
}


//split_readable$
ghost
fn split_readable (r:ref U32.t) (i:iname)
requires inv i (readable r)
ensures inv i (readable r) ** readable r
opens [i]
{
    with_invariants i {
        later_elim_timeless _;
        unfold readable;
        with p v. assert (pts_to r #p v);
        share r;
        (* just folding readable would now be ambiguous, need the explicit intro. *)
        // fold readable;
        // fold readable;
        intro_readable r (p /. 2.0R) _;
        intro_readable r (p /. 2.0R) _;
        later_intro (readable r)
    };
}
//end split_readable$