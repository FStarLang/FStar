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

module Records
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module U8 = FStar.UInt8

(* test record mutation and permissions for records of byte refs *)

noeq
type rec2 = {
  r1: R.ref U8.t;
  r2: R.ref U8.t;
}

type rec_repr = {
  v1: U8.t;
  v2: U8.t;
}

let rec_perm (r:rec2) (v:rec_repr)
  : slprop
  = R.pts_to r.r1 v.v1 **
    R.pts_to r.r2 v.v2


// When defining a predicate like rec_perm relating 
// a record and a record_repr, it's convenient to define
// a ghost function to fold the predicate.
// Eventually, it would be nice to auto-generate this 
// ghost function from the predicate definition.
// #push-options "--debug Records --debug_level Extreme"

ghost
fn fold_rec_perm (r:rec2) (#v1 #v2:erased U8.t)
  requires
    R.pts_to r.r1 v1 **
    R.pts_to r.r2 v2
  ensures
    (rec_perm r {v1; v2})
{
  fold (rec_perm r {v1; v2})
}


// Then, mutating a single field of the record involves:

fn mutate_r2 (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists* (v_:rec_repr) .
    rec_perm r v_ ** pure (v_.v2 == 0uy /\ v_.v1 == v.v1)
{
  unfold (rec_perm r v); //1. unfolding the predicate
  r.r2 := 0uy;           //2. working with the fields
  fold_rec_perm r;       //3. folding it back up
  ()
}



fn alloc_rec (v1 v2:U8.t)
  requires emp
  returns r:rec2
  ensures (rec_perm r {v1; v2})
{
  let r1 = alloc #U8.t v1;
  let r2 = alloc #U8.t v2; 
  let r = { r1; r2 };
  (* Unfortunately, these two rewrites are still needed
     to "rename" r1 and r2 as r.r1 and r.r2 *)
  rewrite (R.pts_to r1 v1)
      as  (R.pts_to r.r1 v1);
  rewrite (R.pts_to r2 v2)
      as  (R.pts_to r.r2 v2);
  fold_rec_perm r;
  r
}


//Here's another more compact way, using rename

fn alloc_rec_alt (v1 v2:U8.t)
  requires emp
  returns r:rec2
  ensures (rec_perm r {v1; v2})
{
  let r1 = alloc v1;
  let r2 = alloc v2; 
  let r = { r1; r2 };
  rewrite each r1 as r.r1, r2 as r.r2;
  fold_rec_perm r;
  r
}


//Here's yet another way, a bit more explicit

fn alloc_rec_alt_alt (v1 v2:U8.t)
  requires emp
  returns r:rec2
  ensures (rec_perm r {v1; v2})
{
  let r1 = alloc v1;
  let r2 = alloc v2; 
  let r = { r1; r2 };
  with w1 w2.
    rewrite each r1 as r.r1, r2 as r.r2 in 
      (R.pts_to r1 w1 ** R.pts_to r2 w2);
  fold_rec_perm r;
  r
}

//Some alternate ways to do it, useful test cases

// helpers 


fn get_witness (x:R.ref U8.t) (#y:Ghost.erased U8.t)
requires R.pts_to x y
returns z:Ghost.erased U8.t
ensures R.pts_to x y ** pure (y==z)
{   
    y
}



fn unfold_and_fold_manually (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists* (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 v.v1 **
        R.pts_to r.r2 v.v2);

  rewrite (R.pts_to r.r1 v.v1 **
           R.pts_to r.r2 v.v2)
    as (rec_perm r v);
  
  ()
}



fn explicit_unfold_witness_taking_and_fold (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists* (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 v.v1 **
        R.pts_to r.r2 v.v2);

  r.r2 := 0uy;
  let v2 = get_witness(r.r2);

  rewrite (R.pts_to r.r1 v.v1 **
           R.pts_to r.r2 v2)
    as    (rec_perm r {v with v2});
  ()
}



fn explicit_unfold_slightly_better_witness_taking_and_fold (r:rec2) (#v:Ghost.erased rec_repr)
  requires rec_perm r v
  ensures exists* (v_:rec_repr) . rec_perm r v_
{
  rewrite (rec_perm r v)
    as (R.pts_to r.r1 v.v1 **
        R.pts_to r.r2 v.v2);

  r.r2 := 0uy;
  with v2. 
   rewrite (R.pts_to r.r1 v.v1 **
            R.pts_to r.r2 v2)
    as    (rec_perm r {v with v2});

  ()
}

