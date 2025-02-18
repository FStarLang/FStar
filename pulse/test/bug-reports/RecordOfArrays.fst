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

module RecordOfArrays
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module US = FStar.SizeT

// Similar to Records, but with arrays

noeq
type rec_array = {
  r1: A.array U8.t;
  r2: A.array U8.t;
}

type rec_array_repr = {
  v1: Seq.seq U8.t;
  v2: Seq.seq U8.t;
}

let rec_array_perm (r:rec_array) (v:rec_array_repr)
  : slprop = 
  A.pts_to r.r1 v.v1 **
  A.pts_to r.r2 v.v2

//Using record syntax directly in Pulse slprops
//leads to strange type inference errors
let mk_rec_array_repr (v1 v2:Seq.seq U8.t) = { v1=v1; v2=v2 }


ghost
fn fold_rec_array_perm (r:rec_array) (#v1 #v2:erased (Seq.seq U8.t))
  requires
    A.pts_to r.r1 v1 **
    A.pts_to r.r2 v2
  ensures
    rec_array_perm r (mk_rec_array_repr v1 v2)
{
  fold (rec_array_perm r (mk_rec_array_repr v1 v2))
}



// Then, mutating a one of the arrays of the record involves:

fn mutate_r2 (r:rec_array) (#v:(v:Ghost.erased rec_array_repr { Seq.length v.v2 > 0 }))
  requires rec_array_perm r v
  ensures exists* (v_:rec_array_repr) .
    rec_array_perm r v_ ** pure (v_.v2 `Seq.equal` Seq.upd v.v2 0 0uy /\ v_.v1 == v.v1)
{
  unfold (rec_array_perm r v); //1. unfolding the predicate
  ((r.r2).(0sz) <- 0uy);       //2. working with the fields
  fold_rec_array_perm r;       //3. folding it back up
  ()
}


// Some alternate more explicit ways


fn get_witness_array (x:A.array U8.t) (#y:Ghost.erased (Seq.seq U8.t))
requires A.pts_to x y
returns z:Ghost.erased (Seq.seq U8.t)
ensures A.pts_to x y ** pure (y==z)
{   
    y
}


let rec_array_repr_with_v2 (r:rec_array_repr) v2 = {r with v2}


fn mutate_rec_get_witness (l:US.t) (r:rec_array) (#v:Ghost.erased rec_array_repr)
  requires (
    rec_array_perm r v **
    pure (US.v l > 0 /\ A.length r.r2 == (US.v l) /\ Seq.length v.v2 == (US.v l))
  )
  ensures exists* v_.
    rec_array_perm r v_ **
    pure (Seq.length v.v2 > 0 /\ v_.v2 `Seq.equal` Seq.upd v.v2 0 0uy /\ v_.v1 == v.v1)
{
  rewrite (rec_array_perm r v)
    as (A.pts_to r.r1 v.v1 **
        A.pts_to r.r2 v.v2);
  
  ((r.r2).(0sz) <- 0uy);

  let y = get_witness_array (r.r2);   

  rewrite (A.pts_to r.r1 v.v1 **
           A.pts_to r.r2 y)
    as    (rec_array_perm r (rec_array_repr_with_v2 v y));
    
  ()
}

