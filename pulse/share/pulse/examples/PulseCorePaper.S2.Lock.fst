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

module PulseCorePaper.S2.Lock
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Atomic

noeq
type lock = { r:A.atomic_box U32.t; i:iname }
[@@pulse_unfold]
let maybe b p = if b then p else emp
[@@pulse_unfold]
let lock_inv (r:A.atomic_box U32.t) p : slprop = exists* v. (r |-> v) ** (maybe (v = 0ul) p)
[@@pulse_unfold]
let protects l p = inv l.i (lock_inv l.r p)

fn dup (l:lock) (p:slprop)
preserves protects l p
ensures protects l p
{
  dup_inv l.i (lock_inv l.r p);
}

fn create (p:slprop)
requires p
returns l:lock
ensures protects l p
{
   let r = A.alloc_box 0ul; 
   let i = new_invariant (lock_inv r p);
   ({r; i})
}



fn release (#p:slprop) (l:lock)
preserves protects l p
requires p
{
  with_invariants unit emp_inames l.i (lock_inv l.r p)
    p (fun _ -> emp)
  fn _ {
    with v. assert l.r |-> v;
    drop_ (maybe (v = 0ul) _);
    A.store_box l.r 0ul;
  }
}


divergent
fn rec acquire #p (l:lock)
preserves protects l p
ensures p
{
  let retry =
    with_invariants bool emp_inames l.i (lock_inv l.r p)
      emp (fun retry -> cond retry emp p)
  fn _ {
    with v. assert (l.r |-> v);
    let b = A.compare_exchange_box l.r 0ul 1ul;
    if b {
      rewrite each v as 0ul;
      rewrite p as cond false emp p;
      false
    } else {
      rewrite emp as cond true emp p;
      true
    }
  };
  unfold cond;
  if retry { acquire l }
}

