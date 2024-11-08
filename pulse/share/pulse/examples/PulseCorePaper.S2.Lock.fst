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
module Box = Pulse.Lib.Box

module B = Pulse.Lib.Box
assume
val cas_box_alt (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
  : stt_atomic bool #Observable emp_inames 
    (pts_to r i)
    (fun b ->
      if b then (pts_to r v ** pure (reveal i == u)) 
           else (pts_to r i))

noeq
type lock = { r:Pulse.Lib.Box.box U32.t; i:iname }
[@@pulse_unfold]
let maybe b p = if b then p else emp
[@@pulse_unfold]
let lock_inv r p : slprop = exists* v. Box.pts_to r v ** (maybe (v = 0ul) p)
[@@pulse_unfold]
let protects l p = inv l.i (lock_inv l.r p)


fn create (p:slprop)
requires p
returns l:lock
ensures protects l p
{
   let r = Box.alloc 0ul; 
   let i = new_invariant (lock_inv r p);
   ({r; i} <: lock)
}



fn release (#p:slprop) (l:lock)
requires protects l p ** p
ensures protects l p
{
  later_credit_buy 1;
  with_invariants l.i
  { 
    later_elim _;
    drop_ (maybe _ _);
    Pulse.Lib.Primitives.write_atomic_box l.r 0ul;
    later_intro (lock_inv l.r p);
  }
}



fn rec acquire #p (l:lock)
requires protects l p
ensures protects l p ** p
{
  later_credit_buy 1;
  let retry = with_invariants l.i
    returns retry:bool 
    ensures later (lock_inv l.r p) ** (if retry then emp else p)
  {
    later_elim _;
    let b = cas_box_alt l.r 0ul 1ul;
    if b {
      assert p;
      later_intro (lock_inv l.r p);
      false
    } else {
      later_intro (lock_inv l.r p);
      true
    }
  };
  if retry { acquire l }
}

