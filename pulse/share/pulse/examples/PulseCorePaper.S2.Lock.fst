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
// let storable = is_big
// let sprop = s:slprop { storable s }

module B = Pulse.Lib.Box
assume
val cas_box_alt (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
  : stt_atomic bool #Observable emp_inames 
    (B.pts_to r i)
    (fun b ->
      if b then (B.pts_to r v ** pure (reveal i == u)) 
           else (B.pts_to r i))

noeq
type lock = { r:Pulse.Lib.Box.box U32.t; i:iname }
[@@pulse_unfold]
let maybe b p = if b then p else emp
[@@pulse_unfold]
let lock_inv r p : v:slprop { is_storable p ==> is_storable v } = exists* v. Box.pts_to r v ** (maybe (v = 0ul) p)
[@@pulse_unfold]
let protects l p = inv l.i (lock_inv l.r p)


atomic
fn mk_lock (r:Box.box U32.t) (i:iname) #p
requires inv i (lock_inv r p)
returns l:lock
ensures protects l p
{
  let res = {r;i};
  rewrite each r as res.r, i as res.i; (* proof hint *)
  res
}



fn create (p:storable)
requires p
returns l:lock
ensures protects l p
{
   let r = Box.alloc 0ul; 
   let i = new_invariant (lock_inv r p);
   mk_lock r i
}



fn release (#p:slprop) (l:lock)
requires protects l p ** p
ensures protects l p
{
  with_invariants l.i
  { 
    drop_ (maybe _ _);
    Pulse.Lib.Primitives.write_atomic_box l.r 0ul;
  }
}



fn rec acquire #p (l:lock)
requires protects l p
ensures protects l p ** p
{
  let retry = with_invariants l.i
    returns retry:bool 
    ensures lock_inv l.r p ** (if retry then emp else p)
  {
    let b = cas_box_alt l.r 0ul 1ul;
    if b { false } else { true }
  };
  if retry { acquire l }
}

