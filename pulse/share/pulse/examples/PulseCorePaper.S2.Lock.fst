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
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module Box = Pulse.Lib.Box
// let storable = is_big
// let sprop = s:slprop { storable s }

noeq
type lock = { r:Pulse.Lib.Box.box U32.t; i:iname }
[@@pulse_unfold]
let maybe b p = if b then p else emp
[@@pulse_unfold]
let lock_inv r p : v:slprop { is_slprop2 p ==> is_slprop2 v } = exists* v. Box.pts_to r v ** (maybe (v = 0ul) p)
[@@pulse_unfold]
let protects l p = inv l.i (lock_inv l.r p)

```pulse
fn create (p:storable)
requires p
returns l:lock
ensures protects l p
{
   let r = Box.alloc 0ul; 
   let i = new_invariant (lock_inv r p);
   let l = {r;i};
   rewrite each r as l.r, i as l.i; (* proof hint *)
   l
}
```

```pulse
fn release (#p:slprop) (l:lock)
requires protects l p ** p
ensures protects l p
{
  unfold protects;
  with_invariants l.i
    returns _ : unit
    ensures lock_inv l.r p
    opens [l.i]
  { 
    drop_ (maybe _ _);
    Pulse.Lib.Primitives.write_atomic_box l.r 0ul;
  };
  fold protects;
}
```
module B = Pulse.Lib.Box
assume
val cas_box_alt (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
  : stt_atomic bool #Observable emp_inames 
    (B.pts_to r i)
    (fun b ->
      if b then (B.pts_to r v ** pure (reveal i == u)) 
           else (B.pts_to r i))

```pulse
fn rec acquire #p (l:lock)
requires protects l p
ensures protects l p ** p
{
  unfold protects;
  let b = with_invariants l.i
    returns b:bool 
    ensures lock_inv l.r p ** maybe b p
  {
    let b = cas_box_alt l.r 0ul 1ul;
    if b { true } else { false }
  };
  fold protects;
  if b { () } else { acquire l }
}
```
