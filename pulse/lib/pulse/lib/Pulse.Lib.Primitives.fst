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

module Pulse.Lib.Primitives
#lang-pulse


let read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
= Pulse.Lib.Core.as_atomic _ _ ((let open Pulse.Lib.Reference in ( ! )) r #n #p)

let write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
= Pulse.Lib.Core.as_atomic _ _ ((let open Pulse.Lib.Reference in ( := )) r x #n)


fn cas_impl
    (r:ref U32.t)
    (u v:U32.t)
    (#i:erased U32.t)
requires
  pts_to r i
  returns b:bool
ensures
  cond b (pts_to r v ** pure (reveal i == u)) 
         (pts_to r i)
{
  let u' = !r;
  if (u = u')
  {
    r := v;
    fold (cond true (pts_to r v ** pure (reveal i == u)) (pts_to r i));
    true
  }
  else
  {
    fold cond false (pts_to r v ** pure (reveal i == u)) (pts_to r i);
    false
  }
}


let cas r u v #i = Pulse.Lib.Core.as_atomic _ _ (cas_impl r u v #i)

atomic fn read_atomic_box (r:B.box U32.t) (#n:erased U32.t) (#p:perm)
  preserves r |-> Frac p n
  returns x:U32.t
  ensures pure (reveal n == x)
{
  Box.to_ref_pts_to r;
  let x = read_atomic (Box.box_to_ref r);
  Box.to_box_pts_to r;
  x
}

atomic fn write_atomic_box (r:B.box U32.t) (x:U32.t) (#n:erased U32.t)
  requires r |-> n
  ensures r |-> x
{
  Box.to_ref_pts_to r;
  write_atomic (Box.box_to_ref r) x;
  Box.to_box_pts_to r;
}

atomic fn cas_box (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
  requires r |-> i
  returns b: bool
  ensures cond b ((r |-> v) ** pure (reveal i == u)) (r |-> i)
{
  Box.to_ref_pts_to r;
  let b = cas (Box.box_to_ref r) u v;
  if (b) {
    unfold cond;
    Box.to_box_pts_to r;
    fold cond true ((r |-> v) ** pure (reveal i == u)) (r |-> i);
    b
  } else {
    unfold cond;
    Box.to_box_pts_to r;
    fold cond false ((r |-> v) ** pure (reveal i == u)) (r |-> i);
    b
  }
}
