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

module B = Pulse.Lib.Box

friend Pulse.Lib.Box

let read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
: stt_atomic U32.t emp_inames
    (pts_to r #p n)
    (fun x -> pts_to r #p n ** pure (reveal n == x))
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

let read_atomic_box b #n #p = read_atomic b #n #p

let write_atomic_box b x #n = write_atomic b x #n

let cas_box r u v #i = cas r u v #i
