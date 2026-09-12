(*
   Copyright 2008-2026 Microsoft Research

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

(* Section 72.2.  A [ghost fn] parameter.

   [justif] is erased: [stt_ghost] is [@@erasable], so the whole arrow is
   non-informative and nothing about it survives to run time.  Deleting every
   binder of [with_justif] would turn it into a value, so {!Mono.keep_thunk}
   puts the last one back -- and a binder put back that way is there for the
   arity and for nothing else.  Its callers pass [()].

   Until section 72.2 that was encoded for a *type* binder only, so [justif]
   kept its function type while its argument was erased to [()].  The IR
   accepted it and the C compiler did not:

     void ( *justif)(void) = ((custard_unit)0);
     PulseGhostFn_with_justif(justif());

   which is a unit where a function pointer belongs, and then a call through
   it.  Nothing between Pulse and the C compiler had anything to say. *)
module PulseGhostFn
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

noextract
fn with_justif (p : slprop) (justif : ghost fn () preserves p)
  preserves p returns _:unit
{ justif () }

fn main ()
  requires emp
  returns r : U32.t
  ensures emp
{
  with_justif emp
    fn _ {
      ()
    };
  0ul
}
