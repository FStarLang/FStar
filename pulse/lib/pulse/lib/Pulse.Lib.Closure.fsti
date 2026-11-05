(*
   Copyright 2025 Microsoft Research

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

(* First-class, manually managed closures.

   A [closure t] boxes a function of type [t], of any arity and effect, from
   [bool -> UInt32.t] to [ref bool -> ref bool -> stt unit p q], together with
   whatever it captures, as one pointer.  Under C that pointer can be passed
   as the [void *] of a C API taking a callback, such as [pthread_create],
   with a small C trampoline calling back through it.

   The closure is heap-allocated by [alloc] and released by [free]; there is
   no reference counting, so the permission [is_closure] is what keeps the
   closure alive and it is fractional so that it can be shared between
   threads.  The specification of the boxed function is its type: the
   predicate is not indexed by the boxed value.

   Under [--codegen C] (custard) a [closure t] is a [custard_closure *]: a
   pointer to a header holding a code pointer, followed by the captured
   environment.  [alloc] converts its argument into a lifted top-level
   function and an environment, [call c x1 .. xn] is an indirect call
   [c->code(c, x1, .., xn)], and [free] is [free(c)].  The C backend requires
   the result of [call] to be applied to all the arguments of [t] right away
   (after [let f = call c], [f] may only be used as the head of a full
   application).  The other backends use the model in [Pulse.Lib.Closure.fst],
   where a closure is just its function. *)
module Pulse.Lib.Closure
#lang-pulse

open PulseCore.FractionalPermission
open Pulse.Lib.Core
open Pulse.Lib.Send

module T = FStar.Tactics.V2

val closure (t: Type0) : Type0

val is_closure (#t: Type0) ([@@@mkey] c: closure t) (#[T.exact (`1.0R)] p: perm) : slprop

val is_closure_timeless (#t: Type0) ([@@@mkey] c: closure t) (p: perm)
  : Lemma (timeless (is_closure c #p))
          [SMTPat (timeless (is_closure c #p))]

instance val is_send_is_closure (#t: Type0) (c: closure t) (p: perm)
  : is_send (is_closure c #p)

(* Box [f], with everything it captures. *)
fn alloc (#t: Type0) (f: t)
  returns c: closure t
  ensures is_closure c

(* The boxed function.  Under [--codegen C] the result must be applied to all
   of its arguments immediately. *)
unobservable
fn call (#t: Type0) (c: closure t) (#p: perm)
  preserves is_closure c #p
  returns f: t

fn free (#t: Type0) (c: closure t)
  requires is_closure c

ghost
fn share (#t: Type0) (c: closure t) (#p: perm)
  requires is_closure c #p
  ensures is_closure c #(p /. 2.0R)
  ensures is_closure c #(p /. 2.0R)

ghost
fn gather (#t: Type0) (c: closure t) (#p0 #p1: perm)
  requires is_closure c #p0
  requires is_closure c #p1
  ensures is_closure c #(p0 +. p1)
