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

(* The model: a closure is its function, and owns nothing.  This is what the
   OCaml, F# and Cherry backends extract, and they need nothing more since
   their functions already are closures.  The C backend does not extract this
   file: it maps every name in the interface to a primitive. *)
module Pulse.Lib.Closure
#lang-pulse

open PulseCore.FractionalPermission
open Pulse.Lib.Core
open Pulse.Lib.Send

let closure t = t

let is_closure #t c #p = emp

let is_closure_timeless #t c p = ()

instance is_send_is_closure #t c p = is_send_placeless emp #placeless_emp

fn alloc (#t: Type0) (f: t)
  returns c: closure t
  ensures is_closure c
{
  fold (is_closure #t f #1.0R);
  f
}

unobservable
fn call (#t: Type0) (c: closure t) (#p: perm)
  preserves is_closure c #p
  returns f: t
{
  c
}

fn free (#t: Type0) (c: closure t)
  requires is_closure c
{
  unfold is_closure c #1.0R
}

ghost
fn share (#t: Type0) (c: closure t) (#p: perm)
  requires is_closure c #p
  ensures is_closure c #(p /. 2.0R)
  ensures is_closure c #(p /. 2.0R)
{
  unfold is_closure c #p;
  fold is_closure c #(p /. 2.0R);
  fold is_closure c #(p /. 2.0R)
}

ghost
fn gather (#t: Type0) (c: closure t) (#p0 #p1: perm)
  requires is_closure c #p0
  requires is_closure c #p1
  ensures is_closure c #(p0 +. p1)
{
  unfold is_closure c #p0;
  unfold is_closure c #p1;
  fold is_closure c #(p0 +. p1)
}
