(*
   Copyright 2008-2018 Microsoft Research

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
module IfcReificationRegressionTest

open FStar.DM4F.IntST

assume val b : bool
assume val s0 : int
let x = reify (ifc b) s0

unfold let x0 (b:bool) = reify (ifc b)

let x1 (b:bool) =
  match b with
  | true -> (fun s0 ->
    let (_,s) = reify (incr ()) s0 in
    let (y,s) = reify (STINT?.get ()) s in
    let (_,s) = reify (decr ()) s in
    (y,s))
  | _ -> (fun s0 ->
    let (x,s) = reify (STINT?.get ()) s0 in
    (fun s0 -> (x+1, s0)) s)

let x2 (b:bool) =
  match b with
  | true -> (fun s0 ->
    let (_,s) = reify (incr ()) s0 in
    let (y,s) = reify (STINT?.get ()) s in
    let (_,s) = reify (decr ()) s in
    (y,s))
  | _ -> (fun s0 -> reify (STINT?.get () + 1) s0)

let x3 (b:bool) (s0:int) =
  match b with
  | true ->
    let (_,s) = reify (incr ()) s0 in
    let (y,s) = reify (STINT?.get ()) s in
    let (_,s) = reify (decr ()) s in
    (y,s)
  | _ -> reify (STINT?.get () + 1) s0

let bidule0 = assert (forall s0. x0 true s0 = x0 false s0)
let bidule1 = assert (forall s0. x1 true s0 = x1 false s0)
let bidule2 = assert (forall s0. x2 true s0 = x2 false s0)
let bidule3 = assert (forall s0. x3 true s0 = x3 false s0)
