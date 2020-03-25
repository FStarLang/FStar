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
module Bug170b

open FStar.Classical

assume val p2b: p:Type -> Tot (b:bool{b = true <==> p})

type b2p : bool -> Type =
  | B2pI : b2p true

assume val p2p2 : a:Type -> a -> Tot (b2p(p2b a))

type v = a : Type -> ((a-> Tot bool) -> a -> Tot bool) -> a -> Tot bool
type u = v -> Tot bool

val sb : v -> Tot v
let sb (z : v) = fun (a:Type) r (x : a) -> r (z a r) x

val le : i : (u -> Tot bool) -> x: u -> Tot bool
let le i x = x (fun (a : Type) r y -> i (fun (v : v)-> sb v a r y))

val wf : u
let wf (z : v) = let y : (u -> Tot bool) = z u le in p2b (x : u -> b2p (le y x) -> Tot (b2p (y x)))

let omega =
  (fun (i : u -> Tot bool) (y : (x1 : u -> b2p (le i x1) -> Tot (b2p (i x1)))) ->
    y wf
      (p2p2
         ( x2 : u ->
           b2p (le (fun (a : u) -> i (fun (v : v) -> sb v u le a)) x2) ->
           b2p (i (fun (v : v) -> sb v u le x2)))
         (fun (x3 : u) (h0 : b2p (le (fun (a : u) -> i (fun (v : v) -> sb v u le a)) x3)) ->
           y (fun (v : v) -> sb v u le x3) h0)))
