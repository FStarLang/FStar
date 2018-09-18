(*
   Copyright 2015 Chantal Keller and Catalin Hritcu, Microsoft Research and Inria

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

(* Defining accessibility predicates and well-founded recursion like in Coq
   https://coq.inria.fr/library/Coq.Init.Wf.html
*)

module FStar.WellFounded
noeq
type acc (a: Type) (r: (a -> a -> Type)) (x: a) : Type =
  | AccIntro : (y: a -> r y x -> Tot (acc a r y)) -> acc a r x

type well_founded (a: Type) (r: (a -> a -> Type)) = x: a -> Tot (acc a r x)

val acc_inv: #aa: Type -> #r: (aa -> aa -> Type) -> x: aa -> a: (acc aa r x) ->
  Tot (e: (y: aa -> r y x -> Tot (acc aa r y)){e << a})
let acc_inv #aa #r x a = match a with | AccIntro h1 -> h1
assume
val axiom1_dep: #a: Type -> #b: (a -> Type) -> f: (y: a -> Tot (b y)) -> x: a -> Lemma (f x << f)

val axiom1: #a: Type -> #b: Type -> f: (a -> Tot b) -> x: a -> Lemma (precedes (f x) f)
let axiom1 #a #b f x = axiom1_dep f x

let apply (#a: Type) (#b: (a -> Type)) (f: (x: a -> Tot (b x))) (x: a)
  : Pure (b x) (requires True) (ensures (fun r -> r == f x /\ f x << f)) =
  axiom1_dep #a #b f x;
  f x

val fix_F: 
  #aa: Type ->
  #r: (aa -> aa -> Type) ->
  #p: (aa -> Type) ->
  (x: aa -> (y: aa -> r y x -> Tot (p y)) -> Tot (p x)) ->
  x: aa ->
  a: (acc aa r x) ->
  Tot (p x) (decreases a)
let rec fix_F #aa #r #p f x a =
  f x
    (fun y h ->
        axiom1_dep (acc_inv x a) y;
        axiom1 (acc_inv x a y) h;
        fix_F f y (acc_inv x a y h))

val fix: 
  #aa: Type ->
  #r: (aa -> aa -> Type) ->
  well_founded aa r ->
  p: (aa -> Type) ->
  (x: aa -> (y: aa -> r y x -> Tot (p y)) -> Tot (p x)) ->
  x: aa ->
  Tot (p x)
let fix #aa #r rwf p f x = fix_F f x (rwf x)

