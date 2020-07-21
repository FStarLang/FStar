(*
   Copyright 2008-2020 Microsoft Research

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

module SMTReification

type repr (a:Type) (_:unit) = a & int

let return (a:Type) (x:a) : repr a () = x, 0

let bind (a:Type) (b:Type) (f:repr a ()) (g:a -> repr b ()) : repr b () =
  let x, n = f in
  let y, m = g x in
  y, n + m

reifiable reflectable total
layered_effect {
  MST : a:Type -> eqtype_as_type unit -> Effect
  with
  repr = repr;
  return = return;
  bind = bind
}

assume val pure_wp_monotonic (#a:Type) (wp:pure_wp a)
: Lemma (forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q))

let lift_pure_mst (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
: Pure (repr a ()) (requires wp (fun _ -> True)) (ensures fun _ -> True)
= pure_wp_monotonic wp;
  f (), 0

sub_effect PURE ~> MST = lift_pure_mst

let set (n:int) : MST unit () = MST?.reflect ((), n)

let incr_and_set (n:int) : MST unit () = set (n+1)

//AR: 07/03: backtracking on smt reification for layered effects
//let reify_incr_and_set () = assert (snd (reify (incr_and_set 0)) == 1)
