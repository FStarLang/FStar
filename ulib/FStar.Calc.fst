(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Guido Martinez, Aseem Rastogi, Nikhil Swamy
*)

module FStar.Calc

open FStar.Squash
open FStar.Preorder

noeq
type calc_chain #a : list (relation a) -> a -> a -> Type =
  | CalcRefl : #x:a -> calc_chain [] x x
  | CalcStep :
    rs:(list (relation a)) -> #p:(relation a) ->
    #x:a -> #y:a -> #z:a -> calc_chain rs x y -> squash (p y z) -> calc_chain (p::rs) x z

let rec elim_calc_chain #a (rs:list (relation a)) (#x #y:a) (pf:calc_chain rs x y)
  : Lemma (ensures (calc_chain_related rs x y))
  = let steps = [delta_only [`%calc_chain_related]; iota; zeta] in
    let t = norm steps (calc_chain_related rs x y) in
    norm_spec steps (calc_chain_related rs x y);
    match pf with
    | CalcRefl -> ()
    | CalcStep tl pf _ -> elim_calc_chain tl pf

let _calc_init (#a:Type) (x:a) : calc_chain [] x x = CalcRefl

let calc_init #a x = return_squash (_calc_init x) 

let _calc_step (#t:Type) (#rs:list (relation t)) (#x #y:t)
  (p:relation t)
  (z:t)
  (pf:calc_chain rs x y)
  (j:squash (p y z))
  : GTot (calc_chain (p::rs) x z)
  = CalcStep rs pf j

let calc_step #a #x #y p z #rs pf j =
  bind_squash (pf ()) (fun pk -> return_squash (_calc_step p z pk (j ())))

let calc_finish #a p #x #y #rs pf =
  let steps = [delta_only [`%calc_chain_related]; iota; zeta] in
  let t = norm steps (calc_chain_related rs x y) in
  norm_spec steps (calc_chain_related rs x y);
  let _ : squash (p x y) = bind_squash (pf ()) (fun pk -> elim_calc_chain rs pk) in
  ()

let calc_push_impl #p #q f =
  Classical.arrow_to_impl f
