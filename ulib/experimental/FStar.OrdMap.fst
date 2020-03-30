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
module FStar.OrdMap

open FStar.OrdSet
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

let map_t (k:eqtype) (v:Type) (f:cmp k) (d:ordset k f) =
  g:F.restricted_t k (fun _ -> option v){forall x. mem x d == Some? (g x)}

noeq
type ordmap (k:eqtype) (v:Type) (f:cmp k) =
  | Mk_map: d:ordset k f -> m:map_t k v f d -> ordmap k v f

let empty (#k:eqtype) (#v:Type) #f =
  let d = OrdSet.empty in
  let g = F.on_dom k (fun x -> None) in
  Mk_map d g

let const_on (#k:eqtype) (#v:Type) #f d x =
  let g = F.on_dom k (fun y -> if mem y d then Some x else None) in
  Mk_map d g

let select (#k:eqtype) (#v:Type) #f x m = (Mk_map?.m m) x

let insert (#a:eqtype) (#f:cmp a) (x:a) (s:ordset a f) = union #a #f (singleton #a #f x) s

let update (#k:eqtype) (#v:Type) #f x y m =
  let s' = insert x (Mk_map?.d m) in
  let g' = F.on_dom k (fun (x':k) -> if x' = x then Some y else (Mk_map?.m m) x') in
  Mk_map s' g'

let contains (#k:eqtype) (#v:Type) #f x m = mem x (Mk_map?.d m)

let dom (#k:eqtype) (#v:Type) #f m = (Mk_map?.d m)

let remove (#k:eqtype) (#v:Type) #f x m =
  let s' = remove x (Mk_map?.d m) in
  let g' = F.on_dom k (fun x' -> if x' = x then None else (Mk_map?.m m) x') in
  Mk_map s' g'

let choose (#k:eqtype) (#v:Type) #f m =
  match OrdSet.choose (Mk_map?.d m) with
    | None   -> None
    | Some x -> Some (x, Some?.v ((Mk_map?.m m) x))

let size (#k:eqtype) (#v:Type) #f m = OrdSet.size (Mk_map?.d m)

let equal (#k:eqtype) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) =
  forall x. select #k #v #f x m1 == select #k #v #f x m2

let eq_intro (#k:eqtype) (#v:Type) #f m1 m2 = ()

let eq_lemma (#k:eqtype) (#v:Type) #f m1 m2 =
  let Mk_map s1 g1 = m1 in
  let Mk_map s2 g2 = m2 in
  let _ = cut (feq g1 g2) in
  let _ = OrdSet.eq_lemma s1 s2 in
  ()

let upd_order (#k:eqtype) (#v:Type) #f x y x' y' m =
  let (Mk_map s1 g1) = update #k #v #f x' y' (update #k #v #f x y m) in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x' y' m) in
  cut (feq g1 g2)

let upd_same_k (#k:eqtype) (#v:Type) #f x y y' m =
  let (Mk_map s1 g1) = update #k #v #f x y m in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x y' m) in
  cut (feq g1 g2)

let sel_upd1 (#k:eqtype) (#v:Type) #f x y m = ()

let sel_upd2 (#k:eqtype) (#v:Type) #f x y x' m = ()

let sel_empty (#k:eqtype) (#v:Type) #f x = ()

let sel_contains (#k:eqtype) (#v:Type) #f x m = ()

let contains_upd1 (#k:eqtype) (#v:Type) #f x y x' m = ()

let contains_upd2 (#k:eqtype) (#v:Type) #f x y x' m = ()

let contains_empty (#k:eqtype) (#v:Type) #f x = ()

let contains_remove (#k:eqtype) (#v:Type) #f x y m = ()

let eq_remove (#k:eqtype) (#v:Type) #f x m =
  let (Mk_map s g) = m in
  let m' = remove #k #v #f x m in
  let (Mk_map s' g') = m' in
  let _ = cut (feq g g') in
  ()

let choose_empty (#k:eqtype) (#v:Type) #f = ()

private val dom_empty_helper: #k:eqtype -> #v:Type -> #f:cmp k -> m:ordmap k v f
                      -> Lemma (requires (True))
                               (ensures  ((dom #k #v #f m = OrdSet.empty) ==>
                                          (m == empty #k #v #f)))
let dom_empty_helper (#k:eqtype) (#v:Type) #f m =
  let (Mk_map s g) = m in
  if (not (s = OrdSet.empty)) then ()
  else
    let (Mk_map s' g') = empty #k #v #f in
    cut (feq g g')

let choose_m (#k:eqtype) (#v:Type) #f m =
  dom_empty_helper #k #v #f m;
  let c = choose #k #v #f m in
  match c with
    | None        -> ()
    | Some (x, y) ->
      let m' = remove #k #v #f x m in
      let (Mk_map s' g') = m' in
      let (Mk_map s'' g'') = update #k #v #f x y m' in
      cut (feq (Mk_map?.m m) g'')

let size_empty (#k:eqtype) (#v:Type) #f = ()

let size_remove (#k:eqtype) (#v:Type) #f y m = ()

let dom_lemma (#k:eqtype) (#v:Type) #f x m = ()

let contains_const_on (#k:eqtype) (#v:Type) #f d x y = ()

let select_const_on (#k:eqtype) (#v:Type) #f d x y = ()

let sel_rem1 (#k:eqtype) (#v:Type) #f x m = ()

let sel_rem2 (#k:eqtype) (#v:Type) #f x x' m = ()

let rem_upd (#k:eqtype) (#v:Type) #f x y x' m = ()
