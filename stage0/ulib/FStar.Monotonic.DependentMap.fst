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
module FStar.Monotonic.DependentMap
(** A library for mutable partial, dependent maps,
    that grow monotonically,
    while subject to an invariant on the entire map *)
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module DM = FStar.DependentMap

/// `map a b`: Represent the partial map as a list of pairs of points
let map a b = list (x:a & b x)

/// `repr r`: Converts the list of pairs into a DM.t
let rec repr (#a:eqtype) (#b:a -> Type) (r:map a b)
    : GTot (partial_dependent_map a b)
    = match r with
      | [] -> empty_partial_dependent_map
      | (|x, y|)::tl -> DM.upd (repr tl) x (Some y)

/// Three basic operations on map: empty, sel upd
let empty #a #b = []

let rec sel #a #b r x =
    match r with
    | [] -> None
    | (|x', y|)::tl ->
      if x = x' then Some y else sel tl x

let upd #a #b r x v = (|x, v|)::r

////////////////////////////////////////////////////////////////////////////////

/// `grows'` and `grows`: a preorder of invariant-respecting maps
///    - Needs to be introduced in 2 steps because of an F* limitation
let grows' (#a:eqtype) (#b:a -> Type) (#inv:(partial_dependent_map a b -> Type))
           (m1:imap a b inv) (m2:imap a b inv) =
    forall x.{:pattern (Some? (sel m1 x))}
           Some? (sel m1 x) ==>
              Some? (sel m2 x) /\
              Some?.v (sel m1 x) == Some?.v (sel m2 x)
let grows #a #b #inv = grows' #a #b #inv

let contains_stable #a #b #inv #r t x y = ()
let defined_stable #a #b #inv #r t x = ()
////////////////////////////////////////////////////////////////////////////////

//The main stateful interface is minimal and straigtforward
let alloc #a #b #inv #r _ = ralloc r []

let extend #a #b #inv #r t x y =
    recall t;
    let cur = !t in
    t := upd cur x y;
    mr_witness t (contains t x y)

let lookup #a #b #inv #r t x =
    let m = !t in
    let y = sel m x in
    match y with
    | None -> y
    | Some b ->
      mr_witness t (contains t x b);
      y

let rec mmap_f #a #b #c m f =
  match m with
  | [] ->
   assert (DM.equal (empty_partial_dependent_map #a #c)
                    (DM.map (f_opt f) (empty_partial_dependent_map #a #b)));
   assert_norm (repr #a #c [] == empty_partial_dependent_map #a #c);
   []
  | (| x, y |)::tl -> (| x, f x y |)::(mmap_f #a #b #c tl f)  //AR: doesn't work without these implicits

let map_f #a #b #c #inv #inv' #r #r' t f
  = let m = !t in
    ralloc r' (mmap_f m f)
