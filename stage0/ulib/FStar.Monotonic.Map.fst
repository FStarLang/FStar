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
(** A library for monotonic references to partial, dependent maps, with a whole-map invariant *)
module FStar.Monotonic.Map

open FStar.HyperStack
open FStar.HyperStack.ST

module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* Partial, dependent maps *)
type map' (a:Type) (b:a -> Type) =
  (x:a -> Tot (option (b x)))

(* Partial, dependent maps, with a whole-map invariant *)
type map (a:Type) (b:a -> Type) (inv:map' a b -> Type0) =
  m:map' a b{inv m}

let upd (#a:eqtype) #b (m:map' a b) (x:a) (y:b x)
  : Tot (map' a b)
  = fun z -> if x = z then Some y else m z

let sel #a #b (m:map' a b) (x:a)
  : Tot (option (b x))
  = m x

let grows_aux #a #b #inv :Preorder.preorder (map a b inv) =
  fun (m1 m2:map a b inv) ->
  forall x.{:pattern (Some? (m1 x))}
      Some? (m1 x) ==> Some? (m2 x) /\ Some?.v (m1 x) == Some?.v (m2 x)

[@@"opaque_to_smt"]
let grows #a #b #inv = grows_aux #a #b #inv

(* Monotone, partial, dependent maps, with a whole-map invariant *)
type t r a b inv = m_rref r (map a b inv) grows  //maybe grows can include the inv?

let empty_map a b
  : Tot (map' a b)
  = fun x -> None

type rid = HST.erid

let alloc (#r:rid) #a #b #inv
  : ST (t r a b inv)
       (requires (fun h -> inv (empty_map a b) /\ witnessed (region_contains_pred r)))
       (ensures (fun h0 x h1 ->
    inv (empty_map a b) /\
    ralloc_post r (empty_map a b) h0 x h1))
  = ralloc r (empty_map a b)

let defined #r #a #b #inv (m:t r a b inv) (x:a) (h:HS.mem)
  : GTot Type0
  = Some? (sel (HS.sel h m) x)

let contains #r #a #b #inv (m:t r a b inv) (x:a) (y:b x) (h:HS.mem)
  : GTot Type0
  = Some? (sel (HS.sel h m) x) /\ Some?.v (sel (HS.sel h m) x) == y

let value #r #a #b #inv (m:t r a b inv) (x:a) (h:HS.mem{defined m x h})
  : GTot (r:b x{contains m x r h})
  = Some?.v (sel (HS.sel h m) x)

let fresh #r #a #b #inv (m:t r a b inv) (x:a) (h:HS.mem)
  : GTot Type0
  = None? (sel (HS.sel h m) x)

let contains_stable #r #a #b #inv (m:t r a b inv) (x:a) (y:b x)
  : Lemma (ensures (stable_on_t m (contains m x y)))
  = reveal_opaque (`%grows) (grows #a #b #inv)

let extend (#r:rid) (#a:eqtype) (#b:a -> Type) (#inv:(map' a b -> Type0)) (m:t r a b inv) (x:a) (y:b x)
  : ST unit
      (requires (fun h -> let cur = HS.sel h m in inv (upd cur x y) /\ sel cur x == None))
      (ensures (fun h0 u h1 ->
      let cur = HS.sel h0 m in
      let hsref = m in
            HS.contains h1 m
            /\ modifies (Set.singleton r) h0 h1
            /\ modifies_ref r (Set.singleton (HS.as_addr hsref)) h0 h1
            /\ HS.sel h1 m == upd cur x y
            /\ HST.witnessed (defined m x)
            /\ HST.witnessed (contains m x y)))
  = recall m;
    reveal_opaque (`%grows) (grows #a #b #inv);
    let cur = !m in
    m := upd cur x y;
    contains_stable m x y;
    mr_witness m (defined m x);
    mr_witness m (contains m x y)

let lookup #r #a #b #inv (m:t r a b inv) (x:a)
  : ST (option (b x))
       (requires (fun h -> True))
       (ensures (fun h0 y h1 ->
       h0==h1 /\
       y == sel (HS.sel h1 m) x /\
       (None? y ==> fresh m x h1) /\
       (Some? y ==>
         defined m x h1 /\
         contains m x (Some?.v y) h1 /\
         HST.witnessed (defined m x) /\
         HST.witnessed (contains m x (Some?.v y)))))
= reveal_opaque (`%grows) (grows #a #b #inv);
  let y = sel !m x in
  match y with
    | None -> y
    | Some b ->
        contains_stable m x b;
        mr_witness m (defined m x);
        mr_witness m (contains m x b);
        y
