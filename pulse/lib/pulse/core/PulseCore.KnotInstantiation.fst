(*
   Copyright 2024 Microsoft Research

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

module PulseCore.KnotInstantiation
open PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module PM = PulseCore.MemoryAlt
module HS = PulseCore.HeapSig
module IT = PulseCore.IndirectionTheory
open FStar.Ghost {erased, hide, reveal}

[@@erasable]
let hogvs (x:Type u#4) : Type u#4 = address ^-> hogs_val_ x

let map_hogvs #a #b (f:a -> b) : (hogvs a ^-> hogvs b) =
  F.on_dom (hogvs a) fun x -> F.on_dom address fun a -> map_hogs_val f (x a)

noeq type premem_ (x: Type u#4) : Type u#4 = {
  hogs: hogvs x;
  saved_credits: erased nat;
  timeless_heap: timeless_heap_sig.mem;
}

let map_premem #a #b (f: a->b) : (premem_ a ^-> premem_ b) =
  F.on_dom (premem_ a) fun m -> { m with hogs = map_hogvs f m.hogs }

let map_hogvs_id (a:Type) (x:hogvs a) : squash (map_hogvs (id #a) == id #(hogvs a)) =
  f_ext (map_hogvs (id #a)) (id #(hogvs a)) fun x ->
    f_ext (map_hogvs (id #a) x) (id x) fun _ -> ()

let map_hogvs_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (map_hogvs b2c) (map_hogvs a2b) ==
            map_hogvs (compose b2c a2b)))
= let lhs = compose (map_hogvs b2c) (map_hogvs a2b) in
  let rhs = map_hogvs (compose b2c a2b) in
  f_ext lhs rhs fun x -> f_ext (lhs x) (rhs x) fun _ -> ()

let map_premem_id (a:Type) (x:premem_ a) : squash (map_premem (id #a) == id #(premem_ a)) =
  f_ext (map_premem (id #a)) (id #(premem_ a)) fun x -> map_hogvs_id a x.hogs

let map_premem_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (map_premem b2c) (map_premem a2b) ==
            map_premem (compose b2c a2b)))
= let lhs = compose (map_premem b2c) (map_premem a2b) in
  let rhs = map_premem (compose b2c a2b) in
  f_ext lhs rhs fun x -> map_hogvs_comp a b c b2c a2b

let functor_heap : functor u#3 premem_ = {
  fmap = map_premem;
  fmap_id = map_premem_id;
  fmap_comp = map_premem_comp;
}

let premem: Type u#4 = knot_t functor_heap

let read (m: premem) (a: address) : hogs_val = (unpack m).hogs a

let level_ (w: premem) : GTot nat = IT.level w

let credits_ (m: premem) : GTot nat = (unpack m).saved_credits
let timeless_heap_of (m: premem) = (unpack m).timeless_heap

let approx (n: erased nat) : (mem_pred ^-> mem_pred) = approx #_ #functor_heap n
let approx_def n p w =
  assert_norm (approx n p w == (if IT.level w >= n then False else p w))

let premem_of2 (x: premem2) : premem_ mem_pred =
  { hogs = F.on _ x.hogs; saved_credits = x.saved_credits; timeless_heap = x.timeless_heap }
let premem2of_ (x: premem_ mem_pred) : premem2 =
  { hogs = x.hogs; saved_credits = x.saved_credits; timeless_heap = x.timeless_heap }

let pack (n: erased nat) (x: premem2) : premem = pack n (premem_of2 x)
let unpack (x: premem) : premem2 = premem2of_ (unpack x)

let read_pack n x a =
  let x' = premem_of2 x in
  unpack_pack n x';
  assert_norm ((map_premem (approx n) x').hogs a == map_hogs_val (approx n) (x'.hogs a))
let timeless_heap_of_pack n x =
  let x': premem_ (IT.predicate functor_heap) = premem_of2 x in
  IT.unpack_pack n x';
  assert_norm ((map_premem (IT.approx #_ #functor_heap n) x').timeless_heap == x'.timeless_heap)
let credits_pack n x =
  let x': premem_ (IT.predicate functor_heap) = premem_of2 x in
  IT.unpack_pack n x';
  assert_norm ((map_premem (IT.approx #_ #functor_heap n) x').saved_credits == x'.saved_credits)
let level_pack n x =
  unpack_pack n (premem_of2 x)

let mem_ext (w1: premem) (w2: premem { level_ w1 == level_ w2 /\ credits_ w1 == credits_ w2 /\ timeless_heap_of w1 == timeless_heap_of w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2) =
  pack_unpack w1;
  pack_unpack w2;
  f_ext (IT.unpack w1).hogs (IT.unpack w2).hogs fun a -> h a

let mem_pred_ext (f g: mem_pred) (h: (w:premem -> squash (f w <==> g w))) : squash (f == g) =
  f_ext f g fun w ->
    h w;
    PropositionalExtensionality.apply (f w) (g w)

let approx_read (m: premem) a =
  pack_unpack m;
  IT.unpack_pack (level_ m) (IT.unpack m)

let age_to_ (m: premem) (n: erased nat) :
    n:premem { credits_ n == credits_ m /\ timeless_heap_of n == timeless_heap_of m } =
  pack n (unpack m)

let read_age_to_ (m: premem) (n: erased nat) a :
    Lemma (read (age_to_ m n) a == (map_hogs_val (approx n) (read m a)))
    [SMTPat (read (age_to_ m n) a)] =
  ()

let level_age_to_ m (n: erased nat) :
    Lemma (level_ (age_to_ m n) == reveal n) [SMTPat (level_ (age_to_ m n))] =
  ()
