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
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module PM = PulseCore.MemoryAlt
module HS = PulseCore.HeapSig
open FStar.Ghost {erased, hide, reveal}

let address = erased nat
let timeless_heap_sig : HS.heap_sig u#3 = PM.pulse_heap_sig

[@@erasable]
noeq type hogs_val_ (x: Type u#4) =
  | None
  | Inv : x -> hogs_val_ x
  | Pred : x -> hogs_val_ x

let hogs_val_le #t (x y: hogs_val_ t) : prop =
  match x, y with
  | None, _ -> True
  | Inv p, Inv q -> p == q
  | Pred p, Pred q -> p == q
  | _ -> False

let map_hogs_val #x #y (f: x->y) (v: hogs_val_ x) : hogs_val_ y =
  match v with
  | None -> None
  | Pred p -> Pred (f p)
  | Inv p -> Inv (f p)

let f_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x;
  F.extensionality _ _ f g

val premem: Type u#4
let mem_pred : Type u#4 = premem ^-> prop

let hogs_val = hogs_val_ mem_pred

val read (m: premem) (a: address) : hogs_val
val level_ (w: premem) : GTot nat
val credits_ (m: premem) : GTot nat
val timeless_heap_of (m: premem) : timeless_heap_sig.mem

val approx (n: erased nat) : (mem_pred ^-> mem_pred)
val approx_def (n: erased nat) (p: mem_pred) w :
    Lemma (approx n p w == (if level_ w >= n then False else p w))
      [SMTPat (approx n p w)]

noeq type premem2 : Type u#4 = {
  hogs: address -> hogs_val;
  saved_credits: erased nat;
  timeless_heap: timeless_heap_sig.mem;
}

val pack (n: erased nat) (x: premem2) : premem

val read_pack n x a :
    Lemma (read (pack n x) a == map_hogs_val (approx n) (x.hogs a))
      [SMTPat (read (pack n x) a)]
val timeless_heap_of_pack n x :
    Lemma (timeless_heap_of (pack n x) == x.timeless_heap)
      [SMTPat (timeless_heap_of (pack n x))]
val credits_pack n x :
    Lemma (credits_ (pack n x) == reveal x.saved_credits)
      [SMTPat (credits_ (pack n x))]
val level_pack n x :
    Lemma (level_ (pack n x) == reveal n)
      [SMTPat (level_ (pack n x))]

val mem_ext (w1: premem) (w2: premem { level_ w1 == level_ w2 /\ credits_ w1 == credits_ w2 /\ timeless_heap_of w1 == timeless_heap_of w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2)

val mem_pred_ext (f g: mem_pred) (h: (w:premem -> squash (f w <==> g w))) : squash (f == g)

val approx_read (m: premem) a :
    Lemma (map_hogs_val (approx (level_ m)) (read m a) == read m a)
    [SMTPat (read m a)]

val age_to_ (m: premem) (i: erased nat) :
    n:premem { credits_ n == credits_ m /\ timeless_heap_of n == timeless_heap_of m /\ level_ n == reveal i }

val read_age_to_ (m: premem) (n: erased nat) a :
    Lemma (read (age_to_ m n) a == (map_hogs_val (approx n) (read m a)))
    [SMTPat (read (age_to_ m n) a)]

val level_age_to_ m (n: erased nat) :
    Lemma (level_ (age_to_ m n) == reveal n) [SMTPat (level_ (age_to_ m n))]
