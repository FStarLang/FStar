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

module FStar.PartialMap

val t (k:eqtype) (v:Type u#a) : Type u#a

val empty (k:eqtype) (v:Type) : t k v

val sel (#k:eqtype) (#v:Type) (x:k) (m:t k v) : option v

val upd (#k:eqtype) (#v:Type) (x:k) (y:v) (m:t k v) : t k v

val remove (#k:eqtype) (#v:Type) (x:k) (m:t k v) : t k v

let contains (#k:eqtype) (#v:Type) (x:k) (m:t k v) : bool =
  Some? (sel x m)

val sel_upd (#k:eqtype) (#v:Type) (x:k) (y:v) (m:t k v)
  : Lemma (ensures sel x (upd x y m) == Some y)
          [SMTPat (sel x (upd x y m))]

val sel_upd_distinct_key (#k:eqtype) (#v:Type) (x1 x2:k) (y:v) (m:t k v)
  : Lemma (requires x1 =!= x2)
          (ensures sel x2 (upd x1 y m) == sel x2 m)
          [SMTPat (sel x2 (upd x1 y m))]

val sel_remove (#k:eqtype) (#v:Type) (x:k) (m:t k v)
  : Lemma (ensures sel x (remove x m) == None)
          [SMTPat (sel x (remove x m))]

val sel_remove_distinct_key (#k:eqtype) (#v:Type) (x1 x2:k) (m:t k v)
  : Lemma (requires x1 =!= x2)
          (ensures sel x2 (remove x1 m) == sel x2 m)
          [SMTPat (sel x2 (remove x1 m))]

val sel_empty (#k:eqtype) (v:Type) (x:k)
  : Lemma (ensures sel x (empty k v) == None)
          [SMTPat (sel x (empty k v))]

val equal (#k:eqtype) (#v:Type) (m1 m2:t k v) : prop

val eq_intro (#k:eqtype) (#v:Type) (m1 m2:t k v)
  : Lemma (requires forall (x:k). sel x m1 == sel x m2)
          (ensures equal m1 m2)
          [SMTPat (equal m1 m2)]

val eq_elim (#k:eqtype) (#v:Type) (m1 m2:t k v)
  : Lemma (requires equal m1 m2)
          (ensures m1 == m2)
          [SMTPat (equal m1 m2)]
