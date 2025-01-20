(*
   Copyright 2008-2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

/// A partial map, partial in the sense that selecting a key in the map may fail
///   (by returning None)

module FStar.PartialMap

/// The main map type

val t (k:eqtype) ([@@@strictly_positive] v:Type u#a) : Type u#a

/// An empty map

val empty (k:eqtype) (v:Type) : t k v

/// A constructor that constructs the map from a function

val literal (#k:eqtype) (#v:Type) (f:k -> option v) : t k v

/// Select a key from the map, may fail by returning None

val sel (#k:eqtype) (#v:Type) (m:t k v) (x:k) : option v

/// Updating a key in the map

val upd (#k:eqtype) (#v:Type) (m:t k v) (x:k) (y:v) : t k v

/// Removing a key from the map

val remove (#k:eqtype) (#v:Type) (m:t k v) (x:k) : t k v

/// Helper function to check if a key exists in the map

let contains (#k:eqtype) (#v:Type) (m:t k v) (x:k) : bool =
  Some? (sel m x)

/// A constant map

let const (k:eqtype) (#v:Type) (y:v) : t k v =
  literal (fun x -> Some y)

/// The reasoning principles provided by the map

val sel_empty (#k:eqtype) (v:Type) (x:k)
  : Lemma (ensures sel (empty k v) x == None)
          [SMTPat (sel (empty k v) x)]

val sel_literal (#k:eqtype) (#v:Type) (f:k -> option v) (x:k)
  : Lemma (ensures sel (literal f) x == f x)
          [SMTPat (sel (literal f) x)]

val sel_upd (#k:eqtype) (#v:Type) (m:t k v) (x:k) (y:v)
  : Lemma (ensures sel (upd m x y) x == Some y)
          [SMTPat (sel (upd m x y) x)]

val sel_upd_distinct_key (#k:eqtype) (#v:Type) (m:t k v) (x1 x2:k) (y:v)
  : Lemma (requires x1 =!= x2)
          (ensures sel (upd m x1 y) x2 == sel m x2)
          [SMTPat (sel (upd m x1 y) x2)]

val sel_remove (#k:eqtype) (#v:Type) (m:t k v) (x:k)
  : Lemma (ensures sel (remove m x) x == None)
          [SMTPat (sel (remove m x) x)]

val sel_remove_distinct_key (#k:eqtype) (#v:Type) (m:t k v) (x1 x2:k)
  : Lemma (requires x1 =!= x2)
          (ensures sel (remove m x1) x2 == sel m x2)
          [SMTPat (sel (remove m x1) x2)]

/// The map type supports extensional equality
///
/// Below are the intro and elim forms

val equal (#k:eqtype) (#v:Type) (m1 m2:t k v) : prop

val eq_intro (#k:eqtype) (#v:Type) (m1 m2:t k v)
  : Lemma (requires forall (x:k). sel m1 x == sel m2 x)
          (ensures equal m1 m2)
          [SMTPat (equal m1 m2)]

val eq_elim (#k:eqtype) (#v:Type) (m1 m2:t k v)
  : Lemma (requires equal m1 m2)
          (ensures m1 == m2)
          [SMTPat (equal m1 m2)]
