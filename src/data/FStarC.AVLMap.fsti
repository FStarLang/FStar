(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.AVLMap

(* Persistent maps as AVL trees, ordered by a comparison function passed
   explicitly.  This is the representation behind FStarC.PSMap and
   FStarC.PIMap. *)

open FStarC.Effect

val t (k v : Type0) : Type0

(* A comparison returns a negative, zero or positive number. *)
type cmp (k : Type0) = k -> k -> FStarC.SmallInt.t

val empty (#k #v : Type0) : t k v

val add (#k #v : Type0) (c : cmp k) (key : k) (value : v) (m : t k v) : t k v

val find (#k #v : Type0) (c : cmp k) (key : k) (m : t k v) : option v

val remove (#k #v : Type0) (c : cmp k) (key : k) (m : t k v) : t k v

(* In increasing order of keys. *)
val fold (#k #v : Type0) (#a : Type) (f : k -> v -> a -> ML a) (m : t k v) (acc : a) : ML a

val fold_pure (#k #v : Type0) (#a : Type) (f : k -> v -> a -> a) (m : t k v) (acc : a) : a

val iter (#k #v : Type0) (f : k -> v -> ML unit) (m : t k v) : ML unit

(* The first [Some] that [f] returns, in increasing order of keys. *)
val find_map (#k #v : Type0) (#a : Type) (f : k -> v -> ML (option a)) (m : t k v) : ML (option a)
