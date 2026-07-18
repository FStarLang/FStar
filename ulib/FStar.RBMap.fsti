(*
   Copyright 2008-2025 Microsoft Research

   Authors: Guido Martínez

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

module FStar.RBMap

open FStar.Class.Ord.Raw

new val t (a b :Type0) : Type0

val empty () : t 'a 'b

val singleton (x :'a) (y : 'b) : t 'a 'b

val is_empty (s : t 'a 'b) : bool

val add {| ord 'a |} (x:'a) (vx : 'b) (s:t 'a 'b) : t 'a 'b

val filter {| ord 'a |} (predicate: 'a -> 'b -> bool) (set: t 'a 'b) : t 'a 'b

val extract_min #a #b {| ord a |} (m : t a b{not (is_empty m)}) : t a b & (a & b)

val remove {| ord 'a |} (x : 'a) (m : t 'a 'b) : t 'a 'b

val mem {| ord 'a |} (x : 'a) (m : t 'a 'b) : bool

val lookup {| ord 'a |} (x : 'a) (m : t 'a 'b) : option 'b

val keys (s : t 'a 'b) : list 'a

val to_list (s : t 'a 'b) : list ('a & 'b)

val equal {| ord 'a, Class.Eq.Raw.deq 'b |} (s1 s2 : t 'a 'b) : bool

val union {| ord 'a |} (s1 s2 : t 'a 'b) : t 'a 'b

(* Intersect the maps. It's left-biased: prefer values on the first map. *)
val inter {| ord 'a |} (s1 s2 : t 'a 'b) : t 'a 'b

val for_all (p : 'a -> 'b -> bool) (s : t 'a 'b) : bool

val for_any (p : 'a -> 'b -> bool) (s : t 'a 'b) : bool

val from_list {| ord 'a |} (xs : list ('a & 'b)) : t 'a 'b

val addn {| ord 'a |} (xs : list ('a & 'b)) (s : t 'a 'b) : t 'a 'b
