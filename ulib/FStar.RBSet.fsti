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

module FStar.RBSet

(* This module implements sets based on red-black trees.
   It does not expose functional properties, it is mostly
   useful for unverified code. *)

open FStar.Class.Ord.Raw

new val t (a:Type0) : Type0

val empty () : t 'a

val singleton (x : 'a) : t 'a

val is_empty (s : t 'a) : bool

val add {| ord 'a |} (x:'a) (s : t 'a) : t 'a

val filter {| ord 'a |} (predicate : 'a -> bool) (set : t 'a): t 'a

val extract_min #a {| ord a |} (s : t a{not (is_empty s)}) : t a & a

val remove {| ord 'a |} (x : 'a) (s : t 'a) : t 'a

val mem {| ord 'a |} (x : 'a) (s : t 'a) : bool

val elems (s : t 'a) : list 'a

val equal {| ord 'a |} (s1 s2 : t 'a) : bool

val union {| ord 'a |} (s1 s2 : t 'a) : t 'a

val inter {| ord 'a |} (s1 s2 : t 'a) : t 'a

val diff {| ord 'a |} (s1 s2 : t 'a) : t 'a

val subset {| ord 'a |} (s1 s2 : t 'a) : bool

val for_all (p:'a -> bool) (s:t 'a) : bool

val for_any (p:'a -> bool) (s:t 'a) : bool

val from_list {| ord 'a |} (xs : list 'a) : t 'a

val addn {| ord 'a |} (xs : list 'a) (s : t 'a) : t 'a

val collect #a {| ord a |} (f : a -> t a) (l : list a) : t a
