(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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

module FStar.Compiler.Set

open FStar.Class.Ord
open FStar.Class.Show

val set (a:Type0) : Type0

type t = set

val empty (#a:Type) {| ord a |} () : set a
val singleton (#a:Type) {| ord a |} (x:a) : set a

val is_empty (#a:Type) {| ord a |} (s:set a) : bool

val from_list (#a:Type) {| ord a |} (l:list a) : set a
val elems (#a:Type) {| ord a |} (s:set a) : list a

val add (#a:Type) {| ord a |} (x:a) (s:set a) : set a
val addn (#a:Type) {| ord a |} (x:list a) (s:set a) : set a

val remove (#a:Type) {| ord a |} (x:a) (s:set a) : set a

val mem (#a:Type) {| ord a |} (x:a) (s:set a) : bool

val equal (#a:Type) {| ord a |} (s1:set a) (s2:set a) : bool

val subset (#a:Type) {| ord a |} (s1:set a) (s2:set a) : bool

val union (#a:Type) {| ord a |} (s1:set a) (s2:set a) : set a
val inter (#a:Type) {| ord a |} (s1:set a) (s2:set a) : set a
val diff  (#a:Type) {| ord a |} (s1:set a) (s2:set a) : set a
  
val collect (#a:Type) (#b:Type) {| ord b |} (f : a -> set b) (l : list a) : set b

val for_all (#a:Type) {| ord a |} (p:(a -> bool)) (s:set a) : bool
val for_any (#a:Type) {| ord a |} (p:(a -> bool)) (s:set a) : bool

instance val showable_set (a:Type) (_ : ord a) (_ : showable a) : Tot (showable (set a))
