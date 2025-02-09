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

module FStarC.Common
open FStarC.Effect

val snapshot (push: 'a -> 'b) (stackref: ref (list 'c)) (arg: 'a) : (int & 'b)

val rollback (pop: unit -> 'a) (stackref: ref (list 'c)) (depth: option int) : 'a

val runtime_assert (b:bool) (msg:string) : unit

(* Why two? This function was added during a refactoring, and
both variants existed. We cannot simply move to ";" since that is a
breaking change to anything that parses F* source code (like Vale). *)
val string_of_list  : ('a -> string) -> list 'a -> string
val string_of_list' : ('a -> string) -> list 'a -> string

val list_of_option (o:option 'a) : list 'a

val string_of_option (f : 'a -> string) (o : option 'a) : string

(* Was List.init, but F* doesn't have this in ulib *)
val tabulate (n:int) (f : int -> 'a) : list 'a

(** max_prefix f xs returns (l, r) such that
  * every x in l satisfies f
  * l@r == xs
  * and l is the largest list satisfying that
  *)
val max_prefix (f : 'a -> bool) (xs : list 'a) : list 'a & list 'a

(** max_suffix f xs returns (l, r) such that
  * every x in r satisfies f
  * l@r == xs
  * and r is the largest list satisfying that
  *)
val max_suffix (f : 'a -> bool) (xs : list 'a) : list 'a & list 'a

val eq_list (f: 'a -> 'a -> bool) (l1 l2 : list 'a) : bool

val psmap_to_list (m : PSMap.t 'a) : list (string & 'a)
val psmap_keys (m : PSMap.t 'a) : list string
val psmap_values (m : PSMap.t 'a) : list 'a

val option_to_list (o : option 'a) : list 'a
