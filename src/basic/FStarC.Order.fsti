(*
   Copyright 2008-2020 Microsoft Research

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

module FStarC.Order
open FStarC.Effect

type order = | Lt | Eq | Gt

// Some derived checks
val ge (o : order) : bool
val le (o : order) : bool
val ne (o : order) : bool
val gt (o : order) : bool
val lt (o : order) : bool
val eq (o : order) : bool

// Lexicographical combination, thunked to be lazy
val lex (o1 : order) (o2 : unit -> order) : order

val order_from_int (i : int) : order

val compare_int (i : int) (j : int) : order

val compare_bool (b1 b2 : bool) : order

(*
 * It promises to call the comparator in strictly smaller elements
 * Useful when writing a comparator for an inductive type,
 *   that contains the list of itself as an argument to one of its
 *   data constructors
 *)
val compare_list (#a:Type)
  (l1 l2:list a)
  (f:(x:a{x << l1} -> y:a{y << l2} -> order))
  : order

val compare_option (f : 'a -> 'a -> order) (x : option 'a) (y : option 'a) : order
