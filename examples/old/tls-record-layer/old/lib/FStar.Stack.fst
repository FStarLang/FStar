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
(** An implementation of a stack using the list module. *)

module FStar.Stack
type stack (a:Type) = list a

val push : #a:Type -> stack a -> a -> Tot (stack a)
let push st e = e :: st

val tail : #a:Type -> stack a -> Tot (stack a)
let tail st =
  match st with
  | [] -> []
  | h::tl -> tl

let isNonEmpty = Cons?

val top : #a:Type -> l:stack a{isNonEmpty l} -> Tot a
let top l =
  match l with
  | h::tl -> h

val pop : #a:Type -> l:stack a{isNonEmpty l} -> Tot (a * stack a)
let pop l =
  match l with
  | h::tl -> h,tl
