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
module Bug024

(* Example 1 works now *)

(* Example 2 *)

(* Adding this signature makes it work
val nth : list 'a -> int *)
(* Also removing the rec makes it work *)
let rec nth l = match l with
    | [] -> 0
    | x::xs -> 1

(* Example 3

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

val length_nil : unit -> Lemma
      (ensures (length [] = 0))
let length_nil () = ()

assume val impossible : u : unit { False } -> Tot 'a

(* Getting incomplete patterns here, with or without the [] pattern,
   caused by the same problem as length_nil I think; it should clearly
   be a different error message when the [] pattern is present *)
val index : l : list 'a -> n:int{(0 <= n) /\ (n < length l)} -> Tot 'a
let rec index l n =
  match l with
  | [] -> length_nil(); impossible()
  | h :: t -> if n = 0 then h else index t (n-1)

*)
