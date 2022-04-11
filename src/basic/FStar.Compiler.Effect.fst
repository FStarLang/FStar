(*
   Copyright 2008-2017 Microsoft Research

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

module FStar.Compiler.Effect

new_effect ALL = ALL_h unit

let all_pre = all_pre_h unit
let all_post' (a : Type) (pre:Type) = all_post_h' unit a pre
let all_post (a : Type) = all_post_h unit a
let all_wp (a : Type) = all_wp_h unit a

let lift_pure_all (a:Type) (p:pure_wp a)
  : all_wp a
  = fun post h -> p (fun x -> post (V x) h)

sub_effect PURE ~> ALL { lift_wp = lift_pure_all }


effect All (a:Type) (pre:all_pre) (post:(h:unit -> Tot (all_post' a (pre h)))) =
  ALL a
      (fun (p : all_post a) (h : unit) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1))

effect ML (a:Type) = ALL a (fun (p:all_post a) (_:unit) -> forall (a:result a) (h:unit). p a h)

let ( |> ) (x : 'a) (f : ('a -> ML 'b)) : ML 'b = f x
let ( <| ) (f : ('a -> ML 'b)) (x : 'a) : ML 'b = f x

assume
val ref (a:Type0) : Type0

assume
val (!) (#a:Type) (r:ref a)
  : ML a

assume
val (:=) (#a:Type) (r:ref a) (x:a)
  : ML unit

assume
val alloc (#a:Type) (x:a)
  : ML (ref a)

assume
val raise (e: exn) : ML 'a

assume
val exit : int -> ML 'a

assume
val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a

exception Failure of string

assume
val failwith : string -> ML 'a
