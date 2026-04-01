(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.All

include FStar.Exn

(** Abstract reference type — no heap model *)
new
val ref ([@@@ strictly_positive] a:Type0) : Type0

(** References support decidable equality *)

(** STATE effect: same WP as DIV (underspecified state) *)
new_effect STATE = DIV

unfold let lift_div_state (a:Type) (wp:pure_wp a) = wp
sub_effect DIV ~> STATE = lift_div_state

effect St (a:Type) = STATE a (pure_null_wp a)

(** Reference operations — underspecified *)
val alloc : #a:Type0 -> a -> St (ref a)
val op_Bang : #a:Type0 -> ref a -> St a
val op_Colon_Equals : #a:Type0 -> ref a -> a -> St unit

(** ALL effect: same WP as EXN (combines state + exceptions + divergence) *)
new_effect ALL = EXN

unfold let lift_exn_all (a:Type) (wp:ex_wp a) = wp
sub_effect EXN ~> ALL = lift_exn_all

unfold let lift_state_all (a:Type) (wp:pure_wp a) (p:ex_post a) = wp (fun a -> p (V a))
sub_effect STATE ~> ALL = lift_state_all

effect ML (a:Type) = ALL a (fun (p:ex_post a) -> forall (r:result a). p r)

val exit : int -> ML 'a
val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a

exception Failure of string
val failwith : string -> ML 'a
