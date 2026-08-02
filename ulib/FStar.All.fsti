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

(** STATE effect: underspecified state *)
assume effect STATE

assume sub_effect DIV ~> STATE

effect St (a:Type) = STATE a

(** Reference operations — underspecified *)
val alloc : #a:Type0 -> a -> St (ref a)
val op_Bang : #a:Type0 -> ref a -> St a
val op_Colon_Equals : #a:Type0 -> ref a -> a -> St unit

(** ALL effect: combines state, exceptions and divergence *)
assume effect ALL

assume sub_effect EXN ~> ALL
assume sub_effect STATE ~> ALL

effect ML (a:Type) = ALL a

val exit : int -> ML 'a (ensures fun _ -> False)
val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a

exception Failure of string
val failwith : s:string -> ML 'a (ensures fun _ -> False)
