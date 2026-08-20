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

(** References always exist, so [ref a] is inhabited. This cannot be
    proven, since [alloc] below is itself effectful; it is an axiom
    about the (OCaml) realization of [ref]. It is needed to define
    top-level references, e.g. [let r : ref int = alloc 0]. *)
val nonempty_ref (a:Type0) : Lemma (nonempty (ref a)) [SMTPat (nonempty (ref a))]

(** References support decidable equality *)

(** STATE effect: underspecified state *)
assume effect STATE

assume sub_effect DIV ~> STATE

effect St (a:Type) = STATE a

(** Reference operations — underspecified *)
val alloc : #a:Type0 -> a -> St (ref a)
val ( ! ) : #a:Type0 -> ref a -> St a
val ( := ) : #a:Type0 -> ref a -> a -> St unit

(** ALL effect: combines state, exceptions and divergence *)
assume effect ALL

assume sub_effect EXN ~> ALL
assume sub_effect STATE ~> ALL

effect ML (a:Type) = ALL a

val exit : int -> ML 'a (ensures fun _ -> False)
val try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a

exception Failure of string
val failwith : s:string -> ML 'a (ensures fun _ -> False)
