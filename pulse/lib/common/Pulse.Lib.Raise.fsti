(*
   Copyright 2025 Microsoft Research

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
module Pulse.Lib.Raise
open Pulse.Lib.NonInformative
open FStar.ExtractAs

[@@Tactics.Typeclasses.tcclass; erasable]
val raisable : p:prop { Type u#(max a b) } // hack to specify universe parameters

instance val raisable_non_info : non_informative (raisable u#a u#b)

[@@Tactics.Typeclasses.tcinstance]
val raisable_inst : raisable u#a u#(max a b)

(** [raise_t a] is an isomorphic copy of [a] (living in universe a) in universe [b] **)
inline_for_extraction [@@extract_as (`(fun (t: Type u#a) -> t))]
val raise_t {| raisable u#a u#b |} (t : Type u#a) : Type u#b

(** [raise_val x] injects a value [x] of type [a] to [raise_t a] **)
inline_for_extraction [@@extract_as (`(fun (#a: Type u#a) (x: a) -> x))]
val raise_val : #a:Type u#a -> {| raisable u#a u#b |} -> x:a -> raise_t u#a u#b a

(** [downgrade_val x] projects a value [x] of type [raise_t a] to [a] **)
inline_for_extraction [@@extract_as (`(fun (#a: Type u#a) (x: a) -> x))]
val downgrade_val : #a:Type u#a -> {| raisable u#a u#b |} -> x:raise_t u#a u#b a -> a

val downgrade_val_raise_val (#a: Type u#a) {| raisable u#a u#b |} (x: a) :
  Lemma (downgrade_val (raise_val x) == x) [SMTPat (raise_val x)]

val raise_val_downgrade_val (#a: Type u#a) {| raisable u#a u#b |} (x: raise_t u#a u#b a) : 
  Lemma (raise_val (downgrade_val x) == x) [SMTPat (downgrade_val x)]

let lift_dom (#a : Type u#a) {| raisable u#a u#b |} (#b: Type u#c) (q:a -> b) : raise_t u#a u#b a -> b =
  fun v -> q (downgrade_val v)

let lift_codom (#a: Type u#a) (#b: Type u#b) {| raisable u#b u#c |} (q:a -> b) : a -> raise_t u#b u#c b =
  fun v -> raise_val (q v)