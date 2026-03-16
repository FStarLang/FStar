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

module Pulse.Lib.GhostSet
include FStar.GhostSet

val mem_as_set' #t f (x: t) (l: list t)
  : Lemma (mem x (as_set' f l) <==> List.memP x l)
          [SMTPat (mem x (as_set' f l))]

val decide_eq_f #t : decide_eq t
let as_set #t = as_set' #t decide_eq_f

val is_finite #t (x: set t) : prop
val is_finite_prop #t (x: set t) : Lemma (is_finite x <==> exists l. x == as_set l)
val is_finite_elim #t (x: set t { is_finite x }) : GTot (l: list t { x == as_set l })

val is_finite_empty t : Lemma (is_finite (empty #t)) [SMTPat (is_finite (empty #t))]
val is_finite_singleton #t f (x:t) : Lemma (is_finite (singleton f x)) [SMTPat (is_finite (singleton f x))]
val is_finite_union #t (x y: set t) : Lemma (is_finite (union x y) <==> is_finite x /\ is_finite y) [SMTPat (is_finite (union x y))]
val is_finite_intersect #t (x y: set t) : Lemma (is_finite x \/ is_finite y ==> is_finite (intersect x y)) [SMTPat (is_finite (intersect x y))]