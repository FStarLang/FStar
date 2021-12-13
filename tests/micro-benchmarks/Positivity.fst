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
module Positivity

open FStar.All

type mlist (a:Type) =
  | MNil : mlist a
  | MCons: a -> nlist a -> mlist a

and nlist (a:Type) =
  | NNil : nlist a
  | NCons: a -> mlist a -> nlist a

(* this is ok since it's an effectful arrow *)
noeq type t1 =
  | C1: (t1 -> ML t1) -> t1

(* checking type abbreviations *)

type t2 (a:Type) = nat -> a

type t3 (a:Type) = nat -> t2 a

noeq type t4 =
  | C4: t3 t4 -> t4

open FStar.ST
noeq
type t =
  | MkT : ref t -> t //relies in assume_strictly_positive

(*
 * #868
 *)
let l_868: eqtype = (y: Seq.seq int {Seq.mem 2 y })
type essai_868 = | T of list (l_868 * essai_868)

type t_t12 = unit

noeq type t12 (a:Type) =
  | C121 : t_t12 -> a -> t12 a


assume val t_t14 : Type0

noeq type t14 =
  | C141: t_t14 -> t14


(*
 * Using the strictly_positive attribute on binders
 *)
assume val t_t15 (a:Type0) : Type0

[@@ expect_failure]
noeq
type t_t16 =
  | C161: t_t15 t_t16 -> t_t16

assume val t_t17 ([@@@ strictly_positive] a:Type0) (b:Type0) : Type0

//fails since we don't know if the second binder of t_t17 is positive
[@@ expect_failure]
noeq
type t_t18 =
  | C181: t_t17 t_t18 t_t18 -> t_t18

noeq
type t_t18 =
  | C181: t_t17 t_t18 nat -> t_t18

(*
 * strictly positive attribute is checked properly
 *)

val t_t19 ([@@@ strictly_positive] a:Type0) : Type0

[@@ expect_failure]
let t_t19 a = a -> int

let t_t19 a = list a

(*
 * This type should be rejected since f may be instantiated with an arrow
 *   that could lead to proof of False, e.g.
 *
 * let f_false : Type0 -> Type0 = fun a -> (a -> squash False)
 *
 * let g : f_false (t_t20 f_false) =
 *   fun x ->
 *   match x with
 *   | C201 h -> h x
 *
 * let r1 : squash False = g (C201 g)
 *
 *)

[@@ expect_failure]
noeq
type t_t20 (f:Type0 -> Type0) =
  | C201 : f (free f) -> free f

