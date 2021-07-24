(*
   Copyright 2021 Microsoft Research

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

module FStar.Classical.Lemmas

/// This module provides alternatives to utilities in FStar.Classical.
/// The alternatives here take lemmas instead of squashes as input.

(* ubool represents a non-necessarily-decidable boolean, i.e., a
   [Type0] used as a logical proposition *)

type ubool = Type0

(* impl_intro_lemma introduces the fact [p ==> q].  It takes as input a
   lemma requiring [p] and ensuring [q]. *)

val impl_intro_lemma
  (#p: ubool)
  (#q: ubool)
  ($h: (unit -> Lemma (requires p) (ensures q)))
  : Lemma (p ==> q)

(* forall_intro_lemma introduces the fact [forall (x: a). p x ==> q x].  It
   takes as input a lemma that takes an [x:a], requires [p x], and
   ensures [q x]. *)

val forall_intro_lemma
  (#a: Type)
  (#p: (a -> ubool))
  (#q: (a -> ubool))
  ($h: (x: a -> Lemma (requires p x) (ensures (q x))))
  : Lemma (forall (x: a). p x ==> q x)

(* forall_intro_2_lemma introduces the fact [forall (x: a) (y: b). p x y
   ==> q x y].  It takes as input a lemma that takes an [x:a] and
   [y:b], requires [p x y], and ensures [q x y]. *)

val forall_intro_2_lemma
  (#a: Type)
  (#b: Type)
  (#p: (a -> b -> ubool))
  (#q: (a -> b -> ubool))
  ($h: (x: a -> y: b -> Lemma (requires p x y) (ensures (q x y))))
  : Lemma (forall (x: a) (y: b). p x y ==> q x y)

(* exists_elim_lemma establishes [goal] using two input lemmas.  The
   first lemma, [existence], establishes that [exists (x: a). property x].
   The second lemma, [instance_implies_goal], takes an [x:a] as input,
   requires [property x], and ensures [goal]. *)

val exists_elim_lemma
  (#a:Type)
  (#goal:ubool)
  (#property:a -> ubool)
  ($existence:(unit -> Lemma (ensures exists (x: a). property x)))
  ($instance_implies_goal:(x:a -> Lemma (requires property x) (ensures goal)))
  : Lemma (goal)

(* or_elim_lemma establishes [l \/ r ==> goal] using two input lemmas.
   The first lemma requires [l] and ensures [goal].  The second lemma
   requires [r] and ensures [goal]. *)

val or_elim_lemma
  (#l #r #goal: ubool)
  ($hl:(unit -> Lemma (requires l) (ensures goal)))
  ($hr:(unit -> Lemma (requires r) (ensures goal)))
  : Lemma ((l \/ r) ==> goal)

(* or_elim_3_lemma establishes [l \/ m \/ r ==> goal] using three input
   lemmas.  The first lemma requires [l] and ensures [goal].  The
   second lemma requires [m] and ensures [goal].  The third lemma
   requires [r] and ensures [goal]. *)

val or_elim_3_lemma
  (#l #m #r #goal:ubool)
  ($hl:(unit -> Lemma (requires l) (ensures goal)))
  ($hm:(unit -> Lemma (requires m) (ensures goal)))
  ($hr:(unit -> Lemma (requires r) (ensures goal)))
  : Lemma (l \/ m \/ r ==> goal)
