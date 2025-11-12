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

module Pulse.Lib.Send
open Pulse.Lib.Core
open Pulse.Class.Duplicable
open PulseCore.Observability
open Pulse.Main
module T = FStar.Tactics.V2
#lang-pulse

[@@Tactics.Typeclasses.tcclass; erasable]
type is_send_across (#b:Type0) (g: loc_id -> b) (p: slprop) =
  l:loc_id -> l':loc_id { g l == g l' } -> stt_ghost unit emp_inames (on l p) (fun _ -> on l' p)

irreducible let anywhere (l: loc_id) = ()

[@@Tactics.Typeclasses.tcclass; erasable]
type placeless (p: slprop) =
  is_send_across anywhere p

[@@deprecated "impersonate is unsound; only use for model implementations"]
noextract inline_for_extraction
fn impersonate
    u#a (a: Type u#a)
    (l: loc_id) (pre: slprop) (post: a -> slprop)
    {| placeless pre, ((x:a) -> placeless (post x)) |}
    (f: unit -> stt a (loc l ** pre) (fun x -> loc l ** post x))
  requires pre
  returns x: a
  ensures post x

[@@deprecated "atomic_impersonate is unsound; only use for model implementations"]
noextract inline_for_extraction
atomic fn atomic_impersonate
    u#a (a: Type u#a)
    (#[T.exact (`emp_inames)] is: inames)
    (l: loc_id) (pre: slprop) (post: a -> slprop)
    {| placeless pre, ((x:a) -> placeless (post x)) |}
    (f: unit -> stt_atomic a is (loc l ** pre) (fun x -> loc l ** post x))
  opens is
  requires pre
  returns x: a
  ensures post x

[@@deprecated "unobservable_impersonate is unsound; only use for model implementations"]
noextract inline_for_extraction
unobservable fn unobservable_impersonate
    u#a (a: Type u#a)
    (#[T.exact (`emp_inames)] is: inames)
    (l: loc_id) (pre: slprop) (post: a -> slprop)
    {| placeless pre, ((x:a) -> placeless (post x)) |}
    (f: unit -> stt_atomic a #Neutral is (loc l ** pre) (fun x -> loc l ** post x))
  opens is
  requires pre
  returns x: a
  ensures post x

ghost fn ghost_impersonate
    (#[T.exact (`emp_inames)] is: inames)
    (l: loc_id) (pre post: slprop) {| placeless pre, placeless post |}
    (f: unit -> stt_ghost unit is (loc l ** pre) (fun _ -> loc l ** post))
  opens is
  requires pre
  ensures post

ghost fn placeless_move (p: slprop) {| placeless p |} l1 l2
  requires on l1 p
  ensures on l2 p

ghost fn placeless_on_intro (p: slprop) {| placeless p |} l
  requires p
  ensures on l p

ghost fn placeless_on_elim (p: slprop) {| placeless p |} l
  requires on l p
  ensures p

instance val placeless_on (l: loc_id) (p: slprop) : placeless (on l p)
instance val placeless_emp : placeless emp
instance val placeless_star (a b: slprop) {| placeless a, placeless b |} : placeless (a ** b)
instance val placeless_pure (p: prop) : placeless (pure p)
instance val placeless_later_credit amt : placeless (later_credit amt)
instance val placeless_equiv a b : placeless (equiv a b)
instance val placeless_slprop_ref_pts_to x y : placeless (slprop_ref_pts_to x y)
instance val placeless_exists #a (p: a -> slprop) {| ((x:a) -> placeless (p x)) |} :
  placeless (exists* x. p x)

let in_same_process p = exists* l. loc l ** pure (process_of l == process_of p)
val timeless_in_same_process p : Lemma (timeless (in_same_process p)) [SMTPat (timeless (in_same_process p))]
instance val duplicable_in_same_process p : duplicable (in_same_process p)

[@@Tactics.Typeclasses.tcclass; erasable]
let is_send p = is_send_across process_of p

ghost fn is_send_across_elim #b (g: loc_id -> b) p {| inst: is_send_across g p |} #l l'
  requires on l p
  requires pure (g l == g l')
  ensures on l' p

ghost fn is_send_elim p {| inst: is_send p |} #l l'
  requires on l p
  requires pure (process_of l == process_of l')
  ensures on l' p

ghost fn is_send_elim_on p {| is_send p |} #l
  preserves in_same_process l
  requires on l p
  ensures p

ghost fn is_send_intro_on p {| is_send p |} l
  preserves in_same_process l
  requires p
  ensures on l p

ghost fn is_send_elim_on' p {| is_send p |} #l
  preserves loc l
  requires on (process_of l) p
  ensures p

ghost fn is_send_intro_on' p {| is_send p |} l
  preserves loc l
  requires p
  ensures on (process_of l) p

instance val is_send_across_placeless #b #g p {| inst: placeless p |} : is_send_across #b g p
instance val is_send_across_star #b #g p q {| is_send_across #b g p, is_send_across #b g q |} : is_send_across g (p ** q)
instance val is_send_across_exists #b #g #a (p: a->slprop) {| ((x:a) -> is_send_across #b g (p x)) |} :
  is_send_across g (exists* x. p x)

instance is_send_placeless p {| inst: placeless p |} : is_send p = is_send_across_placeless p
instance val is_send_in_same_process p : is_send (in_same_process p)
instance is_send_star p q {| ip: is_send p, iq: is_send q |} : is_send (p ** q) = is_send_across_star p q #ip #iq
instance is_send_exists #a (p: a->slprop) {| i: ((x:a) -> is_send (p x)) |} :
  is_send (exists* x. p x) = is_send_across_exists p #i

val on_same_process (p: slprop) : slprop
ghost fn on_same_process_elim p {| is_send p |}
  requires on_same_process p
  ensures p
ghost fn on_same_process_intro p
  requires p
  ensures on_same_process p
val timeless_on_same_process (p: timeless_slprop) :
  Lemma (timeless (on_same_process p)) [SMTPat (timeless (on_same_process p))]
instance val is_send_on_same_process p : is_send (on_same_process p)

val sendable (p: slprop) : slprop
ghost fn sendable_elim p
  requires sendable p
  ensures p
ghost fn sendable_intro p {| is_send p |}
  requires p
  ensures sendable p
instance val is_send_sendable p : is_send (sendable p)

inline_for_extraction noextract fn fork'
  (pre:slprop) {| is_send pre |}
  (f: (unit -> stt unit pre (fun _ -> emp)))
  requires pre