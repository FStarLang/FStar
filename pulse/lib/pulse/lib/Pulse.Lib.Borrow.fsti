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

module Pulse.Lib.Borrow
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Shift
#lang-pulse

[@@erasable]
val lifetime : Type0

inline_for_extraction noextract
instance noninformative_lifetime : NonInformative.non_informative lifetime =
  { reveal = ((fun a -> a) <: NonInformative.revealer lifetime) }

[@@coercion]
val lifetime_alive : lifetime -> slprop

val lifetime_opened : [@@@mkey] lifetime -> list slprop -> slprop

val lifetime_dead : lifetime -> slprop

ghost fn begin_lifetime ()
  returns a: lifetime
  ensures a

ghost fn end_lifetime (a: lifetime)
  requires a
  ensures lifetime_dead a

val (>:>) (a: lifetime) (p: slprop) : slprop

val borrowed (a: lifetime) (p: slprop) : slprop

ghost fn borrow' (a: lifetime) (p: slprop)
  preserves a
  requires later p
  ensures a >:> p
  ensures borrowed a p

ghost fn borrow (a: lifetime) (p: slprop)
  preserves a
  requires p
  ensures a >:> p
  ensures borrowed a p

ghost fn share_borrow' #a (p q1 q2: slprop)
  requires a >:> p
  requires shift (later p) (later q1 ** later q2 ** trade (later q1 ** later q2) (later p))
  ensures a >:> q1
  ensures a >:> q2

ghost fn share_borrow #a (p q1 q2: timeless_slprop)
  requires a >:> p
  requires shift p (q1 ** q2 ** trade (q1 ** q2) p)
  ensures a >:> q1
  ensures a >:> q2

ghost fn weaken_opened' #a (p q: slprop) #qs
  requires lifetime_opened a (p::qs)
  requires trade (later q) (later p)
  ensures lifetime_opened a (q::qs)

ghost fn weaken_opened #a (p q: timeless_slprop) #qs
  requires lifetime_opened a (Cons #slprop p qs)
  requires trade q p
  ensures lifetime_opened a (Cons #slprop q qs)

ghost fn sub_borrow' (#a: lifetime) (p q: slprop)
  requires trade (later p) (later q ** trade (later q) (later p))
  preserves a
  requires a >:> p
  ensures a >:> q

ghost fn sub_borrow (#a: lifetime) (p q: timeless_slprop)
  requires trade p (q ** trade q p)
  preserves a
  requires a >:> p
  ensures a >:> q

ghost fn open_lifetime (a: lifetime)
  requires a
  ensures lifetime_opened a []

ghost fn close_lifetime (a: lifetime)
  requires lifetime_opened a []
  ensures a

ghost fn use_borrow' (a: lifetime) (p: slprop) #q
  requires lifetime_opened a q
  requires a >:> p
  ensures lifetime_opened a (p::q)
  ensures later p

ghost fn end_use_borrow' (a: lifetime) (p: slprop) (#qs: list slprop)
  requires lifetime_opened a (p::qs)
  requires later p
  ensures lifetime_opened a qs
  ensures a >:> p

ghost fn use_borrow (a: lifetime) (p: timeless_slprop) (#q: list slprop)
  requires lifetime_opened a q
  requires a >:> p
  ensures lifetime_opened a (Cons #slprop p q)
  ensures p

ghost fn end_use_borrow (a: lifetime) (p: slprop) (#qs: list slprop)
  requires lifetime_opened a (p::qs)
  requires p
  ensures lifetime_opened a qs
  ensures a >:> p

ghost fn end_borrow' (a: lifetime) p
  preserves lifetime_dead a
  requires borrowed a p
  ensures later p

ghost fn end_borrow (a: lifetime) (p: timeless_slprop)
  preserves lifetime_dead a
  requires borrowed a p
  ensures p
