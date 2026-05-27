(*
   Copyright 2008-2020 Microsoft Research

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

module WorkingWithSquashedProofs

//Mixing squashed and constructive proofs
//With prop being opaque and squash : prop -> Type0, many of the old
//FStar.Squash operations are no longer needed.

//Suppose I have some predicates
assume
val foo (a:Type) (x:a) : prop
assume
val bar (a:Type) (x:a) : prop

//And let's say I have a way of proving some Lemma based on a proof of this `pred`
assume
val foo_pf_implies_bar (a:Type u#a) (x:a) (pf:squash (foo a x))
  : Lemma (bar a x)

//Now, if I have `foo` in a refinement, I can still prove `bar`, like so
//Since props are squashed automatically, we just need classical reasoning

//We can use FStar.Classical for disjunction elimination
open FStar.Classical

// Say I have a lemma proving a disjunction
assume
val foo_or_bar (#a:_) (x:a) : Lemma (foo a x \/ bar a x)

assume
val baz (a:Type) (x:a) : prop

// And let's say I have separate lemmas proving
// foo implies baz
// and bar implies baz
assume
val foo_baz (#a:_) (x:a)
  : Lemma
    (requires foo a x)
    (ensures baz a x)

assume
val bar_baz (#a:_) (x:a)
  : Lemma
    (requires bar a x)
    (ensures baz a x)

let valid_baz (a:Type) (x:a)
  : Lemma (baz a x)
  = foo_or_bar x;
    or_elim #(foo a x) #(bar a x) #(fun _ -> baz a x)
      (fun _ -> foo_baz x)
      (fun _ -> bar_baz x)

// And here's a variant where the lemmas I want to call
// expect proof terms of foo or bar
assume
val c_foo_baz (#a:_) (x:a) (_:foo a x)
  : Lemma
    (ensures baz a x)

assume
val c_bar_baz (#a:_) (x:a) (_:bar a x)
  : Lemma
    (ensures baz a x)

let valid_baz_alt (a:Type) (x:a)
  : Lemma (baz a x)
  = foo_or_bar x;
    or_elim #(foo a x) #(bar a x) #(fun _ -> baz a x)
      (fun _ -> c_foo_baz x ())
      (fun _ -> c_bar_baz x ())
