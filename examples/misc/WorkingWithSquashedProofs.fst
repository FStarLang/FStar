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
open FStar.Squash

//Mixing squashed an constructive proofs
//It's a bit bureaucratic and technical ... I wish this part of F* were simpler
//There's a bunch of redundancy between Lemma, squash, GTot, prop, etc.
//which is always confusing.

//Suppose I have some predicates, it could be that inductive type about
//interleaving that you had
assume
val foo (a:Type) (x:a) : Type
assume
val bar (a:Type) (x:a) : Type

//And let's say I have a way of proving some Lemma based on a proof of this `pred`
assume
val foo_pf_implies_bar (a:Type) (x:a) (pf:foo a x)
  : Lemma (bar a x)

//Now, if I have `foo` in a refinement, I can still prove `bar, like so

//One can use FStar.Squash.bind_squash for that, but it takes a couple of steps

//expect_failure is an attribute that tells F* that this next definition will fail
[@expect_failure] //but this doesn't quite work because `bind_squash` expects a GTot function but we are giving it a Lemma, which isn't identical
let foo_implies_bar (a:Type) (x:a{foo a x})
  : Lemma (bar a x)
  = let s : squash (foo a x) = () in
    FStar.Squash.bind_squash #(foo a x) #(bar a x) s (foo_pf_implies_bar a x)

//So, to make it work, we need to turn a lemma into a GTot function returning a squash
let lemma_as_squash #a #b ($lem: (a -> Lemma b)) (x:a)
  : GTot (squash b)
  = lem x

//Now, I can use FStar.Squash.bind_squash to complete the proof
let foo_implies_bar (a:Type) (x:a{foo a x})
  : Lemma (bar a x)
  = FStar.Squash.bind_squash () (lemma_as_squash (foo_pf_implies_bar a x))

// Another example, this time with disjunctions

// Say I have a lemma proving a disjunction
assume
val foo_or_bar (#a:_) (x:a) : Lemma (foo a x \/ bar a x)

assume
val baz (a:Type) (x:a) : Type

// And let's say I have separate lemmas proving
// foo implies baz
// and bar impliez baz
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
  = let s_fb : squash (foo a x \/ bar a x) = foo_or_bar x in
    FStar.Squash.bind_squash s_fb (fun (fb:(foo a x \/ bar a x)) ->
    FStar.Squash.bind_squash fb  (fun (c_fb:Prims.either (foo a x) (bar a x)) ->
     let s_baz : squash (baz a x) =
       match c_fb with
       | Prims.Inl f ->
         // let sf = FStar.Squash.return_squash f in
         foo_baz x
       | Prims.Inr b ->
         // let sg = FStar.Squash.return_squash b in
         bar_baz x
     in
     s_baz))


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
  = let s_fb : squash (foo a x \/ bar a x) = foo_or_bar x in
    FStar.Squash.bind_squash s_fb (fun (fb:(foo a x \/ bar a x)) ->
    FStar.Squash.bind_squash fb  (fun (c_fb:Prims.either (foo a x) (bar a x)) ->
     let s_baz : squash (baz a x) =
       match c_fb with
       | Prims.Inl f ->
         c_foo_baz x f
       | Prims.Inr b ->
         c_bar_baz x b
     in
     s_baz))

//We can wrap that up into a combinator like so
// See also FStar.Classical.or_elim which is a variant of this
let elim_squash_or (#r:_) (#p #q:_) (f:squash (p \/ q)) (left: p -> GTot r) (right: q -> GTot r)
  : GTot (squash r)
  = FStar.Squash.bind_squash #_ #r f (fun pq ->
    FStar.Squash.bind_squash pq (fun c ->
    match c with
    | Prims.Inl x -> FStar.Squash.return_squash (left x)
    | Prims.Inr x -> FStar.Squash.return_squash (right x)))

let valid_baz_alt_alt (a:Type) (x:a)
  : GTot (squash (baz a x))
  = let fb : squash (foo a x \/ bar a x) = foo_or_bar x in
    FStar.Squash.join_squash
      (elim_squash_or fb
        (lemma_as_squash (c_foo_baz x))
        (lemma_as_squash (c_bar_baz x)))
