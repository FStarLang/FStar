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

module Z3EncodingIssue


/// This module illustrates a z3 encoding issue when a layered effect is written in a particular style

/// Suppose we want to write an effect that works on a single global buffer
///
/// One way to define this effect is to index it with a wp that is written only
///   over the contents of the buffer (i.e. Seq.seq),
///   while the encoding of the effect (repr) takes care of heap etc.
///
/// This results in an interesting smtencoding problem,
///   in summary we end up emitting a quantifier that has no good patterns for one of the variables
///
/// Keep reading the module to see the issue
///
/// (But all is not lost, there exists an alternative style which comes with all the goodies
///    of the layered effects in this setting, see MSeqExn.fst for the alternative style)


module Seq = FStar.Seq

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer


type u8 = uint_8
type u32 = uint_32


/// The global buffer


assume val buf : B.buffer u8


/// The pre- and postconditions only talk about the contents of the buffer (as a sequence)


type pre_t = Seq.seq u8 -> Type0
type post_t (a:Type) = a -> Seq.seq u8 -> Type0
type wp_t (a:Type) = post_t a -> pre_t


/// The underlying representation


type repr (a:Type) (wp:wp_t a) =
  unit -> STATE a (fun p h0 -> wp (fun x s1 -> forall h1. (B.as_seq h1 buf == s1 ==> p x h1)) (B.as_seq h0 buf))


/// Combinators

inline_for_extraction
let return (a:Type) (x:a)
: repr a (fun p s -> p x s)
= fun _ -> x

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b (fun p -> wp_f (fun x -> (wp_g x) p))
= admit ();  //this proof requires monotonicity of wps, the problem is independent so let's just admit it
  fun _ ->
  let x = f () in
  (g x) ()

inline_for_extraction
let subcomp (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall p s. wp_g p s ==> wp_f p s)
  (ensures fun _ -> True)
= f

inline_for_extraction
let if_then_else (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:Type0)
: Type
= repr a
  (fun post s ->
    (p ==> wp_f post s) /\
    ((~ p) ==> wp_g post s))


reifiable reflectable
layered_effect {
  CHACHA : a:Type -> wp_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


/// Lift from DIV

let lift_div_chacha (a:Type)
  (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: repr a (fun p s -> wp (fun x -> p x s))
= fun _ -> f ()


sub_effect DIV ~> CHACHA = lift_div_chacha


/// Hoare-style abbreviation as usual


effect Chacha (a:Type)
  (pre:Seq.seq u8 -> Type0)
  (post:Seq.seq u8 -> a -> Seq.seq u8 -> Type0)
= CHACHA a (fun p s -> pre s /\ (forall x s1. post s x s1 ==> p x s1))


/// Let's try to define an action

/// Suppose there is a trivial STATE function that we want to lift to CHACHA


assume val fn (_:unit) : STATE unit (fun p h -> p () h)



/// The problem comes when we reflect it into CHACHA
///
/// The code below does not verify with the spec written in the hoare-style
///
/// BUT goes through when the spec is written in CHACHA (in the wp-style)
///
/// The culprit is the (forall s1) quantifier in the encoding of Chacha to CHACHA
///
/// Here is the problem (abusing <: to mean ascription and subtyping and subcomp, hopefully it's clear from the context)
///
/// The typechecker has to typecheck:
///
/// CHACHA?.reflect fn <: Chacha unit (requires fun _ -> True) (ensures fun s0 _ s1 -> s0 == s1)
///
/// It unfolds the effect abbreviation on the right, to get:
///
/// CHACHA?.reflect fn <: CHACHA unit (fun p s -> forall x s1. s == s1 ==> p x s1)
///
/// The problem is translated to typechecking:
///
/// fn <: repr unit (fun p s -> forall x s1. s == s1 ==> p x s1)
///
/// Unfolding the definition of repr:
///
/// fn <: unit -> STATE unit (fun p h0 -> forall x s1. B.as_seq h0 buf == s1 ==> (forall h1. B.as_seq h1 buf == s1 ==> p x h1))
///
/// We know fn : unit -> STATE unit (fun p h -> p () h), and so, the problem is translated to
///
/// unit -> STATE unit (fun p h -> p () h) <: unit -> STATE unit (fun p h0 -> forall x s1. B.as_seq h0 buf == s1 ==> (forall h1. B.as_seq h1 buf == s1 ==> p x h1))
///
/// Which translates to the subcomp problem:
///
/// STATE unit (fun p h -> p () h) <: STATE unit (fun p h0 -> forall x s1. B.as_seq h0 buf == s1 ==> (forall h1. B.as_seq h1 buf == s1 ==> p x h1))
///
/// Applying the subcomp rule for STATE (i.e. STATE a wp1 <: STATE a wp2 if forall p h. wp2 p h ==> wp1 p h):
///
/// forall p h0. (forall x s1. B.as_seq h0 buf == s1 ==> (forall h1. B.as_seq h1 buf == s1 ==> p x h1)) ==>
///              p () h0
///
/// This formula is then sent to Z3
///
/// To prove it, Z3 has to fire the (forall x s1) quantifier, but there is no good pattern for it that contains s1
///
/// And so the proof fails in Z3
///
/// With the spec written in CHACHA, the query is different (this quantifier does not even come up), and then it works out
///
/// Interestingly, if we write this example with a ref nat in FStar.ST instead of a buffer, the query is exactly the same,
///   BUT this time it succeeds! See the code below after chacha_fn


[@expect_failure]
let chacha_fn ()
: Chacha unit
  (requires fun _ -> True)
  (ensures fun s0 _ s1 -> s0 == s1)
= CHACHA?.reflect fn

let chacha_fn_ok ()
: CHACHA unit (fun p s -> p () s)
= CHACHA?.reflect fn




open FStar.ST

module Heap = FStar.Heap

/// A layered effect to work with a single global reference


assume val state : ref int


type hpre_t = int -> Type0
type hpost_t (a:Type) = a -> int -> Type0
type hwp_t (a:Type) = hpost_t a -> hpre_t


type hrepr (a:Type) (wp:hwp_t a) =
  unit ->
  STATE a (fun p h0 -> wp (fun x n -> forall h1. Heap.sel h1 state == n ==> p x h1) (Heap.sel h0 state))


let hreturn (a:Type) (x:a)
: hrepr a (fun p n -> p x n)
= fun _ -> x

let hbind (a:Type) (b:Type)
  (wp_f:hwp_t a) (wp_g:a -> hwp_t b)
  (f:hrepr a wp_f) (g:(x:a -> hrepr b (wp_g x)))
: hrepr b (fun p -> wp_f (fun x -> (wp_g x) p))
= admit ();  //again, needs monotonicity
  fun _ ->
  let x = f () in
  (g x) ()

let hsubcomp (a:Type)
  (wp_f:hwp_t a) (wp_g:hwp_t a)
  (f:hrepr a wp_f)
: Pure (hrepr a wp_g)
  (requires forall p n. wp_g p n ==> wp_f p n)
  (ensures fun _ -> True)
= f

let hif_then_else (a:Type)
  (wp_then:hwp_t a) (wp_else:hwp_t a)
  (f:hrepr a wp_then) (g:hrepr a wp_else)
  (p:Type0)
: Type
= hrepr a
  (fun post n ->
    (p ==> wp_then post n) /\
    ((~ p) ==> wp_else post n))


reifiable reflectable
layered_effect {
  REF : a:Type -> wp:hwp_t a -> Effect
  with
  repr = hrepr;
  return = hreturn;
  bind = hbind;
  subcomp = hsubcomp;
  if_then_else = hif_then_else
}

let lift_div_ref (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: hrepr a (fun p n -> wp (fun x -> p x n))
= fun _ -> f ()

sub_effect DIV ~> REF = lift_div_ref


effect Ref (a:Type) (pre:int -> Type0) (post:int -> a -> int -> Type0) =
  REF a (fun p n0 -> pre n0 /\ (forall x n1. post n0 x n1 ==> p x n1))


assume val hfn (_:unit) : STATE unit (fun p h -> p () h)


(*
 * NOTE: IF THIS PROOF FAILS WHEN YOU ARE MAKING SOME F* CHANGES,
 *       FEEL FREE TO ADMIT IT,
 *       IT RELIES ON A FUNKY QUANTIFIER INSTANTIATION
 *
 *       YOU COULD READ THE COMMENTS IN THIS MODULE IF YOU ARE CURIOUS
 *)

let ref_hfn ()
: Ref unit
  (requires fun _ -> True)
  (ensures fun n0 _ n1 -> n0 == n1)
= REF?.reflect hfn
