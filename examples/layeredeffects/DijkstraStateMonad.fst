(*
   Copyright 2019 Microsoft Research

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

module DijkstraStateMonad
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics

/// This example illustrates how to derive a WP-indexed state monad
/// from a free state monad, parametric in the type of the state

/// `m s a`: A classic free state monad
noeq
type m (s:Type0) (a:Type) =
  | Ret : a -> m s a
  | Get : (s -> m s a) -> m s a
  | Put : x:s -> m s a -> m s a

/// It's easy to sequentially compose terms in `m`
let rec bind_m #s #a #b (x:m s a) (y: (a -> m s b)) : m s b =
  match x with
  | Ret x -> y x
  | Get k -> Get (fun s -> W.axiom1 k s; bind_m (k s) y)
  | Put s k -> Put s (bind_m k y)

/// Now, we want to build an indexed version of m, where the index is
/// a weakest precondition for the computation


/// A postcondition is a predicate relating a result and final state
let post_t (s:Type0) (a:Type) = a * s -> Type0

/// A precondition is a predicate on the initial state (we don't
/// really use this type in what follows)
let pre_t (s:Type) = s -> Type0

/// Although we usually write WPs as transformers from post-conditions
/// to preconditions, I've swapped the order of arguments here since
/// it makes some of the technicalities of the proof simpler.
///
/// The main technicality that comes up is that WPs are essentially
/// continuations and so our proofs are going to make use of
/// functional extensionality to relate WPs
///
/// So, notice that wp_t is a domain-restricited function from initial
/// states `s`. See FStar.FunctionalExtensionality for more
/// explanations, but it is only on these domain-restricted functions
/// that that functional extensionality axiom is available
let wp_t (s:Type0) (a:Type) = s ^-> (post_t s a -> Type0)

/// Here's the WP of a Put action;
/// (Notice that it has to be domain-restricted, that's the `F.on`)
let wp_put #s #a (f: wp_t s a)
  : s -> wp_t s a
  = fun s -> F.on _ (fun s0 -> f s)

/// The WP of return
let wp_return #s #a (x:a)
  : wp_t s a
  = F.on _ (fun s0 post -> post (x, s0))

/// The WP of m is defined by recursion on the computation tree
///
///   -- we need to explicitly invoke the library for well-founded
///      since F*'s SMT automation does not encode that
///      well-foundedness for function types automatically
let rec wp_of #a #s (x:m s a)
  : wp_t s a
  = match x with
    | Ret v -> wp_return v
    | Get k -> F.on _ (fun s0 -> W.axiom1 k s0; (wp_of (k s0)) s0)
    | Put s k -> wp_put (wp_of k) s

/// We prove the soundness of the wp semantics by giving it a model in
/// terms of F*'s pure computations
let rec run (#a:_) (#s:_) (m:m s a) (s0:s) (post: post_t s a)
  : Pure (a * s)
         (requires
           wp_of m s0 post)
         (ensures
           post)
  = match m with
    | Ret x -> (x, s0)
    | Get k ->
      W.axiom1 k s0;
      run (k s0) s0 post
    | Put s k ->
      run k s post

/// Now we're going to package up this WP semantics into an effect in
/// F* by building an WP-indexed computation type. We have to define:
///
///   1. a representation type
///   2. a return
///   3. a bind
///   4. a subsumption rule
///   5. a rule for conditionals
///   6. a way to lift F*'s native pure wp-indexed terms to the new effect
///
/// We'll prove steps 1-3. And we'll define 4-6, but admitting their
/// associated proofs. Essentially, in this small example, the
/// representation I've chosen isn't really compatible with a
/// meaningful subsumption rule (which is the essence of 4, 5, 6)
///
/// The main work of doing steps 2 and 3 is to prove that that wp_of
/// is a monad morphism from m to wp_t. i.e., we have to show that the
/// return
///
///    a. wp_of (return x) == wp_return x
///    b. wp_of (bind f g) == wp_bind (wp_of f) (wp_of . g)
///

/// `irepr`: The underlying representation of our computation type
let irepr a s (wp: wp_t s a) =
  unit -> m:m s a { wp_of m `F.feq` wp }

/// The WP of return is the return of the wp
let ireturn (a:Type) (s:Type) (x:a)
  : irepr a s (wp_return x)
  = fun () -> Ret x

/// bind_wp: This is a bind for the WP type `wp_t`
let bind_wp #a #b #s (wp_f:wp_t s a) (wp_g: (a -> wp_t s b))
  : wp_t s b
  = F.on _ (fun s0 post -> wp_f s0 (fun (x, s1) -> wp_g x s1 post))

/// Now things get a bit technical in the main proof of the bind case
/// of the morphisms

/// First, we define a domain-restricted version of function composition
let ( *. ) #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = F.on _ (fun x -> f (g x))

/// An prove a auxiliary lemma about it (that's needed for funcitonal
/// extensionality)
let lem_on_comp #a #b #c (f:b -> c) (g:a -> b)
  : Lemma (F.on _ (f *. g) == f *. g)
  = ()

/// We also rely on eta being a provable equality
let eta (f:'a -> 'b) : Lemma (f == (fun x -> f x)) = ()

/// Now, here's the main lemma of property (b).
///   stating at first using extensional equality
let rec bind_wp_lem' (#a:_) (#b:_) (#s:_) (f:m s a) (g: (a -> m s b))
  : Lemma (wp_of (bind_m f g) `F.feq` bind_wp (wp_of f) (wp_of *. g))
  = match f with
    | Ret x ->
      assert (bind_m f g == g x);
      assert_norm (wp_of #a #s (Ret x) `F.feq` (fun s0 post -> post (x, s0)));
      assert (wp_of (bind_m (Ret x) g) `F.feq` bind_wp (wp_of (Ret x)) (wp_of *. g))
           by (T.dump "A";
               T.norm [delta];
               T.dump "B";
               let x = T.forall_intro () in
               T.dump "C";
               T.mapply (`eta);
               T.dump "D")

    | Put s k ->
      bind_wp_lem' k g;
      assert_norm (wp_put (bind_wp (wp_of k) (wp_of *. g)) s `F.feq`
                   bind_wp (wp_put (wp_of k) s) (wp_of *. g))

    | Get k ->
      let aux (x:s)
        : Lemma
          (ensures (wp_of (bind_m (k x) g) `F.feq`
                    bind_wp (wp_of (k x)) (wp_of *. g)))
          [SMTPat (k x)]
        = W.axiom1 k x;
          bind_wp_lem' (k x) g
      in
      assert_norm (wp_of (bind_m (Get k) g) ==
                   wp_of (Get (fun x -> bind_m (k x) g)));
      assert_norm (wp_of (Get (fun x -> bind_m (k x) g)) ==
                   F.on _ (fun s0 -> (wp_of (bind_m (k s0) g)) s0));

      assert ((fun s0 -> (wp_of (bind_m (k s0) g)) s0) `F.feq`
              (fun s0 -> bind_wp (wp_of (k s0)) (wp_of *. g) s0));
      assert_norm (bind_wp (wp_of (Get k)) (wp_of *. g) ==
                   bind_wp (F.on _ (fun s0 -> wp_of (k s0) s0))
                            (wp_of *. g));
      assert_norm (bind_wp (F.on _ (fun s0 -> wp_of (k s0) s0)) (wp_of *. g) ==
                   F.on _ (fun s0 -> bind_wp (wp_of (k s0)) (wp_of *. g) s0))

/// We now turn the extensional variant of the lemma into an equality
let bind_wp_lem (#a:_) (#b:_) (#s:_) (f:m s a) (g: (a -> m s b))
  : Lemma (wp_of (bind_m f g) == bind_wp (wp_of f) (wp_of *. g))
  = bind_wp_lem' f g

/// Now, we're ready to define a bind on the representation of our
/// indexed computation type
///
/// The index of the result is just the bind of indexes of the
/// arguments
let ibind a b s wp_f (wp_g: a ^-> wp_t s b)
    (f:irepr a s wp_f)
    (g : (x:a -> irepr b s (wp_g x)))
  : irepr b s (bind_wp wp_f wp_g)
  = let m_f = f () in
    let m_g = fun x -> g x () in
    fun () ->
         bind_wp_lem m_f m_g;
         assert (forall x. (wp_of *. m_g) x == wp_g x);
         assert (wp_f == wp_of m_f);
         assert ((wp_of *. m_g) `F.feq` wp_g);
         F.extensionality _ _ ((wp_of *. m_g)) wp_g;
         assert (F.on _ (wp_of *. m_g) == F.on _ wp_g);
         assert (F.on _ wp_g == wp_g);
         lem_on_comp wp_of m_g;
         assert (F.on _ (wp_of *. m_g) == (wp_of *. m_g));
         bind_m m_f m_g

/// Here are a couple of actions lifted into the indexed type
/// Their WPs are just the WPs of the corresponding `m` actions
let iget s : irepr s s (wp_of (Get Ret)) =
    fun () -> Get Ret
let iput s (x:s) : irepr unit s (wp_of (Put x (Ret ()))) =
    fun () -> Put x (Ret ())

/// As explained above, for steps 4--6, This representation doesn't
/// yet allow for subsumption So faking out these rules for now

/// What we really want is a way to subsume the WP of a computation
/// with another WP that implies the original one.
///
/// But we can't prove that on the representation for now
///
/// So, I just admit it
let isubcomp (a:Type) (s:Type) (wp wp':wp_t s a) (f:irepr a s wp)
  : Pure (irepr a s wp')
    (requires
      forall s0 post. wp' s0 post ==> wp s0 post)
    (ensures fun _ -> True)
  = admit()


/// Here's a rule for composing `f` and `g` under a conditional
/// This is proven sound with respect to the subsumption rule
let i_if_then_else (a:Type) (s:Type) (wpf wpg:wp_t s a)
                   (f:irepr a s wpf)
                   (g:irepr a s wpg)
                   (p:Type0)
  : Type
  = irepr a s (F.on _ (fun s0 post -> (p ==> wpf s0 post) /\ (~p ==> wpg s0 post)))

let lift_wp (a:Type)
            (s:Type0)
            (wp:pure_wp a)
  : wp_t s a
  = F.on _ (fun (s0:s) (k:post_t s a) -> wp (fun a -> k (a, s0)))

/// Then, here's a way to lift a pure computation to an irepr
/// Again, without a proof ...
let lift_pure_ifst
    (a:Type)
    (s:Type0)
    (wp:pure_wp a)
    (f:unit -> PURE a wp)
  : irepr a s (lift_wp a s wp)
  = admit();
    let x = f() in
    isubcomp a s (wp_return x) (lift_wp a s wp) (ireturn a s x)


/// Now, we have what we need to turn it into a layered effect
reifiable reflectable
layered_effect {
  IFST : a:Type -> s:Type0 -> wp:wp_t s a -> Effect
  with repr         = irepr;
       return       = ireturn;
       bind         = ibind;
       subcomp      = isubcomp;
       if_then_else = i_if_then_else;

       get = iget;
       put = iput
}
sub_effect PURE ~> IFST = lift_pure_ifst

/// We define an abbreviation for specification is a more familiar
/// Hoare style
effect IFst (a:Type) (s:Type) (pre:s -> Type) (post: s -> a -> s -> Type)
  = IFST a s (F.on _ (fun s0 k -> pre s0 /\ (forall x s1. post s0 x s1 ==> k (x, s1))))

/// And here's a function in the Ifst effect.
///
/// F* infers a VC using `wp_of`. We use a tactic to normalize it into
/// a formula that more efficiently SMT encodeable and the proof is
/// automatic
let iincr ()
  : IFst unit int
    (requires fun s -> True)
    (ensures fun s0 x s1 ->
      s1 == s0 + 1)
  by (T.norm [delta; zeta; iota]; T.smt())
  =
  let x = IFST?.get int in
  let y = x + 1 in
  IFST?.put int y
