(*
   Copyright 2008-2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

/// This module derives a Hoare-style state effect using a free monad representation
///
/// There are several design considerations to make such an effect
///   work well within F*:
///
/// - The effect should support a subsumption relation that allows for
///   strengthening of preconditions and weakening of postconditions
/// - The effect should play nicely with pure pre- and postconditions,
///   i.e. they should be integrated with the hoare indices of the state effect
///   Squash types, refinements, lemmas, etc. are quite commonplace in F*,
///     and so, the effect should work seamlessly with them
///
/// - Then there are other considerations such as bind should be doubly
///     universe polymorphic, etc.
///
/// See also https://fstar-lang.org/oplss2021/code/OPLSS2021.ParDiv.fst
///   for another attempt,
/// The current module enhances it by providing a better integrated PURE effect
///
/// The main trick is to add a Strengthen node in the action tree that
///   strengthens the precondition with a prop

module HoareSTFree

open FStar.Monotonic.Pure

/// Fixing the type of the state to int, it should be possible to make it
///   polymorphic in the state type as in the ParDiv development

type pre = int -> Type0
type post (a:Type) = int -> a -> int -> Type0

/// The free monad would contain an Act node,
///   that has an atomic action, followed by a continuation k
///
/// The following combinators are for the pre- and postcondition of
///   the Act node (derived from the action and k pre and post)

unfold
let act_p (#a:Type) (a_p:pre) (a_q:post a) (k_p:a -> pre) : pre =
  fun s0 -> a_p s0 /\ (forall (x:a) (s1:int). a_q s0 x s1 ==> k_p x s1)

unfold
let act_q (#a:Type) (#b:Type) (a_q:post a) (k_q:a -> post b) : post b =
  fun s0 y s2 -> exists (x:a) (s1:int). a_q s0 x s1 /\ k_q x s1 y s2

/// Logical guard for the rule of consequence, i.e. weakening
///   {p0} c {q0} to {p1} c {q1}

unfold
let weaken_ok (#a:Type) (p0:pre) (q0:post a) (p1:pre) (q1:post a) : Type0 =
  (forall (s:int). p1 s ==> p0 s) /\
  (forall (s0:int) (x:a) (s1:int). p1 s0 ==> q0 s0 x s1 ==> q1 s0 x s1)


/// Precondition of the strengthen node

unfold
let strengthen_pre (p:pre) (phi:pure_pre) : pre =
  fun s -> p s /\ phi

/// A free monad for divergence and int state
///
/// It can also be made total, by indexing with a nat that
///   counts number of actions in the tree
///
/// See https://fstar-lang.org/oplss2021/code/OPLSS2021.ParTot.fst

noeq
type m : a:Type -> p:pre -> q:post a -> Type =
  | Ret:  //parametric on the postcondition q
    #a:Type -> #q:post a ->
    x:a ->
    m a (fun s0 -> q s0 x s0) q
  | Act:
    #a:Type -> #a_p:pre -> #a_q:post a ->
    act:(s0:int -> Pure (a & int) (a_p s0) (fun (x, s1) -> a_q s0 x s1)) ->  //atomic action
    #b:Type -> #k_p:(a -> pre) -> #k_q:(a -> post b) ->
    k:(x:a -> Dv (m b (k_p x) (k_q x))) ->
    m b (act_p a_p a_q k_p) (act_q a_q k_q)
  | Weaken:
    #a:Type -> #p0:pre -> #q0:post a -> #p1:pre -> #q1:post a ->
    #squash (weaken_ok p0 q0 p1 q1) ->
    f:m a p0 q0 ->
    m a p1 q1
  | Strengthen:  //strengthening the precondition with phi
    #a:Type -> #phi:pure_pre -> #p:pre -> #q:post a ->
    f:(squash phi -> Dv (m a p q)) ->
    m a (strengthen_pre p phi) q

/// We first define the effect,
///   later we will give a semantic model and prove soundness of the logic
///   with a definitional interpreter

/// Underlying represetation is a thunked tree

type repr (a:Type) (p:pre) (q:post a) = unit -> Dv (m a p q)

/// return is simple, use the Ret node

let return (a:Type) (x:a) (q:post a) : repr a (fun s0 -> q s0 x s0) q =
  fun _ -> Ret x

/// bind pushes the continuation g inside the tree
///
/// When f is a Ret, apply the result to the continuation
///
/// Note the indices of the return type, this is the hoare logic we want

let rec bind (a b:Type)
  (f_p:pre) (f_q:post a)
  (g_p:a -> pre) (g_q:a -> post b)
  (f:repr a f_p f_q) (g:(x:a -> repr b (g_p x) (g_q x)))
  : repr b (act_p f_p f_q g_p) (act_q f_q g_q)
  = fun _ ->
    let f = f () in
    match f with
    | Ret x -> Weaken (g x ())
    | Act #c #a_p #a_q act #_ #_ #_ k ->
      let k' = fun (x:c) -> (bind _ _ _ _ _ _ (fun _ -> k x) g) () in
      Weaken (Act #c #a_p #a_q act #b #_ #_ k')
    | Weaken f -> Weaken ((bind _ _ _ _ _ _ (fun _ -> f) g) ())
    | Strengthen #_ #phi #p #q f ->
      let f : squash phi -> Dv (m b (act_p p q g_p) (act_q q g_q)) =
        fun _ -> (bind _ _ _ _ _ _ (fun _ -> f ()) g) () in
      let f : m b (strengthen_pre (act_p p q g_p) phi) (act_q q g_q) =
        Strengthen #_ #phi #_ #_ f in
      Weaken f

/// subcomp simply wraps in a Weaken node

let subcomp (a:Type)
  (f_p:pre) (f_q:post a)
  (g_p:pre) (g_q:post a)
  (f:repr a f_p f_q)
  : Pure (repr a g_p g_q)
         (requires weaken_ok f_p f_q g_p g_q)
         (ensures fun _ -> True)
  = fun _ -> Weaken (f ())

/// And that's it!

effect {
  M (a:Type) (p:pre) (q:post a)
  with {repr; return; bind; subcomp}
}

/// We now define a lift from PURE

unfold
let pure_p (#a:Type) (wp:pure_wp a) : pre =
  fun _ -> as_requires wp

unfold
let pure_q (#a:Type) (wp:pure_wp a) : post a =
  fun s0 x s1 -> s0 == s1 /\ as_ensures wp x

let lift_PURE_M (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
  : repr a (pure_p wp) (pure_q wp)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun _ ->
    let f : squash (as_requires wp) -> Dv (m a (fun s0 -> True) (pure_q wp)) =
      fun _ ->
      let x = f () in
      let t : m a (fun s0 -> s0 == s0 /\ as_ensures wp x) (pure_q wp) =
        Ret x in
      let t : m a (fun _ -> True) (pure_q wp) = Weaken t in
      t in
    let t : m a (strengthen_pre (fun _ -> True) (as_requires wp)) (pure_q wp) =
      Strengthen f in
    Weaken t

sub_effect PURE ~> M = lift_PURE_M

/// Using the effect, notice how the pre- and postconditions,
///   refinements are chained seamlessly

assume val p : prop
assume val q : prop

assume val f : squash p -> M unit (fun _ -> True) (fun _ _ s1 -> squash q /\ s1 > 2)
assume val g : unit -> Pure unit True (fun _ -> squash p)
assume val h : unit -> M unit (fun s0 -> squash q /\ s0 > 0) (fun _ _ s1 -> s1 > 2)

let test () : M unit (fun _ -> True) (fun _ _ s1 -> s1 > 0) =
  g ();
  f ();
  h ()


/// And now a semantic model for the free monad, proving soundness of the logic
///
/// We define a definitional interpreter as a state passing function,
///   that interprets the action tree


/// step_result is the result of taking a single step

noeq
type step_result (a:Type) =
  | Step: #p:pre -> #q:post a -> m a p q -> step_result a

/// As computations take step,
///   their preconditions become weaker,
///   while the postconditions become stronger

unfold
let weaker_p (p0 p1:pre) (s0 s1:int) = p0 s0 ==> p1 s1

unfold
let stronger_q (#a:Type) (q0 q1:post a) (s0 s1:int) =
  forall (x:a) (s_final:int). q1 s1 x s_final ==> q0 s0 x s_final

/// The single-step function

let step (#a:Type) (#p:pre) (#q:post a) (f:m a p q)
  : s0:int ->
    Div (step_result a & int)
        (requires p s0)
        (ensures fun (r, s1) ->
                 let Step #_ #p_next #q_next g = r in
                 weaker_p p p_next s0 s1 /\
                 stronger_q q q_next s0 s1)
  = fun s0 ->
    match f with
    | Ret _ -> Step f, s0
    | Act act k ->
      let x, s1 = act s0 in
      Step (k x), s1
    | Weaken f -> Step f, s0
    | Strengthen f -> Step (f ()), s0


/// Wrapper around step, notice the spec of the Div effect

let rec run (#a:Type) (#p:pre) (#q:post a) (f:m a p q)
  : s0:int ->
    Div (a & int) (requires p s0)
                (ensures fun (x, s1) -> q s0 x s1)
  = fun s0 ->
    match f with
    | Ret x -> x, s0
    | _ ->
      let Step f, s1 = step f s0 in
      run f s1
