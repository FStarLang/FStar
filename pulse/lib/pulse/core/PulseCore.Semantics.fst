(*
   Copyright 2024 Microsoft Research

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
module PulseCore.Semantics

module U = FStar.Universe
module ST = PulseCore.HoareStateMonad
module NST = PulseCore.NondeterministicHoareStateMonad
module PNST = PulseCore.PartialNondeterministicHoareStateMonad
module F = FStar.FunctionalExtensionality

open FStar.Ghost
open FStar.FunctionalExtensionality
open PulseCore.PartialNondeterministicHoareStateMonad

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quantifiers is more convenient for the proof done here.

let associative #a (f: a -> a -> a) =
  forall x y z. f x (f y z) == f (f x y) z

let commutative #a (f: a -> a -> a) =
  forall x y. f x y == f y x

let is_unit #a (x:a) (f:a -> a -> a) =
  forall y. f x y == y /\ f y x == y

(**
 * A state typeclass:
 *  - [s] is the type of states
 *  - [is_full_mem] a refinement on states to the entire heap used at runtime
 *  - [pred] is the type of state assertions
 *  - [emp] is the empty state assertion
 *  - [star] is the separating conjunction of state assertions
 *  - [interp p s] is the interpretation of a state assertion [p] in a state [s]
 *  - [evolves] is a preorder on states, constraining how it evolves
 *  - [invariant] is an internal invariant that a caller can instantiate and is maintained
 *                by every action and the semantics as a whole
 *  - [laws] state that {pred, emp, star} are a commutative monoid
 *)
noeq
type state : Type u#(s + 1)= {
  s:Type u#s;
  is_full_mem: s -> prop;
  pred:Type u#s;
  emp: pred;
  star: pred -> pred -> pred;
  interp: pred -> s -> prop;
  invariant: s -> pred;
  laws: squash (associative star /\ commutative star /\ is_unit emp star);
  can_step: s -> FStar.Ghost.erased bool;
}

let full_mem (st:state u#s) : Type u#s = m:st.s { st.is_full_mem m }

(** [post a c] is a postcondition on [a]-typed result *)
let post (s:state) a = a ^-> s.pred

(** We interpret computations into the npst monad,
    for partial, nondeterministic, preorder-state transfomers.
    npst_sep provides separation-logic specifications for those computations.
    pst_sep is analogous, except computation in pst_sep are also total
 **)
let st_sep_aux (st:state)
                (aux:full_mem st -> prop) 
                (inv:full_mem st -> st.pred)
                (a:Type)
                (pre:st.pred)
                (post:a -> st.pred) =
  ST.st #(full_mem st) a
    (fun s0 -> FStar.Ghost.reveal (st.can_step s0) /\ aux s0 /\ st.interp (pre `st.star` inv s0) s0 )
    (fun _ x s1 -> aux s1 /\ st.interp (post x `st.star` inv s1) s1)
     
let st_sep st a pre post = st_sep_aux st (fun _ -> True) st.invariant a pre post

let nst_sep (st:state u#s) (a:Type u#a) (pre:st.pred) (post:a -> st.pred) =
  NST.nst #(full_mem st) a
    (fun s0 -> st.interp (pre `st.star` st.invariant s0) s0 )
    (fun _ x s1 -> st.interp (post x `st.star` st.invariant s1) s1)

let pnst_sep_aux (st:state u#s) (guard:st.s -> FStar.Ghost.erased bool) (a:Type u#a) (pre:st.pred) (post:a -> st.pred) =
  PNST.pnst #(full_mem st) a
    (fun s0 -> FStar.Ghost.reveal (guard s0) /\ st.interp (pre `st.star` st.invariant s0) s0 )
    (fun _ x s1 -> st.interp (post x `st.star` st.invariant s1) s1)

let pnst_sep_can_step (st:state) = pnst_sep_aux st st.can_step

let pnst_sep (st:state) = pnst_sep_aux st (fun _ -> true)


(** [action c s]: atomic actions are, intuitively, single steps of
 *  state-transforming computations (in the nmst monad).
 *  However, we augment them with two features:
 *   1. they have pre-condition [pre] and post-condition [post]
 *   2. their type guarantees that they are frameable
 *  Thanks to Matt Parkinson for suggesting to set up atomic actions
 *  as frame-preserving steps.
 *  Also see: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/views.pdf
 *)
noeq
type action (st:state u#s) (a:Type u#a) : Type u#(max a s) = {
  pre: st.pred;
  post: post st a;
  step: (
    frame:st.pred ->
    st_sep st a (st.star pre frame) 
                (fun x -> st.star (post x) frame)
  )
 }
  
let as_post (#st:state u#s) (#a:Type u#a) (p:st.pred)
: post st a
= F.on_dom a (fun _ -> p)

(** [m #st a pre post]:
 *  A free monad for divergence, state and parallel composition
 *  with generic actions. The main idea:
 *
 *  Every continuation may be divergent. As such, [m] is indexed by
 *  pre- and post-conditions so that we can do proofs
 *  intrinsically.
 *
 *  Universe-polymorphic im both the state and result type
 *
 *)
noeq
type m (#st:state u#s) : (a:Type u#a) -> st.pred -> post st a -> Type u#(max (act + 1) s (a + 1)) =
  | Ret:
      #a:Type u#a ->
      #post:post st a ->
      x:a ->
      m a (post x) post
  | Act:
      #a:Type u#a ->
      #post:post st a ->
      #b:Type u#act ->
      f:action st b ->
      k:(x:b -> Dv (m a (f.post x) post)) ->
      m a f.pre post
  | Par:
      #pre0:_ ->
      #post0:_ ->
      m0:m (U.raise_t unit) pre0 (as_post post0) ->
      #pre1:_ ->
      #post1:_ ->
      m1:m (U.raise_t unit) pre1 (as_post post1) ->
      #a:_ ->
      #post:_ ->
      k:m a (st.star post0 post1) post ->
      m a (st.star pre0 pre1) post

/// The semantics comes in two levels:
///
///   1. A single-step relation [step] which selects an atomic action to
///      execute in the tree of threads
///
///   2. A top-level driver [run] which repeatedly invokes [step]
///      until it returns with a result and final state.

(**
 * [step_result #st a q frame]:
 *    The result of evaluating a single step of a program
 *    - s, c: The state and its monoid
 *    - a : the result type
 *    - q : the postcondition to be satisfied after fully reducing the programs
 *    - frame: a framed assertion to carry through the proof
 *)
noeq
type step_result (#st:state u#s) (a:Type u#a) (q:post st a) (frame:st.pred) =
  | Step: next:_ -> //precondition of the reduct
          m:m a next q -> //the reduct
          step_result a q frame

(**
 * [step f frame]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *)
let rec step 
    (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (f:m a p q)
    (frame:st.pred)
: Tot (pnst_sep_can_step st
        (step_result a q frame)
        (p `st.star` frame)
        (fun x -> Step?.next x `st.star` frame))
      (decreases f)
= match f with
  | Ret x -> 
    weaken <| return <| Step (q x) (Ret x)
  | Act f k ->
    let k (x:_) 
    : Dv (pnst_sep st (step_result a q frame)
                    (f.post x `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let n : m a (f.post x) q = k x in
      weaken (return (Step _ n))
    in
    weaken <| bind (PNST.lift <| (NST.lift <| f.step frame)) k
  | Par #_ #pre0 #post0 (Ret x0) #pre1 #post1 (Ret x1) #a #post k ->
    weaken <| return <| Step _ k
  | Par #_ #pre0 #post0 m0 #pre1 #post1 m1 #a #postk k ->
    let q : post st a = coerce_eq () q in
    let choose (b:bool)
    : pnst_sep_can_step st
        (step_result a q frame)
        (p `st.star` frame)
        (fun x -> (Step?.next x `st.star` frame))
    = if b
      then weaken <| 
           bind (step m0 (pre1 `st.star` frame))
                (fun x -> return <| Step _ <| Par (Step?.m x) m1 k)
      else weaken <| 
           bind (step m1 (pre0 `st.star` frame))
                (fun x -> return <| Step _ <| Par m0 (Step?.m x) k) 
    in
    weaken <| bind (lift <| NST.flip()) choose 

let rec decide_guard
      (#st:state u#s)
      (#pre:st.pred)
      (#a:Type u#a) 
      (#post:post st a)
      (guard: st.s -> erased bool)
      (f:unit -> Dv (pnst_sep_aux st guard a pre post))
: Dv (pnst_sep st a pre post)
= //a trivial model
  decide_guard guard f
  //Though, operationally we'd run `f ()`

(** The main partial correctness result:
 *    m computations can be interpreted into nmst_sep computations 
 *)    
let rec run (#st:state u#s) 
            (#pre:st.pred)
            (#a:Type u#a) 
            (#post:post st a)
            (f:m a pre post)
: Dv (pnst_sep st a pre post)
= match f with
  | Ret x -> 
    weaken <| return x
  | _ ->
    let k (s:step_result a post st.emp)
    : Dv (pnst_sep st a (Step?.next s) post)
    = let Step _ f = s in
      run f
    in
    let step_and_continue 
      : pnst_sep_can_step st a pre post
      = weaken <| bind (step f st.emp) k
    in
    decide_guard st.can_step (fun _ -> step_and_continue)

let ctr = nat
let tape = ctr -> bool
(** The main partial correctness result:
 *    m computations can be interpreted into nmst_sep computations 
 *)    
let run_alt (#st:state u#s) 
            (#pre:st.pred)
            (#a:Type u#a) 
            (#post:post st a)
            (f:m a pre post)
            (s0:full_mem st { st.interp (st.star pre (st.invariant s0)) s0 })
            (t:tape)
            (ctr:ctr)
: Dv (res:(a & full_mem st) { st.interp (st.star (post res._1) (st.invariant res._2)) res._2 })
= let (x, s, _) = repr (run f) s0 t ctr in
  (x, s)


(** [return]: easy, just use Ret *)
let ret (#st:state) (#a:Type) (x:a) (post:post st a)
  : m a (post x) post
  = Ret x

let raise_action
    (#st:state u#s)
    (#t:Type u#a)
    (a:action st t)
 : action st (U.raise_t u#a u#(max a b) t)
 = {
      pre = a.pre;
      post = F.on_dom _ (fun (x:U.raise_t u#a u#(max a b) t) -> a.post (U.downgrade_val x));
      step = (fun frame ->
               ST.weaken <|
               ST.bind (a.step frame) <|
               (fun x -> ST.return <| U.raise_val u#a u#(max a b) x))
   }

let act
    (#st:state u#s)
    (#t:Type u#act)
    (a:action st t)
: m t a.pre a.post
= Act a Ret

(**
 * [bind]: sequential composition works by pushing `g` into the continuation
 * at each node, finally applying it at the terminal `Ret`
 *)
let rec mbind
     (#st:state u#s)
     (#a:Type u#a)
     (#b:Type u#b)
     (#p:st.pred)
     (#q:post st a)
     (#r:post st b)
     (f:m a p q)
     (g: (x:a -> Dv (m b (q x) r)))
  : Dv (m u#s u#b u#act b p r)
  = match f with
    | Ret x -> g x
    | Act act k ->
      Act act (fun x -> mbind (k x) g)
    | Par #_ #pre0 #post0 ml
             #pre1 #post1 mr
             #postk k ->
      let k : m b (post0 `st.star` post1) r = mbind k g in
      let ml' : m (U.raise_t u#0 u#b unit) pre0 (as_post post0) =
         mbind ml (fun _ -> Ret #_ #(U.raise_t u#0 u#b unit) #(as_post post0) (U.raise_val u#0 u#b ()))
      in
      let mr' : m (U.raise_t u#0 u#b unit) pre1 (as_post post1) =
         mbind mr (fun _ -> Ret #_ #(U.raise_t u#0 u#b unit) #(as_post post1) (U.raise_val u#0 u#b ()))
      in
      Par ml' mr' k

let act_as_m0
    (#st:state u#s)
    (#t:Type u#0)
    (a:action st t)
: Dv (m t a.pre a.post)
= let k (x:U.raise_t u#0 u#act t)
    : Dv (m t (a.post (U.downgrade_val x)) a.post) 
    = Ret (U.downgrade_val x)
  in
  mbind (act (raise_action a)) k

let act_as_m1
    (#st:state u#s)
    (#t:Type u#1)
    (a:action st t)
: Dv (m u#s u#1 u#(max 1 b) t a.pre a.post)
= let k (x:U.raise_t t)
    : Dv (m t (a.post (U.downgrade_val x)) a.post) 
    = Ret (U.downgrade_val x)
  in
  mbind (act (raise_action a)) k

let act_as_m2
    (#st:state u#s)
    (#t:Type u#2)
    (a:action st t)
: Dv (m u#s u#2 u#(max 2 b) t a.pre a.post)
= let k (x:U.raise_t t)
    : Dv (m t (a.post (U.downgrade_val x)) a.post) 
    = Ret (U.downgrade_val x)
  in
  mbind (act (raise_action a)) k

noeq
type liftable : Type u#(1 + (max a b)) = {
  downgrade_val : (t:Type u#a -> U.raise_t u#a u#(max a b) t -> t);
  laws : squash (forall (t:Type u#a) (x:t). downgrade_val t (U.raise_val x) == x)
}

let act_as_m_poly
    (#st:state u#s)
    (#t:Type u#a)
    (l:liftable u#a u#b)
    (a:action st t)
: Dv (m u#s u#a u#(max a b) t a.pre a.post)
= let k (x:U.raise_t u#a u#(max a b) t)
    : Dv (m t (a.post (l.downgrade_val _ x)) a.post) 
    = Ret (l.downgrade_val _ x)
  in
  mbind (act (raise_action a)) k

(* Next, a main property of this semantics is that it supports the
   frame rule. Here's a proof of it *)

/// First, we prove that individual actions can be framed
///
/// --- That's not so hard, since we specifically required actions to
///     be frameable
let frame_action (#st:state u#s) (#a:Type u#act) 
                 (f:action st a) (frame:st.pred)
: g:action st a { g.post == F.on_dom a (fun x -> f.post x `st.star` frame) /\
                  g.pre == f.pre `st.star` frame }
= let step (fr:st.pred) 
    : st_sep st a 
      ((f.pre `st.star` frame) `st.star` fr)
      (F.on_dom a (fun x -> (f.post x `st.star` frame) `st.star` fr))
    = f.step (frame `st.star` fr)
  in
  { pre = _;
    post = F.on_dom a (fun x -> f.post x `st.star` frame);
    step }

/// Now, to prove that computations can be framed, we'll just thread
/// the frame through the entire computation, passing it over every
/// frameable action
let rec frame (#st:state u#s)
              (#a:Type u#a)
              (#p:st.pred)
              (#q:post st a)
              (fr:st.pred)
              (f:m a p q)
   : Dv (m u#s u#a u#act a (p `st.star` fr) (F.on_dom a (fun x -> q x `st.star` fr)))
   = match f with
     | Ret x -> Ret x
     | Act f k ->
       Act (frame_action f fr) (fun x -> frame fr (k x))
     | Par #_ #pre0 #post0 m0 #pre1 #post1 m1 #postk k ->
       let m0'
         : m (U.raise_t u#0 u#a unit) (pre0 `st.star` fr) 
             (F.on_dom _ (fun x -> (as_post post0) x `st.star` fr))
         = frame fr m0 in
       let m0'
         : m (U.raise_t u#0 u#a unit) (pre0 `st.star` fr) (as_post (post0 `st.star` fr))
         = m0'
       in
       let k' = frame fr k in
       Par m0' m1 k'

(**
 * [par]: Parallel composition
 * Works by just using the `Par` node and `Ret` as its continuation
 **)
let par (#st:state u#s)
        #p0 #q0 (m0:m unit p0 (as_post q0))
        #p1 #q1 (m1:m unit p1 (as_post q1))
 : Dv (m u#s u#0 u#act unit (p0 `st.star` p1) (as_post (q0 `st.star` q1)))
 = let m0' = mbind m0 (fun _ -> Ret #_ #_ #(as_post q0) (U.raise_val u#0 u#0 ())) in
   let m1' = mbind m1 (fun _ -> Ret #_ #_ #(as_post q1) (U.raise_val u#0 u#0 ())) in
   Par m0' m1' (Ret ())

let conv (#st:state u#s) (a:Type u#a)
         (#p:st.pred)
         (#q:post st a)
         (q':post st a { forall x. q x == q' x })
: Lemma (m u#s u#a u#act a p q == m u#s u#a u#act a p q')
= F.extensionality _ _ q q'
