(*
   Copyright 2019-2021 Microsoft Research

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
module OPLSS2021.ParNDSDiv
module U = FStar.Universe
(**
 * This module provides a semantic model for a combined effect of
 * divergence, state and parallel composition of atomic actions.
 *
 * It also builds a generic separation-logic-style program logic
 * for this effect, in a partial correctness setting.

 * It is also be possible to give a variant of this semantics for
 * total correctness. However, we specifically focus on partial correctness
 * here so that this semantics can be instantiated with lock operations,
 * which may deadlock. See ParTot.fst for a total-correctness variant of
 * these semantics.
 *
 *)

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quanitifers was more convenient for the proof done here.

let associative #a (f: a -> a -> a) =
  forall x y z. f x (f y z) == f (f x y) z

let commutative #a (f: a -> a -> a) =
  forall x y. f x y == f y x

let is_unit #a (x:a) (f:a -> a -> a) =
  forall y. f x y == y /\ f y x == y


(**
 * In addition to being a commutative monoid over the carrier [r]
 * a [comm_monoid s] also gives an interpretation of `r`
 * as a predicate on states [s]
 *)
noeq
type comm_monoid (s:Type) = {
  r:Type;
  emp: r;
  star: r -> r -> r;
  interp: r -> s -> prop;
  laws: squash (associative star /\ commutative star /\ is_unit emp star)
}

(** [post a c] is a postcondition on [a]-typed result *)
let post #s a (c:comm_monoid s) = a -> c.r

(** [action c s]: atomic actions are, intuitively, single steps of
 *  computations interpreted as a [s -> a & s].
 *  However, we augment them with two features:
 *   1. they have pre-condition [pre] and post-condition [post]
 *   2. their type guarantees that they are frameable
 *  Thanks to Matt Parkinson for suggesting to set up atomic actions
 *  this way.
 *  Also see: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/views.pdf
 *)
noeq
type action #s (c:comm_monoid s) (a:Type) = {
   pre: c.r;
   post: a -> c.r;
   sem: (frame:c.r ->
         s0:s{c.interp (c.star pre frame) s0} ->
         (x:a & s1:s{c.interp (post x `c.star` frame) s1}));
}

(** [m s c a pre post] :
 *  A free monad for divergence, state and parallel composition
 *  with generic actions. The main idea:
 *
 *  Every continuation may be divergent. As such, [m] is indexed by
 *  pre- and post-conditions so that we can do proofs
 *  intrinsically.
 *
 *  Universe-polymorphic in both the state and result type
 *
 *)
noeq
type m (#s:Type u#s) (#c:comm_monoid u#s u#s s) : (a:Type u#a) -> c.r -> post a c -> Type =
  | Ret : #a:_ -> #post:(a -> c.r) -> x:a -> m a (post x) post
  | Act : #a:_ -> #post:(a -> c.r) -> #b:_ -> f:action c b -> k:(x:b -> Dv (m a (f.post x) post)) -> m a f.pre post
  | Par : pre0:_ -> post0:_ -> m0: m (U.raise_t unit) pre0 (fun _ -> post0) ->
          pre1:_ -> post1:_ -> m1: m (U.raise_t unit) pre1 (fun _ -> post1) ->
          #a:_ -> #post:_ -> k:m a (c.star post0 post1) post ->
          m a (c.star pre0 pre1) post


/// We assume a stream of booleans for the semantics given below
/// to resolve the nondeterminism of Par
assume
val bools : nat -> bool

/// The semantics comes in two levels:
///
///   1. A single-step relation [step] which selects an atomic action to
///      execute in the tree of threads
///
///   2. A top-level driver [run] which repeatedly invokes [step]
///      until it returns with a result and final state.

(**
 * [step_result s c a q frame]:
 *    The result of evaluating a single step of a program
 *    - s, c: The state and its monoid
 *    - a : the result type
 *    - q : the postcondition to be satisfied after fully reducing the programs
 *    - frame: a framed assertion to carry through the proof
 *)
noeq
type step_result #s (#c:comm_monoid s) a (q:post a c) (frame:c.r) =
  | Step: p:_ -> //precondition of the reduct
          m a p q -> //the reduct
          state:s {c.interp (p `c.star` frame) state} -> //the next state, satisfying the precondition of the reduct
          nat -> //position in the stream of booleans (less important)
          step_result a q frame

(**
 * [step i f frame state]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *
 *)
let rec step #s #c (i:nat) #pre #a #post (f:m a pre post) (frame:c.r) (state:s)
  : Div (step_result a post frame)
        (requires
          c.interp (pre `c.star` frame) state)
        (ensures fun _ -> True)
  = match f with
    | Ret x ->
        //Nothing to do, just return
        Step (post x) (Ret x) state i

    | Act act1 k ->
        //Evaluate the action and return the continuation as the reduct
        let (| b, state' |) = act1.sem frame state in
        Step (act1.post b) (k b) state' i

    | Par pre0 post0 (Ret x0)
          pre1 post1 (Ret x1)
          k ->
        //If both sides of a `Par` have returned
        //then step to the continuation
        Step (post0 `c.star` post1) k state i

    | Par pre0 post0 m0
          pre1 post1 m1
          k ->
        //Otherwise, sample a boolean and choose to go left or right to pick
        //the next command to reduce
        //The two sides are symmetric
        if bools i
        then let Step pre0' m0' state' j =
                 //Notice that, inductively, we instantiate the frame extending
                 //it to include the precondition of the other side of the par
                 step (i + 1) m0 (pre1 `c.star` frame) state in
             Step (pre0' `c.star` pre1) (Par pre0' post0 m0' pre1 post1 m1 k) state' j
        else let Step pre1' m1' state' j =
                 step (i + 1) m1 (pre0 `c.star` frame) state in
             Step (pre0 `c.star` pre1') (Par pre0 post0 m0 pre1' post1 m1' k) state' j

(**
 * [run i f state]: Top-level driver that repeatedly invokes [step]
 *
 * The type of [run] is the main theorem. It states that it is sound
 * to interpret the indices of `m` as a Hoare triple in a
 * partial-correctness semantics
 *
 *)
let rec run #s #c (i:nat) #pre #a #post (f:m a pre post) (state:s)
  : Div (a & s)
    (requires
      c.interp pre state)
    (ensures fun (x, state') ->
      c.interp (post x) state')
  = match f with
    | Ret x -> x, state
    | _ ->
      let Step pre' f' state' j = step i f c.emp state in
      run j f' state'

/// eff is a dependent parameterized monad. We give a return and bind
/// for it, though we don't prove the monad laws

(** [return]: easy, just use Ret *)
let return #s (#c:comm_monoid s) #a (x:a) (post:a -> c.r)
  : m a (post x) post
  = Ret x

(**
 * [bind]: sequential composition works by pushing `g` into the continuation
 * at each node, finally applying it at the terminal `Ret`
 *)
let rec bind (#s:Type u#s)
             (#c:comm_monoid s)
             (#a:Type u#a)
             (#b:Type u#b)
             (#p:c.r)
             (#q:a -> c.r)
             (#r:b -> c.r)
             (f:m a p q)
             (g: (x:a -> Dv (m b (q x) r)))
  : Dv (m b p r)
  = match f with
    | Ret x -> g x
    | Act act k ->
      Act act (fun x -> bind (k x) g)
    | Par pre0 post0 ml
          pre1 post1 mr
          k ->
      let k : m b (post0 `c.star` post1) r = bind k g in
      let ml' : m (U.raise_t u#0 u#b unit) pre0 (fun _ -> post0) =
         bind ml (fun _ -> Ret (U.raise_val u#0 u#b ()))
      in
      let mr' : m (U.raise_t u#0 u#b unit) pre1 (fun _ -> post1) =
         bind mr (fun _ -> Ret (U.raise_val u#0 u#b ()))
      in
      Par #s #c pre0 post0 ml'
                pre1 post1 mr'
                #b #r k

(* Next, a main property of this semantics is that it supports the
   frame rule. Here's a proof of it *)

/// First, we prove that individual actions can be framed
///
/// --- That's not so hard, since we specifically required actions to
///     be frameable
let frame_action (#s:Type) (#c:comm_monoid s) (#a:Type) (f:action c a) (fr:c.r)
  : g:action c a { g.post == (fun x -> f.post x `c.star` fr) /\
                   g.pre == f.pre `c.star` fr }
  = let pre = f.pre `c.star` fr in
    let post x = f.post x `c.star` fr in
    let sem (frame:c.r) (s0:s{c.interp (c.star pre frame) s0})
      : (x:a & s1:s{c.interp (post x `c.star` frame) s1})
      = let (| x, s1 |) = f.sem (fr `c.star` frame) s0 in
        (| x, s1 |)
    in
    { pre = pre;
      post = post;
      sem = sem }

/// Now, to prove that computations can be framed, we'll just thread
/// the frame through the entire computation, passing it over every
/// frameable action
let rec frame (#s:Type u#s)
              (#c:comm_monoid s)
              (#a:Type u#a)
              (#p:c.r)
              (#q:a -> c.r)
              (fr:c.r)
              (f:m a p q)
   : Dv (m a (p `c.star` fr) (fun x -> q x `c.star` fr))
   = match f with
     | Ret x -> Ret x
     | Act f k ->
       Act (frame_action f fr) (fun x -> frame fr (k x))
     | Par pre0 post0 m0 pre1 post1 m1 k ->
       Par (pre0 `c.star` fr) (post0 `c.star` fr) (frame fr m0)
           pre1 post1 m1
           (frame fr k)

(**
 * [par]: Parallel composition
 * Works by just using the `Par` node and `Ret` as its continuation
 **)
let par #s (#c:comm_monoid s)
        #p0 #q0 (m0:m unit p0 (fun _ -> q0))
        #p1 #q1 (m1:m unit p1 (fun _ -> q1))
 : Dv (m unit (p0 `c.star` p1) (fun _ -> q0 `c.star` q1))
 = let m0' : m (U.raise_t unit) p0 (fun _ -> q0) =
       bind m0 (fun _ -> Ret (U.raise_val u#0 u#0 ()))
   in
   let m1' : m (U.raise_t unit) p1 (fun _ -> q1) =
     bind m1 (fun _ -> Ret (U.raise_val u#0 u#0 ()))
   in
   Par p0 q0 m0'
       p1 q1 m1'
       (Ret ())

////////////////////////////////////////////////////////////////////////////////
//The rest of this module shows how this semantic can be packaged up as an
//effect in F*
////////////////////////////////////////////////////////////////////////////////

/// Now for an instantiation of the state with a heap
/// just to demonstrate how that would go

/// Heaps are usually in a universe higher than the values they store
/// Pick it in universe 1
assume val heap : Type u#1
[@@erasable]
assume type r : Type u#1
assume val emp : r
assume val star : r -> r -> r
assume val interp : r -> heap -> prop
/// Assume some monoid of heap assertions
let hm : comm_monoid u#1 u#1 heap = {
  r = r;
  emp = emp;
  star = star;
  interp = interp;
  laws = magic()
}

/// The representation of our effect is a thunked,
/// potentially divergent `m` computation
let comp (a:Type u#a) (p:hm.r) (q:a -> hm.r)
  = unit -> Dv (m a p q)

let ret (a:Type u#a) (x:a) (p: a -> hm.r)
  : comp a (p x) p
  = fun _ -> return x p

let bnd (a:Type u#a) (b:Type u#b) (p:hm.r) (q: a -> hm.r) (r: b -> hm.r)
        (f:comp a p q) (g: (x:a -> comp b (q x) r))
  : comp b p r
  = fun _ -> bind (f()) (fun x -> g x ())

reifiable
reflectable
effect {
   C (a:Type) (pre:hm.r) (q: a -> hm.r)
   with { repr = comp;
          return = ret;
          bind = bnd }
}


////////////////////////////////////////////////////////////////////////////////
// Some technicalities to lift pure and divergent computations to our new effect
////////////////////////////////////////////////////////////////////////////////
assume
val bind_pure_c_ (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre:hm.r)
  (post:b -> hm.r)
  (f:eqtype_as_type unit -> PURE a wp)
  (g:(x:a -> comp b pre post))
 : Pure (comp b
              pre
              post)
        (requires wp (fun _ -> True))
        (ensures fun _ -> True)

polymonadic_bind (PURE, C) |> C = bind_pure_c_

assume
val bind_div_c_ (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre:hm.r)
  (post:b -> hm.r)
  (f:eqtype_as_type unit -> DIV a wp)
  (g:(x:a -> comp b pre post))
 : Pure (comp b
              pre
              post)
        (requires wp (fun _ -> True))
        (ensures fun _ -> True)

polymonadic_bind (DIV, C) |> C = bind_div_c_

////////////////////////////////////////////////////////////////////////////////
// Assuming a simple heap model for this demo
////////////////////////////////////////////////////////////////////////////////
open FStar.Ghost

/// For this demo, we'll also assume that this assertions are affine
///  i.e., it's ok to forget some properties of the heap
assume
val hm_affine (r0 r1:hm.r) (h:heap)
  : Lemma (hm.interp (r0 `hm.star` r1) h ==>
           hm.interp r0 h)

/// Here's a ref type
assume
val ref : Type u#0 -> Type u#0

/// And two atomic heap assertions
assume
val pts_to (r:ref 'a) (x:'a) : hm.r
assume
val pure (p:prop) : hm.r


/// sel: Selected a reference from a heap, when that ref is live
assume
val sel (x:ref 'a) (v:erased 'a) (h:heap{hm.interp (pts_to x v) h})
  : 'a

/// this tells us that sel is frameable
assume
val sel_ok (x:ref 'a) (v:erased 'a) (h:heap) (frame:hm.r)
  : Lemma (hm.interp (pts_to x v `hm.star` frame) h ==>
           (hm_affine (pts_to x v) frame h;
            let v' = sel x v h in
            hm.interp ((pts_to x v `hm.star` pure (reveal v == v')) `hm.star` frame) h))

/// upd: updates a heap at a given reference, when the heap contains it
assume
val upd (x:ref 'a) (v0:erased 'a) (v:'a) (h:heap{hm.interp (pts_to x v0) h})
  : Tot heap

/// and upd is frameable too
assume
val upd_ok (x:ref 'a) (v0:erased 'a) (v:'a) (h:heap) (frame:hm.r)
  : Lemma (hm.interp (pts_to x v0 `hm.star` frame) h ==>
           (hm_affine (pts_to x v0) frame h;
            let h' = upd x v0 v h in
            hm.interp (pts_to x v `hm.star` frame) h'))

assume
val rewrite (#a:Type u#a) (p: a -> hm.r) (x:erased a) (y:a)
    : C unit (p y  `star` pure (reveal x == y)) (fun _ -> p x)

////////////////////////////////////////////////////////////////////////////////

/// Here's a sample action for dereference
let (!) (#v0:erased 'a) (x:ref 'a)
  : C 'a (pts_to x v0) (fun v -> pts_to x v0 `star` pure (reveal v0 == v))
  = C?.reflect (fun _ ->
    let act : action hm 'a =
    {
      pre = pts_to x v0;
      post = (fun v -> pts_to x v0 `star` pure (reveal v0 == v)) ;
      sem = (fun frame h0 ->
        hm_affine (pts_to x v0) frame h0;
        sel_ok x v0 h0 frame;
        (| sel x v0 h0, h0 |))
    } in
    Act act Ret)

/// And a sample action for assignment
let (:=) (#v0:erased 'a) (x:ref 'a) (v:'a)
  : C unit (pts_to x v0) (fun _ -> pts_to x v)
  = C?.reflect (fun _ ->
    let act : action hm unit =
    {
      pre = pts_to x v0;
      post = (fun _ -> pts_to x v);
      sem = (fun frame h0 ->
        hm_affine (pts_to x v0) frame h0;
        upd_ok x v0 v h0 frame;
        (| (), upd x v0 v h0 |))
    } in
    Act act Ret)

let frame_r (#a:Type u#a) (#p:hm.r) (#q: a -> hm.r) (#fr:hm.r)
            (f: unit -> C a p q)
    : C a (p `star` fr) (fun x -> q x `star` fr)
    = let ff : m a p q = (reify (f())) () in
      C?.reflect (fun () -> frame fr ff)

let par_c (#p0:hm.r) (#q0: hm.r)
          (#p1:hm.r) (#q1: hm.r)
          ($f0: unit -> C unit p0 (fun _ -> q0))
          ($f1: unit -> C unit p1 (fun _ -> q1))
    : C unit (p0 `star` p1) (fun _ -> q0 `star` q1)
    = let ff0 : m unit p0 (fun _ -> q0) = reify (f0()) () in
      let ff1 : m unit p1 (fun _ -> q1) = reify (f1()) () in
      C?.reflect (fun () -> par ff0 ff1)

let incr (#v0:erased int) (x:ref int)
  : C unit (pts_to x v0) (fun u -> pts_to x (v0 + 1))
  = let v = !x in
    frame_r (fun _ -> x := v + 1);
    rewrite (fun y -> pts_to x (y + 1)) v0 v

let par_incr (#v0 #v1:erased int)
             (x0 x1: ref int)
  : C unit (pts_to x0 v0 `star` pts_to x1 v1)
           (fun _ -> pts_to x0 (v0 + 1) `star` pts_to x1 (v1 + 1))
  = par_c (fun _ -> incr x0)
          (fun _ -> incr x1)
