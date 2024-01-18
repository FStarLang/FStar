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
module PulseCore.Semantics
module U = FStar.Universe

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
type m (#s:Type u#s) (#c:comm_monoid u#s s) 
  : (a:Type u#a) -> c.r -> post a c -> Type = 
  | Ret : #a:Type u#a -> #post:(a -> c.r) -> x:a -> m a (post x) post
  | Act : #a:Type u#a -> #post:(a -> c.r) -> #b:Type u#s -> f:action c b -> k:(x:b -> Dv (m a (f.post x) post)) -> m a f.pre post
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

module U = FStar.Universe
// let raise_action 
//     (#s:Type u#s)
//     (#c:comm_monoid s)
//     (#t:Type u#a)
//     (a:action u#s u#a c t)
//  : action c (U.raise_t u#a u#s t)
//  = {
//       pre = a.pre;
//       post = (fun (x:U.raise_t u#a u#s t) -> a.post (U.downgrade_val x));
//       sem = (fun frame s0 -> 
//                 let (| x, s1 |) = a.sem frame s0 in
//                 (| U.raise_val u#a u#s x, s1 |))
//    }

let act
    (#s:Type u#s)
    (#c:comm_monoid s)
    (#t:Type u#s)
    (a:action c t)
: m t a.pre a.post
= Act a Ret

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