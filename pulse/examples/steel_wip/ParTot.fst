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
module ParTot

(**
 * This module provides a semantic model for a combined effect of
 * state and parallel composition of atomic actions.
 *
 * It also builds a generic separation-logic-style program logic
 * for this effect, in a total correctness setting.
 *
 *)

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quanitifers was more convenient for the done here.

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
type comm_monoid (s:Type u#1) : Type u#1 = {
  r:Type u#0;
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
 *  A free monad for state and parallel composition
 *  with generic actions. The main idea:
 *
 *  [m] is indexed by
 *  pre- and post-conditions so that we can do proofs
 *  intrinsically.
 *
 *  Additionally, we index programs by a measure of the number of
 *  of the actions they contain so as to enable a termination proof
 *  in the semantics
 *
 *)
noeq 
type m (s:Type u#1) (c:comm_monoid s) : (a:Type0) -> c.r -> post a c -> nat -> Type =
  | Ret : #a:Type0 -> #post:(a -> c.r) -> x:a -> m s c a (post x) post 0
  | Act : #a:Type0 -> #post:(a -> c.r) -> #b:Type0 -> f:action c b -> #n:_ -> k:(x:b -> m s c a (f.post x) post n) -> m s c a f.pre post (n + 1)
  | Par : pre0:_ -> #a0:_ -> post0:_ -> n0:_ -> m0: m s c a0 pre0 post0 n0 ->
          pre1:_ -> #a1:_ -> post1:_ -> n1:_ -> m1: m s c a1 pre1 post1 n1 ->
          #a:_ -> #post:_ -> n:_ -> k:(x0:a0 -> x1:a1 -> (m s c a (c.star (post0 x0) (post1 x1)) post) n) ->
          m s c a (c.star pre0 pre1) post (n0 + n1 + n + 1)


/// We assume a stream of booleans for the semantics given below
/// to resolve the nondeterminism of Par
assume
val bools : nat -> bool

/// The semantics comes is in two levels:
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
type step_result s (c:comm_monoid s) a (q:post a c) (frame:c.r) =
  | Step: p:_ -> //precondition of the reduct
          #n:_ -> //action count of the reduct
          reduct:m s c a p q n -> //the reduct
          state:s {c.interp (p `c.star` frame) state} -> //the next state, satisfying the precondition of the reduct
          nat -> //position in the stream of booleans (less important)
          step_result s c a q frame

(**
 * [step i f frame state]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *
 *)
let rec step #s #c (i:nat) #pre #a #post #n (f:m s c a pre post n) (frame:c.r) (state:s)
  : Pure (step_result s c a post frame)
         (requires
           c.interp (pre `c.star` frame) state)
         (ensures fun sr ->
           Ret? sr.reduct \/ sr.n < n)
         (decreases n)
  = match f with
    | Ret x ->
        //Nothing to do, just return
        Step (post x) (Ret x) state i

    | Act act1 k ->
        //Evaluate the action and return the continuation as the reduct
        let (| b, state' |) = act1.sem frame state in
        Step (act1.post b) (k b) state' i

    | Par pre0 post0 n0 (Ret x0)
          pre1 post1 n1 m1
          n k ->
        let Step pre1' #n1' m1' state' j =
            step (i + 1) m1 (pre0 `c.star` frame) state in
        begin
        match m1' with 
        | Ret x1 ->
          Step (post0 x0 `c.star` post1 x1) (k x0 x1) state' j

        | _ -> 
          Step (pre0 `c.star` pre1') (Par pre0 post0 n0 (Ret x0) pre1' post1 n1' m1' n k) state' j
        end

    | Par pre0 post0 n0 m0 
          pre1 post1 n1 (Ret x1)
          n k ->
        let Step pre0' #n0' m0' state' j =
            step (i + 1) m0 (pre1 `c.star` frame) state in
        begin
        match m0' with 
        | Ret x0 ->
          Step (post0 x0 `c.star` post1 x1) (k x0 x1) state' j

        | _ -> 
          Step (pre0' `c.star` pre1) (Par pre0' post0 n0' m0' pre1 post1 n1 (Ret x1) n k) state' j
        end

    | Par pre0 post0 n0 m0
          pre1 post1 n1 m1
          n k ->
        //Otherwise, sample a boolean and choose to go left or right to pick
        //the next command to reduce
        //The two sides are symmetric
        if bools i
        then let Step pre0' #n0' m0' state' j =
                 //Notice that, inductively, we instantiate the frame extending
                 //it to include the precondition of the other side of the par
                 step (i + 1) m0 (pre1 `c.star` frame) state in
             Step (pre0' `c.star` pre1) (Par pre0' post0 n0' m0' pre1 post1 n1 m1 n k) state' j
        else let Step pre1' #n1' m1' state' j =
                 step (i + 1) m1 (pre0 `c.star` frame) state in
             Step (pre0 `c.star` pre1') (Par pre0 post0 n0 m0 pre1' post1 n1' m1' n k) state' j

(**
 * [run i f state]: Top-level driver that repeatedly invokes [step]
 *
 * The type of [run] is the main theorem. It states that it is sound
 * to interpret the indices of `m` as a Hoare triple in a
 * total-correctness semantics
 *
 *)
let rec run #s #c (i:nat) #pre #a #post #n (f:m s c a pre post n) (state:s)
  : Pure (a & s)
    (requires
      c.interp pre state)
    (ensures fun (x, state') ->
      c.interp (post x) state')
    (decreases n)
  = match f with
    | Ret x -> x, state
    
    | _ ->
      let Step pre' f' state' j = step i f c.emp state in
      run j f' state'
