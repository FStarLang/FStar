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
module OPLSS2021.ParTot

(** [action c s]: atomic actions are, intuitively, single steps of
 *  computations interpreted as a [s -> a & s].
 *)
let action s (a:Type) = s -> a & s

(** [m s a n] :
 *  A free monad for state and parallel composition
 *  with generic actions. 
 
 *  Additionally, we index programs by a measure of the number of
 *  of the actions they contain so as to enable a termination proof
 *  in the semantics
 *
 *  Think of this as an infinitely branching computation tree
 *    -Ret nodes are the leaves of the tree
 *    -Act nodes have an action and the "children" of the node
 *         are in the continuation k, one child for each element of the
 *         action's result type b
 *    -Par nodes make this a kind of forest of infinitely branching trees
 *)
noeq 
type m (s:Type) : Type -> nat -> Type =
  | Ret : #a:_ -> x:a -> m s a 0
  | Act : #a:_ -> #b:_ -> f:action s b -> #n:_ -> k:(x:b -> m s a n) -> m s a (n + 1)
  | Par : #a:_ -> #a0:_ -> n0:_ -> m0: m s a0 n0 ->
          #a1:_ -> n1:_ -> m1: m s a1 n1 ->
          n:_ -> k: m s a n ->
          m s a (n0 + n1 + n + 1)

/// A stream of booleans for the semantics given below
/// to resolve the nondeterminism of Par
let tape = nat -> bool

/// The semantics comes is in two levels:
///
///   1. A single-step relation [step] which selects an atomic action to
///      execute in the tree of threads
///
///   2. A top-level driver [run] which repeatedly invokes [step]
///      until it returns with a result and final state.

(**
 * [step_result s a]:
 *    The result of evaluating a single step of a program
 *)
noeq
type step_result s a =
  | Step: n:_ -> //action count of the reduct
          reduct:m s a n  -> //the reduct
          s ->
          nat -> //position in the stream of booleans (less important)
          step_result s a

(**
 * [step i f frame state]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *
 *)
let rec step #s #a (i:nat) #n (f:m s a n) (state:s) (bools:tape)
  : Pure (step_result s a)
         (requires
           True)
         (ensures fun sr ->
           Ret? sr.reduct \/ sr.n < n)
         (decreases n)
  = match f with
    | Ret x ->
        //Nothing to do, just return
        Step _ (Ret x) state i

    | Act act1 k ->
        //Evaluate the action and return the continuation as the reduct
        let ( b, state' ) = act1 state in
        Step _ (k b) state' i

    | Par n0 (Ret x0)
          n1 m1
          n k ->
        let Step n1' m1' state' j =
            step (i + 1) m1 state bools
        in
        begin
        match m1' with 
        | Ret x1 ->
          Step _ k state' j

        | _ -> 
          Step _ (Par n0 (Ret x0) n1' m1' n k) state' j
        end

    | Par n0 m0 
          n1 (Ret x1)
          n k ->
        let Step n0' m0' state' j =
            step (i + 1) m0 state bools in
        begin
        match m0' with 
        | Ret x0 ->
          Step _ k state' j

        | _ -> 
          Step _ (Par n0' m0' n1 (Ret x1) n k) state' j
        end

    | Par n0 m0
          n1 m1
          n k ->
        //Otherwise, sample a boolean and choose to go left or right to pick
        //the next command to reduce
        //The two sides are symmetric
        if bools i
        then let Step n0' m0' state' j = 
                 step (i + 1) m0 state bools in
             Step _ (Par n0' m0' n1 m1 n k) state' j
        else let Step n1' m1' state' j =
                 step (i + 1) m1 state bools in
             Step _ (Par n0 m0 n1' m1' n k) state' j

(**
 * [run i f state]: Top-level driver that repeatedly invokes [step]
 *
 * The type of [run] interprets `f` as a state-passing, 
 * tape-sampling function is the main theorem. 
 *
 *)
let rec run #s #a #n (f:m s a n) (state:s) (bools:tape) (pos:nat)
  : (a & s)
  = match f with
    | Ret x -> x, state
    
    | _ ->
      let Step _ f' state' pos' = step pos f state bools in
      run f' state' bools pos'

