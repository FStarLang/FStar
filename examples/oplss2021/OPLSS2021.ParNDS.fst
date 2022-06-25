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
module OPLSS2021.ParNDS
open OPLSS2021.NDS

(** [action c s]: atomic actions are, intuitively, single steps of
 *  computations interpreted as a [s -> a & s].
 *  However, we augment them with two features:
 *   1. they have pre-condition [pre] and post-condition [post]
 *   2. their type guarantees that they are frameable
 *)
let action s (a:Type) = s -> a & s

(** [m s a n] :
 *  A free monad for state and parallel composition
 *  with generic actions. 
 
 *  Additionally, we index programs by a measure of the number of
 *  of the actions they contain so as to enable a termination proof
 *  in the semantics
 *
 *)
noeq 
type m (s:Type0) : Type -> nat -> Type =
  | Ret : #a:_ -> x:a -> m s a 0
  | Act : #a:_ -> #b:_ -> f:action s b -> #n:_ -> k:(x:b -> m s a n) -> m s a (n + 1)
  | Par : #a:_ -> #a0:_ -> n0:_ -> m0: m s a0 n0 ->
          #a1:_ -> n1:_ -> m1: m s a1 n1 ->
          n:_ -> k: m s a n ->
          m s a (n0 + n1 + n + 1)


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
type step_result s a =
  | Step: n:_ -> //action count of the reduct
          reduct:m s a n  -> //the reduct
          step_result s a

(**
 * [step i f frame state]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *
 *)
let rec step (#s:Type0) #a #n (f:m s a n)
  : NDS (sr:step_result s a { Ret? sr.reduct \/ sr.n < n } ) s
        (decreases n)
  = match f with
    | Ret x ->
        //Nothing to do, just return
        Step _ (Ret x)

    | Act act1 k ->
        //Evaluate the action and return the continuation as the reduct
        let s0 = get () in
        let ( b, s1 ) = act1 s0 in
        put s1;
        Step _ (k b)

    | Par n0 (Ret x0)
          n1 m1
          n k ->
        let Step n1' m1' = step m1 in
        begin
        match m1' with 
        | Ret x1 ->
          Step _ k

        | _ -> 
          Step _ (Par n0 (Ret x0) n1' m1' n k)
        end

    | Par n0 m0 
          n1 (Ret x1)
          n k ->
        let Step n0' m0' =
            step m0 in
        begin
        match m0' with 
        | Ret x0 ->
          Step _ k

        | _ -> 
          Step _ (Par n0' m0' n1 (Ret x1) n k)
        end

    | Par n0 m0
          n1 m1
          n k ->
        //Otherwise, sample a boolean and choose to go left or right to pick
        //the next command to reduce
        //The two sides are symmetric
        if sample ()
        then let Step _ m0' = step m0 in
             Step _ (Par _ m0' _ m1 _ k)
        else let Step _ m1' = step m1 in
             Step _ (Par _ m0 _ m1' _ k)

(**
//  * [run i f state]: Top-level driver that repeatedly invokes [step]
//  *
//  * The type of [run] interprets `f` as a state-passing, 
//  * tape-sampling function is the main theorem. 
//  *
//  *)
let rec run #s #a #n (f:m s a n)
  : NDS a s
  = match f with
    | Ret x -> x
    
    | _ ->
      let Step _ f' = step f in
      run f'

