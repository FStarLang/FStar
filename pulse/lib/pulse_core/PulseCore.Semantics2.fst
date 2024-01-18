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
module PulseCore.Semantics2
module U = FStar.Universe
open FStar.Preorder

assume
val nmst (#s:Type u#s)
         (rel:FStar.Preorder.preorder s)
         (a:Type u#a)
         (pre:s -> prop)
         (post:s -> a -> s -> prop)
: Type u#0

assume
val return (#s:Type u#s)
           (#rel:preorder s)
           (#a:Type u#a)
           (x:a)
: nmst rel a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)
           

let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop

assume
val bind
      (#a:Type)
      (#b:Type)
      (#s:Type u#2)
      (#rel:preorder s)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:nmst rel a req_f ens_f)
      (g:(x:a -> Dv (nmst rel b (req_g x) (ens_g x))))
: nmst rel b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
    

assume
val weaken
      (#a:Type)
      (#s:Type u#2)
      (#rel:preorder s)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:nmst rel a req_f ens_f)
    : Pure (nmst rel a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)

assume
val flip (#s:Type u#s) (#rel:preorder s) (_:unit)
  : nmst rel bool (fun _ -> True) (fun s0 x s1 -> s0 == s1)

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
 * A state typeclass:
 *  - [s] is the type of states
 *  - [pred] is the type of state assertions
 *  - [emp] is the empty state assertion
 *  - [star] is the separating conjunction of state assertions
 *  - [interp p s] is the interpretation of a state assertion [p] in a state [s]
 *  - [evolves] is a preorder on states, constraining how it evolves
 *  - [laws] state that {pred, emp, star} are a commutative monoid
 *)
noeq
type state : Type u#3 = {
  s:Type u#2;
  pred:Type u#2;
  emp: pred;
  star: pred -> pred -> pred;
  interp: pred -> s -> prop;
  evolves: FStar.Preorder.preorder s;
  laws: squash (associative star /\ commutative star /\ is_unit emp star)
}

(** [post a c] is a postcondition on [a]-typed result *)
let post (s:state) a = a -> s.pred

(** [action c s]: atomic actions are, intuitively, single steps of
 *  computations interpreted as a [s -> a & s].
 *  However, we augment them with two features:
 *   1. they have pre-condition [pre] and post-condition [post]
 *   2. their type guarantees that they are frameable
 *  Thanks to Matt Parkinson for suggesting to set up atomic actions
 *  this way.
 *  Also see: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/views.pdf
 *)

let nmst_p (st:state) (a:Type u#a) (pre:st.pred) (post:post st a) =
  nmst st.evolves a (st.interp pre) (fun _ x s1 -> st.interp (post x) s1)

noeq
type action (st:state) (a:Type u#2) = {
  pre: st.pred;
  post: post st a;
  step: (
    frame:st.pred ->
    nmst_p st a (st.star pre frame) (fun x -> st.star (post x) frame)
  )
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
type m (#st:state) : (a:Type u#a) -> st.pred -> post st a -> Type =
  | Ret:
      #a:Type u#a ->
      #post:(a -> st.pred) ->
      x:a ->
      m a (post x) post
  | Act:
      #a:Type u#a ->
      #post:(a -> st.pred) ->
      #b:Type ->
      f:action st b ->
      k:(x:b -> Dv (m a (f.post x) post)) ->
      m a f.pre post
  | Par:
      #pre0:_ ->
      #post0:_ ->
      m0: m (U.raise_t unit) pre0 (fun _ -> post0) ->
      #pre1:_ ->
      #post1:_ ->
      m1: m (U.raise_t unit) pre1 (fun _ -> post1) ->
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
 * [step_result s c a q frame]:
 *    The result of evaluating a single step of a program
 *    - s, c: The state and its monoid
 *    - a : the result type
 *    - q : the postcondition to be satisfied after fully reducing the programs
 *    - frame: a framed assertion to carry through the proof
 *)
noeq
type step_result (#st:state) a (q:post st a) (frame:st.pred) =
  | Step: next:_ -> //precondition of the reduct
          m a next q -> //the reduct
          // state:st.s {st.interp (p `st.star` frame) state} -> //the next state, satisfying the precondition of the reduct
          step_result a q frame

open FStar.Preorder

(**
 * [step i f frame state]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *
 *)
let rec step 
    (#st:state)
    (#p:st.pred)
    (#a:Type)
    (#q:post st a)
    (f:m a p q)
    (frame:st.pred)
: Tot (nmst_p st
        (step_result a q frame)
        (p `st.star` frame)
        (fun x -> (Step?.next x `st.star` frame)))
      (decreases f)
= match f with
  | Ret x -> 
    let n
     : nmst st.evolves 
            (step_result a q frame)
            (fun _ -> True)
            (fun s0 v s1 -> Step (q x) (Ret x) == v /\ s0 == s1) 
     = return (Step (q x) (Ret x))
    in
    weaken n
  | Act f k ->
    let k (x:_) 
    : Dv (nmst_p st (step_result a q frame)
                    (f.post x `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let n : m a (f.post x) q = k x in
      weaken (return (Step _ n))
    in
    let n = bind (f.step frame) k in
    weaken n
  | Par #_ #pre0 #post0 (Ret x0) #pre1 #post1 (Ret x1) #a #post k ->
    weaken <| return <| Step _ k
  | Par #_ #pre0 #post0 m0 #pre1 #post1 m1 #a #post k ->
    let go_left
    : nmst_p st
        (step_result a q frame)
        (p `st.star` frame)
        (fun x -> (Step?.next x `st.star` frame))
    = let k (x:step_result (U.raise_t unit) (fun _ -> post0) (pre1 `st.star` frame))
       : Dv (nmst_p st 
              (step_result a q frame)
              (Step?.next x `st.star` (pre1 `st.star` frame))   
              (fun y -> Step?.next y `st.star` frame))
       = let Step pre0' m0' = x in
         weaken <| return <| Step _ <| Par m0' m1 k
      in
      weaken <| bind (step m0 (pre1 `st.star` frame)) k
    in
    let go_right
    : nmst_p st
          (step_result a q frame)
          (p `st.star` frame)
          (fun x -> (Step?.next x `st.star` frame))
    = let k (x:step_result (U.raise_t unit)
               (fun _ -> post1) (pre0 `st.star` frame))
       : Dv (nmst_p st 
              (step_result a q frame)
              (Step?.next x `st.star` (pre0 `st.star` frame))   
              (fun y -> Step?.next y `st.star` frame))
       = let Step pre1' m1' = x in
         weaken <| return <| Step _ <| Par m0 m1' k
      in
      weaken <| bind (step m1 (pre0 `st.star` frame)) k
    in
    weaken <| bind (flip()) (fun b -> if b then go_left else go_right)

let rec run (#st:state) #pre #a #post (f:m a pre post)
  : Dv (nmst_p st a pre post)
  = match f with
    | Ret x -> 
      weaken <| return x
    | _ ->
      let k (s:step_result a post st.emp)
        : Dv (nmst_p st a (Step?.next s) post)
        = let Step _ f = s in
          run f
      in
      weaken <| bind (step f st.emp) k
 
(*)
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