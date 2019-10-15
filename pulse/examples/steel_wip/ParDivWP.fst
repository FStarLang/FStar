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
module ParDivWP

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

let rs (#s:Type) (#c:comm_monoid s) (pre:c.r) = state:s{c.interp pre state}
let wp_post (#s:Type) (#c:comm_monoid s) (a:Type) (post:post a c) = (x:a -> rs (post x) -> prop)
let wp_pre (#s:Type) (#c:comm_monoid s) (pre:c.r) = rs pre -> prop
let wp (#s:Type) (#c:comm_monoid s) (pre:c.r) (a:Type) (post:post a c) = wp_post a post -> wp_pre pre
let triv_wp (#s:Type) (#c:comm_monoid s) 
            (pre:c.r)
            (a:Type) 
            (post:post a c)
  : wp pre a post
  = fun (k:wp_post a post) (s0:rs pre) -> forall (x:a) (s1:rs (post x)). k x s1
let return_wp (#s:Type) (#c:comm_monoid s) (#a:Type) (x:a) (post: post a c)
  : wp (post x) a post
  = fun k s0 -> k x s0 
let bind_wp (#s:Type) (#c:comm_monoid s)
            (#pre_a:c.r) (#a:Type) (#post_a:post a c)
            (#b:Type) (#post_b:post b c)
            (f:wp pre_a a post_a)
            (g: (x:a -> wp (post_a x) b post_b))
  : wp pre_a b post_b
  = fun k -> f (fun x -> g x k)
 
let bind_action #s (#c:comm_monoid s) #a #b 
                (f:action c b)
                (#post_g:post a c)
                (wp_g:(x:b -> wp (f.post x) a post_g))
   : wp f.pre a post_g
   = fun k s0 -> 
       let (| x, s1 |) = f.sem c.emp s0 in
       wp_g x k s1

let wp_par #s (#c:comm_monoid s) (#pre: c.r)
             #a0 (pre0:_) (post0: post a0 c) (wp0: wp pre0 a0 post0)
             #a1 (pre1:_) (post1: post a1 c) (wp1: wp pre1 a1 post1)
   : wp (pre0 `c.star` pre1) (a0 & a1) (fun (x0, x1) -> post0 x0 `c.star` post1 x1)
   = fun k s -> 
      let s0, s1, frame = split s pre0 pre1 in
      as_requires wp0 s0 /\
      as_requires wp1 s1 /\      
      (forall x0 s0' x1 s1'. 
        joinable s0' s1' frame /\
        as_ensures wp0 s0 x0 s0' /\
        as_ensures wp1 s1 x1 s1' ==>
        k (x0, x1) (join s0' s1' frame))

let bind_par #s (#c:comm_monoid s) (#pre: c.r)
             #a0 (post0: post a0 c)
             #a1 (post1: post a1 c)   
             #a  #post (wp_a:(x0:a0 -> x1:a1 -> wp (post0 x0 `c.star` post1 x1) a post))
   : wp pre a post
   = (fun k s0 -> forall (x0:a0) (x1:a1) (s1:rs (c.star (post0 x0) (post1 x1))). wp_a x0 x1 k s1)
             

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
type m (s:Type u#s) (c:comm_monoid s) : (a:Type u#a) -> pre:c.r -> post:post a c -> wp pre a post -> Type =
  | Ret : #a:_ 
        -> #post:(a -> c.r) 
        -> x:a
        -> m s c a (post x) post (return_wp x post)
        
  | Act : #a:_ 
        -> #b:_
        -> f:action c b
        -> #post_g:post a c 
        -> #wp_g:(x:b -> wp (f.post x) a post_g)
        -> g:(x:b -> Dv (m s c a (f.post x) post_g (wp_g x)))
        -> m s c a f.pre post_g (bind_action f wp_g)
        
  | Par : pre0:_ -> #a0:_ -> post0:_ -> m0: m s c a0 pre0 post0 (triv_wp pre0 a0 post0) ->
          pre1:_ -> #a1:_ -> post1:_ -> m1: m s c a1 pre1 post1 (triv_wp pre1 a1 post1) ->
          #a:_ -> #post:_ -> wp_k:(x0:a0 -> x1:a1 -> wp (post0 x0 `c.star` post1 x1) a post)
               -> k:(x0:a0 -> x1:a1 -> Dv (m s c a (c.star (post0 x0) (post1 x1)) post (wp_k x0 x1))) ->
          m s c a (c.star pre0 pre1) post (bind_par post0 post1 wp_k)


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


let frame_post #s (#c:comm_monoid s) #a (post:post a c) (frame:c.r) = fun x -> post x `c.star` frame

///
/// [step_result s c a q frame]:
///   The result of evaluating a single step of a program
///   - s, c: The state and its monoid
///   - a : the result type
///   - q : the postcondition to be satisfied after fully reducing the programs
///   - frame: a framed assertion to carry through the proof
noeq
type step_result s (c:comm_monoid s) a (q:post a c) (frame:c.r) (k:wp_post a q) =
  | Step: p:_ -> //precondition of the reduct
          wp:wp p a q ->
          m s c a p q wp -> //the reduct
          state:rs (p `c.star` frame) { 
            (assume (c.interp p state);
             wp k state)
          } ->
          //the next state, satisfying the precondition of the reduct
          nat -> //position in the stream of booleans (less important)
          step_result s c a q frame k

let triv_post #s (#c:comm_monoid s) (a:Type) (post:post a c) : wp_post a post = fun _ _ -> True

/// [step i f frame state]: Reduces a single step of [f], while framing
/// the assertion [frame]
let rec step #s #c (i:nat) #pre #a #post 
             (frame:c.r)
             (#wp:wp pre a post)
             (f:m s c a pre post wp)
             (k:wp_post a post)
             (state:s)
  : Div (step_result s c a post frame k)
        (requires
          c.interp (pre `c.star` frame) state /\
          c.interp pre state /\
          wp k state)
        (ensures fun _ -> True)
  = match f with
    | Ret x ->
        //Nothing to do, just return
        Step (post x) wp (Ret x) state i
    
    | Act act1 #post_g #wp_g g ->
        //Evaluate the action and return the continuation as the reduct
        let (| b, state' |) = act1.sem frame state in
        assert (c.interp (act1.post b `c.star` frame) state');
        assert (wp == bind_action act1 wp_g);
        assert (bind_action act1 wp_g k state);
        assume (c.interp (act1.post b) state');
        let (| emp_b, emp_state' |) = act1.sem c.emp state in
        assume (b == emp_b);
        assume (emp_state' == state');
        assert (wp_g b k state');
        Step (act1.post b) (wp_g b) (g b) state' i
    
    | Par pre0 post0 (Ret x0)
          pre1 post1 (Ret x1)
          wp_k k ->
        assert (wp == bind_par post0 post1 wp_k);
        //If both sides of a `Par` have returned
        //then step to the continuation
        Step (post0 x0 `c.star` post1 x1)
             (wp_k x0 x1) 
             (k x0 x1) 
             state
             i

    
    | Par pre0 #a0 post0 m0
          pre1 #a1 post1 m1
          #a #post wp_kont kont ->
        assert (wp == bind_par post0 post1 wp_kont);      
        assert (bind_par #_ #_ #(c.star pre0 pre1) post0 post1 wp_kont k state );
        assert (triv_wp #_ #_ (pre0 `c.star` (pre1 `c.star` frame)) a0 post0 (triv_post a0 post0) state);

        //Otherwise, sample a boolean and choose to go left or right to pick
        //the next command to reduce
        //The two sides are symmetric
        if bools i
        then let Step pre0' wp0' m0' state' j =
                 //Notice that, inductively, we instantiate the frame extending
                 //it to include the precondition of the other side of the par
                 assert (c.interp (pre0 `c.star` (pre1 `c.star` frame)) state);
                 assume (c.interp pre0 state);
                 step (i + 1) (pre1 `c.star` frame) m0 (triv_post a0 post0) state in
             Step (pre0' `c.star` pre1) 
                  (bind_par post0 post1 wp_kont)
                  (Par pre0' post0 m0' pre1 post1 m1 wp_kont kont)
                  state'
                  j
        else admit()
        
        let Step pre1' m1' state' j =
                 step (i + 1) m1 (pre0 `c.star` frame) state in
             Step (pre0 `c.star` pre1') (Par pre0 post0 m0 pre1' post1 m1' k) state' j

// (**
//  * [run i f state]: Top-level driver that repeatedly invokes [step]
//  *
//  * The type of [run] is the main theorem. It states that it is sound
//  * to interpret the indices of `m` as a Hoare triple in a
//  * partial-correctness semantics
//  *
//  *)
// let rec run #s #c (i:nat) #pre #a #post (f:m s c a pre post) (state:s)
//   : Div (a & s)
//     (requires
//       c.interp pre state)
//     (ensures fun (x, state') ->
//       c.interp (post x) state')
//   = match f with
//     | Ret x -> x, state
//     | _ ->
//       let Step pre' f' state' j = step i f c.emp state in
//       run j f' state'

// ////////////////////////////////////////////////////////////////////////////////
// //The rest of this module shows how this semantic can be packaged up as an
// //effect in F*
// ////////////////////////////////////////////////////////////////////////////////

// (** [eff a pre post] : The representation-type for a layered effect
//  *
//  *   - Note, we'll probably have to add a thunk to make it work with
//  *     the current implementation but that's a detail
//  *)
// let eff #s (#c:comm_monoid s) a (pre:c.r) (post: a -> c.r) =
//   m s c a pre post

// /// eff is a monad: we give a return and bind for it, though we don't
// /// prove the monad laws


// (** [return]: easy, just use Ret *)
// let return #s (#c:comm_monoid s) #a (x:a) (post:a -> c.r)
//   : eff a (post x) post
//   = Ret x

// (**
//  * [bind]: sequential composition works by pushing `g` into the continuation
//  * at each node, finally applying it at the terminal `Ret`
//  *)
// let rec bind #s (#c:comm_monoid s) #a #b (#p:c.r) (#q:a -> c.r) (#r:b -> c.r)
//              (f:eff a p q)
//              (g: (x:a -> eff b (q x) r))
//   : Dv (eff b p r)
//   = match f with
//     | Ret x -> g x
//     | Act act k ->
//       Act act (fun x -> bind (k x) g)
//     | Par pre0 post0 l
//           pre1 post1 r
//           k ->
//       Par pre0 post0 l pre1 post1 r (fun x0 x1 -> bind (k x0 x1) g)

// (**
//  * [par]: Parallel composition
//  * Works by just using the `Par` node and `Ret` as its continuation
//  **)
// let par #s (#c:comm_monoid s)
//         #a0 #p0 #q0 (m0:eff a0 p0 q0)
//         #a1 #p1 #q1 (m1:eff a1 p1 q1)
//  : eff (a0 & a1) (p0 `c.star` p1) (fun (x0, x1) -> q0 x0 `c.star` q1 x1)
//  = Par p0 q0 m0
//        p1 q1 m1
//        #_ #(fun (x0, x1) -> c.star (q0 x0) (q1 x1)) (fun x0 x1 -> Ret (x0, x1))


// /// Now for an instantiation of the state with a heap
// /// just to demonstrate how that would go

// /// Heaps are usually in a universe higher than the values they store
// /// Pick it in universe 1
// assume val heap : Type u#1

// /// Assume some monoid of heap assertions
// assume val hm : comm_monoid heap

// /// For this demo, we'll also assume that this assertions are affine
// ///  i.e., it's ok to forget some properties of the heap
// assume val hm_affine (r0 r1:hm.r) (h:heap)
//   : Lemma (hm.interp (r0 `hm.star` r1) h ==>
//            hm.interp r0 h)

// /// Here's a ref type
// assume val ref : Type u#0 -> Type u#0

// /// And two atomic heap assertions
// assume val ptr_live (r:ref 'a) : hm.r
// assume val pts_to (r:ref 'a) (x:'a) : hm.r

// /// sel: Selected a reference from a heap, when that ref is live
// assume val sel (x:ref 'a) (h:heap{hm.interp (ptr_live x) h})
//   : Tot 'a
// /// this tells us that sel is frameable
// assume val sel_ok (x:ref 'a) (h:heap) (frame:hm.r)
//   : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
//            (hm_affine (ptr_live x) frame h;
//             let v = sel x h in
//             hm.interp (pts_to x v `hm.star` frame) h))


// /// upd: updates a heap at a given reference, when the heap contains it
// assume val upd (x:ref 'a) (v:'a) (h:heap{hm.interp (ptr_live x) h})
//   : Tot heap
// /// and upd is frameable too
// assume val upd_ok (x:ref 'a) (v:'a) (h:heap) (frame:hm.r)
//   : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
//            (hm_affine (ptr_live x) frame h;
//             let h' = upd x v h in
//             hm.interp (pts_to x v `hm.star` frame) h'))

// /// Here's a sample action for dereference
// let (!) (x:ref 'a)
//   : eff 'a (ptr_live x) (fun v -> pts_to x v)
//   = let act : action hm 'a =
//     {
//       pre = ptr_live x;
//       post = pts_to x;
//       sem = (fun frame h0 ->
//         hm_affine (ptr_live x) frame h0;
//         sel_ok x h0 frame;
//         (| sel x h0, h0 |))
//     } in
//     Act act Ret

// /// And a sample action for assignment
// let (:=) (x:ref 'a) (v:'a)
//   : eff unit (ptr_live x) (fun _ -> pts_to x v)
//   = let act : action hm unit =
//     {
//       pre = ptr_live x;
//       post = (fun _ -> pts_to x v);
//       sem = (fun frame h0 ->
//         hm_affine (ptr_live x) frame h0;
//         upd_ok x v h0 frame;
//         (| (), upd x v h0 |))
//     } in
//     Act act Ret
