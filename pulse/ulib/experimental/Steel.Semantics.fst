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
module Steel.Semantics
module T = FStar.Tactics

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
#push-options "--using_facts_from '+Prims +FStar.Pervasives +Steel.Semantics' --max_fuel 0 --max_ifuel 2 --initial_ifuel 2"

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quanitifers was more convenient for the proof done here.

let symmetry #a (equals: a -> a -> prop) =
  forall x y. {:pattern (x `equals` y)}
    x `equals` y ==> y `equals` x

let transitive #a (equals:a -> a -> prop) =
  forall x y z. x `equals` y /\ y `equals` z ==> x `equals` z

let associative #a (equals: a -> a -> prop) (f: a -> a -> a)=
  forall x y z.{:pattern f x (f y z) \/ f (f x y) z}
    f x (f y z) `equals` f (f x y) z

let commutative #a (equals: a -> a -> prop) (f: a -> a -> a) =
  forall x y.{:pattern f x y}
    f x y `equals` f y x

let is_unit #a (x:a) (equals: a -> a -> prop) (f:a -> a -> a) =
  forall y. {:pattern f x y \/ f y x}
    f x y `equals` y /\
    f y x `equals` y

let equals_ext #a (equals:a -> a -> prop) (f:a -> a -> a) =
  forall x1 x2 y. x1 `equals` x2 ==> f x1 y `equals` f x2 y

let fp_heap_0 (#heap:Type) (#hprop:Type)
              (interp:hprop -> heap -> prop)
              (pre:hprop)
    = h:heap{interp pre h}

let depends_only_on_0 (#heap:Type) (#hprop:Type)
                      (interp:hprop -> heap -> prop)
                      (disjoint: heap -> heap -> prop)
                      (join: (h0:heap -> h1:heap{disjoint h0 h1} -> heap))
                      (q:heap -> prop) (fp: hprop) =
  (forall h0 h1. q h0 /\ disjoint h0 h1 ==> q (join h0 h1)) /\
  (forall (h0:fp_heap_0 interp fp) (h1:heap{disjoint h0 h1}). q h0 <==> q (join h0 h1))

let fp_prop_0 (#heap:Type) (#hprop:Type)
              (interp:hprop -> heap -> prop)
              (disjoint: heap -> heap -> prop)
              (join: (h0:heap -> h1:heap{disjoint h0 h1} -> heap))
              (fp:hprop) =
  p:(heap -> prop){p `(depends_only_on_0 interp disjoint join)` fp}

noeq
type st0 = {
  heap:Type;
  hprop:Type;

  disjoint: heap -> heap -> prop;
  join: h0:heap -> h1:heap{disjoint h0 h1} -> heap;

  interp: hprop -> heap -> prop;

  emp:hprop;
  star: hprop -> hprop -> hprop;
  refine: (fp:hprop -> fp_prop_0 interp disjoint join fp -> hprop);

  equals: hprop -> hprop -> prop;
}

/// disjointness is symmetric
let disjoint_sym (st:st0)
  = forall h0 h1. st.disjoint h0 h1 <==> st.disjoint h1 h0

let disjoint_join (st:st0)
  = forall m0 m1 m2.
       st.disjoint m1 m2 /\
       st.disjoint m0 (st.join m1 m2) ==>
       st.disjoint m0 m1 /\
       st.disjoint m0 m2 /\
       st.disjoint (st.join m0 m1) m2 /\
       st.disjoint (st.join m0 m2) m1

let join_commutative (st:st0 { disjoint_sym st })
  = forall m0 m1.
      st.disjoint m0 m1 ==>
      st.join m0 m1 == st.join m1 m0

let join_associative (st:st0{disjoint_join st})
  = forall m0 m1 m2.
      st.disjoint m1 m2 /\
      st.disjoint m0 (st.join m1 m2) ==>
      st.join m0 (st.join m1 m2) == st.join (st.join m0 m1) m2

////////////////////////////////////////////////////////////////////////////////

let interp_extensionality #r #s (equals:r -> r -> prop) (f:r -> s -> prop) =
  forall x y h. {:pattern equals x y; f x h} equals x y /\ f x h ==> f y h

let affine (st:st0) =
  forall r0 r1 s. {:pattern (st.interp (r0 `st.star` r1) s) }
    st.interp (r0 `st.star` r1) s ==> st.interp r0 s

let emp_valid (st:st0) =
  forall s.{:pattern st.interp st.emp s}
    st.interp st.emp s

////////////////////////////////////////////////////////////////////////////////

let depends_only_on (#st:st0) (q:st.heap -> prop) (fp: st.hprop) =
  depends_only_on_0 st.interp st.disjoint st.join q fp

let weaken_depends_only_on (st:st0)
  = forall (q:st.heap -> prop) (fp fp': st.hprop).
      depends_only_on q fp ==>
      depends_only_on q (fp `st.star` fp')

let fp_prop (#st:st0) (fp:st.hprop) =
  fp_prop_0 st.interp st.disjoint st.join fp

let lemma_weaken_depends_only_on (#st:st0{weaken_depends_only_on st})
       (fp0 fp1:st.hprop)
       (q:fp_prop fp0)
  : Lemma (q `depends_only_on` (fp0 `st.star` fp1))
  = ()

let refine_equiv (st:st0) =
  forall (p:st.hprop) (q:fp_prop p) (h:st.heap).
    (st.interp p h /\ q h <==> st.interp (st.refine p q) h)

let refine_star (st:st0{weaken_depends_only_on st}) =
  forall (p0 p1:st.hprop) (q:fp_prop p0).
     (lemma_weaken_depends_only_on p0 p1 q;
      st.equals (st.refine (p0 `st.star` p1) q)
                (st.refine p0 q `st.star` p1))

let interp_depends_only (st:st0) =
  forall p. st.interp p `depends_only_on` p

////////////////////////////////////////////////////////////////////////////////
let st_laws (st:st0) =
    (* standard laws about the equality relation *)
    symmetry st.equals /\
    transitive st.equals /\
    interp_extensionality st.equals st.interp /\
    interp_depends_only st /\
    (* standard laws for star forming a CM *)
    associative st.equals st.star /\
    commutative st.equals st.star /\
    is_unit st.emp st.equals st.star /\
    equals_ext st.equals st.star /\
    (* We're working in an affine interpretation of SL *)
    affine st /\
    emp_valid st /\
    (* laws about disjoint and join *)
    disjoint_sym st /\
    disjoint_join st /\
    join_commutative st /\
    join_associative st /\
    (* refinement *)
    weaken_depends_only_on st /\
    refine_equiv st /\
    refine_star st

let st = s:st0 { st_laws s }

(** [post a c] is a postcondition on [a]-typed result *)
let post (st:st) (a:Type) = a -> st.hprop

let hheap (#st:st) (fp:st.hprop) = fp_heap_0 st.interp fp

let pre_action (#st:st) (fp:st.hprop) (a:Type) (fp':a -> st.hprop) =
  hheap fp -> (x:a & hheap (fp' x))

let is_frame_preserving (#st:st) #a #fp #fp' (f:pre_action fp a fp') =
  forall frame h0.
    st.interp (fp `st.star` frame) h0 ==>
    (let (| x, h1 |) = f h0 in
     st.interp (fp' x `st.star` frame) h1)

let action_depends_only_on_fp (#st:st) (#pre:st.hprop) #a #post (f:pre_action pre a post)
  = forall (h0:hheap pre)
      (h1:st.heap {st.disjoint h0 h1})
      (post: (x:a -> fp_prop (post x))).
      (st.interp pre (st.join h0 h1) /\ (
       let (| x0, h |) = f h0 in
       let (| x1, h' |) = f (st.join h0 h1) in
       x0 == x1 /\
       (post x0 h <==> post x1 h')))

let action (#st:st) (fp:st.hprop) (a:Type) (fp':a -> st.hprop) =
  f:pre_action fp a fp'{
    is_frame_preserving f /\
    action_depends_only_on_fp f
  }

let wp_post (#st:st) (a:Type) (post:post st a) = x:a -> fp_prop (post x)
let wp_pre (#st:st) (pre:st.hprop) = fp_prop pre
let wp (#st:st) (pre:st.hprop) (a:Type) (post:post st a) = wp_post a post -> wp_pre pre

let return_wp (#st:st) (#a:Type) (x:a) (post: post st a)
  : wp (post x) a post
  = fun (k:wp_post a post) s0 -> k x s0

let bind_wp (#st:st)
            (#pre_a:st.hprop) (#a:Type) (#post_a:post st a)
            (#b:Type) (#post_b:post st b)
            (f:wp pre_a a post_a)
            (g: (x:a -> wp (post_a x) b post_b))
  : wp pre_a b post_b
  = fun k -> f (fun x -> g x k)

let frame_post (#st:st) (#a:Type) (p:post st a) (frame:st.hprop)
  : post st a
  =  fun x -> p x `st.star` frame

// let action_framing (#st:st) #b (f:action st b)
//   = forall (h0:fp_heap f.pre)
//       (h1:st.heap {st.disjoint h0 h1})
//       (post: (x:b -> fp_prop (f.post x))).
//       (st.interp f.pre (st.join h0 h1) /\ (
//        let (| x0, h |) = f.sem h0 in
//        let (| x1, h' |) = f.sem (st.join h0 h1) in
//        x0 == x1 /\
//        (post x0 h <==> post x1 h')))

let action_framing_lemma (#st:st) #pre #b #post (f:action pre b post)
                         (h0:hheap pre)
                         (h1:st.heap {st.disjoint h0 h1})
                         (q: (x:b -> fp_prop (post x)))
  : Lemma (st.interp pre (st.join h0 h1) /\ (
           let (| x0, h |) = f h0 in
           let (| x1, h' |) = f (st.join h0 h1) in
           x0 == x1 /\
           (q x0 h <==> q x1 h')))
  = assert (action_depends_only_on_fp f);
    assert (st.interp pre (st.join h0 h1));
    let (| x0, h |) = f h0 in
    let (| x1, h' |) = f (st.join h0 h1) in
    //Wow, a very manual instantiation ...
    assert (action_depends_only_on_fp f ==> x0 == x1 /\ (q x0 h <==> q x1 h'))
        by (T.norm [delta_only [`%action_depends_only_on_fp]];
            let lem = T.implies_intro () in
            let hh = quote h0 in
            let bp0 = T.instantiate (T.binder_to_term lem) hh in
            let hh = quote h1 in
            let bp1 = T.instantiate (T.binder_to_term bp0) hh in
            let qq = quote q in
            let bp2 = T.instantiate (T.binder_to_term bp1) qq in
            T.smt())

let wp_action (#st:st) (#fpre:st.hprop) #b #fpost (f:action fpre b fpost)
  : wp fpre b fpost
  = fun (k:wp_post b fpost) s0 ->
      st.interp fpre s0  /\
      (let (| x, s1 |) = f s0 in
       k x s1)

let bind_action (#st:st) #fpre #a #fpost #b
                (f:action fpre a fpost)
                (#post_g:post st b)
                (wp_g:(x:a -> wp (fpost x) b post_g))
   : wp fpre b post_g
   = bind_wp (wp_action f) wp_g

let triv_post #st (a:Type) (p:post st a) : wp_post a p =
  let k (x:a) : fp_prop (p x) =
    let p : fp_prop (p x) = fun s -> True in
    p
  in
  k

let as_requires (#st:st) (#aL:Type) (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
  : fp_prop preL
  = wpL (triv_post aL postL)

// let join_ext (#st:st) (l r : st.r) (sL sR rest: st.s)
//     : Lemma
//       (requires
//         st.interp l sL /\
//         st.interp r sR /\
//         st.interp (l `st.star` r)
//                   (st.join (sL, st.join(sR, rest))))
//       (ensures
//         st.interp (l `st.star` r)
//                   (st.join (sL, sR)))
//    = admit()

// let wp_par_post (#st:st)
//            #aL (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
//            #aR (#preR:st.hprop) (#postR: post st aR) (wpR: wp preR aR postR)
//            (k:wp_post (aL & aR) (fun (xL, xR) -> postL xL `st.star` postR xR))
//   : fp_prop st.emp
//   = admit()

  // let app_k xL xR : rs_prop (postL xL `st.star` postR xR) = k (xL, xR) in

  //   let p : rs_prop' st.emp =
  //       fun (rest:rs st.emp) ->
  //         forall (xL:aL) (sL':rs (postL xL))
  //           (xR:aR) (sR':rs (postR xR)).
  //             {:pattern (st.interp (postL xL) sL'); (st.interp (postR xR) sR')}
  //           let s1 = st.join (sL', st.join (sR', rest)) in
  //           st.interp (postL xL) sL' /\
  //           st.interp (postR xR) sR' /\
  //           st.interp (postL xL `st.star` postR xR) s1 ==>
  //           app_k xL xR s1
  //   in
  //   let aux (rest:st.s)
  //     : Lemma
  //       (requires
  //         p rest)
  //       (ensures
  //         p (fst (st.split st.emp rest)))
  //       [SMTPat ()] //(st.split st.emp rest)]
  //     = let aux' xL sL' xR sR'
  //           : Lemma
  //             (requires
  //               st.interp (postL xL) sL' /\
  //               st.interp (postR xR) sR' /\
  //               st.interp (postL xL `st.star` postR xR)
  //                         (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))))
  //             (ensures
  //               app_k xL xR (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))))
  //             [SMTPat ()]
  //           = let s1' = (st.join (sL', st.join(sR', rest))) in
  //             let s1 = (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))) in
  //             assert (s1 == st.join (sL', sR'));
  //             assert (s1' == st.join (s1, rest));
  //             assert (st.interp (postL xL `st.star` postR xR) s1');
  //             assert (app_k xL xR s1');
  //             assert (app_k xL xR (fst (st.split (postL xL `st.star` postR xR) s1')));
  //             assert (fst (st.split (postL xL `st.star` postR xR) s1') ==
  //                     fst (st.split (postL xL `st.star` postR xR) s1));
  //             assert (app_k xL xR s1)
  //       in
  //       ()
  //   in
  //   let aux (rest:st.s)
  //     : Lemma
  //       (requires
  //         p (fst (st.split st.emp rest)))
  //       (ensures
  //         p rest)
  //       [SMTPat ()] //st.split st.emp rest)]
  //     = let aux' xL sL' xR sR'
  //           : Lemma
  //             (requires
  //               st.interp (postL xL) sL' /\
  //               st.interp (postR xR) sR' /\
  //               st.interp (postL xL `st.star` postR xR)
  //                         (st.join (sL', st.join(sR', rest))))
  //             (ensures
  //               app_k xL xR (st.join (sL', st.join(sR', rest))))
  //             [SMTPat ()]
  //           = let s1 = (st.join (sL', st.join(sR', rest))) in
  //             let s1' = (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))) in
  //             join_ext (postL xL) (postR xR) sL' sR' rest;
  //             assert (st.interp (postL xL `st.star` postR xR) (st.join(sL', sR')));
  //             assert (st.interp (postL xL `st.star` postR xR) s1');
  //             assert (app_k xL xR s1');
  //             assert (app_k xL xR (fst (st.split (postL xL `st.star` postR xR) s1')));
  //             assert (fst (st.split (postL xL `st.star` postR xR) s1') ==
  //                     fst (st.split (postL xL `st.star` postR xR) s1));
  //             assert (app_k xL xR s1)
  //       in
  //       ()
  //   in
  //   assert (forall rest. p rest <==> p (fst (st.split st.emp rest)));
  //   p


// let rs_prop_emp_any (#st:st) (k:rs_prop st.emp) (s0 s1:st.s)
//   : Lemma (k s0 ==> k s1)
//   = ()

let post_star (#st:st)
              #aL (postL: post st aL)
              #aR (postR: post st aR)
   : post st (aL & aR)
   = fun (xL, xR) -> postL xL `st.star` postR xR

let wp_par (#st:st)
           #aL (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
           #aR (#preR:st.hprop) (#postR: post st aR) (wpR: wp preR aR postR)
   : wp (preL `st.star` preR)
        (aL & aR)
        (post_star postL postR)
   = fun (k:wp_post (aL & aR) (post_star postL postR)) (s:st.heap) ->
        st.interp (preL `st.star` preR) s /\
        as_requires wpL s /\
        as_requires wpR s /\
        (forall (f:action (preL `st.star` preR) (aL & aR) (post_star postL postR)).
           (let (| (xL, xR), s' |) = f s in
             k (xL, xR) s'))

let bind_par (#st:st)
           #aL (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
           #aR (#preR:st.hprop) (#postR: post st aR) (wpR: wp preR aR postR)
           #a  #post (wp_k:(xL:aL -> xR:aR -> wp (postL xL `st.star` postR xR) a post))
  : wp (preL `st.star` preR)
       a
       post
  = bind_wp (wp_par wpL wpR) (fun (xL, xR) -> wp_k xL xR)


(** [m s c a pre post] :
//  *  A free monad for divergence, state and parallel composition
//  *  with generic actions. The main idea:
//  *
//  *  Every continuation may be divergent. As such, [m] is indexed by
//  *  pre- and post-conditions so that we can do proofs
//  *  intrinsically.
//  *
//  *  Universe-polymorphic in both the state and result type
//  *
//  *)
noeq
type m (st:st) : (a:Type u#a) -> pre:st.hprop -> post:post st a -> wp pre a post -> Type =
  | Ret : #a:_
        -> post:post st a
        -> x:a
        -> m st a (post x) post (return_wp x post)

  | Act : #a:_
        -> b:_
        -> fpre: _
        -> fpost: _
        -> f:action fpre b fpost
        -> #post_g:post st a
        -> #wp_g:(x:b -> wp (fpost x) a post_g)
        -> g:(x:b -> Dv (m st a (fpost x) post_g (wp_g x)))
        -> m st a fpre post_g (bind_action f wp_g)

  | Par : preL:_ -> aL:_ -> postL:_ -> wpL:wp preL aL postL -> mL: m st aL preL postL wpL ->
          preR:_ -> aR:_ -> postR:_ -> wpR:wp preR aR postR -> mR: m st aR preR postR wpR ->
          #a:_ -> post:_ -> wp_k:(xL:aL -> xR:aR -> wp (postL xL `st.star` postR xR) a post)
          -> k:(xL:aL -> xR:aR -> Dv (m st a (postL xL `st.star` postR xR) post (wp_k xL xR))) ->
          m st a (st.star preL preR) post (bind_par wpL wpR wp_k)


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

let action_result (#st:st) #fpre #a #fpost (f:action fpre a fpost) (v:a) (s0 s1:st.heap) (frame:st.hprop) =
  st.interp (fpre `st.star` frame) s0  /\
  st.interp (fpost v `st.star` frame) s1 /\
  f s0 == (| v, s1 |)

noeq
type step_result (#st:st) a (q:post st a) (frame:st.hprop) (k:wp_post a q) =
  | Step: fpre:st.hprop -> //the original precondition
          b:Type ->
          fpost:(b -> st.hprop) ->
          act:action fpre b fpost ->
          initial_state:st.heap ->
          v:b ->
          state:st.heap { action_result act v initial_state state frame } ->
          wp:wp (fpost v) a q { wp k state } ->
          m st a (fpost v) q wp -> //the reduct
          nat -> //position in the stream of booleans (less important)
          step_result a q frame k

/// [step i f frame state]: Reduces a single step of [f], while framing
/// the assertion [frame]

// #reset-options
// #restart-solver
// #push-options "--max_fuel 0 --max_ifuel 4 --initial_ifuel 4 --z3rlimit_factor 4 --query_stats"

let step_act (#st:st) (i:nat) #pre #a #post
             (frame:st.hprop)
             (#wp:wp pre a post)
             (f:m st a pre post wp { Act? f })
             (k:wp_post a post)
             (state:st.heap)
  : Div (step_result a post frame k)
        (requires
          st.interp (pre `st.star` frame) state /\
          st.interp pre state /\
          wp k state)
        (ensures fun _ -> True)
  =
    let Act b fpre fpost act1 #post_g #wp_g g = f in
    //Evaluate the action and return the continuation as the reduct
    let (| vb, state' |) = act1 state in
    Step fpre b fpost act1 state vb state' (wp_g vb) (g vb) i

#push-options "--query_stats"
#push-options "--max_ifuel 4 --initial_ifuel 4"


let id_action (#st:st) #a (x:a) (post:post st a)
   : action (post x) a post
   = fun (s:hheap (post x)) ->
       let res : (x:a & hheap (post x)) = (| x, s |) in
       res

let trigger (#a:Type) (x:a) = True

// let id_action (#st:st) #aL #aR
//               (xL:aL) (xR:aR)
//               (postL:post st aL) (postR:post st aR)
//    : action (postL xL `st.star` postR xR)
//             (aL & aR)
//             (post_star postL postR)
//    = fun (s:hheap (postL xL `st.star` postR xR)) ->
//        let res : (x:(aL & aR) & hheap ((post_star postL postR) x)) =
//          (| (xL, xR), s |)
//        in
//        res
// let trigger (#a:Type) (x:a) = True

let step_par_ret (#st:st) (i:nat) #pre #a #post
                      (frame:st.hprop)
                      (#wp:wp pre a post)
                      (f:m st a pre post wp { Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f) })
                      (k:wp_post a post)
                      (state:st.heap)
  : Div (step_result a post frame k)
        (requires
          st.interp (pre `st.star` frame) state /\
          st.interp pre state /\
          wp k state)
        (ensures fun _ -> True)
  =  let Par preL aL postL wpL (Ret _ xL)
          preR aR postR wpR (Ret _ xR)
          post wp_k kk = f in
      assert (wpL == return_wp xL postL);
      assert (wpR == return_wp xR postR);
      assert (wp == bind_par wpL wpR wp_k);
      assert (wp k state);
      assert (preL == postL xL);
      assert (preR == postR xR);
      assert (forall (f:action (preL `st.star` preR) (aL & aR) (post_star postL postR)).
                 {:pattern (trigger f)}
                (let (| (xL, xR), s' |) = f state in
                 wp_k xL xR k s'));
      assert (trigger (id_action (xL, xR) (post_star postL postR)));
      assert (wp_k xL xR k state);
      Step (postL xL `st.star` postR xR)
           (aL & aR)
           (post_star postL postR)
           (id_action (xL, xR) (post_star postL postR))
           state
           (xL, xR)
           state
           (wp_k xL xR)
           (kk xL xR)
           i

let step_ret (#st:st) (i:nat) #fpre #a #fpost (frame:st.hprop)
             (#wp:wp fpre a fpost)
             (f:m st a fpre fpost wp { Ret? f })
             (k:wp_post a fpost)
             (state:st.heap)
  : Div (step_result a fpost frame k)
        (requires
          st.interp (fpre `st.star` frame) state /\
          st.interp fpre state /\
          wp k state)
        (ensures fun _ -> True)
  = let Ret pp x = f in
    Step (pp x)
         a
         pp
         (id_action x pp)
         state
         x
         state
         wp
         (Ret pp x)
         i

//#push-options "--z3rlimit_factor 2 --z3cliopt 'smt.qi.eager_threshold=100'"
let elim_refine (#st:st) (r0 r1:st.hprop) (p:fp_prop r0) (s:st.heap)
  : Lemma
    (requires
      st.interp (st.refine r0 p `st.star` r1) s)
    (ensures
      st.interp (r0 `st.star` r1) s /\
      st.interp r0 s /\
      st.interp r1 s /\
      p s)
   = ()

let intro_refine (#st:st) (r0 r1:st.hprop) (p:fp_prop r0) (s:st.heap)
  : Lemma
    (requires
      st.interp (r0 `st.star` r1) s /\
      p s)
    (ensures
      st.interp (st.refine r0 p `st.star` r1) s)
   = assert (st.interp (st.refine (r0 `st.star` r1) p) s)

#push-options "--z3rlimit_factor 4"

let rearrange_action_result
    (#st:st) (#fpre:st.hprop) #a #fpost (f:action fpre a fpost)
    (v:a) (s0 s1:st.heap)
    (q:st.hprop) (r:fp_prop q) (frame:st.hprop)
  : Pure (action (fpre `st.star` q) a (fun x -> fpost x `st.star` q))
    (requires
      action_result f v s0 s1 (st.refine q r `st.star` frame))
    (ensures fun g ->
      action_result g v s0 s1 frame)
  = admit()


let rec step (#st:st) (i:nat) #pre #a #post
             (frame:st.hprop)
             (#wp_:wp pre a post)
             (f:m st a pre post wp_)
             (k:wp_post a post)
             (state:st.heap)
  : Div (step_result a post frame k)
        (requires
          st.interp (pre `st.star` frame) state /\
          st.interp pre state /\
          wp_ k state)
        (ensures fun _ -> True)
  = match f with
    // | Ret _ _ ->
    //    step_ret i frame f k state

    // | Act _ _ _ _ _  ->
    //   step_act i frame f k state

    // | Par preL aL postL wpL (Ret _ _)
    //       preR aR postR wpR (Ret _ _)
    //       post wp_kont kont ->
    //   step_par_ret i frame f k state

    | Par preL aL postL wpL mL
          preR aR postR wpR mR
          post wp_kont kont ->

      assert (wp_ == bind_par wpL wpR wp_kont);
      assert (st.interp (preL `st.star` (preR `st.star` frame)) state);
      assert (st.interp (preL `st.star` preR) state);
      assert (as_requires wpL state);
      assert (as_requires wpR state);
      calc (st.equals) {
        preL `st.star` (preR `st.star` frame);
          (st.equals) { }
        (preL `st.star` preR) `st.star` frame;
          (st.equals) { }
        (preR `st.star` preL) `st.star` frame;
          (st.equals) { }
        preR `st.star` (preL `st.star` frame);
      };
      intro_refine preR (preL `st.star` frame) (as_requires wpR) state;
      calc (st.equals) {
        (st.refine preR (as_requires wpR)) `st.star` (preL `st.star` frame);
          (st.equals) { }
        (st.refine preR (as_requires wpR) `st.star` preL) `st.star` frame;
          (st.equals) { }
        (preL `st.star` st.refine preR (as_requires wpR)) `st.star` frame;
          (st.equals) { }
        preL `st.star` ((st.refine preR (as_requires wpR)) `st.star` frame);
      };
      let Step fpre b fpost act initial_state v next_state wpL' mL' j =
            //Notice that, inductively, we instantiate the frame extending
            //it to include the precondition of the other side of the par
            step (i + 1)
                 ((st.refine preR (as_requires wpR)) `st.star` frame)
                 mL
                 (triv_post aL postL)
                 state
      in
      assert (as_requires wpL' next_state);
      assert (as_requires wpR next_state);
      let wpL' : wp (fpost v) aL postL = wpL' in
      let wpR  : wp preR aR postR = wpR in
      let wp_par
        : wp (fpost v `st.star` preR) a post
        = bind_par wpL' wpR wp_kont
      in
      let mL' : m st aL (fpost v) postL wpL' = mL' in
      let next_m
        : m st a (fpost v `st.star` preR) post wp_par
        = Par (fpost v) aL postL wpL' mL'
              preR aR postR wpR mR
              post wp_kont kont
      in
      assume (wp_par k next_state);
      // assert (st.interp (fpost v `st.star` preR) next_state);
      // assume (st.interp (fpre `st.star` preR) state);
      // assert (action_result act v initial_state next_state
      //        ((st.refine preR (as_requires wpR)) `st.star` frame));
      assert (action_result act v initial_state next_state (st.refine preR (as_requires wpR) `st.star` frame));
      let act : action (fpre `st.star` preR) b (fun x -> fpost x `st.star` preR) =
        rearrange_action_result act v initial_state next_state preR (as_requires wpR) frame
      in
      let step =
        Step (fpre `st.star` preR) b (fun x -> fpost x `st.star` preR) act initial_state v next_state
             wp_par
             next_m
             j
      in
      step | _ -> admit()



      admit()

   | _ -> admit()
      assume (bind_par wpL' wpR wp_kont k next_state);
      let step =
        Step fpre b fpost act initial_state v next_state
             (bind_par wpL' wpR wp_kont)
             next_m
             j in
      admit();
      step
//
//      admit()

      // let sL, rest0 = st.split preL state in
      // let sR, rest = st.split preR rest0 in
      // assert (as_requires wpL sL);
      // assert (as_requires wpR sR);

      // assert (as_requires wpL state);
      // assert (as_requires wpR rest0);
      // assert (fst (st.split preR rest0) == fst (st.split preR state));
      // assert (as_requires wpR state);

    | _ -> admit()


//       if bools i
//       then begin
//         calc (st.equals) {
//           preL `st.star` (preR `st.star` frame);
//           (st.equals) { }
//           (preL `st.star` preR) `st.star` frame;
//           (st.equals) { }
//           (preR `st.star` preL) `st.star` frame;
//           (st.equals) { }
//           preR `st.star` (preL `st.star` frame);
//         };
//         assert (st.interp ((st.lift preR (as_requires wpR)) `st.star` (preL `st.star` frame)) state);
//         calc (st.equals) {
//           (st.lift preR (as_requires wpR)) `st.star` (preL `st.star` frame);
//           (st.equals) { }
//           (st.lift preR (as_requires wpR) `st.star` preL) `st.star` frame;
//           (st.equals) { }
//           (preL `st.star` st.lift preR (as_requires wpR)) `st.star` frame;
//           (st.equals) { }
//           preL `st.star` ((st.lift preR (as_requires wpR)) `st.star` frame);
//         };
//         assert (st.interp (preL `st.star` ((st.lift preR (as_requires wpR)) `st.star` frame)) state);
//         let Step preL' wpL' mL' state' j =
//             //Notice that, inductively, we instantiate the frame extending
//             //it to include the precondition of the other side of the par
//             step (i + 1)
//                  ((st.lift preR (as_requires wpR)) `st.star` frame)
//                  mL
//                  (triv_post aL postL)
//                  state
//         in
//         assert (as_requires wpL' state');
//         assert (as_requires wpR state');
//         let sL', rest0' = st.split preL' state' in
//         let sR', rest' = st.split preR rest0' in
//         assert (bind_par wpL wpR wp_kont k state ==>
//                bind_par wpL' wpR wp_kont k state')
//                by  (T.norm [delta_only [`%wp_par; `%bind_wp; `%bind_par; `%wp_par_post]];
//                T.dump "A";
//                T.smt());
//         Step (preL' `st.star` preR)
//              (bind_par wpL' wpR wp_kont)
//              (Par preL' aL postL wpL' mL'
//                   preR  aR postR wpR  mR
//                   post wp_kont kont)
//              state'
//              j
//       end else begin
//         assert (st.interp ((st.lift preL (as_requires wpL)) `st.star` (preR `st.star` frame)) state);
//         calc (st.equals) {
//           (st.lift preL (as_requires wpL)) `st.star` (preR `st.star` frame);
//           (st.equals) { }
//           (st.lift preL (as_requires wpL) `st.star` preR) `st.star` frame;
//           (st.equals) { }
//           (preR `st.star` st.lift preL (as_requires wpL)) `st.star` frame;
//           (st.equals) { }
//           preR `st.star` ((st.lift preL (as_requires wpL)) `st.star` frame);
//         };
//         assert (st.interp (preR `st.star` ((st.lift preL (as_requires wpL)) `st.star` frame)) state);
//         let Step preR' wpR' mR' state' j =
//             //Notice that, inductively, we instantiate the frame extending
//             //it to include the precondition of the other side of the par
//             step (i + 1)
//                  ((st.lift preL (as_requires wpL)) `st.star` frame)
//                  mR
//                  (triv_post aR postR)
//                  state
//         in
//         assert (as_requires wpL state');
//         assert (as_requires wpR' state');
//         let sL', rest0' = st.split preL state' in
//         let sR', rest' = st.split preR' rest0' in
//         assert (bind_par wpL wpR wp_kont k state ==>
//                 bind_par wpL wpR' wp_kont k state')
//                by  (T.norm [delta_only [`%wp_par; `%bind_wp; `%bind_par; `%wp_par_post]];
//                T.dump "A";
//                T.smt());
//         let p' = (preL `st.star` preR') in
//         let wp' = bind_par wpL wpR' wp_kont in
//         calc (st.equals) {
//           preR' `st.star` (preL `st.star` frame);
//           (st.equals) { }
//           (preR' `st.star` preL) `st.star` frame;
//           (st.equals) { }
//           (preL `st.star` preR') `st.star` frame;
//         };
//         Step p'
//              wp'
//              (Par preL aL postL wpL mL
//                   preR'  aR postR wpR' mR'
//                   post wp_kont kont)
//              state'
//              j
//       end


// // (**
// // //  * [run i f state]: Top-level driver that repeatedly invokes [step]
// // //  *
// // //  * The type of [run] is the main theorem. It states that it is sound
// // //  * to interpret the indices of `m` as a Hoare triple in a
// // //  * partial-correctness semantics
// // //  *
// // //  *)
// // let rec run (#st:st) (i:nat)
// //             #pre #a #post (#wp:wp pre a post)
// //             (f:m st a pre post wp) (state:st.s)
// //             (k:wp_post a post)
// //   : Div (a & st.s)
// //     (requires
// //       st.interp pre state /\
// //       wp k state)
// //     (ensures fun (x, state') ->
// //       st.interp (post x) state' /\
// //       k x state')
// //   = match f with
// //     | Ret x -> x, state
// //     | _ ->
// //       let Step pre' wp' f' state' j = step i st.emp f k state in
// //       run j f' state' k


// // ////////////////////////////////////////////////////////////////////////////////
// // //The rest of this module shows how these semantics can be packaged up as an
// // //effect in F*
// // ////////////////////////////////////////////////////////////////////////////////

// // (** [eff a pre post] : The representation-type for a layered effect
// // //  *
// // //  *   - Note, we'll probably have to add a thunk to make it work with
// // //  *     the current implementation but that's a detail
// // //  *)
// // let eff (#st:st) a
// //         (expects:st.r)
// //         (provides: a -> st.r)
// //         (wp:wp expects a provides)
// //   = m st a expects provides wp

// // /// eff is a monad: we give a return and bind for it, though we don't
// // /// prove the monad laws


// // (** [return]: easy, just use Ret *)
// // let return (#st:st) #a (x:a) (post:a -> st.r)
// //   : eff a (post x) post (return_wp x post)
// //   = Ret x

// // let eta2 #a #b #c (f:a -> b -> c) : Lemma ((fun x y -> f x y) == f) = ()

// // (**
// // //  * [bind]: sequential composition works by pushing `g` into the continuation
// // //  * at each node, finally applying it at the terminal `Ret`
// // //  *)
// // let rec bind (#st:st) #a #b (#p:st.r) (#q:a -> st.r) (#r:b -> st.r)
// //              (#wp_f: wp p a q) (f:eff a p q wp_f)
// //              (#wp_g: (x:a -> wp (q x) b r)) (g: (x:a -> eff b (q x) r (wp_g x)))
// //   : Dv (eff b p r (bind_wp wp_f wp_g))
// //   = match f with
// //     | Ret x ->
// //       assert (p == q x);
// //       assert (wp_f == return_wp x q);
// //       assert (eq2 #(wp_post b r -> rs (q x) -> prop) (bind_wp (return_wp x q) wp_g) (wp_g x))
// //         by (T.norm [delta_only [`%bind_wp; `%return_wp]];
// //             T.dump "A";
// //             T.mapply (`eta2));
// //       g x

// //     | Act #_ #a' f #post_h #wp_h h ->
// //       assert (wp_f == bind_action f wp_h);
// //       let g' (x:_) : Dv (eff b (f.post x) r (bind_wp (wp_h x) wp_g))
// //         = bind #st #a' #b (h x) g
// //       in
// //       let res : eff b p r (bind_action f (fun x -> bind_wp (wp_h x) wp_g)) = Act f g' in
// //       calc (==) {
// //         bind_action f (fun x -> bind_wp (wp_h x) wp_g);
// //           == {}
// //         bind_wp (wp_action f) (fun x -> bind_wp (wp_h x) wp_g);
// //           == { admit() (* assoc *) }
// //         bind_wp (bind_wp (wp_action f) (fun x -> wp_h x)) wp_g;
// //           == { }
// //         bind_wp wp_f wp_g;
// //       };
// //       res

// //     | Par preL aL postL wpL mL
// //           preR aR postR wpR mR
// //           post wp_kont kont ->
// //       let kont x0 x1 : Dv (eff b (postL x0 `st.star` postR x1) r (bind_wp (wp_kont x0 x1) wp_g)) = bind (kont x0 x1) g in
// //       let res : m st b (st.star preL preR) r (bind_par wpL wpR (fun x0 x1 -> (bind_wp (wp_kont x0 x1) wp_g))) =
// //           Par preL aL postL wpL mL
// //                     preR aR postR wpR mR
// //                     r (fun x0 x1 -> (bind_wp (wp_kont x0 x1) wp_g)) kont in
// //       calc (==) {
// //         (bind_par wpL wpR (fun x0 x1 -> (bind_wp (wp_kont x0 x1) wp_g)));
// //         == { _ by (T.dump "A"; T.norm [delta_only [`%bind_par]]; T.dump "B"; T.trefl()) }
// //         bind_wp (wp_par wpL wpR) (fun (x0, x1) -> (bind_wp (wp_kont x0 x1) wp_g));
// //         == { admit () (* assoc *) }
// //         bind_wp (bind_wp (wp_par wpL wpR) (fun (x0, x1) -> wp_kont x0 x1)) wp_g;
// //         == {}
// //         (bind_wp (bind_par wpL wpR wp_kont) wp_g);
// //       };
// //       res


// // // // // // (**
// // // // // //  * [par]: Parallel composition
// // // // // //  * Works by just using the `Par` node and `Ret` as its continuation
// // // // // //  **)
// // // // // // let par #s (#c:comm_monoid s)
// // // // // //         #a0 #p0 #q0 (m0:eff a0 p0 q0)
// // // // // //         #a1 #p1 #q1 (m1:eff a1 p1 q1)
// // // // // //  : eff (a0 & a1) (p0 `c.star` p1) (fun (x0, x1) -> q0 x0 `c.star` q1 x1)
// // // // // //  = Par p0 q0 m0
// // // // // //        p1 q1 m1
// // // // // //        #_ #(fun (x0, x1) -> c.star (q0 x0) (q1 x1)) (fun x0 x1 -> Ret (x0, x1))


// // // // // // /// Now for an instantiation of the state with a heap
// // // // // // /// just to demonstrate how that would go

// // // // // // /// Heaps are usually in a universe higher than the values they store
// // // // // // /// Pick it in universe 1
// // // // // // assume val heap : Type u#1

// // // // // // /// Assume some monoid of heap assertions
// // // // // // assume val hm : comm_monoid heap

// // // // // // /// For this demo, we'll also assume that this assertions are affine
// // // // // // ///  i.e., it's ok to forget some properties of the heap
// // // // // // assume val hm_affine (r0 r1:hm.r) (h:heap)
// // // // // //   : Lemma (hm.interp (r0 `hm.star` r1) h ==>
// // // // // //            hm.interp r0 h)

// // // // // // /// Here's a ref type
// // // // // // assume val ref : Type u#0 -> Type u#0

// // // // // // /// And two atomic heap assertions
// // // // // // assume val ptr_live (r:ref 'a) : hm.r
// // // // // // assume val pts_to (r:ref 'a) (x:'a) : hm.r

// // // // // // /// sel: Selected a reference from a heap, when that ref is live
// // // // // // assume val sel (x:ref 'a) (h:heap{hm.interp (ptr_live x) h})
// // // // // //   : Tot 'a
// // // // // // /// this tells us that sel is frameable
// // // // // // assume val sel_ok (x:ref 'a) (h:heap) (frame:hm.r)
// // // // // //   : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
// // // // // //            (hm_affine (ptr_live x) frame h;
// // // // // //             let v = sel x h in
// // // // // //             hm.interp (pts_to x v `hm.star` frame) h))


// // // // // // /// upd: updates a heap at a given reference, when the heap contains it
// // // // // // assume val upd (x:ref 'a) (v:'a) (h:heap{hm.interp (ptr_live x) h})
// // // // // //   : Tot heap
// // // // // // /// and upd is frameable too
// // // // // // assume val upd_ok (x:ref 'a) (v:'a) (h:heap) (frame:hm.r)
// // // // // //   : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
// // // // // //            (hm_affine (ptr_live x) frame h;
// // // // // //             let h' = upd x v h in
// // // // // //             hm.interp (pts_to x v `hm.star` frame) h'))

// // // // // // /// Here's a sample action for dereference
// // // // // // let (!) (x:ref 'a)
// // // // // //   : eff 'a (ptr_live x) (fun v -> pts_to x v)
// // // // // //   = let act : action hm 'a =
// // // // // //     {
// // // // // //       pre = ptr_live x;
// // // // // //       post = pts_to x;
// // // // // //       sem = (fun frame h0 ->
// // // // // //         hm_affine (ptr_live x) frame h0;
// // // // // //         sel_ok x h0 frame;
// // // // // //         (| sel x h0, h0 |))
// // // // // //     } in
// // // // // //     Act act Ret

// // // // // // /// And a sample action for assignment
// // // // // // let (:=) (x:ref 'a) (v:'a)
// // // // // //   : eff unit (ptr_live x) (fun _ -> pts_to x v)
// // // // // //   = let act : action hm unit =
// // // // // //     {
// // // // // //       pre = ptr_live x;
// // // // // //       post = (fun _ -> pts_to x v);
// // // // // //       sem = (fun frame h0 ->
// // // // // //         hm_affine (ptr_live x) frame h0;
// // // // // //         upd_ok x v h0 frame;
// // // // // //         (| (), upd x v h0 |))
// // // // // //     } in
// // // // // //     Act act Ret
