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

module Steel.Semantics.Hoare

module P = FStar.Preorder

open FStar.Tactics

open MST


(*
 * This module provides a semantic model for a combined effect of
 * divergence, state, and parallel composition of atomic actions.
 *
 * It also builds a generic separation-logic-style program logic
 * for this effect, in a partial correctness setting.

 * It is also be possible to give a variant of this semantics for
 * total correctness. However, we specifically focus on partial correctness
 * here so that this semantics can be instantiated with lock operations,
 * which may deadlock. See ParTot.fst for a total-correctness variant of
 * these semantics.
 *
 * The program logic is specified in the Hoare-style pre- and postconditions
 *   See Steel.Semantics.fst for the wp variant
 *)


/// Disabling projectors because we don't use them and they increase the typechecking time

#push-options "--fuel  0 --ifuel 2 --z3rlimit 20 --print_implicits --print_universes \
  --using_facts_from 'Prims FStar.Pervasives FStar.Preorder MST Steel.Semantics.Hoare'"

(**** Begin state defn ****)


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
  forall x y z. //{:pattern f x (f y z) \/ f (f x y) z}
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
  (forall (h0:fp_heap_0 interp fp) (h1:heap{disjoint h0 h1}). q h0 <==> q (join h0 h1))

let fp_prop_0 (#heap:Type) (#hprop:Type)
              (interp:hprop -> heap -> prop)
              (disjoint: heap -> heap -> prop)
              (join: (h0:heap -> h1:heap{disjoint h0 h1} -> heap))
              (fp:hprop) =
  p:(heap -> prop){p `(depends_only_on_0 interp disjoint join)` fp}

noeq
type st0 = {
  heap:Type u#1;
  mem:Type u#1;
  locks_preorder:P.preorder mem;
  hprop:Type u#1;
  heap_of_mem: mem -> heap;
  locks_invariant: mem -> hprop;

  m_disjoint: mem -> heap -> prop;
  disjoint: heap -> heap -> prop;
  join: h0:heap -> h1:heap{disjoint h0 h1} -> heap;
  upd_joined_heap: (m:mem) -> (h:heap{m_disjoint m h}) -> mem;

  interp: hprop -> heap -> prop;

  emp:hprop;
  star: hprop -> hprop -> hprop;

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

let interp_depends_only (st:st0) =
  forall p. st.interp p `depends_only_on` p

let m_implies_disjoint (st:st0) =
  forall (m:st.mem) (h1:st.heap).
       st.m_disjoint m h1 ==> st.disjoint (st.heap_of_mem m) h1

let mem_valid_locks_invariant (st:st0) =
  forall (m:st.mem). st.interp (st.locks_invariant m) (st.heap_of_mem m)

let valid_upd_heap (st:st0{m_implies_disjoint st}) =
  forall (m:st.mem) (h:st.heap{st.m_disjoint m h}).
               st.heap_of_mem (st.upd_joined_heap m h) == st.join (st.heap_of_mem m) h /\
               st.locks_invariant m == st.locks_invariant (st.upd_joined_heap m h)

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
    weaken_depends_only_on st /\
    (* Relations between mem and heap *)
    m_implies_disjoint st /\
    mem_valid_locks_invariant st /\
    valid_upd_heap st

let st = s:st0 { st_laws s }


(**** End state defn ****)


(**** Begin expects, provides, requires, and ensures defns ****)


/// expects (the heap assertion expected by a computation) is simply an st.hprop
///
/// provides, or the post heap assertion, is a st.hprop on [a]-typed result

let post (st:st) (a:Type) = a -> st.hprop



/// requires is a heap predicate that depends only on a pre heap assertion
///   (where the notion of `depends only on` is defined above as part of the state definition)
///
/// we call the type l_pre for logical precondition

let l_pre (#st:st) (pre:st.hprop) = fp_prop pre


/// ensures is a 2-state postcondition of type heap -> a -> heap -> prop
///
/// To define ensures, we need a notion of depends_only_on_2
///
/// Essentially, in the first heap argument, postconditions depend only on the expects hprop
///   and in the second heap argument, postconditions depend only on the provides hprop
///
/// Also note that the support for depends_only_on_2 is not required from the underlying memory model


let depends_only_on_0_2 (#a:Type) (#heap:Type) (#hprop:Type)
  (interp:hprop -> heap -> prop)
  (disjoint:heap -> heap -> prop)
  (join:(h0:heap -> h1:heap{disjoint h0 h1} -> heap))
  (q:heap -> a -> heap -> prop) (fp_pre:hprop) (fp_post:a -> hprop)

= //can join any disjoint heap to the pre-heap and q is still valid
  (forall x (h_pre:fp_heap_0 interp fp_pre) h_post (h:heap{disjoint h_pre h}).
     q h_pre x h_post <==> q (join h_pre h) x h_post) /\

  //can join any disjoint heap to the post-heap and q is still valid
  (forall x h_pre (h_post:fp_heap_0 interp (fp_post x)) (h:heap{disjoint h_post h}).
     q h_pre x h_post <==> q h_pre x (join h_post h))


/// Abbreviations for two-state depends

let fp_prop_0_2 (#a:Type) (#heap #hprop:Type)
  (interp:hprop -> heap -> prop)
  (disjoint:heap -> heap -> prop)
  (join:(h0:heap -> h1:heap{disjoint h0 h1} -> heap))
  (fp_pre:hprop) (fp_post:a -> hprop) =

  q:(heap -> a -> heap -> prop){depends_only_on_0_2 interp disjoint join q fp_pre fp_post}

let depends_only_on2 (#st:st0) (#a:Type) (q:st.heap -> a -> st.heap -> prop) (fp_pre:st.hprop) (fp_post:a -> st.hprop) =
  depends_only_on_0_2 st.interp st.disjoint st.join q fp_pre fp_post

let fp_prop2 (#st:st0) (#a:Type) (fp_pre:st.hprop) (fp_post:a -> st.hprop) =
  q:(st.heap -> a -> st.heap -> prop){depends_only_on2 q fp_pre fp_post}


/// Finally the type of 2-state postconditions

let l_post (#st:st) (#a:Type) (pre:st.hprop) (post:post st a) = fp_prop2 pre post


(**** End expects, provides, requires, and ensures defns ****)


(**** Begin interface of actions ****)

/// Actions are essentially state transformers that preserve frames

let preserves_frame (#st:st) (pre post:st.hprop) (m0 m1:st.mem) =
  forall (frame:st.hprop).
    st.interp (st.locks_invariant m0 `st.star` (pre `st.star` frame)) (st.heap_of_mem m0) ==>
    (st.interp (st.locks_invariant m1 `st.star` (post `st.star` frame)) (st.heap_of_mem m1) /\
     (forall (f_frame:fp_prop frame). f_frame (st.heap_of_mem m0) <==> f_frame (st.heap_of_mem m1)))

let action_t (#st:st) (#a:Type) (pre:st.hprop) (post:post st a) (lpre:l_pre pre) (lpost:l_post pre post) =
  unit ->
  MST a st.mem st.locks_preorder
  (requires fun m0 ->
    st.interp (st.locks_invariant m0 `st.star` pre) (st.heap_of_mem m0) /\
    lpre (st.heap_of_mem m0))
  (ensures fun m0 x m1 ->
    st.interp (st.locks_invariant m1 `st.star` (post x)) (st.heap_of_mem m1) /\
    lpost (st.heap_of_mem m0) x (st.heap_of_mem m1) /\
    preserves_frame pre (post x) m0 m1)

(**** End interface of actions ****)


(**** Begin definition of the computation AST ****)


/// Gadgets for building lpre- and lpostconditions for various nodes


/// Return node is parametric in provides and ensures

let return_lpre (#st:st) (#a:Type) (#post:post st a) (x:a) (lpost:l_post (post x) post)
: l_pre (post x)
= fun h -> lpost h x h

let frame_lpre (#st:st) (#pre:st.hprop) (lpre:l_pre pre) (#frame:st.hprop) (f_frame:fp_prop frame)
: l_pre (pre `st.star` frame)
= fun h -> lpre h /\ f_frame h

let frame_lpost (#st:st) (#a:Type) (#pre:st.hprop) (#post:post st a) (lpre:l_pre pre) (lpost:l_post pre post)
  (#frame:st.hprop) (f_frame:fp_prop frame)
: l_post (pre `st.star` frame) (fun x -> post x `st.star` frame)
= fun h0 x h1 -> lpre h0 /\ lpost h0 x h1 /\ f_frame h1


/// The bind rule bakes in weakening of requires / ensures

let bind_lpre (#st:st) (#a:Type) (#pre:st.hprop) (#post_a:post st a)
  (lpre_a:l_pre pre) (lpost_a:l_post pre post_a)
  (lpre_b:(x:a -> l_pre (post_a x)))
: l_pre pre
= fun h -> lpre_a h /\ (forall (x:a) h1. lpost_a h x h1 ==> lpre_b x h1)

let bind_lpost (#st:st) (#a:Type) (#pre:st.hprop) (#post_a:post st a)
  (lpre_a:l_pre pre) (lpost_a:l_post pre post_a)
  (#b:Type) (#post_b:post st b)
  (lpost_b:(x:a -> l_post (post_a x) post_b))
: l_post pre post_b
= fun h0 y h2 -> lpre_a h0 /\ (exists x h1. lpost_a h0 x h1 /\ (lpost_b x) h1 y h2)


/// Parallel composition is pointwise

let par_lpre (#st:st) (#preL:st.hprop) (lpreL:l_pre preL)
  (#preR:st.hprop) (lpreR:l_pre preR)
: l_pre (preL `st.star` preR)
= fun h -> lpreL h /\ lpreR h

let par_lpost (#st:st) (#aL:Type) (#preL:st.hprop) (#postL:post st aL)
  (lpreL:l_pre preL) (lpostL:l_post preL postL)
  (#aR:Type) (#preR:st.hprop) (#postR:post st aR)
  (lpreR:l_pre preR) (lpostR:l_post preR postR)
: l_post (preL `st.star` preR) (fun (xL, xR) -> postL xL `st.star` postR xR)
= fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1


/// We never use projectors from m, so don't bother generating, typechecking, and verifying them

noeq
type m (st:st) : a:Type u#a -> pre:st.hprop -> post:post st a -> l_pre pre -> l_post pre post -> Type =
  | Ret:
    #a:Type u#a ->
    post:post st a ->
    x:a ->
    lpost:l_post (post x) post ->
    m st a (post x) post (return_lpre #_ #_ #post x lpost) lpost

  | Bind:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post_a:post st a ->
    #lpre_a:l_pre pre ->
    #lpost_a:l_post pre post_a ->
    #b:Type u#a ->
    #post_b:post st b ->
    #lpre_b:(x:a -> l_pre (post_a x)) ->
    #lpost_b:(x:a -> l_post (post_a x) post_b) ->
    f:m st a pre post_a lpre_a lpost_a ->
    g:(x:a -> Dv (m st b (post_a x) post_b (lpre_b x) (lpost_b x))) ->
    m st b pre post_b
      (bind_lpre lpre_a lpost_a lpre_b)
      (bind_lpost lpre_a lpost_a lpost_b)

  | Act:
    a:Type u#a ->
    #pre:st.hprop ->
    #post:post st a ->
    #lpre:l_pre pre ->
    #lpost:l_post pre post ->
    f:action_t #st #a pre post lpre lpost ->
    m st a pre post lpre lpost

  | Frame:
    #a:Type ->
    #pre:st.hprop ->
    #post:post st a ->
    #lpre:l_pre pre ->
    #lpost:l_post pre post ->
    f:m st a pre post lpre lpost ->
    frame:st.hprop ->
    f_frame:fp_prop frame ->
    m st a (pre `st.star` frame) (fun x -> post x `st.star` frame)
      (frame_lpre lpre f_frame)
      (frame_lpost lpre lpost f_frame)

  | Par:
    #aL:Type u#a ->
    #preL:st.hprop ->
    #postL:post st aL ->
    #lpreL:l_pre preL ->
    #lpostL:l_post preL postL ->
    mL:m st aL preL postL lpreL lpostL ->
    #aR:Type u#a ->
    #preR:st.hprop ->
    #postR:post st aR ->
    #lpreR:l_pre preR ->
    #lpostR:l_post preR postR ->
    mR:m st aR preR postR lpreR lpostR ->
    m st (aL & aR) (preL `st.star` preR) (fun (xL, xR) -> postL xL `st.star` postR xR)
      (par_lpre lpreL lpreR)
      (par_lpost lpreL lpostL lpreR lpostR)

  | Weaken:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post:post st a ->
    #lpre:l_pre pre ->
    #lpost:l_post pre post ->
    #wlpre:l_pre pre ->
    #wlpost:l_post pre post ->
    #_:squash
      ((forall h. wlpre h ==> lpre h) /\
       (forall h0 x h1. lpost h0 x h1 ==> wlpost h0 x h1)) ->
    m st a pre post lpre lpost ->
    m st a pre post wlpre wlpost

(**** End definition of the computation AST ****)


(**** Stepping relation ****)

/// All steps preserve frames

noeq
type step_result (#st:st) (a:Type u#a) (q:post st a) =
  | Step:
    next_pre:st.hprop ->
    lpre:l_pre next_pre ->
    lpost:l_post next_pre q ->
    m st a next_pre q lpre lpost ->
    nat ->
    step_result a q


(**** Type of the single-step interpreter ****)


/// Interpreter is setup as a Div function from computation trees to computation trees
///
/// While the requires for the Div is standard (that the expects hprop holds and requires is valid),
///   the ensures is interesting
///
/// As the computation evolves, the requires and ensures associated with the computation graph nodes
///   also evolve
/// But they evolve systematically: preconditions become weaker and postconditions become stronger
///
/// Consider { req } c | st { ens }  ~~> { req1 } c1 | st1 { ens1 }
///
/// Then, req st ==> req1 st1  /\
///       (forall x st_final. ens1 st1 x st_final ==> ens st x st_final)


unfold
let step_req (#st:st)
  (#a:Type u#a) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost)
: st.mem -> Type0
= fun m0 ->
  st.interp (st.locks_invariant m0 `st.star` pre) (st.heap_of_mem m0) /\
  lpre (st.heap_of_mem m0)

let weaker_pre (#st:st)
  (#pre:st.hprop) (lpre:l_pre pre)
  (#next_pre:st.hprop) (next_lpre:l_pre next_pre)
  (m0 m1:st.mem)
= lpre (st.heap_of_mem m0) ==> next_lpre (st.heap_of_mem m1)

let stronger_post (#st:st) (#a:Type u#a)
  (#pre:st.hprop) (#post:post st a)
  (lpost:l_post pre post)
  (#next_pre:st.hprop) (next_lpost:l_post next_pre post)
  (m0 m1:st.mem)
= forall (x:a) (h_final:st.heap).
    next_lpost (st.heap_of_mem m1) x h_final ==>
    lpost (st.heap_of_mem m0) x h_final
    
unfold
let step_ens (#st:st)
  (#a:Type u#a) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost)
: st.mem -> step_result a post -> st.mem -> Type0
= fun m0 r m1 ->
  let Step next_pre next_lpre next_lpost _ _ = r in
  next_lpre (st.heap_of_mem m1) /\
  st.interp (st.locks_invariant m1 `st.star` next_pre) (st.heap_of_mem m1) /\
  preserves_frame pre next_pre m0 m1 /\
  weaker_pre lpre next_lpre m0 m1 /\
  stronger_post lpost next_lpost m0 m1


/// The type of the stepping function

type step_t =
  #st:st -> i:nat ->
  #a:Type u#a ->
  #pre:st.hprop -> #post:post st a -> #lpre:l_pre pre -> #lpost:l_post pre post ->
  f:m st a pre post lpre lpost ->
  MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)


(**** Auxiliary lemmas ****)

/// Some AC lemmas on `st.star`

let equals_ext_right (#st:st) (p q r:st.hprop)
: Lemma
  (requires q `st.equals` r)
  (ensures (p `st.star` q) `st.equals` (p `st.star` r))
= calc (st.equals) {
    p `st.star` q;
       (st.equals) { }
    q `st.star` p;
       (st.equals) { }
    r `st.star` p;
       (st.equals) { }
    p `st.star` r;
  }

let commute_star_right (#st:st) (p q r:st.hprop)
: Lemma
  ((p `st.star` (q `st.star` r)) `st.equals`
   (p `st.star` (r `st.star` q)))
= calc (st.equals) {
    p `st.star` (q `st.star` r);
       (st.equals) { equals_ext_right p (q `st.star` r) (r `st.star` q) }
    p `st.star` (r `st.star` q);
  }

let assoc_star_right (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` ((q `st.star` r) `st.star` s)) `st.equals`
   (p `st.star` (q `st.star` (r `st.star` s))))
= calc (st.equals) {
    p `st.star` ((q `st.star` r) `st.star` s);
       (st.equals) { equals_ext_right p ((q `st.star` r) `st.star` s)
                                        (q `st.star` (r `st.star` s)) }
    p `st.star` (q `st.star` (r `st.star` s));
  }

let commute_assoc_star_right (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` ((q `st.star` r) `st.star` s)) `st.equals`
   (p `st.star` (r `st.star` (q `st.star` s))))
= calc (st.equals) {
    p `st.star` ((q `st.star` r) `st.star` s);
       (st.equals) { equals_ext_right p
                       ((q `st.star` r) `st.star` s)
                       ((r `st.star` q) `st.star` s) }
    p `st.star` ((r `st.star` q) `st.star` s);
       (st.equals) { assoc_star_right p r q s }
    p `st.star` (r `st.star` (q `st.star` s));
  }


/// Apply extensionality manually, control proofs

let apply_interp_ext (#st:st) (p q:st.hprop) (m:st.mem)
: Lemma
  (requires
    st.interp p (st.heap_of_mem m) /\
    p `st.equals` q)
  (ensures st.interp q (st.heap_of_mem m))
= ()

let weaken_fp_prop (#st:st) (frame frame':st.hprop) (m0 m1:st.mem)
: Lemma
  (requires
    forall (f_frame:fp_prop (frame `st.star` frame')).
      f_frame (st.heap_of_mem m0) <==>
      f_frame (st.heap_of_mem m1))
   (ensures
    forall (f_frame:fp_prop frame').
      f_frame (st.heap_of_mem m0) <==>
      f_frame (st.heap_of_mem m1))
= ()


/// Lemmas about preserves_frame

let preserves_frame_trans (#st:st)
  (hp1 hp2 hp3:st.hprop) (m1 m2 m3:st.mem)
: Lemma
  (requires
    preserves_frame hp1 hp2 m1 m2 /\
    preserves_frame hp2 hp3 m2 m3)
  (ensures preserves_frame hp1 hp3 m1 m3)
= ()

#push-options "--z3rlimit 40"
let preserves_frame_star (#st:st) (pre post:st.hprop) (m0 m1:st.mem) (frame:st.hprop)
: Lemma
  (requires preserves_frame pre post m0 m1)
  (ensures preserves_frame (pre `st.star` frame) (post `st.star` frame) m0 m1)
= let aux (frame':st.hprop)
    : Lemma
      (requires
        st.interp (st.locks_invariant m0 `st.star` ((pre `st.star` frame) `st.star` frame')) (st.heap_of_mem m0))
      (ensures
        st.interp (st.locks_invariant m1 `st.star` ((post `st.star` frame) `st.star` frame')) (st.heap_of_mem m1) /\
        (forall (f_frame:fp_prop frame'). f_frame (st.heap_of_mem m0) <==> f_frame (st.heap_of_mem m1)))
    = assoc_star_right (st.locks_invariant m0) pre frame frame';
      apply_interp_ext
        (st.locks_invariant m0 `st.star` ((pre `st.star` frame) `st.star` frame'))
        (st.locks_invariant m0 `st.star` (pre `st.star` (frame `st.star` frame')))
        m0;
      assoc_star_right (st.locks_invariant m1) post frame frame';
      apply_interp_ext
        (st.locks_invariant m1 `st.star` (post `st.star` (frame `st.star` frame')))
        (st.locks_invariant m1 `st.star` ((post `st.star` frame) `st.star` frame'))
        m1;
      weaken_fp_prop frame frame' m0 m1
  in
  Classical.forall_intro (Classical.move_requires aux)

let preserves_frame_star_left (#st:st) (pre post:st.hprop) (m0 m1:st.mem) (frame:st.hprop)
: Lemma
  (requires preserves_frame pre post m0 m1)
  (ensures preserves_frame (frame `st.star` pre) (frame `st.star` post) m0 m1)
= let aux (frame':st.hprop)
    : Lemma
      (requires
        st.interp (st.locks_invariant m0 `st.star` ((frame `st.star` pre) `st.star` frame')) (st.heap_of_mem m0))
      (ensures
        st.interp (st.locks_invariant m1 `st.star` ((frame `st.star` post) `st.star` frame')) (st.heap_of_mem m1) /\
        (forall (f_frame:fp_prop frame'). f_frame (st.heap_of_mem m0) <==> f_frame (st.heap_of_mem m1)))
    = commute_assoc_star_right (st.locks_invariant m0) frame pre frame';
      apply_interp_ext
        (st.locks_invariant m0 `st.star` ((frame `st.star` pre) `st.star` frame'))
        (st.locks_invariant m0 `st.star` (pre `st.star` (frame `st.star` frame')))
        m0;
      commute_assoc_star_right (st.locks_invariant m1) frame post frame';
      apply_interp_ext
        (st.locks_invariant m1 `st.star` (post `st.star` (frame `st.star` frame')))
        (st.locks_invariant m1 `st.star` ((frame `st.star` post) `st.star` frame'))
        m1;
      weaken_fp_prop frame frame' m0 m1
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options


/// Lemma frame_post_for_par is used in the par proof
///
/// E.g. in the par rule, when L takes a step, we can frame the requires of R
///   by using the preserves_frame property of the stepping relation
///
/// However we also need to frame the ensures of R, for establishing stronger_post
///
/// Basically, we need:
///
/// forall x h_final. postR prev_state x h_final <==> postR next_state x h_final
///
/// (the proof only requires the reverse implication, but we can prove iff)
///
/// To prove this, we rely on the framing of all frame fp props provides by the stepping relation
///
/// To use it, we instantiate the fp prop with inst_heap_prop_for_par

let inst_heap_prop_for_par (#st:st) (#a:Type) (#pre:st.hprop) (#post:post st a)
  (lpost:l_post pre post)
  (state:st.mem)
: fp_prop pre
= fun h ->
  forall x final_state. lpost h x final_state <==>
                   lpost (st.heap_of_mem state) x final_state

let frame_post_for_par_tautology (#st:st)
  (#a:Type) (#pre_f:st.hprop) (#post_f:post st a) (lpost_f:l_post pre_f post_f)
  (m0:st.mem)
: Lemma (inst_heap_prop_for_par lpost_f m0 (st.heap_of_mem m0))
= ()

let frame_post_for_par_aux (#st:st)
  (pre_s post_s:st.hprop) (m0 m1:st.mem)
  (#a:Type) (#pre_f:st.hprop) (#post_f:post st a) (lpost_f:l_post pre_f post_f)
: Lemma
  (requires
    preserves_frame pre_s post_s m0 m1 /\
    st.interp (st.locks_invariant m0 `st.star` (pre_s `st.star` pre_f)) (st.heap_of_mem m0))
  (ensures
    inst_heap_prop_for_par lpost_f m0 (st.heap_of_mem m0) <==>
    inst_heap_prop_for_par lpost_f m0 (st.heap_of_mem m1))
= ()

let frame_post_for_par (#st:st)
  (pre_s post_s:st.hprop) (m0 m1:st.mem)
  (#a:Type) (#pre_f:st.hprop) (#post_f:post st a) (lpre_f:l_pre pre_f) (lpost_f:l_post pre_f post_f)
: Lemma
  (requires
    preserves_frame pre_s post_s m0 m1 /\
    st.interp (st.locks_invariant m0 `st.star` (pre_s `st.star` pre_f)) (st.heap_of_mem m0))
  (ensures
    (lpre_f (st.heap_of_mem m0) <==> lpre_f (st.heap_of_mem m1)) /\
    (forall (x:a) (final_state:st.heap).
       lpost_f (st.heap_of_mem m0) x final_state <==>
       lpost_f (st.heap_of_mem m1) x final_state))
= frame_post_for_par_tautology lpost_f m0;
  frame_post_for_par_aux pre_s post_s m0 m1 lpost_f


/// Finally lemmas for proving that in the par rules preconditions get weaker
///   and postconditions get stronger

let par_weaker_pre_and_stronger_post_l (#st:st) (#preL:st.hprop) (lpreL:l_pre preL)
  (#aL:Type) (#postL:post st aL) (lpostL:l_post preL postL)
  (#next_preL:st.hprop) (next_lpreL:l_pre next_preL) (next_lpostL:l_post next_preL postL)
  (#preR:st.hprop) (lpreR:l_pre preR)
  (#aR:Type) (#postR:post st aR) (lpostR:l_post preR postR)
  (state next_state:st.mem)
: Lemma
  (requires
    weaker_pre lpreL next_lpreL state next_state /\
    stronger_post lpostL next_lpostL state next_state /\
    preserves_frame preL next_preL state next_state /\
    lpreL (st.heap_of_mem state) /\
    lpreR (st.heap_of_mem state) /\
    st.interp (st.locks_invariant state `st.star` (preL `st.star` preR)) (st.heap_of_mem state))
  (ensures
    weaker_pre
      (par_lpre lpreL lpreR)
      (par_lpre next_lpreL lpreR)
      state next_state /\
    stronger_post
      (par_lpost lpreL lpostL lpreR lpostR)
      (par_lpost next_lpreL next_lpostL lpreR lpostR)
      state next_state)
= frame_post_for_par preL next_preL state next_state lpreR lpostR;
  assert (weaker_pre (par_lpre lpreL lpreR) (par_lpre next_lpreL lpreR) state next_state) by
    (norm [delta_only [`%weaker_pre; `%par_lpre] ])

let par_weaker_pre_and_stronger_post_r (#st:st) (#preL:st.hprop) (lpreL:l_pre preL)
  (#aL:Type) (#postL:post st aL) (lpostL:l_post preL postL)
  (#preR:st.hprop) (lpreR:l_pre preR)
  (#aR:Type) (#postR:post st aR) (lpostR:l_post preR postR)
  (#next_preR:st.hprop) (next_lpreR:l_pre next_preR)
  (next_lpostR:l_post next_preR postR)
  (state next_state:st.mem)
: Lemma
  (requires
    weaker_pre lpreR next_lpreR state next_state /\
    stronger_post lpostR next_lpostR state next_state /\
    preserves_frame preR next_preR state next_state /\
    lpreR (st.heap_of_mem state) /\
    lpreL (st.heap_of_mem state) /\
    st.interp (st.locks_invariant state `st.star` (preL `st.star` preR)) (st.heap_of_mem state))
  (ensures
    st.interp (st.locks_invariant next_state `st.star` (preL `st.star` next_preR)) (st.heap_of_mem next_state) /\
    weaker_pre
      (par_lpre lpreL lpreR)
      (par_lpre lpreL next_lpreR)
      state next_state /\
    stronger_post
      (par_lpost lpreL lpostL lpreR lpostR)
      (par_lpost lpreL lpostL next_lpreR next_lpostR)
      state next_state)
= commute_star_right (st.locks_invariant state) preL preR;
  apply_interp_ext
    (st.locks_invariant state `st.star` (preL `st.star` preR))
    (st.locks_invariant state `st.star` (preR `st.star` preL))
    state;
  frame_post_for_par preR next_preR state next_state lpreL lpostL;
  assert (weaker_pre (par_lpre lpreL lpreR) (par_lpre lpreL next_lpreR) state next_state) by
    (norm [delta_only [`%weaker_pre; `%par_lpre] ]);
  commute_star_right (st.locks_invariant next_state) next_preR preL;
  apply_interp_ext
    (st.locks_invariant next_state `st.star` (next_preR `st.star` preL))
    (st.locks_invariant next_state `st.star` (preL `st.star` next_preR))
    next_state

(**** Begin stepping functions ****)

let step_ret (#st:st) (i:nat) (#a:Type u#a)
  (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost{Ret? f})

: MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)

= MST?.reflect (fun m0 ->
    let Ret p x lp = f in
    Step (p x) lpre lpost f i, m0)

let lpost_ret_act (#st:st) (#a:Type) (#pre:st.hprop) (#post:post st a) (lpost:l_post pre post)
  (x:a) (state:st.mem)
: l_post (post x) post
= fun _ x h1 -> lpost (st.heap_of_mem state) x h1

let step_act (#st:st) (#a:Type u#a) (i:nat)
  (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost{Act? f})

: MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)

= let m0 = MST.get st.mem st.locks_preorder () in

  let Act #_ #_ #_ #_ #_ #_ f = f in  

  let x = f () in

  let lpost : l_post (post x) post = lpost_ret_act lpost x m0 in

  Step (post x) (fun h -> lpost h x h) lpost (Ret post x lpost) i

let step_bind_ret (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost{Bind? f /\ Ret? (Bind?.f f)})
  (step:step_t)

: MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)

= MST?.reflect (fun m0 ->
    match f with
    | Bind #_ #_ #_ #_ #_ #_ #_ #_ #lpre_b #lpost_b (Ret p x _) g ->  
      Step (p x) (lpre_b x) (lpost_b x) (g x) i, m0)

let step_bind (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost{Bind? f})
  (step:step_t)

: MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)

= match f with
  | Bind (Ret _ _ _) _ -> step_bind_ret i f step

  | Bind #_ #b #pre_a #post_a #lpre_a #lpost_a #a #_ #lpre_b #lpost_b f g ->
    let Step next_pre next_lpre next_lpost f j = step i f in

    let m1 = MST.get st.mem st.locks_preorder () in

    assert ((bind_lpre next_lpre next_lpost lpre_b) (st.heap_of_mem m1))
      by norm ([delta_only [`%bind_lpre]]);

    let f : m st a next_pre post _ _ =
      Bind #st #b #next_pre #post_a #next_lpre #next_lpost #a #post #lpre_b #lpost_b f g in

    Step next_pre
      (bind_lpre next_lpre next_lpost lpre_b)
      (bind_lpost next_lpre next_lpost lpost_b)
      f
      j


let step_frame_ret (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#p:post st a) (#lpre:l_pre pre) (#lpost:l_post pre p)
  (f:m st a pre p lpre lpost{Frame? f /\ Ret? (Frame?.f f)})
  (step:step_t)

: MST (step_result a p) st.mem st.locks_preorder (step_req f) (step_ens f)

= MST?.reflect (fun m0 ->
    match f with  
    | Frame (Ret p x lp) frame f_frame ->
      Step (p x `st.star` frame)
        (fun h -> lpost h x h)
        lpost
        (Ret (fun x -> p x `st.star` frame) x lpost)
        i, m0)


let step_frame (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#p:post st a) (#lpre:l_pre pre) (#lpost:l_post pre p)
  (f:m st a pre p lpre lpost{Frame? f})
  (step:step_t)

: MST (step_result a p) st.mem st.locks_preorder (step_req f) (step_ens f)

= match f with  
  | Frame (Ret p x lp) frame f_frame -> step_frame_ret i f step

  | Frame #_ #_ #f_pre #_ #f_lpre #f_lpost f frame f_frame ->
    let m0 = MST.get st.mem st.locks_preorder () in
    
    let Step next_fpre next_flpre next_flpost f j = step i f in

    let m1 = MST.get st.mem st.locks_preorder () in

    preserves_frame_star f_pre next_fpre m0 m1 frame;

    assert ((frame_lpre next_flpre f_frame) (st.heap_of_mem m1))
      by (norm [delta_only [`%frame_lpre]]);
    assert (st.interp (st.locks_invariant m1 `st.star` (next_fpre `st.star` frame))
                      (st.heap_of_mem m1));

    Step (next_fpre `st.star` frame)
      (frame_lpre next_flpre f_frame)
      (frame_lpost next_flpre next_flpost f_frame)
      (Frame f frame f_frame)
      j


/// Stream of booleans to decide whether we go left or right

assume val go_left : nat -> bool

let step_par_ret (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost{Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f)})
  (step:step_t)

: MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)

= MST?.reflect (fun m0 ->
  match f with
  | Par #_ #aL #_ #_ #_ #_ (Ret pL xL lpL) #aR #_ #_ #_ #_ (Ret pR xR lpR) ->

    let lpost : l_post #st #(aL & aR) _ _ = fun h0 (xL, xR) h1 -> lpL h0 xL h1 /\ lpR h0 xR h1 in

    Step (pL xL `st.star` pR xR)
      (fun h -> lpL h xL h /\ lpR h xR h)
      lpost 
      (Ret (fun (xL, xR) -> pL xL `st.star` pR xR) (xL, xR) lpost)
      i, m0)


let step_par (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost{Par? f})
  (step:step_t)

: MST (step_result a post) st.mem st.locks_preorder (step_req f) (step_ens f)

= match f with
  | Par (Ret _ _ _) (Ret _ _ _) -> step_par_ret i f step

  | Par #_ #aL #preL #postL #lpreL #lpostL mL #aR #preR #postR #lpreR #lpostR mR ->
    if go_left i then begin
      let m0 = MST.get st.mem st.locks_preorder () in

      let Step next_preL next_lpreL next_lpostL mL j = step (i + 1) mL in

      let m1 = MST.get st.mem st.locks_preorder () in

      preserves_frame_star preL next_preL m0 m1 preR;
      par_weaker_pre_and_stronger_post_l lpreL lpostL next_lpreL next_lpostL lpreR lpostR m0 m1;

      Step (next_preL `st.star` preR)
        (par_lpre next_lpreL lpreR)
        (par_lpost next_lpreL next_lpostL lpreR lpostR)
        (Par mL mR)
        j

    end
    else begin
      let m0 = MST.get st.mem st.locks_preorder () in

      let Step next_preR next_lpreR next_lpostR mR j = step (i + 1) mR in

      let m1 = MST.get st.mem st.locks_preorder () in

      preserves_frame_star_left preR next_preR m0 m1 preL;
      par_weaker_pre_and_stronger_post_r lpreL lpostL lpreR lpostR next_lpreR next_lpostR m0 m1;

      Step (preL `st.star` next_preR)
        (par_lpre lpreL next_lpreR)
        (par_lpost lpreL lpostL next_lpreR next_lpostR)
        (Par mL mR)
        j
    end


// // // let step_weaken (#st:st) (i:nat) (#a:Type u#a)
// // //   (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
// // //   (f:m st a pre post lpre lpost{Weaken? f})
// // //   (state:st.mem)

// // // : Div (step_result a post) (step_req f state) (step_ens f state)

// // // = let Weaken #_ #_ #pre #post #lpre #lpost #_ #_ #_ f = f in

// // //   Step pre state pre state lpre lpost f i


// // // /// Step function

// // // let rec step (#st:st) (i:nat) (#a:Type u#a)
// // //   (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
// // //   (f:m st a pre post lpre lpost)
// // //   (state:st.mem)
// // // : Div (step_result a post)
// // //   (step_req f state)
// // //   (step_ens f state)
// // // = match f with
// // //   | Ret _ _ _ -> step_ret i f state
// // //   | Bind _ _ -> step_bind i f state step
// // //   | Act _ -> step_act i f state
// // //   | Frame _ _ _ -> step_frame i f state step
// // //   | Par _ _ -> step_par i f state step
// // //   | Weaken _ -> step_weaken i f state

// // // let rec run (#st:st) (i:nat) (#a:Type u#a) (#pre:st.hprop) (#post:post st a)
// // //   (#lpre:l_pre pre) (#lpost:l_post pre post)
// // //   (f:m st a pre post lpre lpost)
// // //   (state:st.mem)
// // // : Div (a & st.mem)
// // //   (requires
// // //     st.interp (st.locks_invariant state `st.star` pre) (st.heap_of_mem state) /\
// // //     lpre (st.heap_of_mem state))
// // //   (ensures fun (x, new_state) ->
// // //     st.interp (st.locks_invariant new_state `st.star` post x) (st.heap_of_mem new_state) /\
// // //     lpost (st.heap_of_mem state) x (st.heap_of_mem new_state) /\
// // //     preserves_frame pre (post x) state new_state)
// // // = match f with
// // //   | Ret _ x _ -> x, state

// // //   | _ ->
// // //     let Step _ _ new_pre new_state _ _ f j = step i f state in
// // //     let (x, final_state) = run j f new_state in
// // //     preserves_frame_trans pre new_pre (post x) state new_state final_state;
// // //     (x, final_state)


// // // // // (**** Trying to define the layered effect ****)

// // // // // type repr (a:Type) (st:st) (pre:st.hprop) (post:post st a) (lpre:l_pre pre) (lpost:l_post pre post)
// // // // // = unit -> m st a pre post lpre lpost


// // // // // /// This will not be allowed currently as the extra binders must appear before x in the implementation, can change

// // // // // let return (a:Type) (st:st) (post:post st a) (lpost:(x:a -> l_post (post x) post)) (x:a)
// // // // // : repr a st (post x) post (fun h -> (lpost x) h x h) (lpost x)
// // // // // = fun _ -> Ret post x (lpost x)

// // // // // let bind (a:Type) (b:Type) (st:st)
// // // // //   (pre_f:st.hprop) (post_f:post st a) (lpre_f:l_pre pre_f) (lpost_f:l_post pre_f post_f)
// // // // //   (post_g:post st b) (lpre_g:(x:a -> l_pre (post_f x))) (lpost_g:(x:a -> l_post (post_f x) post_g))
// // // // //   (f:repr a st pre_f post_f lpre_f lpost_f)
// // // // //   (g:(x:a -> repr b st (post_f x) post_g (lpre_g x) (lpost_g x)))
// // // // // : repr b st pre_f post_g
// // // // //     (bind_lpre lpre_f lpost_f lpre_g)
// // // // //     (bind_lpost lpre_f lpost_f lpost_g)
// // // // // = fun _ -> Bind (f ()) (fun x -> g x ())

// // // // // let subcomp (a:Type) (st:st)
// // // // //   (pre:st.hprop) (post:post st a)
// // // // //   (lpre_f:l_pre pre) (lpost_f:l_post pre post)
// // // // //   (lpre_g:l_pre pre) (lpost_g:l_post pre post)
// // // // //   (f:repr a st pre post lpre_f lpost_f)
// // // // // : Pure (repr a st pre post lpre_g lpost_g)
// // // // //   (requires
// // // // //     (forall h. lpre_g h ==> lpre_f h) /\
// // // // //     (forall h0 x h1. lpost_f h0 x h1 ==> lpost_g h0 x h1))
// // // // //   (ensures fun _ -> True)
// // // // // = fun _ -> Weaken #_ #a #pre #post #lpre_f #lpost_f #lpre_g #lpost_g #() (f ())
