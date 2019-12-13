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
#push-options "--using_facts_from '-* +Prims +FStar.Pervasives +Steel.Semantics' --max_fuel 0 --max_ifuel 2 --initial_ifuel 2"

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
  //(forall h0 h1. q h0 /\ disjoint h0 h1 ==> q (join h0 h1))
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
    (* refinement *)
    weaken_depends_only_on st /\
    refine_equiv st /\
    refine_star st /\
    (* Relations between mem and heap *)
    m_implies_disjoint st /\
    mem_valid_locks_invariant st /\
    valid_upd_heap st

let st = s:st0 { st_laws s }

let equals_ext_right (#st:st) (p q r:st.hprop) : Lemma
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


let commute4_1_2_3 (#st:st) (p q r s:st.hprop)
  : Lemma (
     ((p `st.star` q) `st.star` (r `st.star` s)) `st.equals`
     ((s `st.star` p) `st.star` (q `st.star` r))
   )
   = calc (st.equals) {
        (p `st.star` q) `st.star` (r `st.star` s);
           (st.equals) { }
        p `st.star` (q `st.star` (r `st.star` s));
           (st.equals) {
             calc (st.equals) {
               q `st.star` (r `st.star` s);
                 (st.equals) { equals_ext_right q (r `st.star` s) (s `st.star` r) }
               s `st.star` (q `st.star` r);
             };
             equals_ext_right p
                 (q `st.star` (r `st.star` s))
                 (s `st.star` (q `st.star` r))
           }
        p `st.star` (s `st.star` (q `st.star` r));
          (st.equals) { }
        (p `st.star` s) `st.star` (q `st.star` r);
          (st.equals) { }
        (s `st.star` p) `st.star` (q `st.star` r);
     }


let refine_star_left (#st:st) (r0 r1:st.hprop) (p:fp_prop r0) (s:st.mem)
  : Lemma
    ((st.interp (r0 `st.star` r1) (st.heap_of_mem s) /\
      p (st.heap_of_mem s)) <==>
      st.interp (st.refine r0 p `st.star` r1) (st.heap_of_mem s))
   = assert (st.interp (st.refine (r0 `st.star` r1) p) (st.heap_of_mem s) <==>
                        st.interp (st.refine r0 p `st.star` r1) (st.heap_of_mem s))

let refine_middle (#st:st) (p q r:st.hprop) (fq:fp_prop q) (state:st.mem)
  : Lemma
    ((st.interp (p `st.star` (q `st.star` r)) (st.heap_of_mem state) /\
      fq (st.heap_of_mem state)) <==>
      st.interp (p `st.star` (st.refine q fq `st.star` r)) (st.heap_of_mem state))
  =   calc (st.equals) {
        p `st.star` (q `st.star` r);
          (st.equals) { }
        (p `st.star` q) `st.star` r;
          (st.equals) { }
        (q `st.star` p) `st.star` r;
          (st.equals) { }
        q `st.star` (p `st.star` r);
      };
      refine_star_left q (p `st.star` r) fq state;
      calc (st.equals) {
        (st.refine q fq) `st.star` (p `st.star` r);
          (st.equals) { }
        (st.refine q fq `st.star` p) `st.star` r;
          (st.equals) { }
        (p `st.star` st.refine q fq) `st.star` r;
          (st.equals) { }
        p `st.star` (st.refine q fq `st.star` r);
      }

let commute4_middle (#st:st) (p q r s:st.hprop)
  : Lemma (
     ((p `st.star` q) `st.star` (r `st.star` s)) `st.equals`
     (p `st.star` (q `st.star` r) `st.star` s))
  = calc (st.equals) {
      (p `st.star` q) `st.star` (r `st.star` s);
         (st.equals) { }
       p `st.star` (q `st.star` (r `st.star` s));
         (st.equals) { }
      (q `st.star` (r `st.star` s)) `st.star` p;
         (st.equals) { }
      ((q `st.star` r) `st.star` s) `st.star` p;
         (st.equals) { }
      p `st.star` (q `st.star` r) `st.star` s;
    }

let commute4_2_3_1 (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` (q `st.star` (r `st.star` s))) `st.equals`
   (p `st.star` ((q `st.star` r) `st.star` s)))
= calc (st.equals) {
    p `st.star` (q `st.star` (r `st.star` s));
       (st.equals) { }
    (q `st.star` (r `st.star` s)) `st.star` p;
       (st.equals) { }
    ((q `st.star` r) `st.star` s) `st.star` p;
       (st.equals) { }
    p `st.star` ((q `st.star` r) `st.star` s);
  }

let commute3_1_2 (#st:st) (p q r:st.hprop)
  : Lemma
    ((p `st.star` (q `st.star` r))  `st.equals`
     (q `st.star` (p `st.star` r)))
  =  calc (st.equals) {
        p `st.star` (q `st.star` r);
          (st.equals) { }
        (p `st.star` q) `st.star` r;
          (st.equals) { }
        (q `st.star` p) `st.star` r;
          (st.equals) { }
        q `st.star` (p `st.star` r);
      }

let commute3_2_1_interp (#st:st) (p q r:st.hprop) state
  : Lemma
    (st.interp (st.locks_invariant state `st.star` (p `st.star` (q `st.star` r))) (st.heap_of_mem state) <==>
     st.interp (st.locks_invariant state `st.star` ((p `st.star` q) `st.star` r)) (st.heap_of_mem state))
  = commute4_2_3_1 (st.locks_invariant state) p q r

let commute4_3_2_1 (#st:st) (p q r s:st.hprop)
: Lemma ((q `st.star` ((s `st.star` p) `st.star` r)) `st.equals`
         (s `st.star` ((q `st.star` p) `st.star` r)))
= calc (st.equals) {
    q `st.star` ((s `st.star` p) `st.star` r);
       (st.equals) { equals_ext_right q ((s `st.star` p) `st.star` r) (s `st.star` (p `st.star` r)) }
    q `st.star` (s `st.star` (p `st.star` r));
       (st.equals) { }
    (q `st.star` s) `st.star` (p `st.star` r);
       (st.equals) { }
    (s `st.star` q) `st.star` (p `st.star` r);
       (st.equals) { }
    s `st.star` (q `st.star` (p `st.star` r));
       (st.equals) { equals_ext_right s (q `st.star` (p `st.star` r)) ((q `st.star` p) `st.star` r) }
    s `st.star` ((q `st.star` p) `st.star` r);
  }

let commute3_2_1_refine_middle_interp (#st:st) (p q r:st.hprop) (fq:fp_prop q) state
: Lemma (st.interp (st.locks_invariant state `st.star` (p `st.star` (st.refine q fq `st.star` r))) (st.heap_of_mem state) <==>
         (fq (st.heap_of_mem state) /\
          st.interp (st.locks_invariant state `st.star` ((q `st.star` p) `st.star` r)) (st.heap_of_mem state)))
= calc (st.equals) {
    st.locks_invariant state `st.star` (p `st.star` (st.refine q fq `st.star` r));
       (st.equals) { }
    (st.locks_invariant state `st.star` p) `st.star` (st.refine q fq `st.star` r);
       (st.equals) { equals_ext_right (st.locks_invariant state `st.star` p) (st.refine q fq `st.star` r) (r `st.star` st.refine q fq) }
    (st.locks_invariant state `st.star` p) `st.star` (r `st.star` st.refine q fq);
       (st.equals) { }
    ((st.locks_invariant state `st.star` p) `st.star` r) `st.star` st.refine q fq;
       (st.equals) { }
    st.refine q fq `st.star` ((st.locks_invariant state `st.star` p) `st.star` r);
  };
  
  refine_star_left q ((st.locks_invariant state `st.star` p) `st.star` r) fq state;

  commute4_3_2_1 p q r (st.locks_invariant state)


(** [post a c] is a postcondition on [a]-typed result *)
let post (st:st) (a:Type) = a -> st.hprop

let hheap (#st:st) (fp:st.hprop) = fp_heap_0 st.interp fp

let hmem (#st:st) (fp:st.hprop) = m:st.mem{st.interp (st.locks_invariant m `st.star` fp) (st.heap_of_mem m)}


/// We now define the notion of depends_only_on for two state postconditions
/// 
/// Essentially the postconditions are (heap -> a -> heap -> prop) functions,
///   where in the first heap argument, they depend only on the expects hprop fp
///   and in the second heap argument, they depend only on the provides hprop fp


let depends_only_on_0_2 (#a:Type) (#heap:Type) (#hprop:Type)
  (interp:hprop -> heap -> prop)
  (disjoint:heap -> heap -> prop)
  (join:(h0:heap -> h1:heap{disjoint h0 h1} -> heap))
  (q:heap -> a -> heap -> prop) (fp_pre:hprop) (fp_post:a -> hprop) =

  //can join any disjoint heap to the pre-heap and q is still valid
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


let weaken_depends_only_on2_pre_right (#st:st) (#a:Type) (q:st.heap -> a -> st.heap -> prop)
  (fp_pre:st.hprop) (fp_post:a -> st.hprop)
  (fp:st.hprop)
: Lemma
  (requires depends_only_on2 q fp_pre fp_post)
  (ensures depends_only_on2 q (fp_pre `st.star` fp) fp_post)
= ()

let weaken_depends_only_on2_pre_left (#st:st) (#a:Type) (q:st.heap -> a -> st.heap -> prop)
  (fp_pre:st.hprop) (fp_post:a -> st.hprop)
  (fp:st.hprop)
: Lemma
  (requires depends_only_on2 q fp_pre fp_post)
  (ensures depends_only_on2 q (fp `st.star` fp_pre) fp_post)
= ()


/// Now the types for pre- and postconditions for the hoare-style specs


let l_pre (#st:st) (pre:st.hprop) = fp_prop pre

let l_post (#st:st) (#a:Type) (pre:st.hprop) (post:post st a) = fp_prop2 pre post


(**** The interface of actions ****)

let action0 (#st:st) (fp:st.hprop) (a:Type) (fp':a -> st.hprop) =
  hmem fp -> (x:a & hmem (fp' x))

let is_frame_preserving (#st:st) #a #fp #fp' (f:action0 fp a fp') =
  forall frame (h0:hmem (fp `st.star` frame)).  //we don't need locks_invariant for h0?
    (let (| x, h1 |) = f h0 in
     st.interp (fp' x `st.star` frame `st.star` st.locks_invariant h1) (st.heap_of_mem h1) /\
     (forall (b:Type0) (post:post st b) (lpost:l_post frame post).
        (forall x h2. lpost (st.heap_of_mem h0) x h2 <==> lpost (st.heap_of_mem h1) x h2)))

let action_depends_only_on_fp (#st:st) (#pre:st.hprop) #a #post (f:action0 pre a post)
  = forall (m0:hmem pre)
      (h1:st.heap {st.m_disjoint m0 h1})
      (post: (x:a -> fp_prop (post x))).
      (let m1 = st.upd_joined_heap m0 h1 in
       let (| x0, m |) = f m0 in
       let (| x1, m' |) = f m1 in
       x0 == x1 /\
       (post x0 (st.heap_of_mem m) <==> post x1 (st.heap_of_mem m')))

let action_t (#st:st) (fp:st.hprop) (a:Type) (fp':a -> st.hprop) =
  f:action0 fp a fp'{
    is_frame_preserving f /\
    action_depends_only_on_fp f
  }


(**** Begin definition of the computation AST ****)

/// Gadgets for building lpre- and lpostconditions for various nodes

let return_lpre (#st:st) (#a:Type0) (#post:post st a) (x:a) (lpost:l_post (post x) post)
: l_pre (post x)
= fun h -> lpost h x h


/// Actions don't have a separate logical payload

let action_lpre (#st:st) (#a:Type0) (#pre:st.hprop) (#post:post st a) (_:action_t pre a post)
: l_pre pre
= st.interp pre

let action_lpost (#st:st) (#a:Type0) (#pre:st.hprop) (#post:post st a) (_:action_t pre a post)
: l_post pre post
= fun h0 x h1 -> st.interp (post x) h1


let frame_lpre (#st:st) (#pre:st.hprop) (lpre:l_pre pre) (#frame:st.hprop) (f_frame:fp_prop frame)
: l_pre (pre `st.star` frame)
= fun h -> lpre h /\ f_frame h

let frame_lpost (#st:st) (#a:Type0) (#pre:st.hprop) (#post:post st a) (lpre:l_pre pre) (lpost:l_post pre post)
  (#frame:st.hprop) (f_frame:fp_prop frame)
: l_post (pre `st.star` frame) (fun x -> post x `st.star` frame)
= fun h0 x h1 -> lpre h0 /\ lpost h0 x h1 /\ f_frame h1


let bind_lpre (#st:st) (#a:Type0) (#pre:st.hprop) (#post_a:post st a)
  (lpre_a:l_pre pre) (lpost_a:l_post pre post_a)
  (lpre_b:(x:a -> l_pre (post_a x)))
: l_pre pre
= fun h -> lpre_a h /\ (forall (x:a) h1. lpost_a h x h1 ==> lpre_b x h1)

let bind_lpost (#st:st) (#a:Type0) (#pre:st.hprop) (#post_a:post st a)
  (lpre_a:l_pre pre) (lpost_a:l_post pre post_a)
  (#b:Type0) (#post_b:post st b)
  (lpost_b:(x:a -> l_post (post_a x) post_b))
: l_post pre post_b
= fun h0 y h2 -> lpre_a h0 /\ (exists x h1. lpost_a h0 x h1 /\ (lpost_b x) h1 y h2)


let par_lpre (#st:st) (#preL:st.hprop) (lpreL:l_pre preL)
  (#preR:st.hprop) (lpreR:l_pre preR)
: l_pre (preL `st.star` preR)
= fun h -> lpreL h /\ lpreR h

let par_lpost (#st:st) (#aL:Type0) (#preL:st.hprop) (#postL:post st aL)
  (lpreL:l_pre preL) (lpostL:l_post preL postL)
  (#aR:Type0) (#preR:st.hprop) (#postR:post st aR)
  (lpreR:l_pre preR) (lpostR:l_post preR postR)
: l_post (preL `st.star` preR) (fun (xL, xR) -> postL xL `st.star` postR xR)
= fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1


//we don't use projectors at all, so don't bother generating (and typechecking!) them
#set-options "--__temp_no_proj Steel.Semantics.Hoare"

noeq
type m (st:st) : (a:Type0) -> pre:st.hprop -> post:post st a -> l_pre pre -> l_post pre post -> Type =
  | Ret:
    #a:Type0 ->
    post:post st a ->
    x:a ->
    lpost:l_post (post x) post ->
    m st a (post x) post (return_lpre #_ #_ #post x lpost) lpost

  | Act:
    #a:Type0 ->
    pre:st.hprop ->
    post:post st a ->
    f:action_t pre a post ->
    m st a pre post (action_lpre f) (action_lpost f)

  | Bind:
    #a:Type0 ->
    #pre:st.hprop ->
    #post_a:post st a ->
    #lpre_a:l_pre pre ->
    #lpost_a:l_post pre post_a ->
    #b:Type0 ->
    #post_b:post st b ->
    #lpre_b:(x:a -> l_pre (post_a x)) ->
    #lpost_b:(x:a -> l_post (post_a x) post_b) ->
    f:m st a pre post_a lpre_a lpost_a ->
    g:(x:a -> Dv (m st b (post_a x) post_b (lpre_b x) (lpost_b x))) ->
    m st b pre post_b
      (bind_lpre lpre_a lpost_a lpre_b)
      (bind_lpost lpre_a lpost_a lpost_b)

  | Frame:
    #a:Type0 ->
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
    #aL:Type0 ->
    #preL:st.hprop ->
    #postL:post st aL ->
    #lpreL:l_pre preL ->
    #lpostL:l_post preL postL ->
    mL:m st aL preL postL lpreL lpostL ->
    #aR:Type0 ->
    #preR:st.hprop ->
    #postR:post st aR ->
    #lpreR:l_pre preR ->
    #lpostR:l_post preR postR ->
    mR:m st aR preR postR lpreR lpostR ->
    m st (aL & aR) (preL `st.star` preR) (fun (xL, xR) -> postL xL `st.star` postR xR)
      (par_lpre lpreL lpreR)
      (par_lpost lpreL lpostL lpreR lpostR)


(**** Setting up the stepping relation ****)


let frame_postcondition_is_framed_0 (#st:st) (#a:Type0) (#post:post st a)
  (frame:st.hprop) (lpost:l_post frame post)
  (m0 m1:st.mem)
= forall x h2. lpost (st.heap_of_mem m0) x h2 <==>
          lpost (st.heap_of_mem m1) x h2

let frame_postcondition_is_framed (#st:st) (frame:st.hprop) (m0 m1:st.mem) =
  forall (a:Type0) (post:post st a) (lpost:l_post frame post).
    frame_postcondition_is_framed_0 frame lpost m0 m1

#push-options "--warn_error -271"
let postcondition_framing_subhprop (#st:st) (frame:st.hprop) (fp:st.hprop) (m0 m1:st.mem)
: Lemma
  (requires frame_postcondition_is_framed (fp `st.star` frame) m0 m1)
  (ensures frame_postcondition_is_framed frame m0 m1)
  [SMTPat (frame_postcondition_is_framed (fp `st.star` frame) m0 m1);
   SMTPat (frame_postcondition_is_framed frame m0 m1)]
= let aux (#a:Type0) (#post:post st a) (lpost:l_post frame post)
    : Lemma
      (ensures frame_postcondition_is_framed_0 frame lpost m0 m1)
      [SMTPat ()]
    = assert (frame_postcondition_is_framed_0 #st #a #post (fp `st.star` frame) lpost m0 m1)
  in
  ()
#pop-options

noeq
type step_result (#st:st) a (q:post st a) (frame:st.hprop) =
  | Step:
    old_state:st.mem ->
    fpost:st.hprop ->
    new_state:hmem (fpost `st.star` frame){frame_postcondition_is_framed frame old_state new_state} ->
    lpre:l_pre fpost{lpre (st.heap_of_mem new_state)} ->
    lpost:l_post fpost q ->
    m st a fpost q lpre lpost ->
    nat ->
    step_result a q frame


(**** Setting up the specs of the interpreter single step ****)


/// While the requires is standard (that the expects hprop holds and requires is valid),
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
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost)
  (state:st.mem)
= st.interp (st.locks_invariant state `st.star` pre `st.star` frame) (st.heap_of_mem state) /\
  lpre (st.heap_of_mem state)

unfold
let step_ens (#st:st)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost)
  (state:st.mem)
: step_result a post frame -> Type0
= fun r ->
  let Step state1 _ new_state new_lpre new_lpost _ _ = r in
  ((state1 == state) /\
   (lpre (st.heap_of_mem state) ==> new_lpre (st.heap_of_mem new_state)) /\
   (forall x h_final. new_lpost (st.heap_of_mem new_state) x h_final ==>
                 lpost (st.heap_of_mem state) x h_final))


/// The type of the stepping function
///
/// We will write auxiliary functions for `bind`, `frame` etc., to which we pass a `step` function
///   that they will invoke on the sub-terms


unfold
let step_t =
  #st:st -> i:nat ->
  #a:Type -> #pre:st.hprop -> #post:post st a -> #lpre:l_pre pre -> #lpost:l_post pre post ->
  frame:st.hprop ->
  f:m st a pre post lpre lpost ->
  state:st.mem ->
  Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

/// Return

let step_ret (#st:st) (i:nat) (#a:Type)
  (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Ret? f})
  (state:st.mem)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= let Ret p x lp = f in
  Step state (p x) state lpre lpost f i


/// Action

let step_act (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Act? f})
  (state:st.mem)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= let Act pre post f = f in
  let (| x, new_state |) = f state in

  let lpost : l_post (post x) post = fun _ x h1 -> st.interp (post x) h1 in
  Step state (post x) new_state (fun h -> lpost h x h) lpost (Ret post x lpost) i


/// Bind and Frame

#push-options "--z3rlimit 20"
let step_bind (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Bind? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Bind #_ #_ #_ #_ #_ #_ #_ #_ #lpre_b #lpost_b (Ret p x _) g ->
    Step state (p x) state (lpre_b x) (lpost_b x) (g x) i

  | Bind #_ #_ #_ #_ #_ #_ #_ #_ #lpre_b #lpost_b f g ->
    let Step state next_pre next_state next_lpre next_lpost f j = step i frame f state in
    
    Step state next_pre next_state
      (bind_lpre next_lpre next_lpost lpre_b)
      (bind_lpost next_lpre next_lpost lpost_b)
      (Bind f g)
      j

#set-options "--z3rlimit 20"
let step_frame (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#p:post st a) (#lpre:l_pre pre) (#lpost:l_post pre p)
  (frame:st.hprop)
  (f:m st a pre p lpre lpost{Frame? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a p frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Frame (Ret p x lp) frame f_frame ->
    Step state (p x `st.star` frame) state
      (fun h -> lpost h x h)
      lpost
      (Ret (fun x -> p x `st.star` frame) x lpost)
      i

  | Frame #_ #_ #f_pre #_ #f_lpre #f_lpost f frame' f_frame' ->
    (*
     * we want the following assertion to hold, for calling step recursively:
     *   assert (st.interp (st.locks_invariant state `st.star` f_pre `st.star` (st.refine frame' f_frame' `st.star` frame)) 
     *                     (st.heap_of_mem state))
     * the following lemma calls (commute and refine_middle) achieve it
     *)
    commute4_1_2_3 f_pre frame' frame (st.locks_invariant state);
    refine_middle (st.locks_invariant state `st.star` f_pre) frame' frame f_frame' state;


    let Step state next_fpre next_state next_flpre next_flpost f j = step i (st.refine frame' f_frame' `st.star` frame) f state in

    (*
     * next_state has type
     *   hmem (next_fpre `st.star` (st.refine frame' f_frame' `st.star` frame))
     * we require it to have type
     *   hmem ((next_fpre `st.star` frame') `st.star` frame)
     * the following refine_middle lemma call, and then an application of associativity achieves it
     *)
    refine_middle (st.locks_invariant next_state `st.star` next_fpre) frame' frame f_frame' next_state;
    commute3_2_1_interp next_fpre frame' frame next_state;

    Step state (next_fpre `st.star` frame') next_state
      (frame_lpre next_flpre f_frame')
      (frame_lpost next_flpre next_flpost f_frame')
      (Frame f frame' f_frame')
      j

let step_par_left (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Par? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Par #_ #aL #preL #postL #lpreL #lpostL mL #aR #preR #postR #lpreR #lpostR mR ->
    commute4_middle (st.locks_invariant state) preL preR frame;
    refine_middle (st.locks_invariant state `st.star` preL) preR frame lpreR state;

    let Step state next_preL next_state next_lpreL next_lpostL mL j = step (i + 1) (st.refine preR lpreR `st.star` frame) mL state in

    refine_middle (st.locks_invariant next_state `st.star` next_preL) preR frame lpreR next_state;
    commute3_2_1_interp next_preL preR frame next_state;

    let lpostR' : l_post (st.refine preR lpreR `st.star` frame) postR = lpostR in

    assert (frame_postcondition_is_framed_0 (st.refine preR lpreR `st.star` frame) lpostR' state next_state);

    Step state (next_preL `st.star` preR) next_state
      (par_lpre next_lpreL lpreR)
      (par_lpost next_lpreL next_lpostL lpreR lpostR)
      (Par mL mR)
      j

let step_par_right (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Par? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Par #_ #aL #preL #postL #lpreL #lpostL mL #aR #preR #postR #lpreR #lpostR mR ->
    commute3_1_2 preL preR frame;
    equals_ext_right (st.locks_invariant state)
      ((preL `st.star` preR) `st.star` frame)
      (preR `st.star` (preL `st.star` frame));
    refine_middle (st.locks_invariant state `st.star` preR) preL frame lpreL state;

    let Step state next_preR next_state next_lpreR next_lpostR mR j = step (i + 1) (st.refine preL lpreL `st.star` frame) mR state in

    commute3_2_1_refine_middle_interp next_preR preL frame lpreL next_state;

    let lpostL' : l_post (st.refine preL lpreL `st.star` frame) postL = lpostL in

    assert (frame_postcondition_is_framed_0 (st.refine preL lpreL `st.star` frame) lpostL' state next_state);

    Step state (preL `st.star` next_preR) next_state
      (par_lpre lpreL next_lpreR)
      (par_lpost lpreL lpostL next_lpreR next_lpostR)
      (Par mL mR)
      j

assume val go_left : nat -> bool

let step_par (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Par? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Par #_ #aL #_ #_ #_ #_ (Ret pL xL lpL) #aR #_ #_ #_ #_ (Ret pR xR lpR) ->

    let lpost : l_post #st #(aL & aR) _ _ = fun h0 (xL, xR) h1 -> lpL h0 xL h1 /\ lpR h0 xR h1 in

    Step state (pL xL `st.star` pR xR) state
      (fun h -> lpL h xL h /\ lpR h xR h)
      lpost 
      (Ret (fun (xL, xR) -> pL xL `st.star` pR xR) (xL, xR) lpost)
      i
  | _ ->
    if go_left i
    then step_par_left i frame f state step
    else step_par_right i frame f state step
#pop-options


/// The `step` function

let rec step : step_t =
  fun #st i #a #pre #post #o_lpre #o_lpost frame f state ->
  match f with
  | Ret _ _ _   ->   step_ret i frame f state
  | Act _ _ _   ->   step_act i frame f state
  | Bind _ _    ->  step_bind i frame f state step
  | Frame _ _ _ -> step_frame i frame f state step
  | Par _ _     ->   step_par i frame f state step


let rec run (#st:st) (i:nat) (#a:Type0) (#pre:st.hprop) (#post:post st a)
  (#lpre:l_pre pre) (#lpost:l_post pre post)
  (f:m st a pre post lpre lpost)
  (state:st.mem)
: Div (a & st.mem)
  (requires
    st.interp (st.locks_invariant state `st.star` pre) (st.heap_of_mem state) /\
    lpre (st.heap_of_mem state))
  (ensures fun (x, new_state) ->
    st.interp (st.locks_invariant new_state `st.star` post x) (st.heap_of_mem new_state) /\
    lpost (st.heap_of_mem state) x (st.heap_of_mem new_state))
= match f with
  | Ret _ x _ -> x, state

  | _ ->
    let Step _ _ state _ _ f j = step i st.emp f state in
    run j f state
