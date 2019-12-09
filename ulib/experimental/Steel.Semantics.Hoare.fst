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


(** [post a c] is a postcondition on [a]-typed result *)
let post (st:st) (a:Type) = a -> st.hprop

let hheap (#st:st) (fp:st.hprop) = fp_heap_0 st.interp fp

let hmem (#st:st) (fp:st.hprop) = m:st.mem{st.interp (st.locks_invariant m `st.star` fp) (st.heap_of_mem m)}

let action0 (#st:st) (fp:st.hprop) (a:Type) (fp':a -> st.hprop) =
  hmem fp -> (x:a & hmem (fp' x))

let is_frame_preserving (#st:st) #a #fp #fp' (f:action0 fp a fp') =
  forall frame (h0:hmem (fp `st.star` frame)).  //we don't need locks_invariant for h0?
    (let (| x, h1 |) = f h0 in
     st.interp (fp' x `st.star` frame `st.star` st.locks_invariant h1) (st.heap_of_mem h1))

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


/// Now the types for pre- and postconditions for the hoare-style specs


let l_pre (#st:st) (pre:st.hprop) = fp_prop pre

let l_post (#st:st) (#a:Type) (pre:st.hprop) (post:post st a) = fp_prop2 pre post


/// Actions don't have a separate logical payload

let action_lpre (#st:st) (#a:Type) (#pre:st.hprop) (#post:post st a) (_:action_t pre a post)
  : l_pre pre =
  st.interp pre

let action_lpost (#st:st) (#a:Type) (#pre:st.hprop) (#post:post st a) (_:action_t pre a post)
  : l_post pre post =
  fun h0 x h1 -> st.interp (post x) h1


//we don't use projectors at all, so don't bother generating (and typechecking!) them
#set-options "--__temp_no_proj Steel.Semantics.Hoare"

noeq
type m (st:st) : (a:Type0) -> pre:st.hprop -> post:post st a -> l_pre pre -> l_post pre post -> Type =
  | Ret:
    #a:Type0 ->
    post:post st a ->
    x:a ->
    lpost:l_post (post x) post ->
    m st a (post x) post (fun h -> lpost h x h) lpost

  | Act:
    #a:Type0 ->
    pre:st.hprop ->
    post:post st a ->
    f:action_t pre a post ->
    m st a pre post (action_lpre f) (action_lpost f)

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
      (fun h -> lpre h /\ f_frame h)
      (fun h0 x h1 -> lpre h0 /\ lpost h0 x h1 /\ f_frame h1)

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
      (fun h -> lpre_a h /\ (forall (x:a) h1. lpost_a h x h1 ==> lpre_b x h1))
      (fun h0 y h2 -> lpre_a h0 /\ (exists x h1. (lpost_b x) h1 y h2))


noeq
type step_result (#st:st) a (q:post st a) (frame:st.hprop) =
  | Step:
    fpost:st.hprop ->
    state:hmem (fpost `st.star` frame) ->
    lpre:l_pre fpost{lpre (st.heap_of_mem state)} ->
    lpost:l_post fpost q ->
    m st a fpost q lpre lpost ->
    nat ->
    step_result a q frame


/// Setting up the specs for the definitional interpreter's `step` function
///
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
  let Step _ new_state new_lpre new_lpost _ _ = r in
  ((lpre (st.heap_of_mem state) ==> new_lpre (st.heap_of_mem new_state)) /\
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
  Step (p x) state lpre lpost f i


/// Action

let step_act (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Act? f})
  (state:st.mem)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= let Act pre post f = f in
  let (| x, state |) = f state in

  let lpost : l_post (post x) post = fun _ x h1 -> st.interp (post x) h1 in
  Step (post x) state (fun h -> lpost h x h) lpost (Ret post x lpost) i


/// Bind and Frame

#push-options "--z3rlimit 60"
let step_bind (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Bind? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Bind #_ #_ #_ #_ #_ #_ #_ #_ #lpre_b #lpost_b (Ret p x _) g ->
    Step (p x) state (lpre_b x) (lpost_b x) (g x) i

  | Bind #_ #_ #_ #_ #_ #_ #_ #_ #lpre_b #lpost_b f g ->
    let Step next_pre next_state next_lpre next_lpost f j = step i frame f state in
    
    Step next_pre next_state
      (fun h -> next_lpre h /\ (forall x h1. next_lpost h x h1 ==> lpre_b x h1))
      (fun h0 y h2 -> next_lpre h0 /\ (exists x h1. (lpost_b x) h1 y h2))
      (Bind f g)
      j

let step_frame (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
  (frame:st.hprop)
  (f:m st a pre post lpre lpost{Frame? f})
  (state:st.mem)
  (step:step_t)

: Div (step_result a post frame) (step_req frame f state) (step_ens frame f state)

= match f with
  | Frame (Ret p x lp) frame f_frame ->
    Step (p x `st.star` frame) state
      (fun h -> lpost h x h)
      lpost
      (Ret (fun x -> p x `st.star` frame) x lpost)
      i

  | Frame #_ #_ #f_pre #_ #f_lpre #f_lpost f frame' f_frame' ->
    (*
     * we want the following assertion to hold, for calling step recursively:
     *   assert (st.interp (st.locks_invariant state `st.star` f_pre `st.star` (st.refine frame' f_frame' `st.star` frame)) 
     *                     (st.heap_of_mem state))
     * the following lemma calls (commute and refine_middle achieve it
     *)
    commute4_1_2_3 f_pre frame' frame (st.locks_invariant state);
    refine_middle (st.locks_invariant state `st.star` f_pre) frame' frame f_frame' state;


    let Step next_fpre next_state next_flpre next_flpost f j = step i (st.refine frame' f_frame' `st.star` frame) f state in

    (*
     * next_state has type
     *   hmem (next_fpre `st.star` (st.refine frame' f_frame' `st.star` frame))
     * we require it to have type
     *   hmem ((next_fpre `st.star` frame') `st.star` frame)
     * the following refine_middle lemma call, and then an application of associativity achieves it
     *)
    refine_middle (st.locks_invariant next_state `st.star` next_fpre) frame' frame f_frame' next_state;
    assume (st.interp (st.locks_invariant next_state `st.star` (next_fpre `st.star` (frame' `st.star` frame)))
                      (st.heap_of_mem next_state)
            
            <==>
            
            st.interp (st.locks_invariant next_state `st.star` (next_fpre `st.star` frame') `st.star` frame)
                      (st.heap_of_mem next_state));

    Step (next_fpre `st.star` frame') next_state
      (fun h -> next_flpre h /\ f_frame' h)
      (fun h0 x h1 -> next_flpre h0 /\ next_flpost h0 x h1 /\ f_frame' h1)
      (Frame f frame' f_frame')
      j
#pop-options


/// The `step` function

let rec step : step_t =
  fun #st i #a #pre #post #lpre #lpost frame f state ->
  match f with
  | Ret _ _ _   ->   step_ret i frame f state
  | Act _ _ _   ->   step_act i frame f state
  | Bind _ _    ->  step_bind i frame f state step
  | Frame _ _ _ -> step_frame i frame f state step

// match f with

//   | _ -> admit ()
 
//admit ()

  //   assume (st.interp (st.locks_invariant state `st.star` f_pre `st.star` frame) (st.heap_of_mem state));
  //   assume (f_lpre (st.heap_of_mem state));

  //   let Step next_pre next_state next_lpre next_lpost f j = step i frame f state in

  //   let lpre (h:st.heap) : prop =
  //     let p = next_lpre h /\ f_frame' h in
  //     assume (p `subtype_of` unit);
  //     p in

  //   let lpost (h0:st.heap) x (h1:st.heap) : prop =
  //     let p = next_lpost h0 x h1 /\ f_frame' h1 in
  //     assume (p `subtype_of` unit);
  //     p in

  //   assume (lpre `depends_only_on` (next_pre `st.star` frame'));
  //   assume (depends_only_on2 lpost (next_pre `st.star` frame') (fun x -> f_post x `st.star` frame));

  //   let next_state : hmem ((next_pre `st.star` frame') `st.star` frame) = magic () in
  //   assume (lpre (st.heap_of_mem next_state));
    
  //   let s = Step (next_pre `st.star` frame') next_state lpre lpost (Frame next_pre f_post next_lpre next_lpost f frame' f_frame') i in
  //   admit ();
  //   s
  
  //   // let lpre = //: l_pre (next_pre `st.star` frame') =
  //   //   fun (h:st.heap) -> next_lpre h /\ f_frame' h in
  //   // let lpre : st.heap -> Type0 = lpre in

  //   // 

    //admit ()


    // commute4_1_2_3 f_pre frame' frame (st.locks_invariant state);
    // refine_middle (st.locks_invariant state `st.star` f_pre) frame' frame f_frame' state;
    // assume (st.interp (st.locks_invariant `st.star` f_pre `st.star` frame) (st.heap_of_mem state));
    //
    //let Step next_pre next_state next_lpre next_lpost f j = step i frame f state in

    // let lpre : l_pre ((next_pre `st.star` frame') `st.star` frame) =
    //   fun h -> next_lpre h /\ f_frame' h in

    // let lpost : l_post ((next_pre `st.star` frame') `st.star` frame) (fun x -> (post x `st.star` frame')) =
    //   fun h0 x h1 -> next_lpost h0 x h1 /\ f_frame' h1 in

    //let next_state : hmem ((next_pre `st.star` frame') `st.star` frame) = magic () in
    //assume (lpre (st.heap_of_mem next_state));

    //Step (next_pre `st.star` frame') next_state lpre lpost (Frame next_pre post next_lpre next_lpost f frame' f_frame') i



   //  let lpre : l_pre (next_pre `st.star` frame) =
   //    fun h -> next_lpre h /\ f_frame h in

   //  assume (lpre (st.heap_of_mem next_state));

   // admit ()
   //Step (next_pre `st.star` frame') next_state lpre lpost (Frame next_pre post next_lpre next_lpost f frame' f_frame') i

   //admit ()

  // | _ -> admit ()








// let step_ret (#st:st) (i:nat)
//   (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
//   (frame:st.hprop)
//   (f:m st a pre post lpre lpost{Ret? f})
//   (state:st.mem)

// : Div
//   (step_result a pre post frame)
//   (requires
//     st.interp (st.locks_invariant state `st.star` pre `st.star` frame) (st.heap_of_mem state) /\
//     lpre (st.heap_of_mem state))
//   (ensures fun _ -> True)

// = let Ret p x lp = f in
//   Step (p x) state lpre lpost f i

// let step_act (#st:st) (i:nat)
//   (#a:Type) (#pre:st.hprop) (#post:post st a) (#lpre:l_pre pre) (#lpost:l_post pre post)
//   (frame:st.hprop)
//   (f:m st a pre post lpre lpost{Act? f})
//   (state:st.mem)

// : Div
//   (step_result a pre post frame)
//   (requires
//     st.interp (st.locks_invariant state `st.star` pre `st.star` frame) (st.heap_of_mem state) /\
//     lpre (st.heap_of_mem state))
//   (ensures fun _ -> True)

// = let Act pre post f = f in
//   let (| x, state |) = f state in

//   let lpost : l_post (post x) post = fun x h0 h1 -> st.interp (post x) h1 in
//   Step (post x) state (fun h -> lpost x h h) lpost (Ret post x lpost) i




// let return_wp (#st:st) (#a:Type) (x:a) (post: post st a)
//   : wp (post x) a post
//   = fun (k:wp_post a post) s0 -> k x s0

// let bind_wp (#st:st)
//             (#pre_a:st.hprop) (#a:Type) (#post_a:post st a)
//             (#b:Type) (#post_b:post st b)
//             (f:wp pre_a a post_a)
//             (g: (x:a -> wp (post_a x) b post_b))
//   : wp pre_a b post_b
//   = fun k -> f (fun x -> g x k)

// let frame_post (#st:st) (#a:Type) (p:post st a) (frame:st.hprop)
//   : post st a
//   =  fun x -> p x `st.star` frame

// // let action_framing (#st:st) #b (f:action st b)
// //   = forall (h0:fp_heap f.pre)
// //       (h1:st.heap {st.disjoint h0 h1})
// //       (post: (x:b -> fp_prop (f.post x))).
// //       (st.interp f.pre (st.join h0 h1) /\ (
// //        let (| x0, h |) = f.sem h0 in
// //        let (| x1, h' |) = f.sem (st.join h0 h1) in
// //        x0 == x1 /\
// //        (post x0 h <==> post x1 h')))

// // let action_framing_lemma (#st:st) #pre #b #post (f:action pre b post)
// //                          (h0:hheap pre)
// //                          (h1:st.heap {st.disjoint h0 h1})
// //                          (q: (x:b -> fp_prop (post x)))
// //   : Lemma (st.interp pre (st.join h0 h1) /\ (
// //            let (| x0, h |) = f h0 in
// //            let (| x1, h' |) = f (st.join h0 h1) in
// //            x0 == x1 /\
// //            (q x0 h <==> q x1 h')))
// //   = assert (action_depends_only_on_fp f);
// //     assert (st.interp pre (st.join h0 h1));
// //     let (| x0, h |) = f h0 in
// //     let (| x1, h' |) = f (st.join h0 h1) in
// //     //Wow, a very manual instantiation ...
// //     assert (action_depends_only_on_fp f ==> x0 == x1 /\ (q x0 h <==> q x1 h'))
// //         by (T.norm [delta_only [`%action_depends_only_on_fp]];
// //             let lem = T.implies_intro () in
// //             let hh = quote h0 in
// //             let bp0 = T.instantiate (T.binder_to_term lem) hh in
// //             let hh = quote h1 in
// //             let bp1 = T.instantiate (T.binder_to_term bp0) hh in
// //             let qq = quote q in
// //             let bp2 = T.instantiate (T.binder_to_term bp1) qq in
// //             T.smt())

// let wp_action (#st:st) (#fpre:st.hprop) #b #fpost (f:action fpre b fpost)
//   : wp fpre b fpost
//   = fun (k:wp_post b fpost) h0 ->
//       st.interp fpre h0 /\ (forall x h1. st.interp (fpost x) h1 ==> k x h1)

// let bind_action (#st:st) #fpre #a #fpost #b
//                 (f:action fpre a fpost)
//                 (#post_g:post st b)
//                 (wp_g:(x:a -> wp (fpost x) b post_g))
//    : wp fpre b post_g
//    = bind_wp (wp_action f) wp_g

// let triv_post #st (a:Type) (p:post st a) : wp_post a p =
//   let k (x:a) : fp_prop (p x) =
//     let p : fp_prop (p x) = fun s -> True in
//     p
//   in
//   k

// let as_requires (#st:st) (#aL:Type) (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
//   : fp_prop preL
//   = wpL (triv_post aL postL)


// let post_star (#st:st)
//               #aL (postL: post st aL)
//               #aR (postR: post st aR)
//    : post st (aL & aR)
//    = fun (xL, xR) -> postL xL `st.star` postR xR

// let wp_par (#st:st)
//            #aL (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
//            #aR (#preR:st.hprop) (#postR: post st aR) (wpR: wp preR aR postR)
//    : wp (preL `st.star` preR)
//         (aL & aR)
//         (post_star postL postR)
//    = fun (k:wp_post (aL & aR) (post_star postL postR)) (s:st.heap) ->
//         st.interp (preL `st.star` preR) s /\
//         as_requires wpL s /\
//         as_requires wpR s /\
//         (forall xL xR s'.
//            st.interp (postL xL `st.star` postR xR) s' ==>
//            k (xL, xR) s')

// let bind_par (#st:st)
//            #aL (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
//            #aR (#preR:st.hprop) (#postR: post st aR) (wpR: wp preR aR postR)
//            #a  #post (wp_k:(xL:aL -> xR:aR -> wp (postL xL `st.star` postR xR) a post))
//   : wp (preL `st.star` preR)
//        a
//        post
//   = bind_wp (wp_par wpL wpR) (fun (xL, xR) -> wp_k xL xR)

// let as_ensures (#st:st) (#aL:Type) (#preL:st.hprop) (#postL: post st aL) (wpL: wp preL aL postL)
//   : x:aL -> fp_prop (postL x)
//   = fun x s -> True

// let and_fp_prop (#st:st) (#fp0 #fp1:st.hprop) (p0:fp_prop fp0) (p1:fp_prop fp1)
//   : fp_prop (fp0 `st.star` fp1)
//   = fun h -> p0 h /\ p1 h

// let wp_of_pre_post (#st:st) (#fp0:st.hprop) (#a:Type) (#fp1:a -> st.hprop)
//                    (pre:fp_prop fp0) (post: (x:a -> fp_prop (fp1 x)))
//    : wp fp0 a fp1
//    = fun (k:wp_post a fp1) (s:st.heap) ->
//       st.interp fp0 s /\
//       pre s /\
//       (forall x s'.
//         st.interp (fp1 x) s' /\
//         post x s' ==>
//         k x s')

// let wp_star_frame (#st:st) #a (#pre0:st.hprop) (#post0:post st a)
//                   (wp0:wp pre0 a post0) (frame:st.hprop) (f_frame:fp_prop frame)
//    : wp (pre0 `st.star` frame) a (fun x -> post0 x `st.star` frame)
//    = wp_of_pre_post (and_fp_prop (as_requires wp0) f_frame) (fun x -> and_fp_prop (as_ensures wp0 x) f_frame)


// (** [m s c a pre post] :
// //  *  A free monad for divergence, state and parallel composition
// //  *  with generic actions. The main idea:
// //  *
// //  *  Every continuation may be divergent. As such, [m] is indexed by
// //  *  pre- and post-conditions so that we can do proofs
// //  *  intrinsically.
// //  *
// //  *  Universe-polymorphic in both the state and result type
// //  *
// //  *)
// #push-options "--print_universes"
// noeq
// type m (st:st) : (a:Type0) -> pre:st.hprop -> post:post st a -> wp pre a post -> Type =
//   | Ret : #a:Type0
//         -> post:post st a
//         -> x:a
//         -> m st a (post x) post (return_wp x post)

//   | Act : #a:Type0
//         -> fpre: st.hprop
//         -> fpost: post st a
//         -> f:action fpre a fpost
//         -> m st a fpre fpost (wp_action f)

//   | Par : preL:_ -> aL:_ -> postL:_ -> wpL:wp preL aL postL -> mL: m st aL preL postL wpL ->
//           preR:_ -> aR:_ -> postR:_ -> wpR:wp preR aR postR -> mR: m st aR preR postR wpR ->
//           m st (aL & aR) (preL `st.star` preR) (postL `post_star` postR) (wp_par wpL wpR)

//   | Bind : pre:st.hprop
//          -> a:Type0
//          -> post_a:post st a
//          -> wp_a:wp pre a post_a
//          -> m st a pre post_a wp_a
//          -> b:Type0
//          -> post_b:post st b
//          -> wp_b:(x:a -> wp (post_a x) b post_b)
//          -> (x:a -> Dv (m st b (post_a x) post_b (wp_b x)))
//          -> m st b pre post_b (bind_wp wp_a wp_b)

//   | Frame : pre:st.hprop ->
//             a:Type0 ->
//             post:post st a ->
//             wp_a:wp pre a post ->
//             m st a pre post wp_a ->
//             frame:st.hprop ->
//             f_frame:fp_prop frame ->
//             m st a (pre `st.star` frame)
//                    (fun x -> post x `st.star` frame)
//                    (wp_star_frame wp_a frame f_frame)


// /// We assume a stream of booleans for the semantics given below
// /// to resolve the nondeterminism of Par
// assume
// val bools : nat -> bool

// /// The semantics comes is in two levels:
// ///
// ///   1. A single-step relation [step] which selects an atomic action to
// ///      execute in the tree of threads
// ///
// ///   2. A top-level driver [run] which repeatedly invokes [step]
// ///      until it returns with a result and final state.

// noeq
// type step_result (#st:st) a (q:post st a) (frame:st.hprop) (k:wp_post a q) =
//   | Step: fpost:st.hprop ->
//           state:hmem (fpost `st.star` frame) ->
//           wp:wp fpost a q { wp k (st.heap_of_mem state) } ->
//           m st a fpost q wp -> //the reduct
//           nat -> //position in the stream of booleans (less important)
//           step_result a q frame k


// /// [step i f frame state]: Reduces a single step of [f], while framing
// /// the assertion [frame]

// // #reset-options
// // #restart-solver
// // #push-options "--max_fuel 0 --max_ifuel 4 --initial_ifuel 4 --z3rlimit_factor 4 --query_stats"

// let step_act (#st:st) (i:nat) #pre #a #post
//              (frame:st.hprop)
//              (#wp:wp pre a post)
//              (f:m st a pre post wp { Act? f })
//              (k:wp_post a post)
//              (state:st.mem)
//   : Div (step_result a post frame k)
//         (requires
//           st.interp (st.locks_invariant state `st.star` pre `st.star` frame) (st.heap_of_mem state) /\
//           st.interp pre (st.heap_of_mem state) /\
//           wp k (st.heap_of_mem state))
//         (ensures fun _ -> True)
//   =
//     let Act fpre fpost act1 = f in
//     //Evaluate the action and return the continuation as the reduct
//     let (| vb, state' |) = act1 state in
//     Step (fpost vb) state' (return_wp vb fpost) (Ret fpost vb) i

// let step_ret (#st:st) (i:nat) #fpre #a #fpost (frame:st.hprop)
//              (#wp:wp fpre a fpost)
//              (f:m st a fpre fpost wp { Ret? f })
//              (k:wp_post a fpost)
//              (state:st.mem)
//   : Div (step_result a fpost frame k)
//         (requires
//           st.interp (st.locks_invariant state `st.star` fpre `st.star` frame) (st.heap_of_mem state) /\
//           st.interp fpre (st.heap_of_mem state) /\
//           wp k (st.heap_of_mem state))
//         (ensures fun _ -> True)
//   = let Ret pp x = f in
//     Step (pp x)
//          state
//          wp
//          f
//          i

// let step_par_ret (#st:st) (i:nat) #pre #a #post
//                       (frame:st.hprop)
//                       (#wp:wp pre a post)
//                       (f:m st a pre post wp { Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f) })
//                       (k:wp_post a post)
//                       (state:st.mem)
//   : Div (step_result a post frame k)
//         (requires
//           st.interp (st.locks_invariant state `st.star` pre `st.star` frame) (st.heap_of_mem state) /\
//           st.interp pre (st.heap_of_mem state) /\
//           wp k (st.heap_of_mem state))
//         (ensures fun _ -> True)
//   =  let Par preL aL postL wpL (Ret _ xL)
//           preR aR postR wpR (Ret _ xR) = f in
//       // assert (wpL == return_wp xL postL);
//       // assert (wpR == return_wp xR postR);
//       // assert (wp == wp_par wpL wpR);
//       // assert (wp k state);
//       // assert (preL == postL xL);
//       // assert (preR == postR xR);
//       Step (postL xL `st.star` postR xR)
//            state
//            (return_wp (xL, xR) (post_star postL postR))
//            (Ret (post_star postL postR) (xL, xR))
//            i

// let refine_star_left (#st:st) (r0 r1:st.hprop) (p:fp_prop r0) (s:st.mem)
//   : Lemma
//     ((st.interp (r0 `st.star` r1) (st.heap_of_mem s) /\
//       p (st.heap_of_mem s)) <==>
//       st.interp (st.refine r0 p `st.star` r1) (st.heap_of_mem s))
//    = assert (st.interp (st.refine (r0 `st.star` r1) p) (st.heap_of_mem s) <==>
//                         st.interp (st.refine r0 p `st.star` r1) (st.heap_of_mem s))

// let refine_middle (#st:st) (p q r:st.hprop) (fq:fp_prop q) (state:st.mem)
//   : Lemma
//     ((st.interp (p `st.star` (q `st.star` r)) (st.heap_of_mem state) /\
//       fq (st.heap_of_mem state)) <==>
//       st.interp (p `st.star` (st.refine q fq `st.star` r)) (st.heap_of_mem state))
//   =   calc (st.equals) {
//         p `st.star` (q `st.star` r);
//           (st.equals) { }
//         (p `st.star` q) `st.star` r;
//           (st.equals) { }
//         (q `st.star` p) `st.star` r;
//           (st.equals) { }
//         q `st.star` (p `st.star` r);
//       };
//       refine_star_left q (p `st.star` r) fq state;
//       calc (st.equals) {
//         (st.refine q fq) `st.star` (p `st.star` r);
//           (st.equals) { }
//         (st.refine q fq `st.star` p) `st.star` r;
//           (st.equals) { }
//         (p `st.star` st.refine q fq) `st.star` r;
//           (st.equals) { }
//         p `st.star` (st.refine q fq `st.star` r);
//       }

// let commute3_1_2 (#st:st) (p q r:st.hprop)
//   : Lemma
//     ((p `st.star` (q `st.star` r))  `st.equals`
//      (q `st.star` (p `st.star` r)))
//   =  calc (st.equals) {
//         p `st.star` (q `st.star` r);
//           (st.equals) { }
//         (p `st.star` q) `st.star` r;
//           (st.equals) { }
//         (q `st.star` p) `st.star` r;
//           (st.equals) { }
//         q `st.star` (p `st.star` r);
//       }

// let equals_ext_right (#st:st) (p q r:st.hprop) : Lemma
//   (requires q `st.equals` r)
//   (ensures (p `st.star` q) `st.equals` (p `st.star` r))
//   = calc (st.equals) {
//       p `st.star` q;
//         (st.equals) { }
//       q `st.star` p;
//         (st.equals) { }
//       r `st.star` p;
//         (st.equals) { }
//       p `st.star` r;
//     }


// let commute4_1_2_3 (#st:st) (p q r s:st.hprop)
//   : Lemma (
//      ((p `st.star` q) `st.star` (r `st.star` s)) `st.equals`
//      ((s `st.star` p) `st.star` (q `st.star` r))
//    )
//    = calc (st.equals) {
//         (p `st.star` q) `st.star` (r `st.star` s);
//            (st.equals) { }
//         p `st.star` (q `st.star` (r `st.star` s));
//            (st.equals) {
//              calc (st.equals) {
//                q `st.star` (r `st.star` s);
//                  (st.equals) { equals_ext_right q (r `st.star` s) (s `st.star` r) }
//                s `st.star` (q `st.star` r);
//              };
//              equals_ext_right p
//                  (q `st.star` (r `st.star` s))
//                  (s `st.star` (q `st.star` r))
//            }
//         p `st.star` (s `st.star` (q `st.star` r));
//           (st.equals) { }
//         (p `st.star` s) `st.star` (q `st.star` r);
//           (st.equals) { }
//         (s `st.star` p) `st.star` (q `st.star` r);
//      }

// let commute4_middle (#st:st) (p q r s:st.hprop)
//   : Lemma (
//      ((p `st.star` q) `st.star` (r `st.star` s)) `st.equals`
//      (p `st.star` (q `st.star` r) `st.star` s))
//   = calc (st.equals) {
//       (p `st.star` q) `st.star` (r `st.star` s);
//          (st.equals) { }
//        p `st.star` (q `st.star` (r `st.star` s));
//          (st.equals) { }
//       (q `st.star` (r `st.star` s)) `st.star` p;
//          (st.equals) { }
//       ((q `st.star` r) `st.star` s) `st.star` p;
//          (st.equals) { }
//       p `st.star` (q `st.star` r) `st.star` s;
//     }

// let refine_middle_left (#st:st) (p q r:st.hprop) (fp:fp_prop p) (state:st.mem)
//   : Lemma
//     ((st.interp (p `st.star` (q `st.star` r)) (st.heap_of_mem state) /\
//       fp (st.heap_of_mem state)) <==>
//       st.interp (q `st.star` (st.refine p fp `st.star` r)) (st.heap_of_mem state))
//   =   commute3_1_2 p q r;
//       refine_middle q p r fp state

// #push-options "--query_stats --z3cliopt 'smt.qi.eager_threshold=100'"

// let strengthen_post (#st:st) #a (#p:post st a) (post':post st a) (frame:st.hprop) (f:fp_prop frame) (k:wp_post a p)
//   : wp_post a post'
//   = fun _ _ ->
//       forall x s'.
//         st.interp (post' x `st.star` frame) s' /\
//         f s' ==> k x s'

// let wp_triple_equiv (#st:st) (#pre:st.hprop) (#a:_) (#post:post st a)
//                     (wp:wp pre a post)
//                     (k:wp_post a post)
//                     (s:st.heap)
//    : Lemma (wp k s <==> (wp_of_pre_post (as_requires wp) (as_ensures wp) k s))
//    = admit()

// #push-options "--z3rlimit_factor 8"
// let rec step (#st:st) (i:nat) #pre #a #post
//              (frame:st.hprop)
//              (#wp_:wp pre a post)
//              (f:m st a pre post wp_)
//              (k:wp_post a post)
//              (state:st.mem)
//   : Div (step_result a post frame k)
//         (requires
//           st.interp (st.locks_invariant state `st.star` pre `st.star` frame) (st.heap_of_mem state) /\
//           st.interp (st.locks_invariant state `st.star` pre) (st.heap_of_mem state) /\
//           wp_ k (st.heap_of_mem state))
//         (ensures fun _ -> True)
//   = match f with
//     | Ret _ _ ->
//       step_ret i frame f k state

//     | Act _ _ _ ->
//       step_act i frame f k state

//     | Par preL aL postL wpL (Ret _ _)
//           preR aR postR wpR (Ret _ _) ->
//       step_par_ret i frame f k state

//     | Par preL aL postL wpL mL
//           preR aR postR wpR mR ->
//       // assert (wp_ == wp_par wpL wpR);
//       // assert (st.interp (preL `st.star` (preR `st.star` frame)) state);
//       // assert (st.interp (preL `st.star` preR) state);
//       // assert (as_requires wpL state);
//       // assert (as_requires wpR state);
//       // assert (st.interp (st.locks_invariant state `st.star` ((preL `st.star` preR) `st.star` frame))
//       //   (st.heap_of_mem state));
//       if bools i then
//       begin
//         commute4_middle (st.locks_invariant state) preL preR frame;
//         // assert (st.interp ((st.locks_invariant state `st.star` preL) `st.star` (preR `st.star` frame))
//         // (st.heap_of_mem state));
//         refine_middle (st.locks_invariant state `st.star` preL) preR frame (as_requires wpR) state;
//         // assert (st.interp
//         //   (st.locks_invariant state `st.star` preL `st.star`
//         //     ((st.refine preR (as_requires wpR)) `st.star` frame))
//         //   (st.heap_of_mem state));
//         let Step next_preL next_state wpL' mL' j =
//                  //Notice that, inductively, we instantiate the frame extending
//                  //it to include the precondition of the other side of the par
//                  step (i + 1)
//                    ((st.refine preR (as_requires wpR)) `st.star` frame)
//                    mL
//                    (triv_post aL postL)
//                    state
//         in
//         // assert (as_requires wpL' next_state);
//         // assert (as_requires wpR next_state);
//         // assert (st.interp
//         //   (st.locks_invariant next_state `st.star`
//         //     (next_preL `st.star` ((st.refine preR (as_requires wpR)) `st.star` frame)))
//         //   (st.heap_of_mem next_state));
//         refine_middle (st.locks_invariant next_state `st.star` next_preL) preR frame (as_requires wpR) next_state;
//         // assert (st.interp ((next_preL `st.star` preR) `st.star` frame) next_state);
//         let next_m
//           : m st (aL & aR) (next_preL `st.star` preR)
//                            (post_star postL postR)
//                            (wp_par wpL' wpR)
//           = Par next_preL aL postL wpL' mL'
//                 preR aR postR wpR mR
//         in
//         commute4_middle (st.locks_invariant next_state) next_preL preR frame;
//         // assert (st.interp
//         //   (st.locks_invariant next_state `st.star` ((next_preL `st.star` preR) `st.star` frame))
//         //   (st.heap_of_mem next_state));
//         Step (next_preL `st.star` preR) next_state (wp_par wpL' wpR) next_m j
//       end
//       else
//       begin
//         commute3_1_2 preL preR frame;
//         equals_ext_right (st.locks_invariant state)
//                          ((preL `st.star` preR) `st.star` frame)
//                          (preR `st.star` (preL `st.star` frame));
//         // assert (st.interp
//         //   (st.locks_invariant state `st.star` preR `st.star`
//         //     (preL `st.star` frame))
//         //   (st.heap_of_mem state));
//         refine_middle (st.locks_invariant state `st.star` preR) preL frame (as_requires wpL) state;
//         // assert (st.interp
//         //   (st.locks_invariant state `st.star` preR `st.star`
//         //     ((st.refine preL (as_requires wpL)) `st.star` frame))
//         //   (st.heap_of_mem state));
//         let Step next_preR next_state wpR' mR' j =
//                  //Notice that, inductively, we instantiate the frame extending
//                  //it to include the precondition of the other side of the par
//                  step (i + 1)
//                    ((st.refine preL (as_requires wpL)) `st.star` frame)
//                    mR
//                    (triv_post aR postR)
//                    state
//         in
//         // assert (as_requires wpL' next_state);
//         // assert (as_requires wpR next_state);
//         // assert (st.interp (next_preL `st.star` ((st.refine preR (as_requires wpR)) `st.star` frame)) next_state);
//         // assert (st.interp
//         //   (st.locks_invariant next_state `st.star`
//         //     (next_preR `st.star` ((st.refine preL (as_requires wpL)) `st.star` frame)))
//         //   (st.heap_of_mem next_state));
//         refine_middle (st.locks_invariant next_state `st.star` next_preR) preL frame (as_requires wpL) next_state;
//         // assert (st.interp
//         //   (st.locks_invariant next_state `st.star`
//         //     (next_preR `st.star` (preL `st.star` frame)))
//         //   (st.heap_of_mem next_state));

//         let next_m
//           : m st (aL & aR) (preL `st.star` next_preR)
//                            (post_star postL postR)
//                            (wp_par wpL wpR')
//           = Par preL aL postL wpL mL
//                 next_preR aR postR wpR' mR'
//         in

//         commute3_1_2 next_preR preL frame;
//         equals_ext_right (st.locks_invariant next_state)
//                          (next_preR `st.star` (preL `st.star` frame))
//                          ((preL `st.star` next_preR) `st.star` frame);
//         // assert (st.interp
//         //   (st.locks_invariant next_state `st.star` ((preL `st.star` next_preR) `st.star` frame))
//         //   (st.heap_of_mem next_state));

//         Step (preL `st.star` next_preR) next_state (wp_par wpL wpR') next_m j
//       end

//     | Bind pre a post_a wp_a (Ret _ x) b post_b wp_b f ->
//       Step (post_a x) state (wp_b x) (f x) i

//     | Bind pre a post_a wp_a m b post_b wp_b f ->
//        // assert (wp_ == bind_wp wp_a wp_b);
//        // assert (wp_ k state);
//        // assert (bind_wp wp_a wp_b k state);
//        // assert (wp_a (fun x -> wp_b x k) state);
//        let Step next_pre next_state wp_a' m' j =
//          step i frame m (fun x -> wp_b x k) state
//        in
//        Step next_pre
//             next_state
//             (bind_wp wp_a' wp_b)
//             (Bind next_pre a post_a wp_a' m' b post_b wp_b f)
//             j

//     | Frame pre a post wp' (Ret _ x) frame' f_frame' ->
//       Step (post x `st.star` frame') state _ (Ret (fun x -> post x `st.star` frame') x) i

//     | Frame pre a post wp' m frame' f_frame' ->

//       commute4_1_2_3 pre frame' frame (st.locks_invariant state);
//       // assert (wp_ ==
//       //         wp_of_pre_post (and_fp_prop (as_requires wp') f_frame')
//       //                        (fun x -> and_fp_prop (as_ensures wp' x) f_frame'));
//       // assert (f_frame' (st.heap_of_mem state));
//       // assert (st.interp ((pre `st.star` frame') `st.star` frame) (st.heap_of_mem state));
//       // assert (st.interp ((pre `st.star` frame') `st.star` (frame `st.star` st.locks_invariant state)) (st.heap_of_mem state));
//       // assert (st.interp ((st.locks_invariant state `st.star` pre) `st.star` (frame' `st.star` frame)) (st.heap_of_mem state));
//       refine_middle (st.locks_invariant state `st.star` pre) frame' frame f_frame' state;
//       // assert (st.interp ((st.locks_invariant state `st.star` pre) `st.star` (st.refine frame' f_frame' `st.star` frame)) (st.heap_of_mem state));
//       let kk = (strengthen_post post frame' f_frame' k) in
//       assert (wp_of_pre_post (as_requires wp') (as_ensures wp') kk (st.heap_of_mem state));
//       wp_triple_equiv wp' kk (st.heap_of_mem state);
//       assert (wp' kk (st.heap_of_mem state));
//       let Step next_pre next_state wp'' m' j =
//         step i (st.refine frame' f_frame' `st.star` frame) m kk state
//       in
//       // assert (st.interp
//       //           (st.locks_invariant next_state `st.star`
//       //              (next_pre `st.star` (st.refine frame' f_frame' `st.star` frame)))
//       //            (st.heap_of_mem next_state));
//       refine_middle (st.locks_invariant next_state `st.star` next_pre) frame' frame f_frame' next_state;
//       // assert (st.interp
//       //           ((st.locks_invariant next_state `st.star` next_pre) `st.star`
//       //               (frame' `st.star` frame))
//       //           (st.heap_of_mem next_state));
//       assert (wp'' kk (st.heap_of_mem next_state));
//       wp_triple_equiv wp'' kk (st.heap_of_mem next_state);
//       assert (wp_of_pre_post (as_requires wp'') (as_ensures wp'') kk (st.heap_of_mem next_state));
//       commute4_middle (st.locks_invariant next_state) next_pre frame' frame;
//       // assert (st.interp
//       //          (st.locks_invariant next_state `st.star`
//       //            ((next_pre `st.star` frame') `st.star` frame))
//       //          (st.heap_of_mem next_state));
//       Step (next_pre `st.star` frame')
//            next_state
//            (wp_of_pre_post (and_fp_prop (as_requires wp'') f_frame')
//                            (fun x -> and_fp_prop (as_ensures wp'' x) f_frame'))
//            (Frame next_pre a post wp'' m' frame' f_frame')
//            j
// #pop-options

// (**
//   * [run i f state]: Top-level driver that repeatedly invokes [step]
//   *
//   * The type of [run] is the main theorem. It states that it is sound
//   * to interpret the indices of `m` as a Hoare triple in a
//   * partial-correctness semantics
//   *
//   *)
// let rec run (#st:st) (i:nat)
//             #pre #a #post (#wp:wp pre a post)
//             (f:m st a pre post wp) (state:st.mem)
//             (k:wp_post a post)
//   : Div (a & st.mem)
//     (requires
//       st.interp (st.locks_invariant state `st.star` pre) (st.heap_of_mem state) /\
//       wp k (st.heap_of_mem state))
//     (ensures fun (x, state') ->
//       st.interp (st.locks_invariant state' `st.star` post x) (st.heap_of_mem state') /\
//       k x (st.heap_of_mem state'))
//   = match f with
//     | Ret _ x ->
//       x, state
//     | _ ->
//       let Step fpre next_state wp mk j =
//         step i st.emp f k state
//       in
//       run j mk next_state k


// ////////////////////////////////////////////////////////////////////////////////
// //The rest of this module shows how these semantics can be packaged up as an
// //effect in F*
// ////////////////////////////////////////////////////////////////////////////////

// (** [eff a pre post] : The representation-type for a layered effect
//   *
//   *   - Note, we'll probably have to add a thunk to make it work with
//   *     the current implementation but that's a detail
//   *)
// let eff a
//         (#st:st)
//         (expects:st.hprop)
//         (provides: a -> st.hprop)
//         (wp:wp expects a provides)
//   = m st a expects provides wp

// /// eff is a monad: we give a return and bind for it, though we don't
// /// prove the monad laws

// (** [return]: just use Ret *)
// let return #a (x:a) (#st:st) (post:a -> st.hprop)
//   : eff a (post x) post (return_wp x post)
//   = Ret post x

// (** [bind]: just use Bind *)
// let rec bind #a #b (#st:st) (#p:st.hprop) (#q:a -> st.hprop) (#r:b -> st.hprop)
//              (#wp_f: wp p a q) (f:eff a p q wp_f)
//              (#wp_g: (x:a -> wp (q x) b r)) (g: (x:a -> eff b (q x) r (wp_g x)))
//   : Dv (eff b p r (bind_wp wp_f wp_g))
//   = Bind p a q wp_f f b r wp_g g

// (**
//  * [par]: just use Par
//  **)
// let par (#st:st)
//         #a0 #p0 #q0 #wp0 (m0:eff a0 p0 q0 wp0)
//         #a1 #p1 #q1 #wp1 (m1:eff a1 p1 q1 wp1)
//  : eff (a0 & a1) (p0 `st.star` p1) (fun (x0, x1) -> q0 x0 `st.star` q1 x1) (wp_par wp0 wp1)
//  = Par p0 a0 q0 wp0 m0
//        p1 a1 q1 wp1 m1

// (**
//  * [frame]: just use Frame
//  **)
// let frame (#st:st)
//           #a #p #q #wp (m0:eff a p q wp)
//           frame (f_frame:fp_prop frame)
//  : eff a (p `st.star` frame) (fun x -> q x `st.star` frame) (wp_star_frame wp frame f_frame)
//  = Frame p a q wp m0 frame f_frame
