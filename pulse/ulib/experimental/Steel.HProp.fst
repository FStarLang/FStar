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
module Steel.HProp
friend Steel.Heap
open Steel.Heap
open FStar.FunctionalExtensionality
open Steel.Permissions
module U32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let heap_prop_is_affine (p:heap -> prop) = forall m0 m1. p m0 /\ disjoint m0 m1 ==> p (join m0 m1)
let a_heap_prop = p:(heap -> prop) { heap_prop_is_affine p }

////////////////////////////////////////////////////////////////////////////////

module W = FStar.WellFounded

noeq
type hprop : Type u#1 =
  | Emp : hprop
  | Pts_to : #a:Type0 -> r:ref a -> perm:permission -> v:a -> hprop
  | Pts_to_array: #t:Type0 -> a:array_ref t -> perm:permission ->
		  contents:Seq.lseq t (U32.v (length a)) -> hprop
  | Refine : hprop -> a_heap_prop -> hprop
  | And  : hprop -> hprop -> hprop
  | Or   : hprop -> hprop -> hprop
  | Star : hprop -> hprop -> hprop
  | Wand : hprop -> hprop -> hprop
  | Ex   : #a:Type0 -> (a -> hprop) -> hprop
  | All  : #a:Type0 -> (a -> hprop) -> hprop

let _ : squash (inversion hprop) = allow_inversion hprop

let rec interp (p:hprop) (m:heap)
  : Tot prop (decreases p)
  = match p with
    | Emp -> True
    | Pts_to #a r perm v ->
      m `contains_addr` r /\
      (match select_addr m r with
        | Ref a' perm' v' ->
          a == a' /\
          v == v' /\
          perm `lesser_equal_permission` perm'
       | _ -> False
     )
    | Pts_to_array #t a perm contents ->
      m `contains_addr` a.array_addr /\
      (match select_addr m a.array_addr with
        | Array t' len' seq ->
	  t' == t /\
	  U32.v a.array_offset + U32.v a.array_length <= len' /\
          (forall (i:nat{i < U32.v a.array_length}).
	    let x = Seq.index contents i in
	    let (x', perm') = Seq.index seq (U32.v a.array_offset + i) in
	    x == x' /\
	    perm `lesser_equal_permission` perm'
          )
	| _ -> False
      )
    | Refine p q ->
      interp p m /\ q m

    | And p1 p2 ->
      interp p1 m /\
      interp p2 m

    | Or  p1 p2 ->
      interp p1 m \/
      interp p2 m

    | Star p1 p2 ->
      exists m1 m2.
        m1 `disjoint` m2 /\
        m == join m1 m2 /\
        interp p1 m1 /\
        interp p2 m2

    | Wand p1 p2 ->
      forall m1.
        m `disjoint` m1 /\
        interp p1 m1 ==>
        interp p2 (join m m1)

    | Ex f ->
      exists x. (W.axiom1 f x; interp (f x) m)

    | All f ->
      forall x. (W.axiom1 f x; interp (f x) m)

let emp = Emp
let pts_to = Pts_to
let pts_to_array = Pts_to_array
let h_and = And
let h_or = Or
let star = Star
let wand = Wand
let h_exists = Ex
let h_forall = All

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////


let equiv_symmetric (p1 p2:hprop) = ()

#set-options "--max_fuel 1 --initial_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let equiv_extensional_on_star (p1 p2 p3:hprop) = ()

////////////////////////////////////////////////////////////////////////////////
//pts_to
////////////////////////////////////////////////////////////////////////////////

let intro_pts_to (#a:_) (x:ref a) (p:permission) (v:a) (m:heap)
  : Lemma
    (requires
       m `contains_addr` x /\
       (match select_addr m x with
         | Ref a' perm' v' ->
           a == a' /\
           v == v' /\
           p `lesser_equal_permission` perm'
	  | _ -> False))
     (ensures
       interp (pts_to x p v) m)
  = ()

let pts_to_injective (#a:_) (x:ref a) (p:permission) (v0 v1:a) (m:heap)
  = ()

////////////////////////////////////////////////////////////////////////////////
// pts_to_array
////////////////////////////////////////////////////////////////////////////////

let intro_pts_to_array
  (#t: Type0)
  (a:array_ref t)
  (perm:permission)
  (contents:Seq.lseq t (U32.v a.array_length))
  (m: heap)
  : Lemma
    (requires (
      m `contains_addr` a.array_addr /\
      (match select_addr m a.array_addr with
        | Array t' len' seq ->
	  t' == t /\
	  U32.v a.array_offset + U32.v a.array_length <= len' /\
          (forall (i:nat{i < U32.v a.array_length}).
	    let x = Seq.index contents i in
	    let (x', perm') = Seq.index seq (U32.v a.array_offset + i) in
	    x == x' /\
	    perm `lesser_equal_permission` perm'
          )
	| _ -> False)
    ))
    (ensures (interp (pts_to_array a perm contents) m))
  =
  ()

let pts_to_array_injective
  (#t: _)
  (a: array_ref t)
  (p:permission)
  (c0 c1: Seq.lseq t (U32.v (length a)))
  (m: heap)
  =
  assert(c0 `Seq.equal` c1)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

let intro_star (p q:hprop) (mp:hheap p) (mq:hheap q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))
  = ()

/// The main caveat of this model is that because we're working
/// with proof-irrelevant propositions (squashed proofs), I end up
/// using the indefinite_description axiom to extract witnesses
/// of disjoint memories from squashed proofs of `star`


#push-options "--max_fuel 1"
let split_mem_ghost (p1 p2:hprop) (m:hheap (p1 `Star` p2))
  : GTot (ms:(hheap p1 & hheap p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = let open FStar.IndefiniteDescription in
    let (| m1, p |)
      : (m1:heap &
        (exists (m2:heap).
          m1 `disjoint` m2 /\
          m == join m1 m2 /\
          interp p1 m1 /\
          interp p2 m2))
        =
      indefinite_description
        heap
        (fun (m1:heap) ->
          exists (m2:heap).
            m1 `disjoint` m2 /\
            m == join m1 m2 /\
            interp p1 m1 /\
            interp p2 m2)
    in
    let p :
      (exists (m2:heap).
        m1 `disjoint` m2 /\
        m == join m1 m2 /\
        interp p1 m1 /\
        interp p2 m2) = p
    in
    let _ = FStar.Squash.return_squash p in
    let (| m2, _ |) =
      indefinite_description
        heap
        (fun (m2:heap) ->
           m1 `disjoint` m2 /\
           m == join m1 m2 /\
           interp p1 m1 /\
           interp p2 m2)
    in
    (m1, m2)

(* Properties of star *)

let star_commutative (p1 p2:hprop) = ()

let star_associative (p1 p2 p3:hprop)
= let ltor (m:heap)
  : Lemma
    (requires interp (p1 `star` (p2 `star` p3)) m)
    (ensures interp ((p1 `star` p2) `star` p3) m)
    [SMTPat (interp (p1 `star` (p2 `star` p3)) m)]
  = let (m1, m2) = split_mem_ghost p1 (p2 `star` p3) m in
    let (m2, m3) = split_mem_ghost p2 p3 m2 in
    intro_star p1 p2 m1 m2;
    intro_star (p1 `star` p2) p3 (m1 `join` m2) m3 in

  let rtol (p1 p2 p3:hprop) (m:heap)
  : Lemma
    (requires interp ((p1 `star` p2) `star` p3) m)
    (ensures interp (p1 `star` (p2 `star` p3)) m)
    [SMTPat (interp (p1 `star` (p2 `star` p3)) m)]
  = let (m1, m3) = split_mem_ghost (p1 `star` p2) p3 m in
    let (m1, m2) = split_mem_ghost p1 p2 m1 in
    intro_star p2 p3 m2 m3;
    intro_star p1 (p2 `star` p3) m1 (m2 `join` m3) in
  ()

let star_congruence (p1 p2 p3 p4:hprop) = ()

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////
let intro_wand_alt (p1 p2:hprop) (m:heap)
  : Lemma
    (requires
      (forall (m0:hheap p1).
         disjoint m0 m ==>
         interp p2 (join m0 m)))
    (ensures
      interp (wand p1 p2) m)
  = ()

let intro_wand (p q r:hprop) (m:hheap q)
  : Lemma
    (requires
      (forall (m:hheap (p `star` q)). interp r m))
    (ensures
      interp (p `wand` r) m)
  = let aux (m0:hheap p)
      : Lemma
        (requires
          disjoint m0 m)
        (ensures
          interp r (join m0 m))
        [SMTPat (disjoint m0 m)]
      = ()
    in
    intro_wand_alt p r m

#push-options "--max_fuel 2 --initial_fuel 2"
let elim_wand (p1 p2:hprop) (m:heap) = ()
#pop-options

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////

let intro_or_l (p1 p2:hprop) (m:hheap p1)
  : Lemma (interp (h_or p1 p2) m)
  = ()

let intro_or_r (p1 p2:hprop) (m:hheap p2)
  : Lemma (interp (h_or p1 p2) m)
  = ()

#push-options "--max_fuel 2 --initial_fuel 2"
let or_star (p1 p2 p:hprop) (m:hheap ((p1 `star` p) `h_or` (p2 `star` p)))
  : Lemma (interp ((p1 `h_or` p2) `star` p) m)
  = ()
#pop-options

let elim_or (p1 p2 q:hprop) (m:hheap (p1 `h_or` p2))
  : Lemma (((forall (m:hheap p1). interp q m) /\
            (forall (m:hheap p2). interp q m)) ==> interp q m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////

let intro_and (p1 p2:hprop) (m:heap)
  : Lemma (interp p1 m /\
           interp p2 m ==>
           interp (p1 `h_and` p2) m)
  = ()

let elim_and (p1 p2:hprop) (m:hheap (p1 `h_and` p2))
  : Lemma (interp p1 m /\
           interp p2 m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

let intro_exists (#a:_) (x:a) (p : a -> hprop) (m:hheap (p x))
  : Lemma (interp (h_exists p) m)
  = ()

let elim_exists (#a:_) (p:a -> hprop) (q:hprop) (m:hheap (h_exists p))
  : Lemma
    ((forall (x:a). interp (p x) m ==> interp q m) ==>
     interp q m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

let intro_forall (#a:_) (p : a -> hprop) (m:heap)
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)
  = ()

let elim_forall (#a:_) (p : a -> hprop) (m:hheap (h_forall p))
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)
  = ()

////////////////////////////////////////////////////////////////////////////////

#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --warn_error -271 --initial_ifuel 1 --max_ifuel 1"
let rec affine_star_aux (p:hprop) (m:heap) (m':heap { disjoint m m' })
  : Lemma
    (ensures interp p m ==> interp p (join m m'))
    [SMTPat (interp p (join m m'))]
  = match p with
    | Emp -> ()

    | Pts_to _ _ _ -> ()
    | Pts_to_array _ _ _ -> ()

    | Refine p q -> affine_star_aux p m m'

    | And p1 p2 -> affine_star_aux p1 m m'; affine_star_aux p2 m m'

    | Or p1 p2 -> affine_star_aux p1 m m'; affine_star_aux p2 m m'

    | Star p1 p2 ->
      let aux (m1 m2:heap) (m':heap {disjoint m m'})
        : Lemma
          (requires
            disjoint m1 m2 /\
            m == join m1 m2 /\
            interp p1 m1 /\
            interp p2 m2)
          (ensures interp (Star p1 p2) (join m m'))
          [SMTPat (interp (Star p1 p2) (join (join m1 m2) m'))]
        = affine_star_aux p2 m2 m';
          // assert (interp p2 (join m2 m'));
          affine_star_aux p1 m1 (join m2 m');
          // assert (interp p1 (join m1 (join m2 m')));
          join_associative m1 m2 m';
          // assert (disjoint m1 (join m2 m'));
          intro_star p1 p2 m1 (join m2 m')
      in
      ()

    | Wand p q ->
      let aux (mp:hheap p)
        : Lemma
          (requires
            disjoint mp (join m m') /\
            interp (wand p q) m)
          (ensures (interp q (join mp (join m m'))))
          [SMTPat  ()]
        = disjoint_join mp m m';
          assert (disjoint mp m);
          assert (interp q (join mp m));
          join_associative mp m m';
          affine_star_aux q (join mp m) m'
      in
      assert (interp (wand p q) m ==> interp (wand p q) (join m m'))

    | Ex #a f ->
      let aux (x:a)
        : Lemma (ensures interp (f x) m ==> interp (f x) (join m m'))
                [SMTPat ()]
        = W.axiom1 f x;
          affine_star_aux (f x) m m'
      in
      ()

    | All #a f ->
      let aux (x:a)
        : Lemma (ensures interp (f x) m ==> interp (f x) (join m m'))
                [SMTPat ()]
        = W.axiom1 f x;
          affine_star_aux (f x) m m'
      in
      ()
#pop-options

let affine_star (p q:hprop) (m:heap)
  : Lemma
    (ensures (interp (p `star` q) m ==> interp p m /\ interp q m))
  = ()

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////

let intro_emp (m:heap)
  : Lemma (interp emp m)
  = ()

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let emp_unit (p:hprop)
  : Lemma
    ((p `star` emp) `equiv` p)
  = let emp_unit_1 (p:hprop) (m:heap)
      : Lemma
        (requires interp p m)
        (ensures  interp (p `star` emp) m)
        [SMTPat (interp (p `star` emp) m)]
      = let emp_m : heap = on _ (fun _ -> None) in
        assert (disjoint emp_m m);
        assert (interp (p `star` emp) (join m emp_m));
        assert (mem_equiv m (join m emp_m));
        intro_star p emp m emp_m
    in
    let emp_unit_2 (p:hprop) (m:heap)
      : Lemma
        (requires interp (p `star` emp) m)
        (ensures interp p m)
        [SMTPat (interp (p `star` emp) m)]
      = affine_star p emp m
    in
    ()
#pop-options

////////////////////////////////////////////////////////////////////////////////
// Frameable heap predicates
////////////////////////////////////////////////////////////////////////////////
let weaken_depends_only_on (q:heap -> prop) (fp fp': hprop)
  : Lemma (depends_only_on q fp ==> depends_only_on q (fp `star` fp'))
  = ()

let refine (p:hprop) (q:fp_prop p) : hprop = Refine p q

let refine_equiv (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (interp p h /\ q h <==> interp (Refine p q) h)
  = ()

#push-options "--initial_fuel 2 --max_fuel 2"
let refine_star (p0 p1:hprop) (q:fp_prop p0)
  : Lemma (equiv (Refine (p0 `star` p1) q) (Refine p0 q `star` p1))
  = ()
#pop-options

#push-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 10"
let refine_star_r (p0 p1:hprop) (q:fp_prop p1)
  : Lemma (equiv (Refine (p0 `star` p1) q) (p0 `star` Refine p1 q))
  = ()
#pop-options

let interp_depends_only (p:hprop)
  : Lemma (interp p `depends_only_on` p)
  = ()

let refine_elim (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (requires
            interp (Refine p q) h)
          (ensures
            interp p h /\ q h)
  = refine_equiv p q h
