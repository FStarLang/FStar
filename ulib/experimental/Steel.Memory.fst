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
module Steel.Memory
open FStar.Real
open Steel.Permissions
module U32 = FStar.UInt32
open FStar.FunctionalExtensionality

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

// In the future, we may have other cases of cells
// for arrays and structs

let array_seq (a: Type) (len: nat) = Seq.lseq (option (a & perm:permission{allows_read perm})) len


noeq
type cell =
  | Ref : a:Type u#0 ->
          perm:permission{allows_read perm} ->
          v:a ->
          cell
  | Array: a:Type u#0 ->
           len: nat ->
           seq:array_seq a len  ->
	   cell

let _ : squash (inversion cell) = allow_inversion cell

let addr = nat

/// This is just the core of a memory, about which one can write
/// assertions. At one level above, we'll encapsulate this memory
/// with a freshness counter, a lock store etc.
let heap = addr ^-> option cell

let contains_addr (m:heap) (a:addr)
  : bool
  = Some? (m a)

let contains_index (#a: Type) (#len: nat) (s: array_seq a len) (i:nat{i < len})
  : bool
  = Some? (Seq.index s i)

let select_addr (m:heap) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

let select_index (#a: Type) (#len: nat) (s: array_seq a len) (i:nat{i < len /\ contains_index s i})
  : (a & perm:permission{allows_read perm})
  = Some?.v (Seq.index s i)

let update_addr (m:heap) (a:addr) (c:cell)
  : heap
  = on _ (fun a' -> if a = a' then Some c else m a')

let disjoint_addr (m0 m1:heap) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some (Ref t0 p0 v0), Some (Ref t1 p1 v1) ->
      summable_permissions p0 p1 /\
      t0 == t1 /\
      v0 == v1
    | Some (Array t0 len0 seq0), Some (Array t1 len1 seq1) ->
      t0 == t1 /\
      len0 == len1 /\
      (forall (i:nat{i < len0}).
        if contains_index seq0 i && contains_index seq1 i then
          let (x0, p0) = select_index seq0 i in
	  let (x1, p1) = select_index seq1 i in
          x0 == x1 /\ summable_permissions p0 p1
        else if (not (contains_index seq0 i)) && (not (contains_index seq1 i)) then True
        else False
      )
    | Some _, None
    | None, Some _
    | None, None ->
      True

    | _ ->
      False

let ref (a:Type) = addr

module U32 = FStar.UInt32

noeq type array_ref (a: Type0) : Type0 = {
  array_addr: addr;
  array_length: U32.t;
  array_offset: U32.t;
}


let invert_array_ref_s (a: Type0)
  : Lemma
    (requires True)
    (ensures (inversion (array_ref a)))
    [ SMTPat (array_ref a) ]
  =
  allow_inversion (array_ref a)

let offset (#t: Type) (a: array_ref t) = a.array_offset

let length (#t: Type) (a: array_ref t) = a.array_length

let disjoint (m0 m1:heap)
  : prop
  = forall a. disjoint_addr m0 m1 a

let disjoint_sym (m0 m1:heap)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
  = ()

let join (m0:heap) (m1:heap{disjoint m0 m1})
  : heap
  = on _ (fun a ->
      match m0 a, m1 a with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some (Ref a0 p0 v0), Some (Ref a1 p1 v1) ->
        Some (Ref a0 (sum_permissions p0 p1) v0)
      | Some (Array a0 len0 seq0), Some (Array a1 len1 seq1) ->
        Some (Array a0 len0 (Seq.init len0 (fun i ->
          if contains_index seq0 i && contains_index seq1 i then
            let (_, p1) = select_index seq1 i in
            let (x0, p0) = select_index seq0 i in
	    Some (x0, (sum_permissions p0 p1 <: (perm:permission{allows_read perm})))
          else if contains_index seq0 i then
            Seq.index seq0 i
          else if contains_index seq1 i then
            Seq.index seq1 i
          else
            None
      )))
  )


#push-options "--initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
let disjoint_join' (m0 m1 m2:heap)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)
          [SMTPat (disjoint m0 (join m1 m2))]
  =
  let aux (a: addr) : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint_addr m0 m1 a /\
           disjoint_addr m0 m2 a)
   =
    ()
  in
  Classical.forall_intro aux;
  let aux' (a: addr) : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
	   disjoint m0 m1 /\
           disjoint m0 m2 /\
	   disjoint_addr (join m0 m1) m2 a /\
           disjoint_addr (join m0 m2) m1 a)
  =
    ()
  in
  Classical.forall_intro aux'
#pop-options

let disjoint_join m0 m1 m2 = disjoint_join' m0 m1 m2

let mem_equiv (m0 m1:heap) =
  forall a. m0 a == m1 a

let mem_equiv_eq (m0 m1:heap)
  : Lemma
    (requires
      m0 `mem_equiv` m1)
    (ensures
      m0 == m1)
    [SMTPat (m0 `mem_equiv` m1)]
  = extensionality _ _ m0 m1

let join_commutative' (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 `mem_equiv` join m1 m0)
    [SMTPat (join m0 m1)]
  =
  let aux (a: addr) : Lemma ((join m0 m1) a == (join m1 m0) a) =
    match (join m0 m1) a, (join m1 m0) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in Classical.forall_intro aux

let join_commutative m0 m1 = ()

#push-options "--z3rlimit 35"
let join_associative' (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) `mem_equiv` join (join m0 m1) m2))
    [SMTPatOr
      [[SMTPat (join m0 (join m1 m2))];
       [SMTPat (join (join m0 m1) m2)]]]
  =
  let aux (a: addr) : Lemma ((join m0 (join m1 m2)) a == (join (join m0 m1) m2) a) =
    match  (join m0 (join m1 m2)) a, (join (join m0 m1) m2) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in Classical.forall_intro aux
#pop-options

let join_associative (m0 m1 m2:heap) = join_associative' m0 m1 m2

#push-options "--initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
let join_associative2 (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2)
    (ensures
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) /\
      join m0 (join m1 m2) `mem_equiv` join (join m0 m1) m2)
    [SMTPat (join (join m0 m1) m2)]
  =
  let aux (a: addr) : Lemma (disjoint_addr m1 m2 a) =
    match  m1 a, m2 a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      ()
    | _ -> ()
  in Classical.forall_intro aux;
  assert(disjoint m1 m2);
  let aux (a: addr) : Lemma (disjoint_addr m0 (join m1 m2) a) =
    match  m0 a, (join m1 m2) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      ()
    | _ -> ()
  in Classical.forall_intro aux;
  assert(disjoint m0 (join m1 m2));
  let aux (a: addr) : Lemma ((join m0 (join m1 m2)) a == (join (join m0 m1) m2) a) =
    match  (join m0 (join m1 m2)) a, (join (join m0 m1) m2) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in Classical.forall_intro aux
#pop-options

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
		  contents:Ghost.erased (Seq.lseq t (U32.v (length a))) -> hprop
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
          (forall (i:nat{i < len'}).
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
              ~ (contains_index seq i)
            else if perm `lesser_equal_permission` zero_permission then True
            else if contains_index seq i then
	      let x = Seq.index contents (i - U32.v a.array_offset) in
	      let (x', perm') = select_index seq i in
	      x == x' /\
	      perm `lesser_equal_permission` perm'
            else False
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
          (forall (i:nat{i < len'}).
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
              ~ (contains_index seq i)
            else if perm `lesser_equal_permission` zero_permission then True
            else if contains_index seq i then
	      let x = Seq.index contents (i - U32.v a.array_offset) in
	      let (x', perm') = select_index seq i in
	      x == x' /\
	      perm `lesser_equal_permission` perm'
            else False
          )
	| _ -> False)
    ))
    (ensures (interp (pts_to_array a perm contents) m))
  =
  ()

let pts_to_array_injective
  (#t: _)
  (a: array_ref t)
  (p:permission{allows_read p})
  (c0 c1: Seq.lseq t (U32.v (length a)))
  (m: heap)
  =
  match select_addr m a.array_addr with
  | Array t' len' seq ->
    let aux (i':nat{i' < U32.v a.array_length}) : Lemma (Seq.index c0 i' == Seq.index c1 i') =
      let i = i' + U32.v a.array_offset in
      assert(contains_index seq i);
      let x0 = Seq.index c0 i' in
      let x1 = Seq.index c1 i' in
      let (x', p') = select_index seq i in
      assert(x' == x0);
      assert(x' == x1);
      assert(x0 == x1)
    in
    Classical.forall_intro aux;
    assert(c0 `Seq.equal` c1)
  | _ -> ()


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

#push-options "--z3rlimit 10"
let star_commutative (p1 p2:hprop) = ()
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 10"
let star_associative (p1 p2 p3:hprop)
= ()
#pop-options

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

#push-options "--z3rlimit 300 --initial_fuel 1 --max_fuel 1 --warn_error -271 --initial_ifuel 1 --max_ifuel 1"
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


#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"


////////////////////////////////////////////////////////////////////////////////
// allocation and locks
////////////////////////////////////////////////////////////////////////////////
noeq
type lock_state =
  | Available : hprop -> lock_state
  | Locked    : hprop -> lock_state

let _ : squash (inversion lock_state) = allow_inversion lock_state

let lock_store = list lock_state

#push-options "--max_ifuel 1 --initial_ifuel 1"
let rec lock_store_invariant (l:lock_store) : hprop =
  match l with
  | [] -> emp
  | Available h :: tl -> h `star` lock_store_invariant tl
  | _ :: tl -> lock_store_invariant tl
#pop-options

noeq
type mem = {
  ctr: nat;
  heap: heap;
  locks: lock_store;
  properties: squash (
    (forall i. i >= ctr ==> heap i == None) /\
    interp (lock_store_invariant locks) heap
  )
}

let _ : squash (inversion mem) = allow_inversion mem

let locks_invariant (m:mem) : hprop = lock_store_invariant m.locks

let heap_of_mem (x:mem) : heap = x.heap

let m_disjoint (m:mem) (h:heap) =
  disjoint (heap_of_mem m) h /\
  (forall i. i >= m.ctr ==> h i == None)

let upd_joined_heap (m:mem) (h:heap{m_disjoint m h}) =
  let h0 = heap_of_mem m in
  let h = join h0 h in
  {m with heap = h}


/// F*'s indefinite_description is only available in the Ghost effect
/// That's to prevent us from mistakenly extracting code that uses the
/// axiom, since, clearly, we can't execute code that invents witnesses
/// from squashed proofs of existentials.
///
/// Here, we're just building a logical model of heaps, so I don't really
/// care about enforcing the ghostiness of indefinite_description.
///
/// So, this axiom explicitly punches a hole in the ghost effect, allowing
/// me to coerce it to Tot
assume
val axiom_ghost_to_tot (#a:Type) (#b:a -> Type) ($f: (x:a -> GTot (b x))) (x:a)
  : Tot (b x)

let split_mem (p1 p2:hprop) (m:hheap (p1 `Star` p2))
  : Tot (ms:(hheap p1 & hheap p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = axiom_ghost_to_tot (split_mem_ghost p1 p2) m
