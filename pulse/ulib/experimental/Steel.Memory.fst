
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

noeq type array_seq_member (a: Type) = {
   value: a;
   perm: (p:permission{allows_read p});
   preorder: Preorder.preorder a
}

let invert_array_seq_member (a: Type0)
  : Lemma
    (requires True)
    (ensures (inversion (array_seq_member a)))
    [ SMTPat (array_seq_member a) ]
  =
  allow_inversion (array_seq_member a)

let array_seq (a: Type) (len: nat) = Seq.lseq (option (array_seq_member a)) len

noeq
type cell =
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
  : (array_seq_member a)
  = Some?.v (Seq.index s i)

let update_addr (m:heap) (a:addr) (c:cell)
  : heap
  = on _ (fun a' -> if a = a' then Some c else m a')

let disjoint_addr (m0 m1:heap) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some (Array t0 len0 seq0), Some (Array t1 len1 seq1) ->
      t0 == t1 /\
      len0 == len1 /\
      (forall (i:nat{i < len0}).
        match contains_index seq0 i, contains_index seq1 i with
	| true, true ->
          let x0 = select_index seq0 i in
	  let x1 = select_index seq1 i in
          x0.value == x1.value /\ summable_permissions x0.perm x1.perm /\
          x0.preorder == x1.preorder
        | _ -> True
      )
    | Some _, None
    | None, Some _
    | None, None ->
      True

    | _ ->
      False

module U32 = FStar.UInt32

noeq type array_ref (a: Type0) : Type0 = {
  array_addr: addr;
  array_max_length: U32.t;
  array_length: n:U32.t{U32.v n <= U32.v array_max_length};
  array_offset: n:U32.t{U32.v n + U32.v array_length <= U32.v array_max_length};
}


let invert_array_ref_s (a: Type0)
  : Lemma
    (requires True)
    (ensures (inversion (array_ref a)))
    [ SMTPat (array_ref a) ]
  =
  allow_inversion (array_ref a)

let length (#t: Type) (a: array_ref t) = a.array_length


let offset (#t: Type) (a: array_ref t) = a.array_offset

let max_length (#t: Type) (a: array_ref t) = a.array_max_length

let address (#t: Type) (a: array_ref t) = a.array_addr

let reference (t: Type u#0) = a:array_ref t{
  length a = 1ul /\ offset a = 0ul /\ max_length a = 1ul
}

let ref_address (#t: Type0) (r: reference t) = r.array_addr

let disjoint_heap (m0 m1:heap)
  : prop
  = forall a. disjoint_addr m0 m1 a

let disjoint_sym_heap (m0 m1:heap)
  : Lemma (disjoint_heap m0 m1 <==> disjoint_heap m1 m0)
  = ()

let join_heap (m0:heap) (m1:heap{disjoint_heap m0 m1})
  : heap
  = on _ (fun a ->
      match m0 a, m1 a with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some (Array a0 len0 seq0), Some (Array a1 len1 seq1) ->
        Some (Array a0 len0 (Seq.init len0 (fun i ->
          match contains_index seq0 i,  contains_index seq1 i with
	  | true, true ->
            let x1 = select_index seq1 i in
            let x0 = select_index seq0 i in
	    Some ({x0 with
              perm = (sum_permissions x0.perm x1.perm <: (perm:permission{allows_read perm}))
            })
          | true, false -> Seq.index seq0 i
          | false, true -> Seq.index seq1 i
	  | false, false -> None
      )))
  )

#push-options "--initial_ifuel 1 --max_ifuel 1 --z3rlimit 200"
let disjoint_join_addr' (m0 m1 m2:heap) (a: addr) : Lemma (disjoint_heap m1 m2 /\
           disjoint_heap m0 (join_heap m1 m2) ==>
	   disjoint_heap m0 m1 /\
           disjoint_heap m0 m2 /\
	   disjoint_addr (join_heap m0 m1) m2 a /\
           disjoint_addr (join_heap m0 m2) m1 a)
  =
  ()
#pop-options

let disjoint_join' (m0 m1 m2:heap)
  : Lemma (disjoint_heap m1 m2 /\
           disjoint_heap m0 (join_heap m1 m2) ==>
           disjoint_heap m0 m1 /\
           disjoint_heap m0 m2 /\
           disjoint_heap (join_heap m0 m1) m2 /\
           disjoint_heap (join_heap m0 m2) m1)
          [SMTPat (disjoint_heap m0 (join_heap m1 m2))]
  =
  Classical.forall_intro (disjoint_join_addr' m0 m1 m2)

let disjoint_join_heap m0 m1 m2 = disjoint_join' m0 m1 m2

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
      disjoint_heap m0 m1)
    (ensures
      join_heap m0 m1 `mem_equiv` join_heap m1 m0)
    [SMTPat (join_heap m0 m1)]
  =
  let aux (a: addr) : Lemma ((join_heap m0 m1) a == (join_heap m1 m0) a) =
    match (join_heap m0 m1) a, (join_heap m1 m0) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in Classical.forall_intro aux

let join_commutative_heap (m0 m1:heap)
: Lemma
  (requires disjoint_heap m0 m1)
  (ensures (disjoint_sym_heap m0 m1; join_heap m0 m1 == join_heap m1 m0))
= ()

#push-options "--z3rlimit 35"
let join_associative' (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint_heap m1 m2 /\
      disjoint_heap m0 (join_heap m1 m2))
    (ensures
      (disjoint_join_heap m0 m1 m2;
       join_heap m0 (join_heap m1 m2) `mem_equiv` join_heap (join_heap m0 m1) m2))
    [SMTPatOr
      [[SMTPat (join_heap m0 (join_heap m1 m2))];
       [SMTPat (join_heap (join_heap m0 m1) m2)]]]
  =
  let aux (a: addr) : Lemma ((join_heap m0 (join_heap m1 m2)) a == (join_heap (join_heap m0 m1) m2) a) =
    match  (join_heap m0 (join_heap m1 m2)) a, (join_heap (join_heap m0 m1) m2) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in Classical.forall_intro aux
#pop-options

let join_associative_heap (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint_heap m1 m2 /\
      disjoint_heap m0 (join_heap m1 m2))
    (ensures
      (disjoint_join_heap m0 m1 m2;
       join_heap m0 (join_heap m1 m2) == join_heap (join_heap m0 m1) m2))

= join_associative' m0 m1 m2

#push-options "--initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
let join_associative2 (m0 m1 m2:heap)
  : Lemma
    (requires
      disjoint_heap m0 m1 /\
      disjoint_heap (join_heap m0 m1) m2)
    (ensures
      disjoint_heap m1 m2 /\
      disjoint_heap m0 (join_heap m1 m2) /\
      join_heap m0 (join_heap m1 m2) `mem_equiv` join_heap (join_heap m0 m1) m2)
    [SMTPat (join_heap (join_heap m0 m1) m2)]
  =
  let aux (a: addr) : Lemma (disjoint_addr m1 m2 a) =
    match  m1 a, m2 a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      ()
    | _ -> ()
  in Classical.forall_intro aux;
  assert(disjoint_heap m1 m2);
  let aux (a: addr) : Lemma (disjoint_addr m0 (join_heap m1 m2) a) =
    match  m0 a, (join_heap m1 m2) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      ()
    | _ -> ()
  in Classical.forall_intro aux;
  assert(disjoint_heap m0 (join_heap m1 m2));
  let aux (a: addr) : Lemma ((join_heap m0 (join_heap m1 m2)) a == (join_heap (join_heap m0 m1) m2) a) =
    match  (join_heap m0 (join_heap m1 m2)) a, (join_heap (join_heap m0 m1) m2) a with
    | Some (Array t2 len2 seq2), Some (Array t3 len3 seq3) ->
      assert(seq2 `Seq.equal` seq3)
    | _ -> ()
  in Classical.forall_intro aux
#pop-options

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let heap_prop_is_affine (p:heap -> prop) = forall m0 m1. p m0 /\ disjoint_heap m0 m1 ==> p (join_heap m0 m1)
let a_heap_prop = p:(heap -> prop) { heap_prop_is_affine p }

////////////////////////////////////////////////////////////////////////////////

module W = FStar.WellFounded

noeq
type hprop : Type u#1 =
  | Emp : hprop
  | Pts_to_array: #t:Type0 -> a:array_ref t -> perm:permission{allows_read perm} ->
		  contents:Ghost.erased (Seq.lseq t (U32.v (length a))) ->
                  preorder: Ghost.erased (Preorder.preorder t) -> hprop
  | Refine : hprop -> a_heap_prop -> hprop
  | And  : hprop -> hprop -> hprop
  | Or   : hprop -> hprop -> hprop
  | Star : hprop -> hprop -> hprop
  | Wand : hprop -> hprop -> hprop
  | Ex   : #a:Type0 -> (a -> hprop) -> hprop
  | All  : #a:Type0 -> (a -> hprop) -> hprop

noeq
type lock_state =
  | Available : hprop -> lock_state
  | Locked    : hprop -> lock_state
  | Invariant : hprop -> lock_state

let lock_store = list lock_state

noeq
type mem = {
  ctr: nat;
  heap: heap;
  locks: lock_store;
}

let heap_of_mem (x:mem) : heap = x.heap

let mem_of_heap (h:heap) : mem = {
  ctr = 0;
  heap = h;
  locks = []
}

let _ : squash (inversion hprop) = allow_inversion hprop

let disjoint m0 m1 =
  m0.ctr == m1.ctr /\
  disjoint_heap m0.heap m1.heap /\
  m0.locks == m1.locks

let disjoint_sym m0 m1 = ()

let join m0 m1 = {
  ctr = m0.ctr;
  heap = join_heap m0.heap m1.heap;
  locks = m0.locks
}

let disjoint_join m0 m1 m2 = ()

let join_commutative m0 m1 = ()

let join_associative m0 m1 m2 = ()

let rec interp_heap (p:hprop) (m:heap)
  : Tot prop (decreases p)
  = match p with
    | Emp -> True
    | Pts_to_array #t a perm contents preorder ->
      m `contains_addr` a.array_addr /\
      (match select_addr m a.array_addr with
        | Array t' len' seq ->
	  t' == t /\
	  U32.v a.array_offset + U32.v a.array_length <= len' /\
          (forall (i:nat{i < len'}).
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
	     (* Outside of the range *)
             True
            else if contains_index seq i then
	      (* In the range, contains some value *)
	      let x = Seq.index contents (i - U32.v a.array_offset) in
	      let x' = select_index seq i in
	      x == x'.value /\
              x'.preorder == Ghost.reveal preorder /\
	      perm `lesser_equal_permission` x'.perm
            else (* In the range, does not contain anything *) False
          )
	| _ -> False
      )
    | Refine p q ->
      interp_heap p m /\ q m

    | And p1 p2 ->
      interp_heap p1 m /\
      interp_heap p2 m

    | Or  p1 p2 ->
      interp_heap p1 m \/
      interp_heap p2 m

    | Star p1 p2 ->
      exists m1 m2.
        m1 `disjoint_heap` m2 /\
        m == join_heap m1 m2 /\
        interp_heap p1 m1 /\
        interp_heap p2 m2

    | Wand p1 p2 ->
      forall m1.
        m `disjoint_heap` m1 /\
        interp_heap p1 m1 ==>
        interp_heap p2 (join_heap m m1)

    | Ex f ->
      exists x. (W.axiom1 f x; interp_heap (f x) m)

    | All f ->
      forall x. (W.axiom1 f x; interp_heap (f x) m)

let interp p m = interp_heap p m.heap

let equiv_heap (p1 p2:hprop) : prop =
  forall (h:heap). interp_heap p1 h <==> interp_heap p2 h

#push-options "--warn_error -271"
let equiv_heap_iff_equiv (p1 p2:hprop)
: Lemma
  (equiv_heap p1 p2 <==> equiv p1 p2)
= let aux_lr ()
    : Lemma
      (requires equiv_heap p1 p2)
      (ensures equiv p1 p2)
      [SMTPat ()]
    = () in

  let aux_rl_helper1 (h:heap)
    : Lemma
      (requires equiv p1 p2 /\ interp_heap p1 h)
      (ensures interp_heap p2 h)
      [SMTPat ()]
    = assert (interp p2 (mem_of_heap h))
  in

  let aux_rl_helper2 (h:heap)
    : Lemma
      (requires equiv p1 p2 /\ interp_heap p2 h)
      (ensures interp_heap p1 h)
      [SMTPat ()]
    = assert (interp p2 (mem_of_heap h))
  in

  let aux_rl ()
    : Lemma
      (requires equiv p1 p2)
      (ensures equiv_heap p1 p2)
      [SMTPat ()]
    = () in
  ()
#pop-options

let emp = Emp
let pts_to_array_with_preorder = Pts_to_array
let pts_to_ref
  (#t: Type0)
  (r: reference t)
  (p:permission{allows_read p})
  (contents: Ghost.erased t)
  (preorder: Ghost.erased (Preorder.preorder t))
  = pts_to_array_with_preorder r p (Seq.Base.create 1 (Ghost.reveal contents)) preorder
let h_and = And
let h_or = Or
let star = Star
let wand = Wand
let h_exists = Ex
let h_forall = All

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////


let equiv_symmetric p1 p2 = ()

#set-options "--max_fuel 1 --initial_fuel 1 --initial_ifuel 0 --max_ifuel 0"

let equiv_extensional_on_star p1 p2 p3 =
  Classical.forall_intro_2 equiv_heap_iff_equiv

////////////////////////////////////////////////////////////////////////////////
// pts_to_array
////////////////////////////////////////////////////////////////////////////////

let intro_pts_to_array_with_preorder
  (#t: Type0)
  (a:array_ref t)
  (perm:permission{allows_read perm})
  (contents:Seq.lseq t (U32.v a.array_length))
  (preorder: Preorder.preorder t)
  (m:heap)
  : Lemma
    (requires (
    m `contains_addr` a.array_addr /\
      (match select_addr m a.array_addr with
        | Array t' len' seq ->
	  t' == t /\
	  U32.v a.array_offset + U32.v a.array_length <= len' /\
          (forall (i:nat{i < len'}).
            if i < U32.v a.array_offset || i >= U32.v a.array_offset + U32.v a.array_length then
	     (* Outside of the range *)
             True
            else if contains_index seq i then
	      (* In the range, contains some value *)
	      let x = Seq.index contents (i - U32.v a.array_offset) in
	      let x' = select_index seq i in
	      x == x'.value /\
              x'.preorder == Ghost.reveal preorder /\
	      perm `lesser_equal_permission` x'.perm
            else (* In the range, does not contain anything *) False
          )
	| _ -> False
      )
    ))
    (ensures (interp_heap (pts_to_array_with_preorder a perm contents preorder) m))
  =
  ()

let pts_to_array_injective #t a p c0 c1 pre m =
  match select_addr m.heap a.array_addr with
  | Array t' len' seq ->
    let aux (i':nat{i' < U32.v a.array_length})
      : Lemma (Seq.index c0 i' == Seq.index c1 i')
    =
      let i = i' + U32.v a.array_offset in
      assert(contains_index seq i);
      let x0 = Seq.index c0 i' in
      let x1 = Seq.index c1 i' in
      let x' = select_index seq i in
      assert(x'.value == x0);
      assert(x'.value == x1);
      assert(x0 == x1)
    in
    Classical.forall_intro aux;
    assert(c0 `Seq.equal` c1)
  | _ -> ()

////////////////////////////////////////////////////////////////////////////////
// pts_to_ref
////////////////////////////////////////////////////////////////////////////////

let pts_to_ref_injective #t a p c0 c1 pre m =
  let s0 = Seq.create 1 c0 in
  let s1 = Seq.create 1 c1 in
  pts_to_array_injective a p s0 s1 pre m;
  assert(s0 `Seq.equal` s1);
  assert(c0 == Seq.index s0 0);
  assert(c1 == Seq.index s1 0)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

let intro_star_heap (p q:hprop) (mp:heap{interp_heap p mp}) (mq:heap{interp_heap q mq})
  : Lemma
    (requires
      disjoint_heap mp mq)
    (ensures
      interp_heap (p `star` q) (join_heap mp mq))
  = ()


let intro_star (p q:hprop) (mp:hmem p) (mq:hmem q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))
  = ()

(* Properties of star *)

#push-options "--z3rlimit 10"
let star_commutative (p1 p2:hprop) = ()
#pop-options

#push-options "--max_fuel 2 --initial_fuel 2 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 10"
let star_associative (p1 p2 p3:hprop)
= ()
#pop-options

let star_congruence (p1 p2 p3 p4:hprop) = Classical.forall_intro_2 equiv_heap_iff_equiv

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////
let intro_wand_alt_heap (p1 p2:hprop) (m:heap)
  : Lemma
    (requires
      (forall (m0:heap{interp_heap p1 m0}).
         disjoint_heap m0 m ==>
         interp_heap p2 (join_heap m0 m)))
    (ensures
      interp_heap (wand p1 p2) m)
= ()

#push-options "--warn_error -271"
let intro_wand_alt p1 p2 m =
  assert (forall (m0:hmem p1). disjoint m0 m ==> interp p2 (join m0 m));
  let aux (h0:heap{interp_heap p1 h0})
    : Lemma
      (disjoint_heap h0 m.heap ==> interp_heap p2 (join_heap h0 m.heap))
      [SMTPat ()]
    = let m0 : mem = { ctr = m.ctr; heap = h0; locks = m.locks } in
      assert (disjoint_heap h0 m.heap ==> disjoint m0 m)
  in
  intro_wand_alt_heap p1 p2 m.heap
#pop-options

let intro_wand p q r m =
  let aux (m0:hmem p)
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
let elim_wand p1 p2 m = ()
#pop-options

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////

let intro_or_l p1 p2 m = ()

let intro_or_r p1 p2 m = ()

#push-options "--max_fuel 2 --initial_fuel 2"
let or_star p1 p2 p m = ()
#pop-options

let elim_or p1 p2 q m = ()


////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////

let intro_and p1 p2 m = ()

let elim_and p1 p2 m = ()


////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

let intro_exists #a x p m = ()

let elim_exists #a p q m = ()


////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

let intro_forall #a p m = ()

let elim_forall #a p m = ()

////////////////////////////////////////////////////////////////////////////////

#restart-solver
#push-options "--z3rlimit 300 --initial_fuel 2 --max_fuel 2 --warn_error -271 --initial_ifuel 1 --max_ifuel 1"
let rec affine_star_aux (p:hprop) (m:heap) (m':heap { disjoint_heap m m' })
  : Lemma
    (ensures interp_heap p m ==> interp_heap p (join_heap m m'))
    [SMTPat (interp_heap p (join_heap m m'))]
  = match p with
    | Emp -> ()
    | Pts_to_array _ _ _ _ -> ()
    | Refine p q -> affine_star_aux p m m'
    | And p1 p2 -> affine_star_aux p1 m m'; affine_star_aux p2 m m'
    | Or p1 p2 -> affine_star_aux p1 m m'; affine_star_aux p2 m m'
    | Star p1 p2 ->
      let aux (m1 m2:heap) (m':heap {disjoint_heap m m'})
        : Lemma
          (requires
            disjoint_heap m1 m2 /\
            m == join_heap m1 m2 /\
            interp_heap p1 m1 /\
            interp_heap p2 m2)
          (ensures interp_heap (Star p1 p2) (join_heap m m'))
          [SMTPat (interp_heap (Star p1 p2) (join_heap (join_heap m1 m2) m'))]
        =
          disjoint_join_heap m' m1 m2;
          assume (disjoint_heap m2 m');
          affine_star_aux p2 m2 m';  //AR: this is the problematic line (disjointness of m2 and m')?
          // assert (interp p2 (join m2 m'));
          affine_star_aux p1 m1 (join_heap m2 m');
          // assert (interp p1 (join m1 (join m2 m')));
          join_associative_heap m1 m2 m';
          // assert (disjoint m1 (join m2 m'));
          intro_star_heap p1 p2 m1 (join_heap m2 m')
      in
      ()
    | Wand p q ->
      let aux (mp:heap{interp_heap p mp})
        : Lemma
          (requires
            disjoint_heap mp (join_heap m m') /\
            interp_heap (wand p q) m)
          (ensures (interp_heap q (join_heap mp (join_heap m m'))))
          [SMTPat  ()]
        = disjoint_join_heap mp m m';
          assert (disjoint_heap mp m);
          assert (interp_heap q (join_heap mp m));
          join_associative_heap mp m m';
          affine_star_aux q (join_heap mp m) m'
      in
      assert (interp_heap (wand p q) m ==> interp_heap (wand p q) (join_heap m m'))
    | Ex #a f ->
      let aux (x:a)
        : Lemma (ensures interp_heap (f x) m ==> interp_heap (f x) (join_heap m m'))
                [SMTPat ()]
        = W.axiom1 f x;
          affine_star_aux (f x) m m'
      in
      ()
    | All #a f ->
      let aux (x:a)
        : Lemma (ensures interp_heap (f x) m ==> interp_heap (f x) (join_heap m m'))
                [SMTPat ()]
        = W.axiom1 f x;
          affine_star_aux (f x) m m'
      in
      ()
#pop-options

let affine_star_heap (p q:hprop) (m:heap)
  : Lemma
    (ensures (interp_heap (p `star` q) m ==> interp_heap p m /\ interp_heap q m)) = ()

let affine_star p q m = ()

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////

let intro_emp m = ()

#push-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let emp_unit (p:hprop)
  : Lemma
    ((p `star` emp) `equiv` p)
  = let emp_unit_1 (p:hprop) (m:heap)
      : Lemma
        (requires interp_heap p m)
        (ensures  interp_heap (p `star` emp) m)
        [SMTPat (interp_heap (p `star` emp) m)]
      = let emp_m : heap = on _ (fun _ -> None) in
        assert (disjoint_heap emp_m m);
        assert (interp_heap (p `star` emp) (join_heap m emp_m));
        assert (mem_equiv m (join_heap m emp_m));
        intro_star_heap p emp m emp_m
    in
    let emp_unit_2 (p:hprop) (m:heap)
      : Lemma
        (requires interp_heap (p `star` emp) m)
        (ensures interp_heap p m)
        [SMTPat (interp_heap (p `star` emp) m)]
      = affine_star_heap p emp m
    in
    ()
#pop-options

////////////////////////////////////////////////////////////////////////////////
// Frameable heap predicates
////////////////////////////////////////////////////////////////////////////////
let depends_only_on (q:heap -> prop) (fp: hprop) =
  (forall h0 h1. q h0 /\ disjoint_heap h0 h1 ==> q (join_heap h0 h1)) /\
  (forall (h0:heap{interp_heap fp h0}) (h1:heap{disjoint_heap h0 h1}). q h0 <==> q (join_heap h0 h1))

let fp_prop fp = p:(heap -> prop){p `depends_only_on` fp}

let weaken_depends_only_on (q:heap -> prop) (fp fp': hprop)
  : Lemma (depends_only_on q fp ==> depends_only_on q (fp `star` fp'))
  = ()

let refine (p:hprop) (q:fp_prop p) : hprop = Refine p q

let refine_equiv (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (interp_heap p h /\ q h <==> interp_heap (Refine p q) h)
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
  : Lemma (interp_heap p `depends_only_on` p)
  = ()

let refine_elim (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (requires
            interp_heap (Refine p q) h)
          (ensures
            interp_heap p h /\ q h)
  = refine_equiv p q h


#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"


////////////////////////////////////////////////////////////////////////////////
// allocation and locks
////////////////////////////////////////////////////////////////////////////////

let lock_addr = nat

let _ : squash (inversion lock_state) = allow_inversion lock_state

#push-options "--max_ifuel 1 --initial_ifuel 1"
let rec lock_store_invariant (e:S.set lock_addr) (l:lock_store) : hprop =
  let current_addr = List.Tot.length l - 1 in
  match l with
  | [] -> emp
  | Available p :: tl -> p `star` lock_store_invariant e tl
  | Locked _ :: tl -> lock_store_invariant e tl
  | Invariant p :: tl ->
    if current_addr `S.mem` e then
      lock_store_invariant e tl
    else
      p `star` lock_store_invariant e tl

#pop-options

let heap_ctr_valid (m:mem) : heap -> prop =
  fun _ ->
  forall (i:nat). i >= m.ctr ==> m.heap i == None

let locks_invariant (e:S.set lock_addr) (m:mem) : hprop =
  refine (lock_store_invariant e m.locks) (heap_ctr_valid m)

let core_mem m = mem_of_heap (heap_of_mem m)

let core_mem_interp hp m = ()

let interp_depends_only_on hp = ()
