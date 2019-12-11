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
module Steel.Heap
open Steel.Permissions
open FStar.FunctionalExtensionality

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell =
  | Ref : a:Type u#0 ->
          perm:permission{allows_read perm} ->
          v:a ->
          cell
  | Array: a:Type u#0 ->
           len: nat ->
           seq:Seq.lseq (a & perm:permission{allows_read perm}) len  ->
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

let select_addr (m:heap) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

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
        let (x0, p0) = Seq.index seq0 i in
	let (x1, p1) = Seq.index seq1 i in
	x0 == x1 /\ summable_permissions p0 p1)

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
	  let (x0, p0) = Seq.index seq0 i in
          let (_, p1) = Seq.index seq1 i in
	  (x0, (sum_permissions p0 p1 <: (perm:permission{allows_read perm})))
      )))
  )


#push-options "--initial_ifuel 1 --max_ifuel 1 --z3rlimit 15"
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

#push-options "--z3rlimit 25"
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
