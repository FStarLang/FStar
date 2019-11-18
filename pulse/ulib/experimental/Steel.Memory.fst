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
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell =
  | Ref : a:Type u#0 ->
          perm:perm ->
          v:a ->
          cell

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
  = F.on _ (fun a' -> if a = a' then Some c else m a')

let disjoint_addr (m0 m1:heap) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some (Ref t0 p0 v0), Some (Ref t1 p1 v1) ->
      p0 +. p1 <=. 1.0R /\
      t0 == t1 /\
      v0 == v1

    | Some _, None
    | None, Some _
    | None, None ->
      True

    | _ ->
      False

let ref (a:Type) = addr

let disjoint (m0 m1:heap)
  : prop
  = forall a. disjoint_addr m0 m1 a

let disjoint_sym (m0 m1:heap)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
  = ()

let join (m0:heap) (m1:heap{disjoint m0 m1})
  : heap
  = F.on _ (fun a ->
      match m0 a, m1 a with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some (Ref a0 p0 v0), Some (Ref a1 p1 v1) ->
        Some (Ref a0 (p0 +. p1) v0))

let disjoint_join' (m0 m1 m2:heap)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)
          [SMTPat (disjoint m0 (join m1 m2))]
  = ()

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
  = F.extensionality _ _ m0 m1

let join_commutative' (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 `mem_equiv` join m1 m0)
    [SMTPat (join m0 m1)]
  = ()

let join_commutative m0 m1 = ()

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
  = ()

let join_associative (m0 m1 m2:heap) = join_associative' m0 m1 m2

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
  = ()

let mem_prop_is_affine (p:mem -> prop) = forall m0 m1. p m0 /\ disjoint m0 m1 ==> p (join m0 m1)
let a_m_prop = p:(mem -> prop) { mem_prop_is_affine p }

////////////////////////////////////////////////////////////////////////////////

module W = FStar.WellFounded

noeq
type hprop : Type u#1 =
  | Emp : hprop
  | Pts_to : #a:Type0 -> r:ref a -> perm:perm -> v:a -> hprop
  | Refine : hprop -> a_m_prop -> hprop
  | And  : hprop -> hprop -> hprop
  | Or   : hprop -> hprop -> hprop
  | Star : hprop -> hprop -> hprop
  | Wand : hprop -> hprop -> hprop
  | Ex   : #a:Type0 -> (a -> hprop) -> hprop
  | All  : #a:Type0 -> (a -> hprop) -> hprop

let rec interp (p:hprop) (m:heap)
  : Tot prop (decreases p)
  = match p with
    | Emp -> True
    | Pts_to #a r perm v ->
      m `contains_addr` r /\
      (let Ref a' perm' v' = select_addr m r in
       a == a' /\
       v == v' /\
       perm <=. perm')

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
let h_and = And
let h_or = Or
let star = Star
let wand = Wand
let h_exists = Ex
let h_forall = All

let star_commutative (p1 p2:hprop) = ()

#push-options "--query_stats --z3rlimit_factor 4 --max_fuel 2 --initial_fuel 2 --max_ifuel 2 --initial_ifuel 2"
let star_associative (p1 p2 p3:hprop) = ()
#pop-options

let star_congruence (p1 p2 p3 p4:hprop) = ()

let sel #a (r:ref a) (m:hheap (ptr r))
  : a
  = let Ref _ _ v = select_addr m r in
    v

let sel_lemma #a (r:ref a) (p:perm) (m:hheap (ptr_perm r p))
  = ()

/// The main caveat of this model is that because we're working
/// with proof-irrelevant propositions (squashed proofs), I end up
/// using the indefinite_description axiom to extract witnesses
/// of disjoint memories from squashed proofs of `star`
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

let upd #a (r:ref a) (v:a)
           (frame:hprop) (m:hheap (ptr_perm r 1.0R  `Star` frame))
  : Tot (m:hheap (Pts_to r 1.0R v `Star` frame))
  = let m0, m1 = split_mem (ptr_perm r 1.0R) frame m in
    let m0' = update_addr m0 r (Ref a 1.0R v) in
    join m0' m1

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

let elim_wand (p1 p2:hprop) (m:heap) = ()

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////

let intro_or_l (p1 p2:hprop) (m:hheap p1)
  : Lemma (interp (h_or p1 p2) m)
  = ()

let intro_or_r (p1 p2:hprop) (m:hheap p2)
  : Lemma (interp (h_or p1 p2) m)
  = ()

let or_star (p1 p2 p:hprop) (m:hheap ((p1 `star` p) `h_or` (p2 `star` p)))
  : Lemma (interp ((p1 `h_or` p2) `star` p) m)
  = ()

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

let intro_pts_to (#a:_) (x:ref a) (p:perm) (v:a) (m:heap)
  : Lemma
    (requires
       m `contains_addr` x /\
       (let Ref a' perm' v' = select_addr m x in
        a == a' /\
        v == v' /\
        p <=. perm'))
     (ensures
       interp (pts_to x p v) m)
  = ()

let intro_star (p q:hprop) (mp:hheap p) (mq:hheap q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))
  = ()

#push-options "--z3rlimit_factor 6 --max_fuel 1 --max_ifuel 2  --initial_fuel 2 --initial_ifuel 2"
let rec affine_star_aux (p:hprop) (m:mem) (m':mem { disjoint m m' })
  : Lemma
    (ensures interp p m ==> interp p (join m m'))
    [SMTPat (interp p (join m m'))]
  = match p with
    | Emp -> ()

    | Pts_to _ _ _ -> ()

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
    (ensures (interp (p `star` q) m ==> interp p m))
  = ()

////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////

let intro_emp (m:heap)
  : Lemma (interp emp m)
  = ()

let emp_unit (p:hprop)
  : Lemma
    ((p `star` emp) `equiv` p)
  = let emp_unit_1 (p:hprop) (m:heap)
      : Lemma
        (requires interp p m)
        (ensures  interp (p `star` emp) m)
        [SMTPat (interp (p `star` emp) m)]
      = let emp_m : heap = F.on _ (fun _ -> None) in
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

////////////////////////////////////////////////////////////////////////////////
noeq
type mem = {
  ctr: nat;
  heap: heap;
  properties: squash (
    forall i. i >= ctr ==> heap i == None
  )
}

let heap_of_mem (x:mem) : heap = x.heap

let alloc #a v frame m
  = let x : ref a = m.ctr in
    let cell = Ref a 1.0R v in
    let mem : heap = F.on _ (fun i -> if i = x then Some cell else None) in
    assert (disjoint mem m.heap);
    assert (mem `contains_addr` x);
    assert (select_addr mem x == cell);
    let mem' = join mem m.heap in
    intro_pts_to x 1.0R v mem;
    assert (interp (pts_to x 1.0R v) mem);
    assert (interp frame m.heap);
    intro_star (pts_to x 1.0R v) frame mem m.heap;
    assert (interp (pts_to x 1.0R v `star` frame) mem');
    let t = {
      ctr = x + 1;
      heap = mem';
      properties = ()
    } in
    (| x, t |)
