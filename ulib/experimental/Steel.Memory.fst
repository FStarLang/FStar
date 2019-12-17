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
open Steel.Permissions

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell =
  | Ref : a:Type u#0 ->
          perm:permission{allows_read perm} ->
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
      summable_permissions p0 p1 /\
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
        Some (Ref a0 (sum_permissions p0 p1) v0))

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

let heap_prop_is_affine (p:heap -> prop) = forall m0 m1. p m0 /\ disjoint m0 m1 ==> p (join m0 m1)
let a_heap_prop = p:(heap -> prop) { heap_prop_is_affine p }

////////////////////////////////////////////////////////////////////////////////

module W = FStar.WellFounded

noeq
type hprop : Type u#1 =
  | Emp : hprop
  | Pts_to : #a:Type0 -> r:ref a -> perm:permission -> v:a -> hprop
  | Refine : hprop -> a_heap_prop -> hprop
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
       perm `lesser_equal_permission` perm')

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

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

let equiv_symmetric (p1 p2:hprop) = ()
let equiv_extensional_on_star (p1 p2 p3:hprop) = ()

////////////////////////////////////////////////////////////////////////////////
//pts_to
////////////////////////////////////////////////////////////////////////////////

let intro_pts_to (#a:_) (x:ref a) (p:permission) (v:a) (m:heap)
  : Lemma
    (requires
       m `contains_addr` x /\
       (let Ref a' perm' v' = select_addr m x in
        a == a' /\
        v == v' /\
        p `lesser_equal_permission` perm'))
     (ensures
       interp (pts_to x p v) m)
  = ()


let pts_to_injective (#a:_) (x:ref a) (p:permission) (v0 v1:a) (m:heap)
  = ()

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


#push-options "--z3rlimit_factor 6 --max_fuel 1 --max_ifuel 2  --initial_fuel 2 --initial_ifuel 2"
#push-options "--warn_error -271" //local patterns miss variables; ok
let rec affine_star_aux (p:hprop) (m:heap) (m':heap { disjoint m m' })
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
// Frameable heap predicates
////////////////////////////////////////////////////////////////////////////////
let weaken_depends_only_on (q:heap -> prop) (fp fp': hprop)
  : Lemma (depends_only_on q fp ==> depends_only_on q (fp `star` fp'))
  = ()

let refine (p:hprop) (q:fp_prop p) : hprop = Refine p q

let refine_equiv (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (interp p h /\ q h <==> interp (Refine p q) h)
  = ()

let refine_star (p0 p1:hprop) (q:fp_prop p0)
  : Lemma (equiv (Refine (p0 `star` p1) q) (Refine p0 q `star` p1))
  = ()

let refine_star_r (p0 p1:hprop) (q:fp_prop p1)
  : Lemma (equiv (Refine (p0 `star` p1) q) (p0 `star` Refine p1 q))
  = ()

let interp_depends_only (p:hprop)
  : Lemma (interp p `depends_only_on` p)
  = ()

let refine_elim (p:hprop) (q:fp_prop p) (h:heap)
  : Lemma (requires
            interp (Refine p q) h)
          (ensures
            interp p h /\ q h)
  = refine_equiv p q h

////////////////////////////////////////////////////////////////////////////////
// allocation and locks
////////////////////////////////////////////////////////////////////////////////
noeq
type lock_state =
  | Available : hprop -> lock_state
  | Locked    : hprop -> lock_state

let lock_store = list lock_state

let rec lock_store_invariant (l:lock_store) : hprop =
  match l with
  | [] -> emp
  | Available h :: tl -> h `star` lock_store_invariant tl
  | _ :: tl -> lock_store_invariant tl

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

let locks_invariant (m:mem) : hprop = lock_store_invariant m.locks

let heap_of_mem (x:mem) : heap = x.heap

let m_disjoint (m:mem) (h:heap) =
  disjoint (heap_of_mem m) h /\
  (forall i. i >= m.ctr ==> h i == None)

let upd_joined_heap (m:mem) (h:heap{m_disjoint m h}) =
  let h0 = heap_of_mem m in
  let h = join h0 h in
  {m with heap = h}

let m_action_depends_only_on #pre #a #post (f:pre_m_action pre a post)
  = forall (m0:hmem pre)
      (h1:heap {m_disjoint m0 h1})
      (post: (x:a -> fp_prop (post x))).
      (let m1 = upd_joined_heap m0 h1 in
       let (| x0, m |) = f m0 in
       let (| x1, m' |) = f m1 in
       x0 == x1 /\
       (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m')))

let is_m_frame_preserving #a #fp #fp' (f:pre_m_action fp a fp') =
  forall frame (m0:hmem (fp `star` frame)).
    (affine_star fp frame (heap_of_mem m0);
     let (| x, m1 |) = f m0 in
     interp (fp' x `star` frame `star` locks_invariant m1) (heap_of_mem m1))

#push-options "--z3rlimit_factor 4 --query_stats"
let frame_fp_prop' #fp #a #fp' frame
                   (q:fp_prop frame)
                   (act:action fp a fp')
                   (h0:hheap (fp `star` frame))
   : Lemma (requires q h0)
           (ensures (
             let (| x, h1 |) = act h0 in
             q h1))
   = assert (interp (Refine (fp `star` frame) q) h0);
     assert (interp (fp `star` (Refine frame q)) h0);
     let (| x, h1 |) = act h0 in
     assert (interp (fp' x `star` (Refine frame q)) h1);
     refine_star_r (fp' x) frame q;
     assert (interp (Refine (fp' x `star` frame) q) h1);
     assert (q h1)

let frame_fp_prop #fp #a #fp' (act:action fp a fp')
                  (#frame:hprop) (q:fp_prop frame)
   = let aux (h0:hheap (fp `star` frame))
       : Lemma
         (requires q h0)
         (ensures
           (let (|x, h1|) = act h0 in
            q h1))
         [SMTPat (act h0)]
       = frame_fp_prop' frame q act h0
     in
     ()
#pop-options

let test_q (pre:_) (a:_) (post:_)
           (k:(x:a -> fp_prop (post x))) : fp_prop pre =
  fun (h:heap) ->
    interp pre h /\
    (forall (f:action pre a post).
      let (| x, h' |) = f h in
      k x h')

////////////////////////////////////////////////////////////////////////////////
// sel
////////////////////////////////////////////////////////////////////////////////
let sel #a (r:ref a) (m:hheap (ptr r))
  : a
  = let Ref _ _ v = select_addr m r in
    v

let sel_lemma #a (r:ref a) (p:permission) (m:hheap (ptr_perm r p))
  = ()


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

let upd_heap #a (r:ref a) (v:a)
  : pre_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)
  = fun h -> (| (), update_addr h r (Ref a full_permission v) |)


let upd_lemma' (#a:_) (r:ref a) (v:a) (h:heap) (frame:hprop)
  : Lemma
    (requires
      interp (ptr_perm r full_permission `star` frame) h)
    (ensures (
      let (| x, h1 |) = upd_heap r v h in
      interp (pts_to r full_permission v `star` frame) h1 /\
      preserves_frame_prop frame h h1))
  = let aux (h0 h1:heap)
     : Lemma
       (requires
         disjoint h0 h1 /\
         h == join h0 h1 /\
         interp (ptr_perm r full_permission) h0 /\
         interp frame h1)
       (ensures (
         let (| _, h' |) = upd_heap r v h in
         let h0' = update_addr h0 r (Ref a full_permission v) in
         disjoint h0' h1 /\
         interp (pts_to r full_permission v) h0' /\
         interp frame h1 /\
         h' == join h0' h1))
       [SMTPat (disjoint h0 h1)]
     = let (| _, h'|) = upd_heap r v h in
       let h0' = update_addr h0 r (Ref a full_permission v) in
       assume (disjoint h0' h1);  //AR: 12/11: TODO
       mem_equiv_eq h' (join h0' h1)
   in
   ()

#push-options "--warn_error -271"
let upd'_is_frame_preserving (#a:_) (r:ref a) (v:a)
  : Lemma (is_frame_preserving (upd_heap r v))
  = let aux (#a:_) (r:ref a) (v:a) (h:heap) (frame:hprop)
      : Lemma
        (requires
          interp (ptr_perm r full_permission `star` frame) h)
        (ensures (
          let (| _, h1 |) = (upd_heap r v h) in
          interp (pts_to r full_permission v `star` frame) h1 /\
          preserves_frame_prop frame h h1))
        [SMTPat ()]
      = upd_lemma' r v h frame
   in
   ()
#pop-options

let upd'_preserves_join #a (r:ref a) (v:a)
                       (h0:hheap (ptr_perm r full_permission))
                       (h1:heap {disjoint h0 h1})
  : Lemma
     (let (| x0, h |) = upd_heap r v h0 in
      let (| x1, h' |) = upd_heap r v (join h0 h1) in
      x0 == x1 /\
      disjoint h h1 /\
      h' == join h h1)
  = let (| x0, h |) = upd_heap r v h0 in
    let (| x1, h' |) = upd_heap r v (join h0 h1) in
    assert (h == update_addr h0 r (Ref a full_permission v));
    assert (h' == update_addr (join h0 h1) r (Ref a full_permission v));
    assert (disjoint h h1);
    assert (h' `mem_equiv` join h h1)

#push-options "--warn_error -271"
let upd'_depends_only_on_fp #a (r:ref a) (v:a)
  : Lemma (action_depends_only_on_fp (upd_heap r v))
  =
    let pre = ptr_perm r full_permission in
    let post = pts_to r full_permission v in
    let aux (h0:hheap pre)
            (h1:heap {disjoint h0 h1})
            (q:fp_prop post)
    : Lemma
      (let (| x0, h |) = upd_heap r v h0 in
        let (| x1, h' |) = upd_heap r v (join h0 h1) in
        x0 == x1 /\
        (q h <==> q h'))
      [SMTPat ()]
    = let (| x0, h |) = upd_heap r v h0 in
      let (| x1, h' |) = upd_heap r v (join h0 h1) in
      assert (x0 == x1);
      upd'_preserves_join r v h0 h1;
      assert (h' == join h h1)
    in
    ()
#pop-options

let upd' #a (r:ref a) (v:a)
  : pre_m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)
  = fun m ->
      upd'_is_frame_preserving r v;
      let (| _, h' |) = upd_heap r v m.heap in
      let m':mem = {m with heap = h'} in
      (| (), m' |)

let upd_is_frame_preserving (#a:_) (r:ref a) (v:a)
  : Lemma (is_m_frame_preserving (upd' r v))
  =
  let aux (#a:_) (r:ref a) (v:a) (frame:hprop) (m:hmem (ptr_perm r full_permission `star` frame))
      : Lemma
        (ensures (
          let (| _, m1 |) = upd' r v m in
          interp (pts_to r full_permission v `star` frame `star` locks_invariant m1) m1.heap))
        [SMTPat ()]
      = star_associative (ptr_perm r full_permission) frame (locks_invariant m);
        star_associative (pts_to r full_permission v) frame (locks_invariant m);
        upd_lemma' r v m.heap (frame `star` locks_invariant m)
   in
   ()

let upd_depends_only_on_fp (#a:_) (r:ref a) (v:a)
  : Lemma (m_action_depends_only_on (upd' r v))
  =
    let pre = ptr_perm r full_permission in
    let post = pts_to r full_permission v in
    let aux (m0:hmem pre)
            (h1:heap {m_disjoint m0 h1})
            (q:fp_prop post)
    : Lemma
      (let (| x0, m |) = upd' r v m0 in
       let (| x1, m' |) = upd' r v (upd_joined_heap m0 h1) in
        x0 == x1 /\
        (q (heap_of_mem m) <==> q (heap_of_mem m')))
      [SMTPat ()]
    = let (| x0, m |) = upd' r v m0 in
      let (| x1, m' |) = upd' r v (upd_joined_heap m0 h1) in
      upd'_preserves_join r v m0.heap h1;
      assert (m'.heap == join m.heap h1)
    in
    ()

let upd #a (r:ref a) (v:a)
  : m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)
  = upd_is_frame_preserving r v;
    upd_depends_only_on_fp r v;
    upd' r v

val alloc' (#a:_) (v:a) (frame:hprop) (tmem:mem{interp frame (heap_of_mem tmem)})
  : (x:ref a &
     tmem:mem { interp (pts_to x full_permission v `star` frame) (heap_of_mem tmem)} )

let alloc' #a v frame m
  = let x : ref a = m.ctr in
    let cell = Ref a full_permission v in
    let mem : heap = F.on _ (fun i -> if i = x then Some cell else None) in
    assert (disjoint mem m.heap);
    assert (mem `contains_addr` x);
    assert (select_addr mem x == cell);
    let mem' = join mem m.heap in
    intro_pts_to x full_permission v mem;
    assert (interp (pts_to x full_permission v) mem);
    assert (interp frame m.heap);
    intro_star (pts_to x full_permission v) frame mem m.heap;
    assert (interp (pts_to x full_permission v `star` frame) mem');
    let t = {
      ctr = x + 1;
      heap = mem';
      locks = m.locks;
      properties = ();
    } in
    (| x, t |)

#push-options "--z3rlimit_factor 4 --query_stats"
let singleton_heap #a (x:ref a) (c:cell) : heap =
    F.on _ (fun i -> if i = x then Some c else None)

let singleton_pts_to #a (x:ref a) (c:cell)
  : Lemma (requires (Ref?.a c == a))
          (ensures (interp (pts_to x (Ref?.perm c) (Ref?.v c)) (singleton_heap x c)))
  = ()

let alloc_pre_m_action (#a:_) (v:a)
  : pre_m_action emp (ref a) (fun x -> pts_to x full_permission v)
  = fun m ->
    let x : ref a = m.ctr in
    let cell = Ref a full_permission v in
    let mem : heap = singleton_heap x cell in
    assert (disjoint mem m.heap);
    assert (mem `contains_addr` x);
    assert (select_addr mem x == cell);
    let mem' = join mem m.heap in
    intro_pts_to x full_permission v mem;
    assert (interp (pts_to x full_permission v) mem);
    let frame = (lock_store_invariant m.locks) in
    assert (interp frame m.heap);
    intro_star (pts_to x full_permission v) frame mem m.heap;
    assert (interp (pts_to x full_permission v `star` frame) mem');
    let t = {
      ctr = x + 1;
      heap = mem';
      locks = m.locks;
      properties = ();
    } in
    (| x, t |)
#pop-options

#push-options "--z3rlimit_factor 16 --query_stats"
let alloc_is_frame_preserving' (#a:_) (v:a) (m:mem) (frame:hprop)
  : Lemma
    (requires
      interp (frame `star` locks_invariant m) (heap_of_mem m))
    (ensures (
      let (| x, m1 |) = alloc_pre_m_action v m in
      interp (pts_to x full_permission v `star` frame `star` locks_invariant m1) (heap_of_mem m1) /\
      preserves_frame_prop frame (heap_of_mem m) (heap_of_mem m1)))
  = let (| x, m1 |) = alloc_pre_m_action v m in
    assert (x == m.ctr);
    assert (m1.ctr = m.ctr + 1);
    assert (m1.locks == m.locks);
    let h = heap_of_mem m in
    let h1 = heap_of_mem m1 in
    let cell = (Ref a full_permission v) in
    assert (h1 == join (singleton_heap x cell) h);
    intro_pts_to x full_permission v (singleton_heap x cell);
    singleton_pts_to x cell;
    assert (interp (pts_to x full_permission v) (singleton_heap x cell));
    assert (interp (frame `star` locks_invariant m) h);
    intro_star (pts_to x full_permission v) (frame `star` locks_invariant m) (singleton_heap x cell) h;
    assert (interp (pts_to x full_permission v `star` (frame `star` locks_invariant m)) h1);
    star_associative (pts_to x full_permission v) frame (locks_invariant m);
    assert (interp (pts_to x full_permission v `star` frame `star` locks_invariant m) h1)
#pop-options

#push-options "--warn_error -271 --z3rlimit_factor 4"
let alloc_is_frame_preserving (#a:_) (v:a)
  : Lemma (is_m_frame_preserving (alloc_pre_m_action v))
  = let aux (frame:hprop) (m:hmem (emp `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = alloc_pre_m_action v m in
            interp (pts_to x full_permission v `star` frame `star` locks_invariant m1) (heap_of_mem m1) /\
            preserves_frame_prop frame (heap_of_mem m) (heap_of_mem m1)))
          [SMTPat ()]
      = alloc_is_frame_preserving' v m frame
    in
    ()
#pop-options

#push-options "--z3rlimit_factor 2"
let alloc_preserves_disjoint (#a:_) (v:a) (m0:hmem emp) (h1:heap {m_disjoint m0 h1})
  : Lemma (let (| x0, m |) = alloc_pre_m_action v m0 in
           disjoint (heap_of_mem m) h1)
  = let (| x0, m |) = alloc_pre_m_action v m0 in
    let h0 = heap_of_mem m0 in
    let h' = heap_of_mem m in
    let aux (ad:addr) : Lemma (disjoint_addr h' h1 ad)
      = if ad >= m0.ctr then ()
        else begin
          let h_alloc = singleton_heap #a m0.ctr (Ref a full_permission v) in
          assert (h' == join h_alloc h0);
          assert (h_alloc ad == None);
         assert (h0 ad == h' ad);
         assert (disjoint_addr h0 h1 ad)
        end
    in Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit_factor 4"
let alloc_preserves_join (#a:_) (v:a) (m0:hmem emp) (h1:heap {m_disjoint m0 h1})
  : Lemma (
      let h0 = heap_of_mem m0 in
      let h = join h0 h1 in
      let m1:mem = { m0 with heap = h } in
      let (| x0, m |) = (alloc_pre_m_action v) m0 in
      let (| x1, m' |) = (alloc_pre_m_action v) m1 in
      heap_of_mem m' == join (heap_of_mem m) h1)
   = let h0 = heap_of_mem m0 in
     let h = join h0 h1 in
     let m1:mem = { m0 with heap = h } in
     let (| x0, m |) = (alloc_pre_m_action v) m0 in
     let (| x1, m' |) = (alloc_pre_m_action v) m1 in
     let h_alloc = singleton_heap #a m0.ctr (Ref a full_permission v) in
     // let hm = heap_of_mem m in
     // let hm' = heap_of_mem m' in
     // assert (hm == join h_alloc h0);
     // assert (hm' == join h_alloc h);
     // assert (hm' == join h_alloc (join h0 h1));
     join_associative' h_alloc h0 h1
#pop-options

#push-options "--warn_error -271 --z3rlimit_factor 4"
let alloc_depends_only_on (#a:_) (v:a)
  : Lemma (m_action_depends_only_on (alloc_pre_m_action v))
  = let aux
        (m0:hmem emp)
        (h1:heap { m_disjoint m0 h1 })
        (post:(x:ref a -> fp_prop (pts_to x full_permission v)))
      : Lemma
          (ensures (
            let h0 = heap_of_mem m0 in
            let h = join h0 h1 in
            let m1 = { m0 with heap = h } in
            let (| x0, m |) = (alloc_pre_m_action v) m0 in
            let (| x1, m' |) = (alloc_pre_m_action v) m1 in
            x0 == x1 /\
            (post x0 (heap_of_mem m) <==> post x1 (heap_of_mem m'))))
          [SMTPat ()]
      =
        let h0 = heap_of_mem m0 in
        let h = join h0 h1 in
        let m1 = { m0 with heap = h } in
        let (| x0, m |) = (alloc_pre_m_action v) m0 in
        let (| x1, m' |) = (alloc_pre_m_action v) m1 in
        assert (x0 == x1);
        alloc_preserves_disjoint v m0 h1;
//        assert (disjoint (heap_of_mem m) h1);
        affine_star (pts_to x0 full_permission v) (locks_invariant m) (heap_of_mem m);
        alloc_preserves_join v m0 h1
//        assert (interp (pts_to x0 full_permission v) (heap_of_mem m));
//        assert (heap_of_mem m' == join (heap_of_mem m) h1)
    in
    ()
#pop-options

let alloc (#a:_) (v:a)
  : m_action emp (ref a) (fun x -> pts_to x full_permission v)
  = alloc_is_frame_preserving v;
    alloc_depends_only_on v;
    alloc_pre_m_action v

#push-options "--query_stats --z3rlimit_factor 4"
// let test2 (#a:_) (v:a) (m0:hmem emp)
//           (h1:heap {m_disjoint m0 h1})
//           (post: (x:ref a -> fp_prop (pts_to x full_permission v)))
//    = let h0 = heap_of_mem m0 in
//      let h = join h0 h1 in
//      let m1 = { m0 with heap = h } in
//      let (| x0, m |) = alloc_m_action v m0 in
//      let (| x1, m' |) = alloc_m_action v m1 in
//      assert (x0 == x1);
//      // assert (forall (x0:ref a). post x0 `depends_only_on` (pts_to x0 full_permission v));
//      // let post' :fp_prop (pts_to x0 full_permission v) = post x0 in
//      // assert (post' `depends_only_on` (pts_to x0 full_permission v));
//      let h = heap_of_mem m in
//      let h' = heap_of_mem m' in
//      let s = singleton_heap x0 (Ref a full_permission v) in
//      singleton_pts_to x0 (Ref a full_permission v);
//      assume (disjoint s h0);
//      assume (disjoint s (join h0 h1));
//      assume (h `mem_equiv` join s h0);
//      assume (h' `mem_equiv` join s (join h0 h1));
//      // assert (h' `mem_equiv` join (singleton_heap x0 (Ref a full_permission v)) (join h0 h1));
//      let post' : fp_prop (pts_to x0 full_permission v) = post x0 in
//      let s : hheap (pts_to x0 full_permission v) = s in
//      assert (post' h <==> post' s);
//      assert (post' h' <==> post' s);
//      assert (post x0 h <==> post x1 h')

let lock (p:hprop) = nat

module L = FStar.List.Tot

let new_lock_pre_m_action (p:hprop)
  : pre_m_action p (lock p) (fun _ -> emp)
  = fun m ->
     let l = Available p in
     let locks' = l :: m.locks in
     assert (interp (lock_store_invariant locks') (heap_of_mem m));
     let mem :mem = { m with locks = locks' } in
     assert (locks_invariant mem == p `star` locks_invariant m);
     assert (interp (locks_invariant mem) (heap_of_mem mem));
     emp_unit (locks_invariant mem);
     star_commutative emp (locks_invariant mem);
     assert (interp (emp `star` locks_invariant mem) (heap_of_mem mem));
     let lock_id = List.Tot.length locks' - 1 in
     (| lock_id, mem |)

let emp_unit_left (p:hprop)
  : Lemma
    ((emp `star` p) `equiv` p)
  = emp_unit p;
    star_commutative emp p

let equiv_star_left (p q r:hprop)
  : Lemma
    (requires q `equiv` r)
    (ensures (p `star` q) `equiv` (p `star` r))
  = ()

#push-options "--warn_error -271"
let new_lock_is_frame_preserving (p:hprop)
  : Lemma (is_m_frame_preserving (new_lock_pre_m_action p))
  = let aux (frame:hprop) (m:hmem (p `star` frame))
      : Lemma
          (ensures (
            let (| x, m1 |) = new_lock_pre_m_action p m in
            interp (emp `star` frame `star` locks_invariant m1) (heap_of_mem m1)))
          [SMTPat ()]
      = let (| x, m1 |) = new_lock_pre_m_action p m in
        assert (m1.locks == Available p :: m.locks);
        assert (locks_invariant m1 == (p `star` locks_invariant m));
        assert (interp ((p `star` frame) `star` locks_invariant m) (heap_of_mem m));
        star_associative p frame (locks_invariant m);
        assert (interp (p `star` (frame `star` locks_invariant m)) (heap_of_mem m));
        star_commutative frame (locks_invariant m);
        equiv_star_left p (frame `star` locks_invariant m) (locks_invariant m `star` frame);
        assert (interp (p `star` (locks_invariant m `star` frame)) (heap_of_mem m));
        star_associative p (locks_invariant m) frame;
        assert (interp ((p `star` locks_invariant m) `star` frame) (heap_of_mem m));
        assert (interp ((locks_invariant m1) `star` frame) (heap_of_mem m));
        assert (heap_of_mem m == heap_of_mem m1);
        star_commutative (locks_invariant m1) frame;
        assert (interp (frame `star` (locks_invariant m1)) (heap_of_mem m1));
        emp_unit_left (frame `star` (locks_invariant m1));
        assert (interp (emp `star` (frame `star` (locks_invariant m1))) (heap_of_mem m1));
        star_associative emp frame (locks_invariant m1)
    in
    ()
#pop-options

let new_lock (p:hprop)
  : m_action p (lock p) (fun _ -> emp)
  = new_lock_is_frame_preserving p;
    new_lock_pre_m_action p

////////////////////////////////////////////////////////////////////////////////
assume
val get_lock (l:lock_store) (i:nat{i < L.length l})
  : (prefix : lock_store &
     li : lock_state &
     suffix : lock_store {
       l == L.(prefix @ (li::suffix)) /\
       L.length (li::suffix) == i + 1
     })

let lock_i (l:lock_store) (i:nat{i < L.length l}) : lock_state =
  let (| _, li, _ |) = get_lock l i in
  li

assume
val lock_store_invariant_append (l1 l2:lock_store)
  : Lemma (lock_store_invariant (l1 @ l2) `equiv`
           (lock_store_invariant l1 `star` lock_store_invariant l2))

let hprop_of_lock_state (l:lock_state) : hprop =
  match l with
  | Available p -> p
  | Locked p -> p

let lock_ok (#p:hprop) (l:lock p) (m:mem) =
  l < L.length m.locks /\
  hprop_of_lock_state (lock_i m.locks l) == p

let lock_store_evolves : Preorder.preorder lock_store =
  fun (l1 l2 : lock_store) ->
    L.length l2 >= L.length l1 /\
    (forall (i:nat{i < L.length l1}).
       hprop_of_lock_state (lock_i l1 i) ==
       hprop_of_lock_state (lock_i l2 i))

let mem_evolves : Preorder.preorder mem =
  fun m0 m1 -> lock_store_evolves m0.locks m1.locks

let lock_ok_stable (#p:_) (l:lock p) (m0 m1:mem)
  : Lemma (lock_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           lock_ok l m1)
  = ()

let pure (p:prop) : hprop = refine emp (fun _ -> p)

let intro_pure (p:prop) (q:hprop) (h:hheap q { p })
  : hheap (pure p `star` q)
  = emp_unit q;
    star_commutative q emp;
    h

let intro_hmem_or (p:prop) (q:hprop) (h:hmem q)
  : hmem (h_or (pure p) q)
  = h

let middle_to_head (p q r:hprop) (h:hheap (p `star` (q `star` r)))
  : hheap (q `star` (p `star` r))
  = star_associative p q r;
    star_commutative p q;
    star_associative q p r;
    h

let maybe_acquire #p (l:lock p) (m:mem { lock_ok l m } )
  : (b:bool &
     m:hmem (h_or (pure (b == false)) p))
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    match li with
    | Available _ ->
      let h = heap_of_mem m in
      assert (interp (lock_store_invariant m.locks) h);
      lock_store_invariant_append prefix (li::suffix);
      assert (lock_store_invariant m.locks `equiv`
             (lock_store_invariant prefix `star`
                      (p `star` lock_store_invariant suffix)));
      assert (interp (lock_store_invariant prefix `star`
                       (p `star` lock_store_invariant suffix)) h);
      let h = middle_to_head (lock_store_invariant prefix) p (lock_store_invariant suffix) h in
      assert (interp (p `star`
                        (lock_store_invariant prefix `star`
                         lock_store_invariant suffix)) h);
      let new_lock_store = prefix @ (Locked p :: suffix) in
      lock_store_invariant_append prefix (Locked p :: suffix);
      assert (lock_store_invariant new_lock_store `equiv`
              (lock_store_invariant prefix `star`
                         lock_store_invariant suffix));
      equiv_star_left p (lock_store_invariant new_lock_store)
                        (lock_store_invariant prefix `star`
                          lock_store_invariant suffix);
      assert (interp (p `star` lock_store_invariant new_lock_store) h);
      let h : hheap (p `star` lock_store_invariant new_lock_store) = h in
      assert (heap_of_mem m == h);
      star_commutative p (lock_store_invariant new_lock_store);
      affine_star (lock_store_invariant new_lock_store) p h;
      assert (interp (lock_store_invariant new_lock_store) h);
      let mem : hmem p = { m with locks = new_lock_store } in
      let b = true in
      let mem : hmem (h_or (pure (b==false)) p) = intro_hmem_or (b == false) p mem in
      (| b, mem |)

    | Locked _ ->
      let b = false in
      assert (interp (pure (b == false)) (heap_of_mem m));
      let h : hheap (locks_invariant m) = heap_of_mem m in
      let h : hheap (pure (b==false) `star` locks_invariant m) =
        intro_pure (b==false) (locks_invariant m) h in
      intro_or_l (pure (b==false) `star` locks_invariant m)
                 (p `star` locks_invariant m)
                 h;
      or_star (pure (b==false)) p (locks_invariant m) h;
      assert (interp (h_or (pure (b==false)) p `star` locks_invariant m) h);
      (| false, m |)

let hmem_emp (p:hprop) (m:hmem p) : hmem emp = m

#push-options "--query_stats --z3rlimit_factor 8"
let release #p (l:lock p) (m:hmem p { lock_ok l m } )
  : (b:bool &
     hmem emp)
  = let (| prefix, li, suffix |) = get_lock m.locks l in
    let h = heap_of_mem m in
    lock_store_invariant_append prefix (li::suffix);
    assert (interp (p `star`
                     (lock_store_invariant prefix `star`
                       (lock_store_invariant (li::suffix)))) h);
    match li with
    | Available _ ->
      (* this case is odd, but not inadmissible.
         We're releasing a lock that was not previously acquired.
         We could either fail, or just silently proceed.
         I choose to at least signal this case in the result
         so that we can decide to fail if we like, at a higher layer.

         Another cleaner way to handle this would be to insist
         that lockable resources are non-duplicable ...
         in which case this would be unreachable, since we have `p star p` *)
      (| false, hmem_emp p m |)

    | Locked _ ->
      assert (interp (p `star`
                        (lock_store_invariant prefix `star`
                          (lock_store_invariant suffix))) h);
      let h = middle_to_head p (lock_store_invariant prefix) (lock_store_invariant suffix) h in
      assert (interp (lock_store_invariant prefix `star`
                        (p `star`
                          (lock_store_invariant suffix))) h);
      let new_lock_store = prefix @ (Available p :: suffix) in
      lock_store_invariant_append prefix (Available p :: suffix);
      assert (lock_store_invariant new_lock_store `equiv`
                (lock_store_invariant prefix `star`
                 (p `star` lock_store_invariant (suffix))));
      assert (interp (lock_store_invariant new_lock_store) h);
      emp_unit_left (lock_store_invariant new_lock_store);
      let mem : hmem emp = { m with locks = new_lock_store } in
      (| true, mem |)
#pop-options
