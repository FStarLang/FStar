(*
   Copyright 2020 Microsoft Research

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
module PulseCore.Heap
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open FStar.PCM
module PP = PulseCore.Preorder

let addr = nat

/// This is just the core of a memory, about which one can write
/// assertions. At one level above, we'll encapsulate this memory
/// with an impredicative invariant store.
type heap : Type u#(a + 1) =
  Seq.seq (option (cell u#a))

let ctr (h: heap) : nat = Seq.length h

[@@"opaque_to_smt"]
let select i h =
  if i < ctr h then Seq.index h i else None

let empty_heap' n = Seq.create n None

let select_empty_heap' a n : Lemma (select a (empty_heap' n) == None) [SMTPat (select a (empty_heap' n))] =
  reveal_opaque (`%select) (select a (empty_heap' n))

let empty_heap = empty_heap' 0

let sel_empty _ = ()

let contains_addr (m:heap) (a:addr)
  : bool
  = Some? (select a m)

let select_some i h :
    Lemma (requires Some? (select i h)) (ensures contains_addr h i /\ i < ctr h)
      [SMTPat (select i h)] =
  reveal_opaque (`%select) (select i h)

let select_addr (m:heap) (a:addr{contains_addr m a})
  : cell
  = Some?.v (select a m)

let update_addr' (m:heap) (a:addr { a < ctr m }) (c:option cell)
  : heap
  = Seq.upd m a c

let select_update_addr' m a b c :
    Lemma (select a (update_addr' m b c) ==
      (if a = b then c else select a m))
    [SMTPat (select a (update_addr' m b c))] =
  reveal_opaque (`%select) (select a)

let update_addr (m:heap) (a:addr { a < ctr m }) (c:cell)
  : heap
  = update_addr' m a (Some c)

let disjoint_cells (c0 c1:cell u#h) : prop =
    let Ref t0 p0 v0 = c0 in
    let Ref t1 p1 v1 = c1 in
    t0 == t1 /\
    p0 == p1 /\
    composable p0 v0 v1

let disjoint_cells_sym (c0 c1:cell u#h)
  : Lemma (requires disjoint_cells c0 c1)
          (ensures disjoint_cells c1 c0)
  = let Ref t0 p0 v0 = c0 in
    let Ref t1 p1 v1 = c1 in
    p0.comm v0 v1;
    ()

let disjoint_addr (m0 m1:heap u#h) (a:addr)
  : prop
  = match select a m0, select a m1 with
    | Some c0, Some c1 ->
      disjoint_cells c0 c1
    | Some _, None
    | None, Some _
    | None, None ->
      True

type core_ref : Type u#0 =
  | Null
  | Addr of addr
let core_ref_eq x y = x=y
let core_ref_null = Null

let core_ref_is_null (r:core_ref) = Null? r

let addr_as_core_ref n = Addr n
let core_ref_as_addr (c:core_ref) =
  match c with
  | Null -> 0
  | Addr n -> n

let addr_core_ref_injective (n:nat)
: Lemma (core_ref_as_addr (addr_as_core_ref n) == n)
= ()
let addr_core_ref_injective_2 (c:core_ref { not (core_ref_is_null c) })
: Lemma (addr_as_core_ref (core_ref_as_addr c) == c)
= ()

let disjoint (m0 m1:heap u#h)
  : prop
  = forall a. disjoint_addr m0 m1 a

#push-options "--warn_error -271"

let disjoint_sym (m0 m1:heap u#h)
  = let aux (m0 m1:heap u#h) (a:addr)
      : Lemma (requires disjoint_addr m0 m1 a)
              (ensures disjoint_addr m1 m0 a)
              [SMTPat (disjoint_addr m1 m0 a)]
    = match select a m0, select a m1 with
      | Some c0, Some c1 -> disjoint_cells_sym c0 c1
      | _ -> ()
    in
    ()

let join_cells (c0:cell u#h) (c1:cell u#h{disjoint_cells c0 c1}) =
  let Ref a0 p0 v0 = c0 in
  let Ref a1 p1 v1 = c1 in
  Ref a0 p0 (op p0 v0 v1)

[@@"opaque_to_smt"]
let join (m0:heap) (m1:heap{disjoint m0 m1})
  : heap
  = Seq.init (max (ctr m0) (ctr m1)) fun a ->
      match select a m0, select a m1 with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some c0, Some c1 ->
        Some (join_cells c0 c1)

let ctr_join_def m0 m1 : Lemma (ctr (join m0 m1) == max (ctr m0) (ctr m1)) [SMTPat (ctr (join m0 m1))] =
  reveal_opaque (`%join) (join m0 m1)

let select_join_def a m0 m1 :
    Lemma (select a (join m0 m1) ==
      (match select a m0, select a m1 with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some c0, Some c1 ->
        Some (join_cells c0 c1)))
      [SMTPat (select a (join m0 m1))] =
  reveal_opaque (`%select) (select a);
  reveal_opaque (`%join) (join m0 m1)

let disjoint_join_cells_assoc (c0 c1 c2:cell u#h)
  : Lemma
    (requires disjoint_cells c1 c2 /\
              disjoint_cells c0 (join_cells c1 c2))
    (ensures  disjoint_cells c0 c1 /\
              disjoint_cells (join_cells c0 c1) c2 /\
              join_cells (join_cells c0 c1) c2 == join_cells c0 (join_cells c1 c2))
  = let Ref a0 p0 v0 = c0 in
    let Ref a1 p1 v1 = c1 in
    let Ref a2 p2 v2 = c2 in
    p0.assoc v0 v1 v2

let disjoint_join' (m0 m1 m2:heap u#h)
  : Lemma (requires disjoint m1 m2 /\
                    disjoint m0 (join m1 m2))
          (ensures  disjoint m0 m1 /\ disjoint (join m0 m1) m2)
          [SMTPat (disjoint (join m0 m1) m2)]
  = let aux (a:addr)
      : Lemma (disjoint_addr m0 m1 a)
              [SMTPat ()]
      = match select a m0, select a m1, select a m2 with
        | Some c0, Some c1, Some c2 ->
          disjoint_join_cells_assoc c0 c1 c2
        | _ -> ()
    in
    assert (disjoint m0 m1);
    let aux (a:addr)
      : Lemma (disjoint_addr (join m0 m1) m2 a)
              [SMTPat ()]
      = match select a m0, select a m1, select a m2 with
        | Some c0, Some c1, Some c2 ->
          disjoint_join_cells_assoc c0 c1 c2
        | _ -> ()
    in
    ()

let mem_equiv (m0 m1:heap) =
  ctr m0 == ctr m1 /\ forall a. select a m0 == select a m1

let mem_equiv_eq (m0 m1:heap)
  : Lemma
    (requires
      m0 `mem_equiv` m1)
    (ensures
      m0 == m1)
    [SMTPat (m0 `mem_equiv` m1)]
  = reveal_opaque (`%select) select; assert Seq.equal m0 m1

let join_cells_commutative (c0:cell u#h) (c1:cell u#h{disjoint_cells c0 c1})
  : Lemma (disjoint_cells_sym c0 c1; join_cells c0 c1 == join_cells c1 c0)
          [SMTPat (join_cells c0 c1)]
  = let Ref a0 p0 v0 = c0 in
    let Ref a1 p1 v1 = c1 in
    p0.comm v0 v1

let join_commutative' (m0 m1:heap)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 `mem_equiv` join m1 m0)
    [SMTPat (join m0 m1)]
  = ()

let join_commutative m0 m1 = ()

let disjoint_join (m0 m1 m2:heap)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)
          [SMTPat (disjoint m0 (join m1 m2))]
  = let aux ()
      : Lemma
        (requires disjoint m1 m2 /\
                  disjoint m0 (join m1 m2))
        (ensures  disjoint m0 m1 /\
                  disjoint m0 m2 /\
                  disjoint (join m0 m1) m2 /\
                  disjoint (join m0 m2) m1)
        [SMTPat ()]
      = disjoint_join' m0 m1 m2;
        join_commutative m0 m1;
        disjoint_join' m0 m2 m1
    in
    ()

#push-options "--z3rlimit 20 --split_queries always"
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
  = disjoint_join m0 m1 m2;
    let l = join m0 (join m1 m2) in
    let r = join (join m0 m1) m2 in
    let aux (a:addr)
        : Lemma (select a l == select a r)
                [SMTPat ()]
        = match select a m0, select a m1, select a m2 with
          | Some c0, Some c1, Some c2 ->
            disjoint_join_cells_assoc c0 c1 c2
          | _ -> ()
    in
    ()
#pop-options

let join_associative (m0 m1 m2:heap) = disjoint_join m0 m1 m2; join_associative' m0 m1 m2

#push-options "--z3rlimit 20 --split_queries always"
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
  = disjoint_join m2 m0 m1;
    join_commutative (join m0 m1) m2;
    join_associative m2 m0 m1
#pop-options

let join_empty h = assert (join h empty_heap `mem_equiv` h)

let join_empty_inverse (m0 m1:heap)
: Lemma 
  (requires disjoint m0 m1 /\ join m0 m1 == empty_heap)
  (ensures m0 == empty_heap /\ m1 == empty_heap)
= assert (m0 `mem_equiv` empty_heap /\ m1 `mem_equiv` empty_heap)

////////////////////////////////////////////////////////////////////////////////
let slprop = p:(heap ^-> prop) { heap_prop_is_affine p }



let interp (p:slprop u#a) (m:heap u#a)
  : Tot prop
  = p m

let as_slprop p = FStar.FunctionalExtensionality.on _ p
let of_slprop p = p
let slprop_inj (f:slprop) = ()

let slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)
  = FStar.PredicateExtensionality.predicateExtensionality _ p q

let emp : slprop u#a = as_slprop (fun h -> True)

let affine_hprop_intro
   (p:heap u#a -> prop)
   (lemma: (h0 : heap u#a) ->  (h1: heap u#a) -> Lemma
     (requires (p h0 /\ disjoint h0 h1))
     (ensures (p (join h0 h1)))
   )
     : Lemma (heap_prop_is_affine p)
  =
  let aux (h0 h1: heap u#a) : Lemma (p h0 /\ disjoint h0 h1 ==> p (join h0 h1)) =
    let aux (_ : squash (p h0 /\ disjoint h0 h1)) : Lemma (disjoint h0 h1 /\ p (join h0 h1)) =
      lemma h0 h1
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_2 aux

let pts_to_cell (#a:Type u#a) (pcm:pcm a) (v:a) (c:cell u#a) =
  let Ref a' pcm' v' = c in
  a == a' /\
  pcm == pcm' /\
  compatible pcm v v'

let pts_to_cell_join (#a:Type u#a) (pcm:pcm a) (v1 v2:a) (c:cell u#a)
: Lemma 
  (requires (pts_to_cell pcm v1 c /\ pts_to_cell pcm v2 c))
  (ensures joinable pcm v1 v2)
= ()

let pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a =
  let hprop  (h: heap) : Tot prop =
    Addr? r /\
    h `contains_addr` (Addr?._0 r) /\
    pts_to_cell pcm v (select_addr h (Addr?._0 r))
  in
  affine_hprop_intro hprop (fun h0 h1 ->
  match r with | Null -> () | Addr r -> (
    match select r h0, select r h1, select r (join h0 h1) with
    | Some (Ref a0 pcm0 v0), Some (Ref a1 pcm1 v1), Some (Ref a01 pcm01 v01) ->
       compatible_elim pcm01 v v0 (compatible pcm01 v v01) (fun frame ->
         pcm01.comm frame v;
         pcm01.assoc_r v frame v1;
         pcm01.comm frame v1;
         let new_frame = (op pcm01 v1 frame) in
         pcm01.comm v new_frame
       )
    | None, Some _, _
    | Some _, None, _ -> ()
    | None, None, _ -> ()
    )
  );
  as_slprop hprop


let h_and (p1 p2:slprop u#a) : slprop u#a =
  as_slprop (fun (h: heap) -> p1 h /\ p2 h)

let h_or (p1 p2:slprop u#a) : slprop u#a =
  as_slprop (fun (h: heap) -> p1 h \/ p2 h)

let star (p1 p2: slprop u#a) : slprop u#a =
  as_slprop (fun (h: heap) -> exists (h1 h2 : heap).
        h1 `disjoint` h2 /\
        h == join h1 h2 /\
        interp p1 h1 /\
        interp p2 h2)

let wand (p1 p2: slprop u#a) : slprop u#a =
  as_slprop (fun (h: heap) ->  forall (h1: heap).
        h `disjoint` h1 /\
        interp p1 h1 ==>
        interp p2 (join h h1))

let h_exists_body (#[@@@strictly_positive] a:Type u#b)
                  ([@@@strictly_positive] f: (a -> slprop u#a))
                  (h:heap)
                  (x:a) : prop =
  interp (f x) h

let h_exists  (#[@@@strictly_positive] a:Type u#b)
              ([@@@strictly_positive] f: (a -> slprop u#a)) : slprop u#a =
  as_slprop (fun (h: heap) -> exists x. h_exists_body f h x)

let h_forall_body (#a:Type u#b) (f: (a -> slprop u#a)) (h:heap) (x:a) : prop =
  interp (f x) h

let h_forall (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a =
  as_slprop (fun (h: heap) -> forall x. h_forall_body f h x)

let h_refine p r = h_and p (as_slprop r)

 ////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////
let affine_star p q h = ()

let equiv_symmetric (p1 p2:slprop u#a) = ()
let equiv_extensional_on_star (p1 p2 p3:slprop u#a) = ()
let emp_unit p
  = let emp_unit_1 p m
      : Lemma
        (requires interp p m)
        (ensures  interp (p `star` emp) m)
        [SMTPat (interp (p `star` emp) m)]
      = assert (disjoint empty_heap m);
        assert (interp (p `star` emp) (join m empty_heap));
        assert (mem_equiv m (join m empty_heap))
    in
    let emp_unit_2 p m
      : Lemma
        (requires interp (p `star` emp) m)
        (ensures interp p m)
        [SMTPat (interp (p `star` emp) m)]
      = affine_star p emp m
    in
    ()

let intro_emp h = ()

let h_exists_cong (#a:Type) (p q : a -> slprop) = ()

let sl_implies (p q:slprop) = forall m. interp p m ==> interp q m
let h_exists_alt (#a:Type) (p q: a -> slprop)
  : Lemma
    (requires (forall x. exists y. p x `sl_implies` q y) /\
              (forall x. exists y. q x `sl_implies` p y))
    (ensures equiv (h_exists p) (h_exists q))
  = ()

let intro_h_exists #a x p h = ()

let elim_h_exists #a p h = ()

let interp_depends_only_on (hp:slprop u#a) = emp_unit hp

////////////////////////////////////////////////////////////////////////////////
//pts_to
////////////////////////////////////////////////////////////////////////////////

let intro_pts_to (#a:_) (#pcm:pcm a) (x:ref a pcm) (v:a) (m:heap)
  : Lemma
    (requires
       Addr? x /\
       m `contains_addr` (Addr?._0 x) /\
       (let Ref a' pcm' v' = select_addr m (Addr?._0 x) in
        a == a' /\
        pcm == pcm' /\
        compatible pcm v v'))
     (ensures
       interp (pts_to x v) m)
  = ()

#push-options "--z3rlimit_factor 4"
let pts_to_compatible_fwd (#a:Type u#a)
                          (#pcm:_)
                          (x:ref a pcm)
                          (v0 v1:a)
                          (m:heap u#a)
  : Lemma
    (requires
      interp (pts_to x v0 `star` pts_to x v1) m)
    (ensures
      composable pcm v0 v1 /\
      interp (pts_to x (op pcm v0 v1)) m)
  = let Addr addr = x in
    let c = select_addr m addr in
    let Ref _ _ v = select_addr m addr in
    let aux (c0 c1: cell u#a)
      : Lemma
        (requires
           c0 `disjoint_cells` c1 /\
           pts_to_cell pcm v0 c0 /\
           pts_to_cell pcm v1 c1 /\
           c == join_cells c0 c1 )
        (ensures
           composable pcm v0 v1 /\
           interp (pts_to x (op pcm v0 v1)) m)
        [SMTPat (c0 `disjoint_cells` c1)]
      = let Ref _ _ v0' = c0 in
        let Ref _ _ v1' = c1 in
        assert (exists frame. composable pcm v0 frame /\ op pcm frame v0 == v0');
        assert (exists frame. composable pcm v1 frame /\ op pcm frame v1 == v1');
        assert (composable pcm v0' v1');
        assert (op pcm v0' v1' == v);
        let aux (frame0 frame1:a)
          : Lemma
            (requires
              composable pcm v0 frame0 /\
              op pcm frame0 v0 == v0' /\
              composable pcm v1 frame1 /\
              op pcm frame1 v1 == v1')
            (ensures (
              composable pcm frame0 frame1 /\
              composable pcm v0 v1 /\
              (let frame = op pcm frame0 frame1 in
               composable pcm frame (op pcm v0 v1) /\
               op pcm frame (op pcm v0 v1) == v)))
            [SMTPat(op pcm frame0 v0);
             SMTPat(op pcm frame1 v1)]
          =  assert (op pcm (op pcm frame0 v0) (op pcm frame1 v1) == v);
             pcm.assoc (op pcm frame0 v0) frame1 v1;
             assert (op pcm (op pcm (op pcm frame0 v0) frame1) v1 == v);
             pcm.comm  (op pcm frame0 v0) frame1;
             assert (op pcm (op pcm frame1 (op pcm frame0 v0)) v1 == v);
             pcm.assoc_r frame1 (op pcm frame0 v0) v1;
             assert (op pcm frame1 (op pcm (op pcm frame0 v0) v1) == v);
             pcm.assoc_r frame0 v0 v1;
             assert (op pcm frame1 (op pcm frame0 (op pcm v0 v1)) == v);
             pcm.assoc frame1 frame0 (op pcm v0 v1);
             pcm.comm frame1 frame0
        in
        ()
    in
    assert (exists c0 c1.
              c0 `disjoint_cells` c1 /\
              pts_to_cell pcm v0 c0 /\
              pts_to_cell pcm v1 c1 /\
              c == join_cells c0 c1)

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 1 --split_queries always"
#restart-solver
let pts_to_compatible_bk 
      (#a:Type u#a)
      (#pcm:_)
      (x:ref a pcm)
      (v0 v1:a)
      (m:heap u#a)
  : Lemma
    (requires
      composable pcm v0 v1 /\
      interp (pts_to x (op pcm v0 v1)) m)
    (ensures
      interp (pts_to x v0 `star` pts_to x v1) m)
  = let Addr addr = x in
    let c = select_addr m addr in
    let Ref _ _ v = select_addr m addr in
    let v01 = (op pcm v0 v1) in
    assert (pts_to_cell pcm v01 c);
    let Ref _ _ v = c in
    assert (compatible pcm v01 v);
    let aux frame
      : Lemma
        (requires
           composable pcm v01 frame /\
           op pcm frame v01 == v)
        (ensures
           exists m0 m1.{:pattern (disjoint m0 m1)}
             interp (pts_to x v0) m0 /\
             interp (pts_to x v1) m1 /\
             disjoint m0 m1 /\
             m `mem_equiv` join m0 m1)
        [SMTPat (composable pcm v01 frame)]
      = let c0 = Ref a pcm v0 in
        pcm.FStar.PCM.assoc_r v0 v1 frame;
        let c1 : cell = Ref a pcm (op pcm v1 frame) in
        compatible_refl pcm v0;
        assert (pts_to_cell pcm v0 c0);
        pcm.FStar.PCM.comm v1 frame;
        assert (compatible pcm v1 (op pcm v1 frame));
        assert (pts_to_cell pcm v1 c1);
        calc (==) {
          (v0 `op pcm` (v1 `op pcm` frame));
            (==) {
                   pcm.FStar.PCM.assoc v0 v1 frame;
                   pcm.FStar.PCM.comm v01 frame
                 }
          (frame `op pcm` v01);
        };
        assert (disjoint_cells c0 c1);
        assert (c == join_cells c0 c1);
        let m0 = update_addr (empty_heap' (ctr m)) addr c0 in
        let m1 = update_addr m addr c1 in
        assert (disjoint m0 m1); //fire the existential
        assert (
          interp (pts_to x v0) m0 /\
          interp (pts_to x v1) m1 /\
          disjoint m0 m1 /\
          m `mem_equiv` join m0 m1
        );
        ()
    in
    ()
#pop-options

let pts_to_compatible (#a:Type u#a)
                      (#pcm:_)
                      (x:ref a pcm)
                      (v0 v1:a)
                      (m:heap u#a) =
    FStar.Classical.forall_intro 
      (FStar.Classical.move_requires (pts_to_compatible_fwd x v0 v1));
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (pts_to_compatible_bk x v0 v1))

let pts_to_join (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v1 v2:a) (m:heap)
  : Lemma (requires (interp (pts_to r v1) m /\ interp (pts_to r v2) m))
          (ensures joinable pcm v1 v2)
  = ()

let pts_to_join' (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v1 v2:a) (m:heap)
  : Lemma (requires (interp (pts_to r v1) m /\ interp (pts_to r v2) m))
          (ensures (exists z. compatible pcm v1 z /\ compatible pcm v2 z /\
                         interp (pts_to r z) m))
  = let Ref a' pcm' v' = (select_addr m (Addr?._0 r)) in
    compatible_refl pcm v'

let pts_to_compatible_equiv (#a:Type) (#pcm:_) (x:ref a pcm) (v0:a) (v1:a{composable pcm v0 v1})
  = FStar.Classical.forall_intro (pts_to_compatible x v0 v1)

let pts_to_not_null (#a:Type) (#pcm:_) (x:ref a pcm) (v:a) (m:heap) = ()


////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

let intro_star (p q:slprop) (mp:hheap p) (mq:hheap q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))
  = ()

let elim_star (p q:slprop) (h:hheap (p `star` q))
  : Lemma
    (requires
      interp (p `star` q) h)
    (ensures exists hl hr.
      disjoint hl hr /\
      h == join hl hr /\
      interp p hl /\
      interp q hr)
  =
  ()

(* Properties of star *)

let star_commutative (p1 p2:slprop) = ()

let star_associative (p1 p2 p3:slprop)
  = let ltor (m m1 m2 m3:heap)
    : Lemma
      (requires
        disjoint m2 m3 /\
        disjoint m1 (join m2 m3) /\
        m == join m1 (join m2 m3) /\
        interp p1 m1 /\
        interp p2 m2 /\
        interp p3 m3 /\
        interp (p1 `star` (p2 `star` p3)) m)
      (ensures
        disjoint m1 m2 /\
        disjoint (join m1 m2) m3 /\
        m == join (join m1 m2) m3 /\
        interp (p1 `star` p2) (join m1 m2) /\
        interp ((p1 `star` p2) `star` p3) m)
      [SMTPat()]
    = disjoint_join m1 m2 m3;
      join_associative m1 m2 m3;
      intro_star p1 p2 m1 m2;
      intro_star (p1 `star` p2) p3 (join m1 m2) m3
   in
   let rtol (m m1 m2 m3:heap)
    : Lemma
      (requires
        disjoint m1 m2 /\
        disjoint (join m1 m2) m3 /\
        m == join (join m1 m2) m3 /\
        interp p1 m1 /\
        interp p2 m2 /\
        interp p3 m3 /\
        interp ((p1 `star` p2) `star` p3) m)
      (ensures
        disjoint m2 m3 /\
        disjoint m1 (join m2 m3) /\
        m == join m1 (join m2 m3) /\
        interp (p2 `star` p3) (join m2 m3) /\
        interp (p1 `star`(p2 `star` p3)) m)
      [SMTPat()]
    = join_associative2 m1 m2 m3;
      intro_star p2 p3 m2 m3;
      intro_star p1 (p2 `star` p3) m1 (join m2 m3)
   in
   ()

let star_congruence (p1 p2 p3 p4:slprop) = ()

////////////////////////////////////////////////////////////////////////////////
// refine
////////////////////////////////////////////////////////////////////////////////

let refine_interp p q h = ()
let refine_equiv p0 p1 q0 q1 = ()
let pure_equiv p q = ()
let pure_interp p h = ()
let pure_star_interp p q h = ()


////////////////////////////////////////////////////////////////////////////////
// Actions:
////////////////////////////////////////////////////////////////////////////////

let full_cell (c:cell) =
  let Ref _ p v = c in
  p.refine v

let full_heap_pred h =
  forall a. contains_addr h a ==> full_cell (select_addr h a)

let ctr_empty () = ()

let ctr_join h1 h2 a = ()

let ctr_prop h = ()

////////////////////////////////////////////////////////////////////////////////
// sel
////////////////////////////////////////////////////////////////////////////////
let sel #a #pcm (r:ref a pcm) (m:full_hheap (ptr r))
  : a
  = let Ref _ _ v = select_addr m (Addr?._0 r) in
    v

let sel_v #a #pcm r v m = sel r m

 
let interp_pts_to (i:core_ref)
                  (#a:Type)
                  (#pcm:FStar.PCM.pcm a)
                  (v:a)
                  (h0:heap)
: Lemma
  (requires interp (pts_to #a #pcm i v) h0)
  (ensures (
    not (core_ref_is_null i) /\ (
    match select (core_ref_as_addr i) h0 with
    | None -> False
    | Some c ->
      let Ref a' pcm' v' = c in
      a == a' /\
      pcm == pcm' /\
      compatible pcm v v')))
= ()

let sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:full_hheap (ptr r))
  : Lemma (interp (pts_to r (sel r m)) m)
  = let Ref _ _ v = select_addr m (Addr?._0 r) in
    assert (sel r m == v);
    compatible_refl pcm v
  
#set-options "--fuel 2 --ifuel 2"
#restart-solver
let sel_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a)
  : action #immut_heap #no_allocs
      (pts_to r v0)
      (v:a{compatible pcm v0 v})
      (fun _ -> pts_to r v0)
  = let f
      : pre_action (pts_to r v0)
                   (v:a{compatible pcm v0 v})
                   (fun _ -> pts_to r v0)
      = fun m0 -> (| sel r m0, m0 |)
    in
    f

let sel_action' (#a:_) (#pcm:_)
                (r:ref a pcm) (v0:erased a) (h:full_hheap (pts_to r v0))
  : v:a{compatible pcm v0 v /\
        (forall frame. composable pcm frame v0 /\
                  interp (pts_to r frame) h ==>
                  compatible pcm frame v)}
  = sel_v r v0 h

let refined_pre_action (#immut:bool) (#allocates:bool)
                       (#[T.exact (`trivial_pre)]pre:heap ->prop)
                       (#[T.exact (`trivial_pre)]post:heap -> prop)
                       (fp0:slprop) (a:Type) (fp1:a -> slprop) =
  m0:full_hheap fp0 ->
  Pure (x:a &
        full_hheap (fp1 x))
       (requires pre m0)
       (ensures fun  (| x, m1 |) ->
         post m1 /\
         (forall frame. frame_related_heaps m0 m1 fp0 (fp1 x) frame immut allocates))

#restart-solver
let refined_pre_action_as_action #immut #allocs #pre #post (#fp0:slprop) (#a:Type) (#fp1:a -> slprop)
                                 ($f:refined_pre_action #immut #allocs #pre #post fp0 a fp1)
  : action #immut #allocs #pre #post fp0 a fp1
  = let g : pre_action fp0 a fp1 = fun m -> f m in
    g

let select_join #a #p (r:ref a p) (x:erased a) (h:full_heap) (hl hr:heap)
  : Lemma
    (requires
      disjoint hl hr /\
      h == join hl hr /\
      interp (pts_to r x) h /\
      interp (pts_to r x) hl /\
      contains_addr hr (Addr?._0 r))
    (ensures (
      let Ref _ _ vl = select_addr hl (Addr?._0 r) in
      let Ref _ _ vr = select_addr hr (Addr?._0 r) in
      sel_v r x h == op p vl vr))
  = ()

#push-options "--z3rlimit_factor 16 --fuel 1 --initial_ifuel 2 --max_ifuel 2"
let select_refine_pre (#a:_) (#p:_)
                      (r:ref a p)
                      (x:erased a)
                      (f:(v:a{compatible p x v}
                        -> GTot (y:a{compatible p y v /\
                                    frame_compatible p x v y})))
   : refined_pre_action #immut_heap #no_allocs
                (pts_to r x)
                (v:a{compatible p x v /\ p.refine v})
                (fun v -> pts_to r (f v))
   = fun h0 ->
       let v = sel_v r x h0 in
       let aux (frame:slprop)
         : Lemma (requires interp (pts_to r x `star` frame) h0)
                 (ensures  interp (pts_to r (f v) `star` frame) h0)
                 [SMTPat ()]
         = let aux (hl hr:_)
             : Lemma
                 (requires disjoint hl hr /\
                           h0 == join hl hr /\
                           interp (pts_to r x) hl /\
                           interp frame hr)
                 (ensures
                           exists hl'. {:pattern disjoint hl' hr}
                             disjoint hl' hr /\
                             h0 == join hl' hr /\
                             interp (pts_to r (f v)) hl' /\
                             interp frame hr)
                 [SMTPat()]
             = let Addr ad = r in
               if contains_addr hr ad
               then begin
                    let Ref _ _ v_l = select_addr hl ad in
                    let Ref _ _ v_r = select_addr hr ad in
                    assert (composable p v_l v_r);
                    select_join r x h0 hl hr;
                    assert (op p v_l v_r == v); //NS: this one seems to be fragile, without the lemma call above
                    assert (compatible p x v_l);
                    let aux (frame_l:a)
                      : Lemma
                        (requires
                          composable p x frame_l /\
                          op p frame_l x == v_l)
                        (ensures
                          exists hl'. {:pattern (disjoint hl' hr)}
                            disjoint hl' hr /\
                            h0 == join hl' hr /\
                            interp (pts_to r (f v)) hl' /\
                            interp frame hr)
                        [SMTPat (composable p x frame_l)]
                      = assert (op p (op p frame_l x) v_r == v);
                        p.comm frame_l x;
                        p.assoc_r x frame_l v_r;
                        assert (op p x (op p frame_l v_r) == v);
                        assert (composable p x (op p frame_l v_r));
                        assert (frame_compatible p x v (f v));
                        assert (composable p (f v) (op p frame_l v_r));
                        assert (op p (f v) (op p frame_l v_r) == v);
                        p.assoc (f v) frame_l v_r;
                        p.comm (f v) frame_l;
                        assert_spinoff (op p (op p frame_l (f v)) v_r == v);
                        let hl' = update_addr hl ad (Ref a p (op p frame_l (f v))) in
                        assert (disjoint hl' hr);
                        assert (h0 == join hl hr);
                        assert (forall a. a <> ad ==> select a hl == select a hl');
                        assert (select ad hl' == Some (Ref a p (op p frame_l (f v))));
                        let aux (a:addr)
                          : Lemma (select a h0 == select a (join hl' hr))
                            [SMTPat (select a h0)]
                          = if (contains_addr hr a && contains_addr hl a)
                            then if a <> ad
                                 then ()
                                 else ()
                            else ()
                        in
                        assert (forall a. select a h0 == select a (join hl' hr));
                        assert (mem_equiv h0 (join hl' hr));
                        mem_equiv_eq h0 (join hl' hr);
                        assert (h0 == join hl' hr)
                    in
                    ()
               end
               else ()
           in
           ()
       in
       (| v, h0 |)
#pop-options

let select_refine (#a:_) (#p:_)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  frame_compatible p x v y})))
   : action #immut_heap #no_allocs (pts_to r x)
            (v:a{compatible p x v /\ p.refine v})
            (fun v -> pts_to r (f v))
   = refined_pre_action_as_action (select_refine_pre r x f)

let update_addr_full_heap (h:full_heap) (a:addr { a < ctr h }) (c:cell{full_cell c}) : full_heap =
  let h' = update_addr h a c in
  assert (forall x. contains_addr h' x ==> x==a \/ contains_addr h x);
  h'

let partial_pre_action (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  full_hheap fp -> (x:a & full_hheap (fp' x))

let upd_gen #a (#p:pcm a)
            (r:ref a p)
            (x v:Ghost.erased a)
            (f: frame_preserving_upd p x v)
  : pre_action (pts_to r x) unit (fun _ -> pts_to r v)
  = fun h ->
     let Ref a p old_v = select_addr h (Addr?._0 r) in
     let new_v = f old_v in
     let cell = Ref a p new_v in
     let h' = update_addr_full_heap h (Addr?._0 r) cell in
     (| (), h' |)

let select_join_both #a (p: pcm a) (r: addr) (h1: heap) (h2: heap { disjoint h1 h2 })
    (x1: a { select r h1 == Some (Ref a p x1) })
    (x2: a { select r h2 == Some (Ref a p x2) })
    : Lemma (select r (join h1 h2) == Some (Ref a p (op p x1 x2))) =
  ()

#push-options "--split_queries always"

let split_off_pcm_val #a (p: pcm a) x y (z:a { composable p y z /\ x == op p y z })
    r (h: heap { select r h == Some (Ref a p x) }) :
    GTot (h1: heap & h2: heap {
      disjoint h1 h2 /\ h == join h1 h2 /\
      select r h1 == Some (Ref a p y) /\
      select r h2 == Some (Ref a p z)
    }) =
  let h1 = update_addr h r (Ref a p y) in
  let h2 = update_addr (empty_heap' (ctr h1)) r (Ref a p z) in
  mem_equiv_eq h (join h1 h2);
  (| h1, h2 |)

let upd_gen_fp1 #a #p r x x1 frame
    (h1: heap {
      select r h1 == Some (Ref a p x1) /\
      compatible p x x1 })
    (h2: heap {
      disjoint h1 h2 /\
      interp frame h2 /\
      full_heap_pred (join h1 h2)
    }) :
    GTot (h1':heap & h2':heap & y':a {
      disjoint h1' h2' /\ join h1 h2 == join h1' h2' /\
      select r h1' == Some (Ref a p x) /\
      select r h2' == Some (Ref a p y') /\
      r < ctr h1' /\ r < ctr h2' /\
      composable p x y' /\ p.refine (op p x y') /\
      interp frame h2'
    }) =
  let x2 = IndefiniteDescription.indefinite_description_ghost _ fun x2 -> composable p x2 x /\ op p x2 x == x1 in
  p.comm x2 x;
  let (| h11, h12 |) = split_off_pcm_val p x1 x x2 r h1 in
  join_associative h11 h12 h2;
  let Some (Ref _ _ y') = select r (join h12 h2) in
  join_commutative h12 h2;
  assert interp frame h2;
  assert interp frame (join h2 h12);
  assert composable p x y';
  assert select r (join h1 h2) == Some (Ref a p (op p x y'));
  assert contains_addr (join h1 h2) r;
  assert full_cell (select_addr (join h1 h2) r);
  assert p.refine (op p x y');
  (| h11, join h12 h2, y' |)

let upd_gen_fp0 #a #p r x frame (h: full_hheap (pts_to #a #p r x `star` frame)) :
    GTot (h1:heap & h2:heap & y:a {
      disjoint h1 h2 /\ h == join h1 h2 /\
      select (Addr?._0 r) h1 == Some (Ref a p x) /\
      select (Addr?._0 r) h2 == Some (Ref a p y) /\
      Addr?._0 r < ctr h /\ Addr?._0 r < ctr h1 /\ Addr?._0 r < ctr h2 /\
      composable p x y /\ p.refine (op p x y) /\
      select (Addr?._0 r) h == Some (Ref a p (op p x y)) /\
      interp frame h2
    }) =
  let h1 = IndefiniteDescription.indefinite_description_ghost _ fun h1 -> exists h2. disjoint h1 h2 /\ h == join h1 h2 /\
    interp (pts_to #a #p r x) h1 /\ interp frame h2 in
  let h2 = IndefiniteDescription.indefinite_description_ghost _ fun h2 -> disjoint h1 h2 /\ h == join h1 h2 /\
    interp (pts_to #a #p r x) h1 /\ interp frame h2 in
  let Some (Ref a1 p1 x1) = select (Addr?._0 r) h1 in assert a1 == a /\ p1 == p;
  let (| h1', h2', y' |) = upd_gen_fp1 #a #p (Addr?._0 r) x x1 frame h1 h2 in
  select_join_both p (Addr?._0 r) h1' h2' x y';
  assert disjoint h1' h2' /\ h == join h1' h2';
  assert select (Addr?._0 r) h1' == Some (Ref a p x);
  assert select (Addr?._0 r) h2' == Some (Ref a p y');
  assert select (Addr?._0 r) h == Some (Ref a p (op p x y'));
  assert contains_addr h (Addr?._0 r);
  assert (Addr?._0 r) < ctr h;
  assert (Addr?._0 r) < ctr h1';
  assert (Addr?._0 r) < ctr h2';
  assert composable p x y';
  assert p.refine (op p x y');
  assert interp frame h2;
  (| h1', h2', y' |)

let upd_gen_fp2 #a p r (x: a) (y: a { composable p x y /\ p.refine (op p x y) }) (v: a) (f: frame_preserving_upd p x v) :
    Lemma (compatible p x (op p x y) /\ f (op p x y) == op p v y /\ composable p v y) =
  p.comm x y; assert compatible p x (op p x y)

let upd_gen_fp3 #a p r
    (x: a) (y: a { composable p x y })
    (z: a { composable p z y })
    (h1: heap { select (Addr?._0 r) h1 == Some (Ref a p x) })
    (h2: heap {
      disjoint h1 h2 /\
      select (Addr?._0 r) h2 == Some (Ref a p y)
    })
    : GTot (h3: heap {
      disjoint h3 h2 /\
      join h3 h2 == update_addr (join h1 h2) (Addr?._0 r) (Ref a p (op p z y)) /\
      interp (pts_to #a #p r z) h3
    }) =
  compatible_refl p z;
  let h3 = update_addr h1 (Addr?._0 r) (Ref a p z) in
  let h' = update_addr (join h1 h2) (Addr?._0 r) (Ref a p (op p z y)) in
  assert disjoint h3 h2;
  introduce forall a. select a (join h3 h2) == select a h' with (
    if a = Addr?._0 r then (
      assert select a (join h3 h2) == Some (Ref _ p (op p z y));
      assert select a h' == Some (Ref _ p (op p z y))
    ) else (
      assert select a h' == select a (join h1 h2);
      assert select a h1 == select a h3
    )
  );
  mem_equiv_eq (join h3 h2) h';
  h3

#push-options "--z3rlimit 10"
let upd_gen_frame_preserving #a #p r x v f : Lemma (is_frame_preserving mut_heap no_allocs (upd_gen #a #p r x v f)) =
  introduce forall (frame: slprop) (h0:full_hheap (pts_to r x `star` frame)).
     (affine_star (pts_to r x) frame h0;
      let (| _, h1 |) = upd_gen r x v f h0 in
      interp (pts_to r v `star` frame) h1) with (
    affine_star (pts_to r x) frame h0;
    let (| _, h1 |) = upd_gen r x v f h0 in
    let addr_r = Addr?._0 r in
    let Ref a p old_v = select_addr h0 addr_r in
    assert h1 == update_addr_full_heap h0 (Addr?._0 r) (Ref a p (f old_v));
    let (| h01, h02, y |) = upd_gen_fp0 #a #p r x frame h0 in
    upd_gen_fp2 p r x y v f;
    let h11 = upd_gen_fp3 p r x y v h01 h02 in
    assert interp (pts_to #a #p r v) h11;
    assert interp frame h02;
    assert join h11 h02 == h1;
    assert interp (pts_to r v `star` frame) h1;
    ()
  )
#pop-options
#pop-options

let upd_gen_action #a #p r x y f =
  upd_gen_frame_preserving r x y f;
  upd_gen r x y f

let upd_gen_modifies
      #a (#p:pcm a) 
      (r:ref a p)
      (x y:Ghost.erased a)
      (f:FStar.PCM.frame_preserving_upd p x y)
      (h:full_hheap (pts_to r x))
: Lemma (
      let (| _, h1 |) = upd_gen_action r x y f h in
      (forall (a:nat). a <> core_ref_as_addr r ==> select a h == select a h1) /\
      related_cells (select (core_ref_as_addr r) h) (select (core_ref_as_addr r) h1)
  )
= let (| _, h1 |) = upd_gen_action r x y f h in
  let (| _, h1'|) = upd_gen #a #p r x y f h in
  assert (h1 == h1')

let upd_action (#a:_) (#pcm:_) (r:ref a pcm)
               (v0:FStar.Ghost.erased a) 
               (v1:a {frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : action (pts_to r v0) unit (fun _ -> pts_to r v1)
  = upd_gen_action r v0 (Ghost.hide v1) (frame_preserving_val_to_fp_upd pcm v0 v1)
  
////////////////////////////////////////////////////////////////////////////////

let free_action (#a:_) (#pcm:_) (r:ref a pcm)
                (v0:FStar.Ghost.erased a{exclusive pcm v0 /\ pcm.refine pcm.FStar.PCM.p.one})
  : action (pts_to r v0) unit (fun _ -> pts_to r pcm.FStar.PCM.p.one)
  = let one = pcm.FStar.PCM.p.one in
    compatible_refl pcm one;
    assert (compatible pcm one one);
    assert (forall (frame:a{composable pcm v0 frame}). frame == one);
    pcm.is_unit one;
    assert (forall (frame:a{composable pcm v0 frame}). composable pcm one frame);
    let f : frame_preserving_upd pcm v0 one =
      fun v -> one in
    upd_gen_action r v0 one f

////////////////////////////////////////////////////////////////////////////////
let split_action #a #pcm r v0 v1
  = let g : refined_pre_action (pts_to r (v0 `op pcm` v1))
                               unit
                               (fun _ -> pts_to r v0 `star` pts_to r v1)
      = fun m ->
          pts_to_compatible_bk r v0 v1 m;
          pts_to_compatible_equiv r v0 v1;
          (| (), m |)
    in
    refined_pre_action_as_action g

////////////////////////////////////////////////////////////////////////////////
let gather_action #a #pcm r v0 v1
  = let g : refined_pre_action (pts_to r v0 `star` pts_to r v1)
                               (_:unit{composable pcm v0 v1})
                               (fun _ -> pts_to r (v0 `op pcm` v1))

      = fun m ->
          pts_to_compatible_fwd r v0 v1 m;
          pts_to_compatible_equiv r v0 v1;
          (| (), m |)
    in
    refined_pre_action_as_action g


////////////////////////////////////////////////////////////////////////////////
let pts_to_not_null_action #a #pcm r v
  = let g : refined_pre_action (pts_to r v)
                               (squash (not (is_null r)))
                               (fun _ -> pts_to r v)
      = fun m ->
          pts_to_not_null r v m;
          (| (), m |)
    in
    refined_pre_action_as_action g

////////////////////////////////////////////////////////////////////////////////
let select_snoc (h: heap) (c: option cell) a :
    Lemma (select a (Seq.snoc h c) == (if a = ctr h then c else select a h))
      [SMTPat (select a (Seq.snoc h c))] =
  reveal_opaque (`%select) (select a)

let extend_full_heap_with (h: full_heap) (c: cell {full_cell c}) :
    h':full_heap {
      h' == Seq.snoc h (Some c) /\
      select (ctr h) h' == Some c
    } =
  let h' = Seq.snoc h (Some c) in
  introduce forall a. contains_addr h' a ==> full_cell (select_addr h' a) with
    introduce _ ==> _ with _.
      if a = ctr h then () else
        assert select_addr h' a == select_addr h a;
  h'

let extend_alt
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:a{pcm.refine x})
: pre_action
    emp
    (ref a pcm)
    (fun r -> pts_to r x)
  = fun h -> 
    let h2 = extend_full_heap_with h (Ref a pcm x) in
    let r: ref a pcm = Addr (ctr h) in
    compatible_refl pcm x;
    intro_pts_to #a #pcm r x h2;
    (| r, h2 |)

#push-options "--z3rlimit 10"
let extend_fp #a #pcm x : Lemma (is_frame_preserving mut_heap allocs (extend_alt #a #pcm x)) =
  introduce forall (frame: slprop) (h0:full_hheap (emp `star` frame)).
     (let (| r, h1 |) = extend_alt #a #pcm x h0 in
      interp (pts_to r x `star` frame) h1) with (
    affine_star emp frame h0;
    let (| r, h1 |) = extend_alt #a #pcm x h0 in
    assert r == Addr (ctr h0);
    assert h1 == Seq.snoc h0 (Some (Ref a pcm x));
    let h2 = update_addr (empty_heap' (ctr h0 + 1)) (ctr h0) (Ref a pcm x) in
    assert interp (pts_to r x) h2;
    assert (forall a. select a h0 == None \/ select a h2 == None);
    assert disjoint h2 h0;
    assert (forall a. select a (join h2 h0) == select a h1);
    mem_equiv_eq (join h2 h0) h1
  )
#pop-options

let extend #a #pcm
        (x:a{pcm.refine x})
 : action #mut_heap #allocs emp (ref a pcm) (fun r -> pts_to r x)
 = extend_fp #a #pcm x; extend_alt x

let extend_modifies_nothing
      #a #pcm (x:a { pcm.refine x })
      (h:full_hheap emp)
= ()

let hprop_sub (p q:slprop) (h0 h1:heap)
  : Lemma (requires (forall (hp:hprop (p `star` q)). hp h0 == hp h1))
          (ensures (forall (hp:hprop q). hp h0 == hp h1))
  = ()

#push-options "--z3rlimit_factor 4 --max_fuel 1 --max_ifuel 1"
#restart-solver
let frame (#a:Type)
          (#immut #allocates #hpre #hpost:_)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action pre a post)
  = let g 
      : refined_pre_action #immut #allocates #hpre #hpost 
          (pre `star` frame) a (fun x -> post x `star` frame)
        = fun h0 ->
              assert (interp (pre `star` frame) h0);
              affine_star pre frame h0;
              let (| x, h1 |) = f h0 in
              assert (interp (post x) h1);
              assert (interp (post x `star` frame) h1);
              assert (forall frame'. frame_related_heaps h0 h1 pre (post x) frame' immut allocates);
              introduce forall frame'.
                    (interp ((pre `star` frame) `star` frame') h0 ==>
                     interp ((post x `star` frame) `star` frame') h1)
              with (
                star_associative pre frame frame';
                star_associative (post x) frame frame'
              );
              (| x, h1 |)
    in
    refined_pre_action_as_action g

let change_slprop (p q:slprop)
                  (proof: (h:heap -> Lemma (requires interp p h) (ensures interp q h)))
  : action #immut_heap #no_allocs p unit (fun _ -> q)
  = let g
      : refined_pre_action p unit (fun _ -> q)
      = fun h ->
          FStar.Classical.forall_intro (FStar.Classical.move_requires proof);
          (| (), h |)
    in
    refined_pre_action_as_action g

// let elim_pure (p:prop)
//   : action (pure p) (u:unit{p}) (fun _ -> emp)
//   = let f
//       : refined_pre_action (pure p) (_:unit{p}) (fun _ -> emp)
//       = fun h -> (| (), h |)
//     in
//     refined_pre_action_as_action f

// let intro_pure (p:prop) (_:squash p)
// : action emp unit (fun _ -> pure p)
// = let f
//     : refined_pre_action emp unit (fun _ -> pure p)
//     = fun h -> (| (), h |)
//   in
//   refined_pre_action_as_action f

let pts_to_evolve (#a:Type u#a) (#pcm:_) (r:ref a pcm) (x y : a) (h:heap)
  : Lemma (requires (interp (pts_to r x) h /\ compatible pcm y x))
          (ensures  (interp (pts_to r y) h))
  = let Ref a' pcm' v' = (select_addr h (Addr?._0 r)) in
    compatible_trans pcm y x v'

// let drop p
// = let f
//     : refined_pre_action p unit (fun _ -> emp)
//     = fun h -> (| (), h |)
//   in
//   refined_pre_action_as_action f


let erase_action_result
      (#pre #post:_)
      (#immut #alloc:_)
      (#fp:slprop)
      (#a:Type)
      (#fp':a -> slprop)
      (act:action #immut #alloc #pre #post fp a fp')
: action #immut #alloc #pre #post fp (erased a) (fun x -> fp' x)
= let g
  : refined_pre_action #immut #alloc #pre #post fp (erased a) (fun x -> fp' x)
  = fun h ->
    let (| x, h1 |) = act h in
    let y : erased a = hide x in
    let h1 : full_hheap (fp' (reveal y)) = h1 in
    (| y, h1 |)
  in
  refined_pre_action_as_action g

let erase_action_result_identity
      (#pre #post:_)
      (#immut #alloc:_)
      (#fp:slprop)
      (#a:Type)
      (#fp':a -> slprop)
      (act:action #immut #alloc #pre #post fp a fp')
      (h:full_hheap fp { pre h})
: Lemma (
    let (| x, h1 |) = act h in
    let (| y, h2 |) = erase_action_result act h in
    x == reveal y /\ h1 == h2
)
= ()
