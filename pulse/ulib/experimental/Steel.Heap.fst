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
module Steel.Heap
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open FStar.PCM
module Frac = Steel.FractionalPermission

#set-options "--fuel 1 --ifuel 1"

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell : Type u#(a + 1) =
  | Ref : a:Type u#a ->
          p:pcm a ->
          frac:Frac.perm{ frac `Frac.lesser_equal_perm` Frac.full_perm } ->
          v:a { frac == Frac.full_perm ==> p.refine v } ->
          cell

let addr = nat

/// This is just the core of a memory, about which one can write
/// assertions. At one level above, we'll encapsulate this memory
/// with a freshness counter, a lock store etc.
let heap : Type u#(a + 1) = addr ^-> option (cell u#a)

let empty_heap : heap = F.on _ (fun _ -> None)

let contains_addr (m:heap) (a:addr)
  : bool
  = Some? (m a)

let select_addr (m:heap) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

let update_addr' (m:heap) (a:addr) (c:option cell)
  : heap
  = F.on _ (fun a' -> if a = a' then c else m a')

let update_addr (m:heap) (a:addr) (c:cell)
  : heap
  = update_addr' m a (Some c)

let disjoint_cells (c0 c1:cell u#h) : prop =
    let Ref t0 p0 f0 v0 = c0 in
    let Ref t1 p1 f1 v1 = c1 in
    t0 == t1 /\
    p0 == p1 /\
    composable p0 v0 v1 /\
    (Frac.sum_perm f0 f1 `Frac.lesser_equal_perm` Frac.full_perm) /\
    (Frac.sum_perm f0 f1 == Frac.full_perm ==> p0.refine (op p0 v0 v1))

let disjoint_cells_sym (c0 c1:cell u#h)
  : Lemma (requires disjoint_cells c0 c1)
          (ensures disjoint_cells c1 c0)
  = let Ref t0 p0 f0 v0 = c0 in
    let Ref t1 p1 f0 v1 = c1 in
    p0.comm v0 v1;
    ()

let disjoint_addr (m0 m1:heap u#h) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some c0, Some c1 ->
      disjoint_cells c0 c1
    | Some _, None
    | None, Some _
    | None, None ->
      True

type ref (a:Type u#a) (pcm:pcm a): Type u#0 =
  | Null
  | Addr of addr

let null (#a:Type u#a) (#pcm:pcm a) : ref a pcm = Null

let is_null (#a:Type u#a) (#pcm:pcm a) (r:ref a pcm) : (b:bool{b <==> r == null}) = Null? r

let disjoint (m0 m1:heap u#h)
  : prop
  = forall a. disjoint_addr m0 m1 a

#push-options "--warn_error -271"

let disjoint_sym (m0 m1:heap u#h)
  = let aux (m0 m1:heap u#h) (a:addr)
      : Lemma (requires disjoint_addr m0 m1 a)
              (ensures disjoint_addr m1 m0 a)
              [SMTPat (disjoint_addr m1 m0 a)]
    = match m0 a, m1 a with
      | Some c0, Some c1 -> disjoint_cells_sym c0 c1
      | _ -> ()
    in
    ()

let join_cells (c0:cell u#h) (c1:cell u#h{disjoint_cells c0 c1}) =
  let Ref a0 p0 f0 v0 = c0 in
  let Ref a1 p1 f1 v1 = c1 in
  Ref a0 p0 (Frac.sum_perm f0 f1) (op p0 v0 v1)

let join (m0:heap) (m1:heap{disjoint m0 m1})
  : heap
  = F.on _ (fun a ->
      match m0 a, m1 a with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some c0, Some c1 ->
        Some (join_cells c0 c1))

let disjoint_join_cells_assoc (c0 c1 c2:cell u#h)
  : Lemma
    (requires disjoint_cells c1 c2 /\
              disjoint_cells c0 (join_cells c1 c2))
    (ensures  disjoint_cells c0 c1 /\
              disjoint_cells (join_cells c0 c1) c2 /\
              join_cells (join_cells c0 c1) c2 == join_cells c0 (join_cells c1 c2))
  = let Ref a0 p0 f0 v0 = c0 in
    let Ref a1 p1 f1 v1 = c1 in
    let Ref a2 p2 f2 v2 = c2 in
    p0.assoc v0 v1 v2

let disjoint_join' (m0 m1 m2:heap u#h)
  : Lemma (requires disjoint m1 m2 /\
                    disjoint m0 (join m1 m2))
          (ensures  disjoint m0 m1 /\ disjoint (join m0 m1) m2)
          [SMTPat (disjoint (join m0 m1) m2)]
  = let aux (a:addr)
      : Lemma (disjoint_addr m0 m1 a)
              [SMTPat ()]
      = match m0 a, m1 a, m2 a with
        | Some c0, Some c1, Some c2 ->
          disjoint_join_cells_assoc c0 c1 c2
        | _ -> ()
    in
    assert (disjoint m0 m1);
    let aux (a:addr)
      : Lemma (disjoint_addr (join m0 m1) m2 a)
              [SMTPat ()]
      = match m0 a, m1 a, m2 a with
        | Some c0, Some c1, Some c2 ->
          disjoint_join_cells_assoc c0 c1 c2
        | _ -> ()
    in
    ()

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

let join_cells_commutative (c0:cell u#h) (c1:cell u#h{disjoint_cells c0 c1})
  : Lemma (disjoint_cells_sym c0 c1; join_cells c0 c1 == join_cells c1 c0)
          [SMTPat (join_cells c0 c1)]
  = let Ref a0 p0 _ v0 = c0 in
    let Ref a1 p1 _ v1 = c1 in
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
        : Lemma (l a == r a)
                [SMTPat ()]
        = match m0 a, m1 a, m2 a with
          | Some c0, Some c1, Some c2 ->
            disjoint_join_cells_assoc c0 c1 c2
          | _ -> ()
    in
    ()

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
  = disjoint_join m2 m0 m1;
    join_commutative (join m0 m1) m2;
    join_associative m2 m0 m1

////////////////////////////////////////////////////////////////////////////////

let slprop = a_heap_prop

module W = FStar.WellFounded


let interp (p:slprop u#a) (m:heap u#a)
  : Tot prop
  = p m

let as_slprop p = p

let emp : slprop u#a = fun h -> True

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
  let Ref a' pcm' _ v' = c in
  a == a' /\
  pcm == pcm' /\
  compatible pcm v v'

let pts_to_cell_join (#a:Type u#a) (pcm:pcm a) (v1 v2:a) (c:cell u#a)
  : Lemma (requires (pts_to_cell pcm v1 c /\ pts_to_cell pcm v2 c))
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
    match h0 r, h1 r, (join h0 h1) r with
    | Some (Ref a0 pcm0 _ v0), Some (Ref a1 pcm1 _ v1), Some (Ref a01 pcm01 _ v01) ->
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
  hprop


let h_and (p1 p2:slprop u#a) : slprop u#a =
  fun (h: heap) -> p1 h /\ p2 h

let h_or (p1 p2:slprop u#a) : slprop u#a =
  fun (h: heap) -> p1 h \/ p2 h

let star (p1 p2: slprop u#a) : slprop u#a =
  fun (h: heap) -> exists (h1 h2 : heap).
        h1 `disjoint` h2 /\
        h == join h1 h2 /\
        interp p1 h1 /\
        interp p2 h2

let wand (p1 p2: slprop u#a) : slprop u#a =
  fun (h: heap) ->  forall (h1: heap).
        h `disjoint` h1 /\
        interp p1 h1 ==>
        interp p2 (join h h1)

let h_exists_body (#a:Type u#b) (f: (a -> slprop u#a)) (h:heap) (x:a) : prop =
  interp (f x) h

let h_exists  (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a =
  fun (h: heap) -> exists x. h_exists_body f h x

let h_forall_body (#a:Type u#b) (f: (a -> slprop u#a)) (h:heap) (x:a) : prop =
  interp (f x) h

let h_forall (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a =
  fun (h: heap) -> forall x. h_forall_body f h x

let h_refine p r = h_and p r

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
      = let emp_m : heap = on _ (fun _ -> None) in
        assert (disjoint emp_m m);
        assert (interp (p `star` emp) (join m emp_m));
        assert (mem_equiv m (join m emp_m))
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
       (let Ref a' pcm' _ v' = select_addr m (Addr?._0 x) in
        a == a' /\
        pcm == pcm' /\
        compatible pcm v v'))
     (ensures
       interp (pts_to x v) m)
  = ()


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
    let Ref _ _ _ v = select_addr m addr in
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
      = let Ref _ _ _ v0' = c0 in
        let Ref _ _ _ v1' = c1 in
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

let pts_to_compatible_bk (#a:Type u#a)
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
    let Ref _ _ _ v = select_addr m addr in
    let v01 = (op pcm v0 v1) in
    assert (pts_to_cell pcm v01 c);
    let Ref _ _ frac v = c in
    assert (compatible pcm v01 v);
    let aux frame
      : Lemma
        (requires
           composable pcm v01 frame /\
           op pcm frame v01 == v)
        (ensures
           exists m0 m1.
             interp (pts_to x v0) m0 /\
             interp (pts_to x v1) m1 /\
             disjoint m0 m1 /\
             m `mem_equiv` join m0 m1)
        [SMTPat (composable pcm v01 frame)]
      = let c0 = Ref a pcm (Frac.half_perm frac) v0 in
        pcm.FStar.PCM.assoc_r v0 v1 frame;
        let c1 : cell = Ref a pcm (Frac.half_perm frac) (op pcm v1 frame) in
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
        let m0 = update_addr empty_heap addr c0 in
        let m1 = update_addr m addr c1 in
        assert (disjoint m0 m1) //fire the existential
    in
    ()

let pts_to_compatible (#a:Type u#a)
                      (#pcm:_)
                      (x:ref a pcm)
                      (v0 v1:a)
                      (m:heap u#a) =
    FStar.Classical.forall_intro (FStar.Classical.move_requires (pts_to_compatible_fwd x v0 v1));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (pts_to_compatible_bk x v0 v1))

let pts_to_join (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v1 v2:a) (m:heap)
  : Lemma (requires (interp (pts_to r v1) m /\ interp (pts_to r v2) m))
          (ensures joinable pcm v1 v2)
  = ()

let pts_to_join' (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v1 v2:a) (m:heap)
  : Lemma (requires (interp (pts_to r v1) m /\ interp (pts_to r v2) m))
          (ensures (exists z. compatible pcm v1 z /\ compatible pcm v2 z /\
                         interp (pts_to r z) m))
  = let Ref a' pcm' _ v' = (select_addr m (Addr?._0 r)) in
    compatible_refl pcm v'

let pts_to_compatible_equiv (#a:Type) (#pcm:_) (x:ref a pcm) (v0:a) (v1:a{composable pcm v0 v1})
  = FStar.Classical.forall_intro (pts_to_compatible x v0 v1)


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
// wand & implications
////////////////////////////////////////////////////////////////////////////////

let stronger_star p q r = ()
let weaken (p q r:slprop) (h:heap u#a) = ()

////////////////////////////////////////////////////////////////////////////////
// Actions:
////////////////////////////////////////////////////////////////////////////////
module PP = Steel.Preorder

let full_heap_pred h =
  forall a. contains_addr h a ==>
       (select_addr h a).frac == Frac.full_perm

#push-options "--fuel 2 --ifuel 2"
let heap_evolves : FStar.Preorder.preorder full_heap =
  fun (h0 h1:heap) ->
    forall (a:addr).
      match h0 a, h1 a with
      | None, _ -> True //an unused address in h0 can evolve anyway

      | Some (Ref a0 p0 f0 v0), Some (Ref a1 p1 f1 v1) ->
        //if a is used h0 then it remains used and ...
        a0 == a1 /\  //its type can't change
        p0 == p1 /\  //its pcm can't change
        PP.preorder_of_pcm p0 v0 v1 //and its value evolves by the pcm's preorder
      | _ -> False
#pop-options

let free_above_addr h a =
  forall (i:nat). i >= a ==> h i == None

let weaken_free_above (h:heap) (a b:nat)
  : Lemma (free_above_addr h a /\ a <= b ==> free_above_addr h b)
  = ()


////////////////////////////////////////////////////////////////////////////////
// sel
////////////////////////////////////////////////////////////////////////////////
let sel #a #pcm (r:ref a pcm) (m:full_hheap (ptr r))
  : a
  = let Ref _ _ _ v = select_addr m (Addr?._0 r) in
    v

let sel_v #a #pcm r v m = sel r m

let sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:full_hheap (ptr r))
  : Lemma (interp (pts_to r (sel r m)) m)
  = let Ref _ _ _ v = select_addr m (Addr?._0 r) in
    assert (sel r m == v);
    compatible_refl pcm v

let witnessed_ref_stability #a #pcm (r:ref a pcm) (fact:a -> prop)
  = let fact_h = witnessed_ref r fact in
    let aux (h0 h1:full_heap)
      : Lemma
        (requires
          fact_h h0 /\
          heap_evolves h0 h1)
        (ensures
          fact_h h1)
        [SMTPat ()]
      = let Addr addr = r in
        assert (interp (ptr r) h0);
        assert (fact (sel r h0));
        assert (contains_addr h1 addr);
        compatible_refl pcm (select_addr h1 addr).v;
        assert (compatible pcm (select_addr h1 addr).v (select_addr h1 addr).v);
        assert (interp (pts_to r (select_addr h1 addr).v) h1);
        assert (interp (ptr r) h1);
        assert (fact (sel r h1))
    in
    ()

#set-options "--fuel 2 --ifuel 2"

let sel_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a)
  : action (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)
  = let f
      : pre_action (pts_to r v0)
                   (v:a{compatible pcm v0 v})
                   (fun _ -> pts_to r v0)
      = fun m0 -> (| sel r m0, m0 |)
    in
    f

let sel_action' (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a) (h:full_hheap (pts_to r v0))
  : v:a{compatible pcm v0 v /\
        (forall frame. composable pcm frame v0 /\
                  interp (pts_to r frame) h ==>
                  compatible pcm frame v)}
  = sel_v r v0 h

let refined_pre_action (fp0:slprop) (a:Type) (fp1:a -> slprop) =
  m0:full_hheap fp0 ->
  Pure (x:a &
        full_hheap (fp1 x))
       (requires True)
       (ensures fun  (| x, m1 |) ->
         forall frame. frame_related_heaps m0 m1 fp0 (fp1 x) frame false)

let refined_pre_action_as_action (#fp0:slprop) (#a:Type) (#fp1:a -> slprop)
                                 ($f:refined_pre_action fp0 a fp1)
  : action fp0 a fp1
  = let g : pre_action fp0 a fp1 = fun m -> f m in
    let aux (frame:slprop)
            (m0:full_hheap (fp0 `star` frame))
      : Lemma
        (ensures
          (affine_star fp0 frame m0;
           let (| x, m1 |) = g m0 in
           interp (fp1 x `star` frame) m1 /\
          (forall (hp:hprop frame). hp m0 == hp m1) /\
          heap_evolves m0 m1 /\
          (forall ctr. m0 `free_above_addr` ctr ==> m1 `free_above_addr` ctr)))
        [SMTPat ()]
      = affine_star fp0 frame m0;
        let (| x', m1' |) = g m0 in
        let (| x, m1 |) = f m0 in
        assert (x == x' /\ m1 == m1')
    in
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
      let Ref _ _ _ vl = select_addr hl (Addr?._0 r) in
      let Ref _ _ _ vr = select_addr hr (Addr?._0 r) in
      sel_v r x h == op p vl vr))
  = ()

#push-options "--z3rlimit_factor 8 --max_fuel 0 --initial_ifuel 2 --max_ifuel 2"
let select_refine_pre (#a:_) (#p:_)
                      (r:ref a p)
                      (x:erased a)
                      (f:(v:a{compatible p x v}
                        -> GTot (y:a{compatible p y v /\
                                    frame_compatible p x v y})))
   : refined_pre_action
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
                    let Ref _ _ frac_l v_l = select_addr hl ad in
                    let Ref _ _ _ v_r = select_addr hr ad in
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
                        assert (op p (op p frame_l (f v)) v_r == v);
                        let hl' = update_addr hl ad (Ref a p frac_l (op p frame_l (f v))) in
                        assert (disjoint hl' hr);
                        assert (h0 == join hl hr);
                        assert (forall a. a <> ad ==> hl a == hl' a);
                        assert (frac_l =!= Frac.full_perm);
                        assert (hl' ad == Some (Ref a p frac_l (op p frame_l (f v))));
                        let aux (a:addr)
                          : Lemma (h0 a == (join hl' hr) a)
                            [SMTPat (h0 a)]
                          = if (contains_addr hr a && contains_addr hl a)
                            then if a <> ad
                                 then ()
                                 else ()
                            else ()
                        in
                        assert (forall a. h0 a == (join hl' hr) a);
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
   : action (pts_to r x)
            (v:a{compatible p x v /\ p.refine v})
            (fun v -> pts_to r (f v))
   = refined_pre_action_as_action (select_refine_pre r x f)


let update_addr_full_heap (h:full_heap) (a:addr) (c:cell{c.frac == Frac.full_perm}) : full_heap =
  let h' = update_addr h a c in
  assert (forall x. contains_addr h' x ==> x==a \/ contains_addr h x);
  h'


let upd' (#a:_) (#pcm:_) (r:ref a pcm) (v0:FStar.Ghost.erased a) (v1:a {frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : pre_action (pts_to r v0) unit (fun _ -> pts_to r v1)
  = fun h ->
    let cell = Ref a pcm Frac.full_perm v1  in
    let h' = update_addr h (Addr?._0 r) cell in
    assert (forall x. contains_addr h' x ==> x==(Addr?._0 r) \/ contains_addr h x);
    assert (h' `contains_addr` Addr?._0 r);
    assert (pts_to_cell pcm v1 cell);
    assert (interp (pts_to r v1) h');
    (| (), h' |)


let definedness #a #pcm (v0:a) (v0_val:a) (v1:a) (vf:a)
  : Lemma (requires
             compatible pcm v0 v0_val /\
             composable pcm v0_val vf /\
             frame_preserving pcm v0 v1)
          (ensures
             composable pcm vf v1 /\
             composable pcm v1 vf)
  = assert (exists vf'. composable pcm vf' v0 /\ op pcm vf' v0 == v0_val);
    let aux (vf':a {composable pcm vf' v0 /\ op pcm vf' v0 == v0_val})
      : Lemma (composable pcm vf v1 /\
               composable pcm v1 vf)
              [SMTPat(op pcm vf' v0)]
        = assert (composable pcm (op pcm vf' v0) vf);
          pcm.comm vf' v0;
          assert (composable pcm (op pcm v0 vf') vf);
          pcm.assoc_r v0 vf' vf;
          assert (composable pcm v0 (op pcm vf' vf));
          pcm.comm vf vf';
          assert (composable pcm v0 (op pcm vf vf'));
          assert (composable pcm (op pcm vf vf') v1);
          pcm.comm (op pcm vf vf') v1;
          pcm.assoc v1 vf vf';
          assert (composable pcm (op pcm v1 vf) vf')
    in
    ()

let composable_compatible #a pcm (x y z:a)
  : Lemma (requires compatible pcm x y /\
                    composable pcm y z)
          (ensures composable pcm x z /\
                   composable pcm z x)
  = let aux (f:a{composable pcm f x /\ op pcm f x == y})
      : Lemma (composable pcm x z /\
               composable pcm z x)
              [SMTPat (op pcm f x)]
      = assert (composable pcm (op pcm f x) z);
        pcm.assoc_r f x z;
        assert (composable pcm f (op pcm x z));
        pcm.comm x z
    in
    let s : squash (exists f. composable pcm f x /\ op pcm f x == y) = () in
    ()

let heap_evolves_by_frame_preserving_update #a #pcm (r:ref a pcm)
                                            (v0:Ghost.erased a)
                                            (v1:a {frame_preserving pcm v0 v1 /\ pcm.refine v1})
                                            (h0:full_hheap (pts_to r v0))
   : Lemma (let h1 = update_addr_full_heap h0 (Addr?._0 r) (Ref a pcm Frac.full_perm v1) in
            heap_evolves h0 h1)
  = let v = sel r h0 in
    PP.frame_preserving_is_preorder_respecting pcm v0 v1;
    assert (PP.preorder_of_pcm pcm v v1)

#push-options "--z3rlimit_factor 4 --max_fuel 1 --initial_ifuel 1 --max_ifuel 2"
#restart-solver
let upd_lemma'_1 (#a:_) #pcm (r:ref a pcm)
                 (v0:Ghost.erased a) (v1:a {frame_preserving pcm v0 v1 /\ pcm.refine v1})
                 (h:full_hheap (pts_to r v0)) (frame:slprop)
                 (h0 hf:heap)
  : Lemma
    (requires
      interp (pts_to r v0 `star` frame) h /\
      disjoint h0 hf /\
      h == join h0 hf /\
      interp (pts_to r v0) h0 /\
      interp frame hf)
    (ensures (
      let (| _, h' |) = upd' r v0 v1 h in
      let cell0 = select_addr h0 (Addr?._0 r) in
      let h0' = update_addr h0 (Addr?._0 r) (Ref a pcm cell0.frac v1) in
      disjoint h0' hf /\
      interp (pts_to r v1) h0' /\
      interp frame hf /\
      h' == join h0' hf /\
      heap_evolves h h' /\
      (forall (hp:hprop frame). hp h == hp h')))
  = let (| _, h'|) = upd' r v0 v1 h in
    let cell0 = select_addr h0 (Addr?._0 r) in
    let cell1 = (Ref a pcm cell0.frac v1) in
    let h0' = update_addr h0 (Addr?._0 r) cell1 in
    assert (interp (pts_to r v1) h0');
    assert (interp frame hf);
    let aux (a:addr)
      : Lemma (disjoint_addr h0' hf a )
              [SMTPat (disjoint_addr h0' hf a)]
      = if a <> (Addr?._0 r) then ()
        else match h0 a, h0' a, hf a with
             | Some (Ref a0 p0 f0 v0_val),
               Some (Ref a0' p0' f0' v0'),
               Some (Ref af pf ff vf) ->
                  assert (a0' == af);
                  assert (p0' == pf);
                  assert (v0' == v1);
                  assert (f0 == f0');
                  assert (Frac.sum_perm f0 ff `Frac.lesser_equal_perm` Frac.full_perm);
                  assert (compatible pcm v0 v0_val);

                  compatible_refl pcm vf;
                  assert (pts_to_cell pcm vf (Some?.v (hf a)));
                  assert (interp (pts_to r vf) hf);

                  compatible_refl pcm v0_val;
                  assert (pts_to_cell pcm v0_val (Some?.v (h0 a)));
                  assert (interp (pts_to r v0_val) h0);
                  assert (interp (pts_to r v0_val `star` pts_to r vf) h);
                  pts_to_compatible r v0_val vf h;
                  assert (composable pcm v0_val vf);

                  assert (interp (pts_to r (op pcm v0_val vf)) h);
                  pcm.comm v0_val vf;
                  definedness #_ #pcm v0 v0_val v1 vf;
                  assert (composable pcm v1 vf);
                  assert (Frac.sum_perm f0' ff `Frac.lesser_equal_perm` Frac.full_perm);
                  assert (pcm.refine v1);
                  assert (exists f0. composable pcm v0 f0 /\ op pcm f0 v0 == v0_val);
                  assert (exists f0. composable pcm v0 f0 /\ composable pcm (op pcm f0 v0) vf);
                  let aux f0
                    : Lemma
                      (requires
                        composable pcm v0 f0 /\
                        composable pcm (op pcm f0 v0) vf)
                      (ensures
                        composable pcm vf v0)
                    [SMTPat (composable pcm v0 f0)]
                    = pcm.comm v0 f0;
                      pcm.assoc_r f0 v0 vf;
                      pcm.comm vf v0
                  in
                  assert (composable pcm vf v0);
                  assert (op pcm vf v1 == v1);
                  pcm.comm vf v1;
                  assert (Frac.sum_perm f0' ff == Frac.full_perm ==> pcm.refine (op pcm v1 vf))

             | _ -> ()
    in
    assert (disjoint h0' hf);
    let aux (a:addr)
         : Lemma (h' a == (join h0' hf) a)
                 [SMTPat ()]
         = if a <> (Addr?._0 r)
           then ()
           else begin
             assert (h0' a == Some cell1);
             match h0 a, hf a with
             | _, None -> ()
             | Some (Ref a0 p0 f0 v0_val),
               Some (Ref af pf ff vf) ->
               let c0 = Some?.v (h0 a) in
               let cf = Some?.v (hf a) in
               assert (a0 == af);
               assert (p0 == pf);
               assert (compatible pcm v0 v0_val);
               assert (disjoint_cells c0 cf);
               assert (composable pcm v0_val vf);
               composable_compatible pcm v0 v0_val vf;
               assert (composable pcm v0 vf);
               assert (disjoint_cells cell1 cf);
               assert (composable pcm v1 vf);
               assert (composable pcm vf v0);
               assert (op pcm vf v1 == v1);
               pcm.comm vf v1
           end
    in
    assert (mem_equiv h' (join h0' hf));
    heap_evolves_by_frame_preserving_update r v0 v1 h;
    let aux (hp:hprop frame)
         : Lemma (ensures (hp h == hp h'))
                 [SMTPat ()]
         = FStar.PropositionalExtensionality.apply (hp h) (hp h')
    in
    assert (forall (hp:hprop frame). hp h == hp h')

let upd_lemma' (#a:_) #pcm (r:ref a pcm)
               (v0:Ghost.erased a) (v1:a {frame_preserving pcm v0 v1 /\ pcm.refine v1})
               (h:full_hheap (pts_to r v0)) (frame:slprop)
  : Lemma
    (requires
      interp (pts_to r v0 `star` frame) h)
    (ensures (
      (let (| x, h1 |) = upd' r v0 v1 h in
       interp (pts_to r v1 `star` frame) h1 /\
       heap_evolves h h1 /\
       (forall (hp:hprop frame). hp h == hp h1))))
  = let aux (h0 hf:heap)
     : Lemma
       (requires
         interp (pts_to r v0 `star` frame) h /\
         disjoint h0 hf /\
         h == join h0 hf /\
         interp (pts_to r v0) h0 /\
         interp frame hf)
       (ensures (
         let (| _, h' |) = upd' r v0 v1 h in
         let cell0 = select_addr h0 (Addr?._0 r) in
         let h0' = update_addr h0 (Addr?._0 r) (Ref a pcm cell0.frac v1) in
         disjoint h0' hf /\
         interp (pts_to r v1) h0' /\
         interp frame hf /\
         h' == join h0' hf /\
         heap_evolves h h' /\
         (forall (hp:hprop frame). hp h == hp h')))
       [SMTPat (disjoint h0 hf)]
     = upd_lemma'_1 r v0 v1 h frame h0 hf
    in
    ()
#pop-options


let upd_action (#a:_) (#pcm:_) (r:ref a pcm)
               (v0:FStar.Ghost.erased a) (v1:a {frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : action (pts_to r v0) unit (fun _ -> pts_to r v1)
  = let g : refined_pre_action (pts_to r v0) unit (fun _ -> pts_to r v1)
      = fun m ->
          let res = upd' r v0 v1 m in
          FStar.Classical.forall_intro (FStar.Classical.move_requires (upd_lemma' r v0 v1 m));
          res
    in
    refined_pre_action_as_action g

let partial_pre_action (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  hheap fp -> (x:a & hheap (fp' x))

let upd_gen #a (#p:pcm a)
               (r:ref a p)
               (x v:Ghost.erased a)
               (f: frame_preserving_upd p x v)
  : partial_pre_action (pts_to r x)
                       unit
                       (fun _ -> pts_to r v)
  = fun h ->
     let Ref _ _ frac old_v = select_addr h (Addr?._0 r) in
     let new_v = f old_v in
     let cell = Ref a p frac new_v in
     let h' = update_addr h (Addr?._0 r) cell in
     (| (), h' |)

let upd_gen_updates_only_r #a (#p:pcm a) (r:ref a p)
                           (x v:Ghost.erased a)
                           (f: frame_preserving_upd p x v)
                           (h0:hheap (pts_to r x))
  : Lemma (let (| _, h1 |) = upd_gen r x v f h0 in
           forall s. s <> (Addr?._0 r) ==> h0 s == h1 s)
  = ()

let frame_preserving_is_preorder_respecting_pcm_t #a (p:pcm a) (x y:a)
  : Lemma (requires frame_preserving p x y)
          (ensures (PP.preorder_of_pcm p x y))
  = PP.frame_preserving_is_preorder_respecting p x y;
    compatible_refl p x

let upd_gen_full_evolution #a (#p:pcm a)
      (r:ref a p)
      (x y:Ghost.erased a)
      (f:frame_preserving_upd p x y)
      (h:full_hheap (pts_to r x))
  : Lemma
    (ensures
      (let (| _, h1 |) = upd_gen r x y f h in
       full_heap_pred h1 /\
       heap_evolves h h1))
  = let old_v = sel_action' r x h in
    let new_v = f old_v in
    assert (frame_preserving p old_v new_v);
    frame_preserving_is_preorder_respecting_pcm_t p old_v new_v;
    assert (PP.preorder_of_pcm p old_v new_v);
    let (| _, h1 |) = upd_gen r x y f h in
    assert (forall a. a<>(Addr?._0 r) ==> h1 a == h a);
    assert (forall (x:addr). contains_addr h1 x ==> x==(Addr?._0 r) \/ contains_addr h x);
    assert (full_heap_pred h1);
    assert (heap_evolves h h1)

#push-options "--z3rlimit_factor 4"

let upd_gen_frame_preserving #a (#p:pcm a)
      (r:ref a p)
      (x y:Ghost.erased a)
      (f:frame_preserving_upd p x y)
      (h:hheap (pts_to r x))
      (frame:slprop)
 : Lemma
   (requires interp (pts_to r x `star` frame) h)
   (ensures
     (let (| b, h1 |) = upd_gen r x y f h in
      interp ((pts_to r y) `star` frame) h1 /\
      (forall (hp:hprop frame). hp h == hp h1)))
 = let Ref _ _ frac old_v = select_addr h (Addr?._0 r) in
   let old_v : a = old_v in
   let (| _, h1 |) = upd_gen r x y f h in
   let new_v = f old_v in
   assert (forall a. a<>(Addr?._0 r) ==> h1 a == h a);
   let aux (hl hr:heap)
       : Lemma
         (requires
           disjoint hl hr /\
           h == join hl hr /\
           interp (pts_to r x) hl /\
           interp frame hr)
         (ensures (
           let (| _, hl' |) = upd_gen r x y f hl in
           disjoint hl' hr /\
           h1 == join hl' hr
           ))
         [SMTPat (disjoint hl hr)]
       = assert (contains_addr hl (Addr?._0 r));
         let Ref _ _ _ old_v_l = select_addr hl (Addr?._0 r) in
         let old_v_l : a = old_v_l in
         let (| _, hl' |) = upd_gen r x y f hl in
         upd_gen_updates_only_r r x y f hl;
         assert (forall s. s<>(Addr?._0 r) ==> hl s == hl' s);
         let Ref _ _ _ new_v_l = select_addr hl' (Addr?._0 r) in
         let new_v_l : a = new_v_l in
         if contains_addr hr (Addr?._0 r)
         then let Ref _ _ _ old_v_r = select_addr hr (Addr?._0 r) in
              let old_v_r : a = old_v_r in
              assert (composable p old_v_l old_v_r);
              assert (op p old_v_l old_v_r == old_v); //old_v_l * old_v_r = old_v
              assert (new_v_l == f old_v_l);
              assert (composable p new_v_l old_v_r);
              assert (op p new_v_l old_v_r == new_v);
              assert (disjoint hl' hr);
              mem_equiv_eq h1 (join hl' hr)
         else begin
           assert (old_v_l == old_v);
           assert (new_v == new_v_l);
           assert (disjoint hl hr);
           assert (disjoint hl' hr);
           assert (h1 (Addr?._0 r) == hl' (Addr?._0 r));
           mem_equiv_eq h1 (join hl' hr);
           assert (h1 == join hl' hr);
           ()
         end
     in
     let aux (hp:hprop frame)
       : Lemma (ensures (hp h == hp h1))
               [SMTPat ()]
       = FStar.PropositionalExtensionality.apply (hp h) (hp h1)
     in
     ()

let upd_gen_action #a (#p:pcm a) (r:ref a p) (x y:Ghost.erased a) (f:frame_preserving_upd p x y)
  : action (pts_to r x)
           unit
           (fun _ -> pts_to r y)
  = let refined : refined_pre_action
                    (pts_to r x)
                    unit
                    (fun _ -> pts_to r y)
     = fun h ->
         let (|u, h1|) = upd_gen r x y f h in
         FStar.Classical.forall_intro (FStar.Classical.move_requires (upd_gen_frame_preserving r x y f h));
         upd_gen_full_evolution #a r x y f h;
         (| (), h1 |)
    in
    refined_pre_action_as_action refined

////////////////////////////////////////////////////////////////////////////////

let free_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:FStar.Ghost.erased a{exclusive pcm v0 /\ pcm.refine pcm.FStar.PCM.p.one})
  : action (pts_to r v0) unit (fun _ -> pts_to r pcm.FStar.PCM.p.one)
  = FStar.PCM.exclusive_is_frame_preserving pcm v0;
    upd_action r v0 pcm.FStar.PCM.p.one

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
#push-options "--z3rlimit 20"
let extend #a #pcm x addr h =
    let r : ref a pcm = Addr addr in
    let h' = update_addr_full_heap h addr (Ref a pcm Frac.full_perm x) in
    assert (h' `free_above_addr` (addr + 1));
    assert (h' `contains_addr` addr);
    assert (interp (pts_to r x) h');
    let extend_aux (frame:slprop) (h0 hf:heap)
      : Lemma
       (requires
          disjoint h0 hf /\
          h == join h0 hf /\
          interp emp h0 /\
          interp frame hf)
       (ensures (
          let h0' = update_addr h0 addr (Ref a pcm Frac.full_perm x) in
          disjoint h0' hf /\
          interp (pts_to r x) h0' /\
          h' == join h0' hf /\
          heap_evolves h h' /\
          interp (pts_to r x `star` frame) h' /\
          (forall (hp:hprop frame). hp h == hp h')
         ))
       [SMTPat (interp emp h0);
        SMTPat (interp frame hf)]
      = let h0' = update_addr h0 addr (Ref a pcm Frac.full_perm x) in
        // assert (disjoint h0' hf);
        // assert (interp (pts_to r x) h0');
        assert (mem_equiv h' (join h0' hf));
        // assert (h' == (join h0' hf));
        intro_star (pts_to r x) frame h0' hf;
        // assert (interp (pts_to r x `star` frame) h');
        let aux (hp:hprop frame)
          : Lemma (ensures (hp h == hp h'))
                  [SMTPat ()]
            = FStar.PropositionalExtensionality.apply (hp h) (hp h')
        in
        ()
     in
     (| r, h' |)
#pop-options


let frame (#a:Type)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action pre a post)
  = let g : refined_pre_action (pre `star` frame) a (fun x -> post x `star` frame)
        = fun h0 ->
              assert (interp (pre `star` frame) h0);
              affine_star pre frame h0;
              let (| x, h1 |) = f h0 in
              assert (interp (post x) h1);
              assert (interp (post x `star` frame) h1);
              assert (forall frame'. frame_related_heaps h0 h1 pre (post x) frame' false);
              let aux (frame':slprop)
                : Lemma (requires
                            interp ((pre `star` frame) `star` frame') h0)
                        (ensures
                            interp ((post x `star` frame) `star` frame') h1)
                        [SMTPat ()]
                = star_associative pre frame frame';
                  star_associative (post x) frame frame'
              in
              assert (forall frame'. frame_related_heaps h0 h1 (pre `star` frame) (post x `star` frame) frame' false);
              (| x, h1 |)
    in
    refined_pre_action_as_action g

let change_slprop (p q:slprop)
                  (proof: (h:heap -> Lemma (requires interp p h) (ensures interp q h)))
  : action p unit (fun _ -> q)
  = let g
      : refined_pre_action p unit (fun _ -> q)
      = fun h ->
          proof h;
          let aux (frame:slprop)
            : Lemma (requires
                        interp (p `star` frame) h)
                    (ensures
                        interp (q `star` frame) h)
                    [SMTPat ()]
            = FStar.Classical.forall_intro (FStar.Classical.move_requires proof)
          in
          (| (), h |)
    in
    refined_pre_action_as_action g

let id_elim_star p q m =
  let starprop (ml:heap) (mr:heap) =
      disjoint ml mr
    /\ m == join ml mr
    /\ interp p ml
    /\ interp q mr
  in
  elim_star p q m;
  let p1 : heap -> prop = fun ml -> (exists mr. starprop ml mr) in
  let ml = IndefiniteDescription.indefinite_description_tot _ p1 in
  let starpropml mr : prop = starprop ml mr in // this prop annotation seems needed
  let mr = IndefiniteDescription.indefinite_description_tot _ starpropml in
  (ml, mr)

let id_elim_exists #a p m =
  let existsprop (x:a) = interp (p x) m in
  elim_h_exists p m;
  let x = IndefiniteDescription.indefinite_description_tot _ existsprop in
  x

let witinv_framon #a (p : a -> slprop)
  : Lemma (requires (is_witness_invariant p))
          (ensures (is_frame_monotonic p))
    =
    let aux x y h frame : Lemma (requires (interp (p x `star` frame) h /\ interp (p y) h))
                                (ensures (interp (p y `star` frame) h)) =
      assert (interp (p x `star` frame) h);
      let (hl, hr) = id_elim_star (p x) frame h in
      affine_star (p x) frame h;
      assert (interp (p x) h);
      assert (x == y);
      ()
    in
    Classical.forall_intro_4 (fun x y m frame -> Classical.move_requires (aux x y m) frame)

let witness_h_exists #a p =
  fun frame h0 ->
  let w = FStar.IndefiniteDescription.indefinite_description_tot
    a
    (fun x -> interp (p x `star` frame) h0) in
  (| w, h0 |)

let lift_h_exists (#a:_) (p:a -> slprop)
  : action (h_exists p) unit
           (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))
  = let g : refined_pre_action (h_exists p) unit (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))
          = fun h ->
              let aux (x:a) (h:heap)
                : Lemma
                  (requires interp (p x) h)
                  (ensures interp (h_exists (U.lift_dom p)) h)
                  [SMTPat (interp (p x) h)]
                = assert (interp (U.lift_dom p (U.raise_val x)) h)
              in
              (| (), h |)
    in
    refined_pre_action_as_action g

let elim_pure (p:prop)
  : action (pure p) (u:unit{p}) (fun _ -> emp)
  = let f
      : refined_pre_action (pure p) (_:unit{p}) (fun _ -> emp)
      = fun h -> (| (), h |)
    in
    refined_pre_action_as_action f

let pts_to_evolve (#a:Type u#a) (#pcm:_) (r:ref a pcm) (x y : a) (h:heap)
  : Lemma (requires (interp (pts_to r x) h /\ compatible pcm y x))
          (ensures  (interp (pts_to r y) h))
  = let Ref a' pcm' _ v' = (select_addr h (Addr?._0 r)) in
    compatible_trans pcm y x v'
