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
module Steel.PCM.Memory
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open Steel.PCM

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell : Type u#(a + 1) =
  | Ref : a:Type u#a ->
          p:pcm a ->
          v:a ->
          squash (defined p v) ->
          cell

let addr = nat

/// This is just the core of a memory, about which one can write
/// assertions. At one level above, we'll encapsulate this memory
/// with a freshness counter, a lock store etc.
let heap : Type u#(a + 1) = addr ^-> option (cell u#a)

let contains_addr (m:heap) (a:addr)
  : bool
  = Some? (m a)

let select_addr (m:heap) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

let update_addr (m:heap) (a:addr) (c:cell)
  : heap
  = F.on _ (fun a' -> if a = a' then Some c else m a')

let combinable_sym (#a:Type) (pcm:pcm a) (x y: a)
  : Lemma (combinable pcm x y ==>
           combinable pcm y x)
  = pcm.comm x y

let disjoint_cells (c0 c1:cell u#h) : prop =
    let Ref t0 p0 v0 _ = c0 in
    let Ref t1 p1 v1 _ = c1 in
    t0 == t1 /\
    p0 == p1 /\
    combinable p0 v0 v1

let disjoint_cells_sym (c0 c1:cell u#h)
  : Lemma (requires disjoint_cells c0 c1)
          (ensures disjoint_cells c1 c0)
  = let Ref t0 p0 v0 _ = c0 in
    let Ref t1 p1 v1 _ = c1 in
    p0.comm v0 v1

let disjoint_addr (m0 m1:heap u#h) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some c0, Some c1 ->
      disjoint_cells c0 c1
    | Some _, None
    | None, Some _
    | None, None ->
      True

let ref (a:Type u#a) (pcm:pcm a): Type u#0 = addr

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
  let Ref a0 p0 v0 _ = c0 in
  let Ref a1 p1 v1 _ = c1 in
  Ref a0 p0 (p0.op v0 v1) ()

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
  = let Ref a0 p0 v0 _ = c0 in
    let Ref a1 p1 v1 _ = c1 in
    let Ref a2 p2 v2 _ = c2 in
    assert (p0 == p1 /\ p1 == p2);
    assert (p0.op v1 v2 =!= p0.undef);
    assert (p0.op v0 (p0.op v1 v2) =!= p0.undef);
    p0.undef_inv v1 v2;
    p0.undef_inv v0 (p0.op v1 v2);
    p0.undef_inv (p0.op v0 v1) v2;
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
  = let Ref a0 p0 v0 _ = c0 in
    let Ref a1 p1 v1 _ = c1 in
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

let heap_prop_is_affine (p:heap -> prop) =
  forall m0 m1. p m0 /\ disjoint m0 m1 ==> p (join m0 m1)
let a_heap_prop : Type u#(a + 1) =
  p:(heap u#a -> prop) { heap_prop_is_affine p }

////////////////////////////////////////////////////////////////////////////////

module W = FStar.WellFounded

[@erasable]
noeq
type slprop : Type u#(a + 1) =
  | Emp : slprop
  | Pts_to : #a:Type u#a -> #pcm:pcm a -> r:ref a pcm -> v:a -> slprop
  | Refine : slprop u#a -> a_heap_prop u#a -> slprop
  | And    : slprop u#a -> slprop u#a -> slprop
  | Or     : slprop u#a -> slprop u#a -> slprop
  | Star   : slprop u#a -> slprop u#a -> slprop
  | Wand   : slprop u#a -> slprop u#a -> slprop
  | Ex     : #a:Type u#a -> (a -> slprop u#a) -> slprop
  | All    : #a:Type u#a -> (a -> slprop u#a) -> slprop

let interp_cell (p:slprop u#a) (c:cell u#a) =
  let Ref a' pcm' v' _ = c in
  match p with
  | Pts_to #a #pcm r v ->
    a == a' /\
    pcm == pcm' /\
    compatible pcm v v'
  | _ -> False

let rec interp (p:slprop u#a) (m:heap u#a)
  : Tot prop (decreases p)
  = match p with
    | Emp -> True
    | Pts_to #a #pcm r v ->
      m `contains_addr` r /\
      interp_cell p (select_addr m r)

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

let emp : slprop u#a = Emp
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

let equiv_symmetric (p1 p2:slprop u#a) = ()
let equiv_extensional_on_star (p1 p2 p3:slprop u#a) = ()

////////////////////////////////////////////////////////////////////////////////
//pts_to
////////////////////////////////////////////////////////////////////////////////

let intro_pts_to (#a:_) (#pcm:pcm a) (x:ref a pcm) (v:a) (m:heap)
  : Lemma
    (requires
       m `contains_addr` x /\
       (let Ref a' pcm' v' _ = select_addr m x in
        a == a' /\
        pcm == pcm' /\
        compatible pcm v v'))
     (ensures
       interp (pts_to x v) m)
  = ()

let pts_to_compatible (#a:Type u#a)
                      (#pcm:_)
                      (x:ref a pcm)
                      (v0 v1:a)
                      (m:heap u#a)
  : Lemma
    (requires
      interp (pts_to x v0 `star` pts_to x v1) m)
    (ensures
      combinable pcm v0 v1 /\
      interp (pts_to x (pcm.op v0 v1)) m)
  = let c = select_addr m x in
    let Ref _ _ v _ = select_addr m x in
    let aux (c0 c1: cell u#a)
      : Lemma
        (requires
           c0 `disjoint_cells` c1 /\
           interp_cell (pts_to x v0) c0 /\
           interp_cell (pts_to x v1) c1 /\
           c == join_cells c0 c1 )
        (ensures
           combinable pcm v0 v1 /\
           interp (pts_to x (pcm.op v0 v1)) m)
        [SMTPat (c0 `disjoint_cells` c1)]
      = let Ref _ _ v0' _ = c0 in
        let Ref _ _ v1' _ = c1 in
        assert (exists frame. pcm.op frame v0 == v0');
        assert (exists frame. pcm.op frame v1 == v1');
        assert (pcm.op v0' v1' == v);
        assert (v =!= pcm.undef);
        let aux (frame0 frame1:a)
          : Lemma
            (requires
              pcm.op frame0 v0 == v0' /\
              pcm.op frame1 v1 == v1' /\
              pcm.op v0' v1' == v)
            (ensures (
              let frame = pcm.op frame0 frame1 in
              pcm.op frame (pcm.op v0 v1) == v /\
              pcm.op v0 v1 =!= pcm.undef))
            [SMTPat(pcm.op frame0 v0);
             SMTPat(pcm.op frame1 v1)]
          = assert (pcm.op (pcm.op frame0 v0) (pcm.op frame1 v1) == v);
            pcm.assoc frame0 v0 (pcm.op frame1 v1);
            assert (pcm.op frame0 (pcm.op v0 (pcm.op frame1 v1)) == v);
            pcm.comm frame1 v1;
            assert (pcm.op frame0 (pcm.op v0 (pcm.op v1 frame1)) == v);
            pcm.assoc v0 v1 frame1;
            assert (pcm.op frame0 (pcm.op (pcm.op v0 v1) frame1) == v);
            pcm.comm (pcm.op v0 v1) frame1;
            pcm.assoc frame0 frame1 (pcm.op v0 v1);
            pcm.undef_inv (pcm.op frame0 frame1) (pcm.op v0 v1)
        in
        ()
    in
    assert (exists c0 c1.
              c0 `disjoint_cells` c1 /\
              interp_cell (pts_to x v0) c0 /\
              interp_cell (pts_to x v1) c1 /\
              c == join_cells c0 c1)

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
// sel
////////////////////////////////////////////////////////////////////////////////
let sel #a #pcm (r:ref a pcm) (m:hheap (ptr r))
  : a
  = let Ref _ _ v _ = select_addr m r in
    v

let sel_lemma (#a:_) (#pcm:_) (r:ref a pcm) (m:hheap (ptr r))
  : Lemma (interp (pts_to r (sel r m)) m)
  = let Ref _ _ v _ = select_addr m r in
    assert (sel r m == v);
    assert (defined pcm v);
    compatible_refl pcm v

let sel_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:erased a)
  : action (pts_to r v0) (v:a{compatible pcm v0 v}) (fun _ -> pts_to r v0)
  = let f
      : pre_action (pts_to r v0)
                   (v:a{compatible pcm v0 v})
                   (fun _ -> pts_to r v0)
      = fun m0 -> (| sel r m0, m0 |)
    in
    f


let update_defined #a pcm (v0:a{defined pcm v0}) (v1:a{frame_preserving pcm v0 v1})
  : Lemma (defined pcm v1)
  = pcm.is_unit v0; pcm.is_unit v1;
    assert (defined pcm (pcm.op v0 pcm.one));
    pcm.comm v0 pcm.one;
    pcm.comm v1 pcm.one;
    assert (defined pcm v1)

let upd' (#a:_) (#pcm:_) (r:ref a pcm) (v0:FStar.Ghost.erased a) (v1:a {frame_preserving pcm v0 v1})
  : pre_action (pts_to r v0) unit (fun _ -> pts_to r v1)
  = fun h ->
    update_defined pcm v0 v1;
    let cell = Ref a pcm v1 () in
    let h' = update_addr h r cell in
    assert (h' `contains_addr` r);
    compatible_refl pcm v1;
    assert (interp_cell (pts_to r v1) cell);
    assert (interp (pts_to r v1) h');
    (| (), h' |)


let definedness #a #pcm (v0:a{defined pcm v0}) (v0_val:a{defined pcm v0_val}) (v1:a{defined pcm v1}) (vf:a{defined pcm vf})
  : Lemma (requires
             compatible pcm v0 v0_val /\
             combinable pcm v0_val vf /\
             frame_preserving pcm v0 v1)
          (ensures
             combinable pcm vf v1 /\
             combinable pcm v1 vf)
  = assert (exists vf'. pcm.op vf' v0 == v0_val);
    let aux (vf':a {pcm.op vf' v0 == v0_val})
      : Lemma (combinable pcm vf v1 /\
               combinable pcm v1 vf)
              [SMTPat(pcm.op vf' v0)]
        = pcm.undef_inv vf' v0;
          assert (defined pcm vf');
          assert (combinable pcm (pcm.op vf' v0) vf);
          pcm.comm (pcm.op vf' v0) vf;
          pcm.assoc vf vf' v0;
          pcm.comm (pcm.op vf vf') v0;
          assert (combinable pcm v0 (pcm.op vf vf'));
          pcm.comm v0 (pcm.op vf vf');
          assert (combinable pcm (pcm.op vf vf') v1);
          pcm.comm (pcm.op vf vf') v1;
          pcm.assoc v1 vf vf';
          assert (combinable pcm (pcm.op v1 vf) vf');
          pcm.undef_inv v1 vf;
          pcm.undef_inv (pcm.op v1 vf) vf';
          assert (combinable pcm v1 vf);
          pcm.comm v1 vf;
          assert (combinable pcm vf v1)
    in
    ()

let combinable_compatible #a pcm (x y z:a)
  : Lemma (requires compatible pcm x y /\
                    combinable pcm y z)
          (ensures combinable pcm x z /\
                   combinable pcm z x)
  = let aux (f:a{pcm.op f x == y})
      : Lemma (combinable pcm x z /\
               combinable pcm z x)
              [SMTPat (pcm.op f x)]
      = assert (combinable pcm (pcm.op f x) z);
        pcm.assoc f x z;
        assert (combinable pcm f (pcm.op x z));
        pcm.undef_inv f (pcm.op x z);
        pcm.comm x z
    in
    let s : squash (exists f. pcm.op f x == y) = () in
    ()

let pts_to_defined #a #pcm (r:ref a pcm) (v:a) (m:hheap (pts_to r v))
  : Lemma (defined pcm v)
  = ()

#push-options "--z3rlimit_factor 2"
let upd_lemma' (#a:_) #pcm (r:ref a pcm)
               (v0:Ghost.erased a) (v1:a {frame_preserving pcm v0 v1})
               (h:hheap (pts_to r v0)) (frame:slprop)
  : Lemma
    (requires
      interp (pts_to r v0 `star` frame) h)
    (ensures (
      (let (| x, h1 |) = upd' r v0 v1 h in
       interp (pts_to r v1 `star` frame) h1)))
  = assert (defined pcm v0); update_defined pcm v0 v1;
    let aux (h0 hf:heap)
     : Lemma
       (requires
         disjoint h0 hf /\
         h == join h0 hf /\
         interp (pts_to r v0) h0 /\
         interp frame hf)
       (ensures (
         let (| _, h' |) = upd' r v0 v1 h in
         let h0' = update_addr h0 r (Ref a pcm v1 ()) in
         disjoint h0' hf /\
         interp (pts_to r v1) h0' /\
         interp frame hf /\
         h' == join h0' hf))
       [SMTPat (disjoint h0 hf)]
     = let (| _, h'|) = upd' r v0 v1 h in
       let cell1 = (Ref a pcm v1 ()) in
       let h0' = update_addr h0 r cell1 in
       assert (interp (pts_to r v1) h0');
       assert (interp frame hf);
       let aux (a:addr)
         : Lemma (disjoint_addr h0' hf a )
                 [SMTPat (disjoint_addr h0' hf a)]
         = if a <> r then ()
           else match h0 a, h0' a, hf a with
                | Some (Ref a0 p0 v0_val _),
                  Some (Ref a0' p0' v0' _),
                  Some (Ref af pf vf _) ->
                  assert (a0' == af);
                  assert (p0' == pf);
                  assert (v0' == v1);
                  assert (compatible pcm v0 v0_val);

                  compatible_refl pcm vf;
                  assert (interp_cell (pts_to r vf) (Some?.v (hf a)));
                  assert (interp (pts_to r vf) hf);

                  compatible_refl pcm v0_val;
                  assert (interp_cell (pts_to r v0_val) (Some?.v (h0 a)));
                  assert (interp (pts_to r v0_val) h0);
                  assert (interp (pts_to r v0_val `star` pts_to r vf) h);
                  pts_to_compatible r v0_val vf h;
                  assert (combinable pcm v0_val vf);

                  assert (interp (pts_to r (pcm.op v0_val vf)) h);
                  pcm.comm v0_val vf;
                  assert (defined pcm (pcm.op vf v0_val));
                  definedness #_ #pcm v0 v0_val v1 vf;
                  assert (combinable pcm v1 vf)
                | _ -> ()
       in
       assert (disjoint h0' hf);
       let aux (a:addr)
         : Lemma (h' a == (join h0' hf) a)
                 [SMTPat ()]
         = if a <> r
           then ()
           else begin
             assert (h' a == Some cell1);
             assert (h0' a == Some cell1);
             match h0 a, hf a with
             | _, None -> ()
             | Some (Ref a0 p0 v0_val _),
               Some (Ref af pf vf _) ->
               let c0 = Some?.v (h0 a) in
               let cf = Some?.v (hf a) in
               assert (a0 == af);
               assert (p0 == pf);
               assert (compatible pcm v0 v0_val);
               assert (disjoint_cells c0 cf);
               assert (combinable pcm v0_val vf);
               combinable_compatible pcm v0 v0_val vf;
               assert (combinable pcm v0 vf);
               assert (disjoint_cells cell1 cf);
               assert (combinable pcm v1 vf);
               assert (combinable pcm vf v0);
               assert (pcm.op vf v1 == v1);
               pcm.comm vf v1
           end
       in
       assert (mem_equiv h' (join h0' hf))
   in
   ()
#pop-options

let upd_action (#a:_) (#pcm:_) (r:ref a pcm) (v0:FStar.Ghost.erased a) (v1:a {frame_preserving pcm v0 v1})
  : action (pts_to r v0) unit (fun _ -> pts_to r v1)
  = let aux (h:hheap (pts_to r v0)) (frame:slprop)
    : Lemma
      (requires
        interp (pts_to r v0 `star` frame) h)
      (ensures (
        (let (| x, h1 |) = upd' r v0 v1 h in
        interp (pts_to r v1 `star` frame) h1)))
      [SMTPat ( interp (pts_to r v0 `star` frame) h)]
    = upd_lemma' r v0 v1 h frame
    in
    upd' r v0 v1
