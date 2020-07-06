module Sec2.IFC
open FStar.Map
let loc = int
type store = m:Map.t loc int{forall l. contains m l}
let upd (s:store) (l:loc) (x:int) : store = Map.upd s l x
let sel (s:store) (l:loc) : int = Map.sel s l
open FStar.Set
let label = Set.set loc
let label_inclusion (l0 l1:label) = Set.subset l0 l1
let bot : label = Set.empty
let single (l:loc) : label = Set.singleton l
let union (l0 l1:label) = Set.union l0 l1
let is_empty #a (s:Set.set a) = forall (x:a). ~ (Set.mem x s)
let comp a = store -> a & store
let havoc s l x = upd s l x
let does_not_read_loc_v #a (f:comp a) (reads:label) (l:loc) (s0:store) v =
    let s0' = havoc s0 l v in
    let x1, s1 = f s0 in
    let x1', s1' = f s0' in
    x1 == x1' /\ //result does not depend on l
    (forall l'. l' <> l ==>                 //for every location l' not equal to l
           sel s1 l' == sel s1' l') /\ //its value in the two states is the same
    (sel s1 l == sel s1' l \/          //and l is itself may be written, in which case its value is the same in both final states
                                      //or its not, but then its values in the initial and final states are the same on both sides
    (sel s1 l == sel s0 l /\
     sel s1' l == sel s0' l))

let does_not_read_loc #a (f:comp a) (reads:label) (l:loc) (s0:store) =
  forall v.
    does_not_read_loc_v f reads l s0 v
let reads_ok #a (f:comp a) (reads:label) =
    (forall (l:loc) (s:store). ~(Set.mem l reads) ==> does_not_read_loc f reads l s)
let writes_ok #a (f:comp a) (writes:Set.set loc) =
    (forall (l:loc). ~(Set.mem l writes) ==>
               (forall (s0:store).
                 let x1, s0' = f s0 in
                 sel s0 l == sel s0' l))
let flow = label & label //from, to
let flows = list flow
let add_source (r:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> union r r0, w0) fs
let add_sink (w:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> r0, union w w0) fs
let has_flow_1 (from to:loc) (f:flow) = from `Set.mem` fst f /\ to `Set.mem` snd f
let has_flow (from to:loc) (fs:flows) = (exists rs. rs `List.Tot.memP` fs /\ has_flow_1 from to rs)
let flows_included_in (fs0 fs1:flows) =
  forall f0. f0 `List.Tot.memP` fs0 ==>
        (forall from to. has_flow_1 from to f0 ==> (exists f1. f1 `List.Tot.memP` fs1 /\ has_flow_1 from to f1))
let flows_equiv (fs0 fs1:flows) = fs0 `flows_included_in` fs1 /\ fs1 `flows_included_in` fs0
let flows_equiv_refl fs
  : Lemma (fs `flows_equiv` fs)
  = ()
let flows_equiv_trans fs0 fs1 fs2
  : Lemma (fs0 `flows_equiv` fs1 /\ fs1 `flows_equiv` fs2 ==> fs0 `flows_equiv` fs2)
  = ()
let flows_included_in_union_distr_dest (a b c:label)
  : Lemma (flows_equiv [a, union b c] [a, b; a, c])
  = ()
let flows_included_in_union_distr_src (a b c:label)
  : Lemma (flows_equiv [union a b, c] [a, c; b, c])
  = ()
let flows_included_in_union (a b c:label)
  : Lemma (flows_equiv ([a, union b c; union a b, c])
                       ([a, b; union a b, c]))
  = ()
let no_leakage_k #a (f:comp a) (from to:loc) (k:int) =
  forall s0.{:pattern (havoc s0 from k)} sel (snd (f s0)) to == (sel (snd (f (havoc s0 from k))) to)
let no_leakage #a (f:comp a) (from to:loc) = forall k. no_leakage_k f from to k
let respects_flows #a (f:comp a) (fs:flows) =
    (forall from to. {:pattern (no_leakage f from to)} ~(has_flow from to fs) /\ from<>to ==> no_leakage f from to)
let ist a (writes:label) (reads:label) (fs:flows) =
  f:(store -> (a * store)) {
    reads_ok f reads /\
    writes_ok f writes  /\
    respects_flows f fs
  }
let iread (l:loc) : ist int bot (single l) [] = fun s -> sel s l, s
let return (a:Type) (x:a) : ist a bot bot [] = fun s -> x,s
let iwrite (l:loc) (x:int) : ist unit (single l) bot [] = fun s -> (), upd s l x

let bind_comp (#a #b:Type)
              (#w0 #r0 #w1 #r1:label)
              (#fs0 #fs1:flows)
              (x:ist a w0 r0 fs0)
              (y: a -> ist b w1 r1 fs1)
  : comp b
  = fun s0 -> let v, s1 = x s0 in y v s1

let bind_comp_reads_ok (#a #b:Type)
                       (#w0 #r0 #w1 #r1:label)
                       (#fs0 #fs1:flows)
                       (x:ist a w0 r0 fs0)
                       (y: a -> ist b w1 r1 fs1)
  : Lemma (reads_ok (bind_comp x y) (union r0 r1))
  = let f = bind_comp x y in
    let reads = union r0 r1 in
    let f_reads_ok (l:loc) (s0:store)
      : Lemma (requires (~(Set.mem l reads)))
              (ensures (does_not_read_loc f reads l s0))
              [SMTPat (does_not_read_loc f reads l s0)]
      = let aux (k:_)
          : Lemma (ensures (does_not_read_loc_v f reads l s0 k))
                  [SMTPat (does_not_read_loc_v f reads l s0 k)]
          = let v, s1 = x s0 in
            let v', s1' = x (havoc s0 l k) in
            assert (does_not_read_loc x r0 l s0);
            assert (does_not_read_loc_v x r0 l s0 k);
            assert (v == v');
            assert (does_not_read_loc (y v) r1 l s1);
            let u, s2 = y v s1 in
            let u', s2' = y v s1' in
            assert (forall l'. l' <> l ==> sel s1 l' == sel s1' l');
            if sel s1 l = sel s1' l
            then (assert (forall l. sel s1 l == sel s1' l);
                 assert (Map.equal s1 s1'))
            else (assert (sel s1 l == sel s0 l /\
                         sel (havoc s0 l k) l == sel s1' l);
                  assert (Map.equal s1' (havoc s1 l k)))
       in
       ()
    in
    ()

let bind_comp_writes_ok (#a #b:Type)
                        (#w0 #r0 #w1 #r1:label)
                        (#fs0 #fs1:flows)
                        (x:ist a w0 r0 fs0)
                        (y: a -> ist b w1 r1 fs1)
  : Lemma (writes_ok (bind_comp x y) (union w0 w1))
  = ()

let rec memP_append_or (#a:Type) (x:a) (l0 l1:list a)
  : Lemma (ensures (List.Tot.memP x (l0 @ l1) <==>
                   (List.Tot.memP x l0 \/ List.Tot.memP x l1)))
          (decreases l0)
  = match l0 with
    | [] -> ()
    | _::tl -> memP_append_or x tl l1

let has_flow_append (from to:loc) (fs fs':flows)
  : Lemma (has_flow from to fs ==>
           has_flow from to (fs @ fs') /\
           has_flow from to (fs' @ fs))
  = let rec aux (rs:_)
      : Lemma (requires
                  List.Tot.memP rs fs)
              (ensures
                 List.Tot.memP rs (fs @ fs') /\
                 List.Tot.memP rs (fs' @ fs))
              [SMTPat (List.Tot.memP rs fs)]
      = memP_append_or rs fs fs';
        memP_append_or rs fs' fs
    in
    ()

let elim_has_flow_seq (from to:loc)
                      (r0 r1 w1:label)
                      (fs0 fs1:flows)
  : Lemma (requires (~(has_flow from to (fs0 @ add_source r0 ((bot, w1)::fs1)))))
          (ensures  (~(has_flow from to fs0) /\
                      (~(Set.mem from r0) \/ ~(Set.mem to w1)) /\
                     ~(has_flow from to (add_source r0 fs1))))
  = assert (add_source r0 ((bot, w1)::fs1) ==
            (Set.union r0 bot, w1)::add_source r0 fs1);
    assert (Set.union r0 bot `Set.equal` r0);
    has_flow_append from to fs0 ((r0, w1)::add_source r0 fs1);
    assert (~(has_flow from to fs0));
    has_flow_append from to ((r0, w1)::add_source r0 fs1) fs0;
    assert (~(has_flow from to (((r0, w1)::add_source r0 fs1))));
    assert ((r0, w1)::add_source r0 fs1 ==
            [r0, w1] @ add_source r0 fs1);
    has_flow_append from from [r0, w1] (add_source r0 fs1)

let rec add_source_monotonic (from to:loc) (r:label) (fs:flows)
  : Lemma (has_flow from to fs ==> has_flow from to (add_source r fs))
  = match fs with
    | [] -> ()
    | _::tl -> add_source_monotonic from to r tl

let has_flow_soundness #a #r #w #fs (f:ist a r w fs)
                       (from to:loc) (s:store) (k:int)
    : Lemma (requires
              (let x, s1 = f s in
               let _, s1' = f (havoc s from k) in
               from <> to /\
               sel s1 to <> sel s1' to))
            (ensures has_flow from to fs)
    = let aux ()
       : Lemma (requires (~(has_flow from to fs)))
               (ensures False)
               [SMTPat ()]
       = assert (respects_flows f fs);
         assert (no_leakage f from to)
      in
      ()

let bind_comp_no_leakage (#a #b:Type)
                         (#w0 #r0 #w1 #r1:label)
                         (#fs0 #fs1:flows)
                         (x:ist a w0 r0 fs0)
                         (y: a -> ist b w1 r1 fs1)
                         (from to:loc)
                         (s0:store) (k:_)
    : Lemma
      (requires from <> to /\ ~(has_flow from to (fs0 @ add_source r0 ((bot, w1)::fs1))))
      (ensures (let f = bind_comp x y in
                let s0' = havoc s0 from k in
                let _, s2 = f s0 in
                let _, s2' = f s0' in
                sel s2 to == sel s2' to))
    = let f = bind_comp x y in
      assert (reads_ok x r0);
      let s0' = havoc s0 from k in
      let _, s2f = f s0 in
      let _, s2f' = f s0' in
      let flows = (fs0 @ add_source r0 ((r1, w1)::fs1)) in
      let v0, s1 = x s0 in
      let v0', s1' = x s0' in
      elim_has_flow_seq from to r0 r1 w1 fs0 fs1;
      assert (~(has_flow from to fs0));
      assert (respects_flows x fs0);
      assert (no_leakage x from to);
      assert (sel s1 to == sel s1' to);
      let _, s2 = y v0 s1 in
      let _, s2' = y v0' s1' in
      assert (s2 == s2f);
      assert (s2' == s2f');
           //Given: (from not-in r0 U r1) \/ (to not-in w1)
           //suppose (from in r0) \/ (from in r1)
           //        them to not-in w1
           //suppose (from not-in r0 U r1)
           //then v0 = v0'
           //     s1' = havoc from s1 k
           //     s2 to = s2' to
      if Set.mem to w1
      then begin
        assert (~(Set.mem from r0));
        assert (reads_ok x r0);
        assert (does_not_read_loc x r0 from s0);
        assert (does_not_read_loc_v x r0 from s0 k);
        assert (v0 == v0');
        assert (forall l. l <> from ==> sel s1 l == sel s1' l);
        assert (Map.equal s1' (havoc s1 from k) \/ Map.equal s1' s1);
        if (sel s1 from = sel s1' from)
        then begin
          assert (Map.equal s1 s1')
          end
        else begin
          assert (Map.equal s1' (havoc s1 from k));
          assert (reads_ok (y v0) r1);
          if (sel s2 to = sel s2' to)
          then ()
          else begin
            assert (sel s2 to <> sel s1 to \/ sel s2' to <> sel s1' to);
            has_flow_soundness (y v0) from to s1 k;
            assert (has_flow from to fs1);
            add_source_monotonic from to r0 fs1
            //y reads from and writes to, so (from, to) should be in fs1
            //so, we should get a contradiction
          end
        end
      end
      else //to is not in w1, so y does not write it
        ()

let bind_comp_flows_ok (#a #b:Type)
                       (#w0 #r0 #w1 #r1:label)
                       (#fs0 #fs1:flows)
                       (x:ist a w0 r0 fs0)
                       (y: a -> ist b w1 r1 fs1)
  : Lemma (respects_flows (bind_comp x y) (fs0 @ add_source r0 ((bot, w1)::fs1)))
  = let f = bind_comp x y in
    let flows = (fs0 @ add_source r0 ((bot, w1)::fs1)) in
    let respects_flows_lemma (from to:loc)
      : Lemma (requires from <> to /\ ~(has_flow from to flows))
              (ensures no_leakage f from to)
              [SMTPat (no_leakage f from to)]
      = let aux (s0:store) (k:_)
         : Lemma (let s0' = havoc s0 from k in
                  let _, s2 = f s0 in
                  let _, s2' = f s0' in
                  sel s2 to == sel s2' to)
                 [SMTPat (havoc s0 from k)]
         = bind_comp_no_leakage x y from to s0 k
        in
        ()
    in
    ()

let triple = label & label & flows
let unit_triple = bot, bot, []
let comp_triple (w0, r0, fs0) (w1, r1, fs1) = (union w0 w1, union r0 r1, (fs0 @ add_source r0 ((bot, w1)::fs1)))

let label_equiv (s0 s1:label) = Set.equal s0 s1
let triple_equiv (w0, r0, f0) (w1, r1, f1) = label_equiv w0 w1 /\ label_equiv r0 r1 /\ flows_equiv f0 f1
let triple_equiv_refl t0
  : Lemma (triple_equiv t0 t0)
  = ()
let rec add_source_bot (f:flows)
    : Lemma (add_source bot f `flows_equiv` f)
    = match f with
      | [] -> ()
      | _::tl -> add_source_bot tl
let left_unit (w, r, f) =
  assert (Set.equal (union bot bot) bot);
  add_source_bot f;
  assert (comp_triple unit_triple (w, r, f) `triple_equiv` (w, r, f))
let flows_included_append (f0 f1 g0 g1:flows)
  : Lemma (requires flows_included_in f0 g0 /\
                    flows_included_in f1 g1)
          (ensures  flows_included_in (f0@f1) (g0@g1))
  = let aux (f:_) (from to:_)
    : Lemma (requires List.Tot.memP f (f0@f1) /\
                      has_flow_1 from to f)
            (ensures (exists g. g `List.Tot.memP` (g0@g1) /\ has_flow_1 from to g))
            [SMTPat (has_flow_1 from to f)]
    = memP_append_or f f0 f1;
      assert (exists g. g `List.Tot.memP` g0 \/ g `List.Tot.memP` g1 /\ has_flow_1 from to g);
      FStar.Classical.forall_intro (fun g -> memP_append_or g g0 g1)
    in
    ()
let flows_equiv_append (f0 f1 g0 g1:flows)
  : Lemma (requires flows_equiv f0 g0 /\ flows_equiv f1 g1)
          (ensures  flows_equiv (f0@f1) (g0@g1))
  = flows_included_append f0 f1 g0 g1;
    flows_included_append g0 g1 f0 f1
let rec append_nil_r #a (l:list a)
  : Lemma (l @ [] == l)
  = match l with
    | [] -> ()
    | _::tl -> append_nil_r tl
let right_unit (w, r, f) =
  calc (==) {
    comp_triple (w, r, f) unit_triple;
    (==) { }
    (w `union` bot, r `union` bot, f @ add_source r ((bot, bot)::[]));
  };
  assert (flows_equiv (add_source r [(bot, bot)]) []);
  flows_equiv_append f (add_source r [(bot, bot)]) f [];
  append_nil_r f;
  assert (comp_triple (w, r, f) unit_triple  `triple_equiv` (w, r, f))
open FStar.Calc
let assoc_comp (w0, r0, fs0) (w1, r1, fs1) (w2, r2, fs2) =
  calc (==) {
    comp_triple (w0, r0, fs0) (comp_triple (w1, r1, fs1) (w2, r2, fs2)) ;
    (==) { }
    comp_triple (w0, r0, fs0) (union w1 w2, union r1 r2, (fs1 @ add_source r1 ((bot, w2)::fs2)));
    (==) { }
    (union w0 (union w1 w2), union r0 (union r1 r2), fs0 @ (add_source r0 ((bot, union w1 w2) :: (fs1 @ add_source r1 ((bot, w2)::fs2)))));
    (==) { assert (forall w0 w1 w2. Set.equal (union w0 (union w1 w2)) (union (union w0 w1) w2)) }
    (union (union w0 w1) w2,
     union (union r0 r1) r2,
     fs0 @ (add_source r0 ((bot, union w1 w2) :: (fs1 @ add_source r1 ((bot, w2)::fs2)))));
    (==) { }
    (union (union w0 w1) w2,
     union (union r0 r1) r2,
     (fs0 @ ((union r0 bot, union w1 w2) :: add_source r0 (fs1 @ add_source r1 ((bot, w2)::fs2)))));
    (==) { assert (forall s. Set.equal (union s bot) s) }
    (union (union w0 w1) w2,
     union (union r0 r1) r2,
     (fs0 @ ((r0, union w1 w2) :: add_source r0 (fs1 @ (r1, w2) ::add_source r1 fs2))));
  };
  calc (==) {
    comp_triple (comp_triple (w0, r0, fs0) (w1, r1, fs1)) (w2, r2, fs2);
    (==) { }
    comp_triple (union w0 w1, union r0 r1, (fs0 @ add_source r0 ((bot, w1)::fs1))) (w2, r2, fs2);
    (==) { }
    (union (union w0 w1) w2,
     union (union r0 r1) r2,
    ((fs0 @ add_source r0 ((bot, w1)::fs1)) @ (add_source (union r0 r1) ((bot, w2) :: fs2))));
    (==) { }
    (union (union w0 w1) w2,
     union (union r0 r1) r2,
     ((fs0 @ ((union r0 bot, w1)::add_source r0 fs1)) @ ((union (union r0 r1) bot, w2) :: add_source (union r0 r1) fs2)));
    (==) { assert (forall s. Set.equal (union s bot) s) }
    (union (union w0 w1) w2,
     union (union r0 r1) r2,
     ((fs0 @ ((r0, w1)::add_source r0 fs1)) @ ((union r0 r1, w2) :: add_source (union r0 r1) fs2)));
  }

let bind (a b:Type)
         (w0 r0 w1 r1:label) (fs0 fs1:flows)
         (x:ist a w0 r0 fs0)
         (y: a -> ist b w1 r1 fs1)
  : ist b (union w0 w1) (union r0 r1) (fs0 @ add_source r0 ((bot, w1)::fs1))
  = let f = fun s0 -> let v, s1 = x s0 in y v s1 in
    bind_comp_reads_ok x y;
    bind_comp_reads_ok x y;
    bind_comp_flows_ok x y;
    f

let subcomp (a:Type) (w0 r0 w1 r1:label) (fs0 fs1:flows) (f:ist a w0 r0 fs0)
  : Pure (ist a w1 r1 fs1)
    (requires label_inclusion w0 w1 /\
              label_inclusion r0 r1 /\
              fs0 `flows_included_in` fs1)
    (fun _ -> True)
  = let f_reads_ok (l:loc) (s0:store)
      : Lemma (requires (~(Set.mem l r1)))
              (ensures (does_not_read_loc f r1 l s0))
              [SMTPat (does_not_read_loc f r1 l s0)]
      = let aux (k :_)
          : Lemma (ensures (does_not_read_loc_v f r1 l s0 k))
                  [SMTPat  (does_not_read_loc_v f r1 l s0 k)]
          = let v, s1 = f s0 in
            let v', s1' = f (havoc s0 l k) in
            assert (does_not_read_loc f r0 l s0);
            assert (v == v');
            assert (not (Set.mem l w0) ==> sel s1' l = k);
            assert (not (Set.mem l w1) ==> sel s1' l = k);
            ()
        in
        ()
    in
    f

reflectable
layered_effect {
  IST : a:Type ->
        w:label ->
        w:label ->
        fs:flows ->
        Effect
  with
    repr = ist;
    return = return;
    bind = bind;
    subcomp = subcomp
}
let read (l:loc) : IST int bot (single l) [] = IST?.reflect (iread l)
let write (l:loc) (x:int) : IST unit (single l) bot [] = IST?.reflect (iwrite l x)

let u : Type = unit
let lift_pure (a:Type) (x:u -> Tot a)
  : ist a bot bot []
  = return a (x())

sub_effect PURE ~> IST = lift_pure

let ref (l:label) = r:loc {r `Set.mem` l}
assume val high : label
let low : label = Set.complement high
let lref = ref low
let href = ref high


let test (l:lref) (h:href)
  : IST unit (union bot (single h))
             (union (single l) bot)
             (add_source (single l) [bot, single h])
  = let x = read l in
    write h x

let test2 (l:lref) (h:href)
  : IST unit (single h)
             (single l)
             [single l, single h]
  = let x = read l in
    write h x

let test3 (l:lref) (h:href)
  : IST unit (single h)
             (single l)
             [single l, single h]
  = write h (read l)

let test3_lab (l:lref) (h:href)
  : IST unit high low [low, high]
  = write h (read l)


let test3_1 (l:lref) (h:href) (x:int)
  : IST int (single h)
          (single l)
          []
  = write h 0;
    read l

let test4 (l:lref) (h:href) (x:int)
  : IST int (single l)
          (single h)
          [single h, bot]
  = write l x;
    read h

let test5 (l:lref) (h:href) (x:int)
  : IST int (single l)
          (single h)
          []
  = write l x;
    read h

let test6 (l:lref) (h:href)
  : IST unit high low [low, high]
  = let x = read l in
    write h x

//This leaks the contents of the href
let test7 (l:lref) (h:href)
  : IST unit (single l)
             (single h)
             [high, low]
  = let x = read h in
    write l x

//But, label-based IFC is inherently imprecise
//This one still reports a leakage, even though it doesn't really leak h
let test8 (l:lref) (h:href)
  : IST unit (single l)
             (union (single h) (single l))
             [(single l `union` single h, single l)]
  = let x0 = read h in
    let x = read l in
    write l x

//But, label-based IFC is inherently imprecise
//This one still reports a leakage, even though it doesn't really leak h
let test9 (l:lref) (h:href)
  : IST unit (single l)
             (union (single h) (single l))
             [(single l `union` single h, single l)]
  = let x= (let x0 = read h in
            read l)
    in
    write l x

assume
val cw0 : label
assume
val cr0 : label
assume
val c0 (_:unit) : IST unit cw0 cr0 []


assume
val cw1 : label
assume
val cr1 : label
assume
val c1 (_:unit) : IST unit cw1 cr1 []

assume
val cw2 : label
assume
val cr2 : label
assume
val c2 (_:unit) : IST unit cw2 cr2 []

let test10 ()
  : IST unit (union cw0 (union cw1 cw2))
             (union cr0 (union cr1 cr2))
             (add_source cr0
               ((bot, union cw1 cw2)::
                (add_source cr1 [bot, cw2])))
  = c0 (); (c1();c2())


let test12 ()
  : IST unit (union cw0 (union cw1 cw2))
             (union cr0 (union cr1 cr2))
             [(cr0, union cw1 cw2);
              (union cr0 cr1, cw2)]
  = c0 (); (c1();c2())

let test12_1 ()
  : IST unit (union cw0 (union cw1 cw2))
             (union cr0 (union cr1 cr2))
             [(cr0, cw1);
              (union cr0 cr1, cw2)]
  = c0 (); (c1();c2())


let test13 ()
  : IST unit (union (union cw0 cw1) cw2)
             (union (union cr0 cr1) cr2)
             (add_source cr0 [bot, cw1] @
              add_source (union cr0 cr1) [bot, cw2])
  = (c0 (); c1());c2()

let test14 ()
  : IST unit (union (union cw0 cw1) cw2)
             (union (union cr0 cr1) cr2)
             ([cr0, cw1;
               union cr0 cr1, cw2])
  = (c0 (); c1()); c2()
