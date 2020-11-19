module Sec2.IFCHoare
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
let pre = store -> Type0
let post a = store -> a -> store -> Type0
let comp a (p:pre) (q:post a) = s0:store{p s0} -> r:(a & store){q s0 (fst r) (snd r)}
let havoc s l x = upd s l x
let does_not_read_loc_v #a #p #q (f:comp a p q) 
                        (reads:label) 
                        (l:loc) 
                        (s0:store{p s0})
                        v =
    let s0' = havoc s0 l v in
    p s0' ==>
   (let x1, s1 = f s0 in
    let x1', s1' = f s0' in
    x1 == x1' /\ //result does not depend on l
    (forall l'. l' <> l ==>                 //for every location l' not equal to l
           sel s1 l' == sel s1' l') /\ //its value in the two states is the same
    (sel s1 l == sel s1' l \/          //and l is itself may be written, in which case its value is the same in both final states
                                      //or its not, but then its values in the initial and final states are the same on both sides
    (sel s1 l == sel s0 l /\
     sel s1' l == sel s0' l)))

let does_not_read_loc #a #p #q (f:comp a p q) (reads:label) (l:loc) (s0:store{p s0}) =
  forall v. does_not_read_loc_v f reads l s0 v
let agree_on (reads:label) (s0 s1: store) = forall l. Set.mem l reads ==> sel s0 l == sel s1 l
let related_runs #a #p #q (f:comp a p q) (s0:store{p s0}) (s0':store{p s0'}) =
      (let x1, s1 = f s0 in
       let x1', s1' = f s0' in
       x1 == x1' /\
       (forall (l:loc). (sel s1 l == sel s1' l \/ (sel s1 l == sel s0 l /\ sel s1' l == sel s0' l))))
let reads_ok #a #p #q (f:comp a p q) (reads:label) =
    forall (s0:store{p s0}) (s0':store{p s0'}). agree_on reads s0 s0' ==> related_runs f s0 s0'
let reads_ok_preserves_equal_locs #a #p #q (f:comp a p q) (reads:label) (s0:store{p s0}) (s0':store{p s0'})
  : Lemma (requires agree_on reads s0 s0' /\ reads_ok f reads)
          (ensures (let x1, s1 = f s0 in
                    let x1', s1' = f s0' in
                    agree_on reads s1 s1'))
  = ()      

let weaken_reads_ok #a #p #q (f:comp a p q) (reads reads1:label)
  : Lemma (requires reads_ok f reads /\
                    label_inclusion reads reads1)
          (ensures reads_ok f reads1)
  = let aux s0 s0'
    : Lemma (requires p s0 /\ p s0' /\ agree_on reads1 s0 s0')
            (ensures agree_on reads s0 s0')
            [SMTPat(agree_on reads1 s0 s0')]
    = ()
    in
    ()
let reads_ok_does_not_read_loc #a #p #q (f:comp a p q) (reads:label) (l:loc{~(Set.mem l reads)}) (s0:store{p s0})
  : Lemma 
    (requires reads_ok f reads)
    (ensures does_not_read_loc f reads l s0)
  = let aux (v:int)
      : Lemma (requires p (havoc s0 l v))
              (ensures does_not_read_loc_v f reads l s0 v)
              [SMTPat ()]
      = assert (agree_on reads s0 (havoc s0 l v));
        ()
    in
    ()
let writes_ok #a #p #q (f:comp a p q) (writes:Set.set loc) =
    (forall (l:loc). ~(Set.mem l writes) ==>
               (forall (s0:store{p s0}).
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
        (forall from to. has_flow_1 from to f0 /\ from <> to ==> (exists f1. f1 `List.Tot.memP` fs1 /\ has_flow_1 from to f1))
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
let no_leakage_k #a #p #q (f:comp a p q) (from to:loc) (k:int) =
  forall (s0:store{p s0}).{:pattern (havoc s0 from k)} 
    p (havoc s0 from k) ==>
    sel (snd (f s0)) to == (sel (snd (f (havoc s0 from k))) to)
let no_leakage #a #p #q (f:comp a p q) (from to:loc) = forall k. no_leakage_k f from to k
let respects_flows #a #p #q (f:comp a p q) (fs:flows) =
    (forall from to. {:pattern (no_leakage f from to)} ~(has_flow from to fs) /\ from<>to ==> no_leakage f from to)
let ist a (writes:label) (reads:label) (fs:flows) (p:pre) (q:store -> a -> store -> Type0) =
  f:comp a p q {
    reads_ok f reads /\
    writes_ok f writes  /\
    respects_flows f fs
  }
let iread (l:loc) : ist int bot (single l) [] (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == sel s0 l) = 
  let f : comp int (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == sel s0 l) = fun s -> sel s l, s in
  f
let return (a:Type) (x:a) : ist a bot bot [] (fun _ -> True) (fun s0 r s1 -> s0 == s1 /\ r == x) = 
  let f : comp a (fun _ -> True) (fun s0 r s1 -> s0 == s1 /\ r == x) = fun s -> x,s in
  f
let iwrite (l:loc) (x:int) : ist unit (single l) bot [] (fun _ -> True) (fun s0 _ s1 -> s1 == upd s0 l x) = 
  let f : comp unit (fun _ -> True) (fun s0 _ s1 -> s1 == upd s0 l x) = fun s -> (), upd s l x in
  f
let bind_comp (#a #b:Type)
              (#w0 #r0 #w1 #r1:label)
              (#fs0 #fs1:flows)
              #p #q #r #s
              (x:ist a w0 r0 fs0 p q)
              (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
  : comp b (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1))
           (fun s0 r s2 -> (exists x s1. q s0 x s1 /\ s x s1 r s2)) 
  = fun s0 -> let v, s1 = x s0 in y v s1


let bind_comp_reads_ok (#a #b:Type)
                       (#w0 #r0 #w1 #r1:label)
                       (#fs0 #fs1:flows)
                       #p #q #r #s
                       (x:ist a w0 r0 fs0 p q)
                       (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
  : Lemma (reads_ok (bind_comp x y) (union r0 r1))
  = let f = bind_comp x y in
    let p_f = (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1)) in
    let reads = union r0 r1 in
    let f_reads_ok (s0:store{p_f s0}) (s0':store{p_f s0'})
      : Lemma 
        (requires agree_on reads s0 s0')
        (ensures  related_runs f s0 s0')
        [SMTPat()]
      = let y1, s1 = x s0 in
        let y1', s1' = x s0' in      
        weaken_reads_ok x r0 reads;
        assert (related_runs x s0 s0');
        weaken_reads_ok (y y1) r1 reads;
        reads_ok_preserves_equal_locs x reads s0 s0';
        assert (forall l. l `Set.mem` r1 ==> sel s1 l == sel s1' l);        
        assert (agree_on r1 s1 s1');
        assert (y1 == y1');
        let res, s2 = y y1 s1 in
        let res', s2' = y y1 s1' in
        assert (res == res')
    in
    ()

let bind_comp_writes_ok (#a #b:Type)
                        (#w0 #r0 #w1 #r1:label)
                        (#fs0 #fs1:flows)
                        #p #q #r #s
                        (x:ist a w0 r0 fs0 p q)
                        (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
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

let has_flow_soundness #a #r #w #fs #p #q (f:ist a r w fs p q)
                       (from to:loc) (s:store{p s}) (k:int{p (havoc s from k)})
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
                         #p #q #r #s
                         (x:ist a w0 r0 fs0 p q)
                         (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
                         (from to:loc)
                         (s0:store) (k:_)
    : Lemma
      (requires (
        let p_f = (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1)) in
        let s0' = havoc s0 from k in
        p_f s0 /\
        p_f s0' /\
        from <> to /\ 
        ~(has_flow from to (fs0 @ add_source r0 ((bot, w1)::fs1)))))
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
        reads_ok_does_not_read_loc x r0 from s0;
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
                       #p #q #r #s
                       (x:ist a w0 r0 fs0 p q)
                       (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
  : Lemma (respects_flows (bind_comp x y) (fs0 @ add_source r0 ((bot, w1)::fs1)))
  = let f = bind_comp x y in
    let p_f = (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1)) in
    let flows = (fs0 @ add_source r0 ((bot, w1)::fs1)) in
    let respects_flows_lemma (from to:loc)
      : Lemma (requires from <> to /\ ~(has_flow from to flows))
              (ensures no_leakage f from to)
              [SMTPat (no_leakage f from to)]
      = let aux (s0:store{p_f s0}) (k:_{p_f (havoc s0 from k)})
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
                      from <> to /\
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


let modifies (w:label) (s0 s1:store) = (forall l.{:pattern (sel s1 l)} ~(Set.mem l w) ==> sel s0 l == sel s1 l)
let frame (a:Type) (w r:label) (fs:flows) #p #q (f:ist a w r fs p q)
  : ist a w r fs p (fun s0 x s1 -> q s0 x s1 /\ modifies w s0 s1)
  = let aux (s0:store{p s0}) (l:loc{~(Set.mem l w)})
      : Lemma (let x, s1 = f s0 in
               sel s0 l == sel s1 l)
               [SMTPat()]
               
      = ()
    in
    let g : comp a p (fun s0 x s1 -> q s0 x s1 /\ modifies w s0 s1) = fun s0 -> f s0 in
    assert (reads_ok f r);
    let read_ok_lem (l:loc) (s:store{p s})
      : Lemma (requires (~(Set.mem l r)))
              (ensures (does_not_read_loc g r l s))
              [SMTPat()]
      = reads_ok_does_not_read_loc g r l s;
        assert (does_not_read_loc f r l s)
    in
    assert (reads_ok g r);    
    assert (writes_ok g w);   
    let respects_flows_lemma (from to:_)
      : Lemma 
        (requires ~(has_flow from to fs) /\ from<>to)
        (ensures (no_leakage g from to))
        [SMTPat(no_leakage g from to)]
      = assert (no_leakage f from to)
    in
    assert (respects_flows g fs);
    g

let pre_bind (a b:Type)
         (w0 r0 w1 r1:label) (fs0 fs1:flows)
         #p #q #r #s
         (x:ist a w0 r0 fs0 p q)
         (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
  : ist b (union w0 w1) (union r0 r1) (fs0 @ add_source r0 ((bot, w1)::fs1))
          (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1))
          (fun s0 r s2 -> (exists x s1. q s0 x s1 /\ s x s1 r s2))
  = let f = bind_comp x y in
    bind_comp_reads_ok x y;
    bind_comp_writes_ok x y;    
    bind_comp_flows_ok x y;
    f

let bind (a b:Type)
         (w0 r0 w1 r1:label) (fs0 fs1:flows)
         #p #q #r #s
         (x:ist a w0 r0 fs0 p q)
         (y: (x:a -> ist b w1 r1 fs1 (r x) (s x)))
  : ist b (union w0 w1) (union r0 r1) (fs0 @ add_source r0 ((bot, w1)::fs1))
          (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 /\ modifies w0 s0 s1 ==> r x s1))
          (fun s0 r s2 -> (exists x s1. (q s0 x s1 /\ modifies w0 s0 s1) /\ (s x s1 r s2 /\ modifies w1 s1 s2)))
  = (pre_bind _ _ _ _ _ _ _ _ (frame _ _ _ _ x) (fun a -> frame _ _ _ _ (y a)))
  

let refine_flow_ist #a #w #r #f #fs #p #q
                (c: ist a w r (f::fs) p q)
  : Pure (ist a w r fs p q)
         (requires 
           (forall from to v. 
             has_flow_1 from to f /\
             from <> to ==>
             (forall s0 x x' s1 s1'. 
               p s0 /\
               p (havoc s0 from v) /\
               q s0 x s1 /\
               modifies w s0 s1 /\
               q (havoc s0 from v) x' s1' /\
               modifies w (havoc s0 from v) s1' ==>
               sel s1 to == sel s1' to)))
         (ensures fun _ -> True)
  = c
  
let consequence (a:Type) (w0 r0:label) p q p' q' (fs0:flows) (f:ist a w0 r0 fs0 p q)
  : Pure (comp a p' q')
    (requires (forall s. p' s ==> p s) /\
              (forall s0 x s1. p' s0 /\ q s0 x s1 ==> q' s0 x s1))
    (fun _ -> True)
  = let g : comp a p' q' = fun s -> f s in
    g

let norm_spec (p:Type) 
  : Lemma (requires (norm [delta;iota;zeta] p))
          (ensures p)
  = ()
let subcomp (a:Type) (w0 r0 w1 r1:label) #p #q #p' #q' (fs0 fs1:flows) (f:ist a w0 r0 fs0 p q)
  : Pure (ist a w1 r1 fs1 p' q')
    (requires label_inclusion w0 w1 /\
              label_inclusion r0 r1 /\
              (norm [delta;iota;zeta] (fs0 `flows_included_in` fs1)) /\
              (forall s. p' s ==> p s) /\
              (forall s0 x s1. p' s0 /\ q s0 x s1 ==> q' s0 x s1))
    (fun _ -> True)
  = let forig = f in
    norm_spec (fs0 `flows_included_in` fs1);
    assert ((fs0 `flows_included_in` fs1));
    let f : comp a p' q' = consequence a w0 r0 p q p' q' fs0 f in
    weaken_reads_ok f r0 r1;
    assert (reads_ok f r1);
    assert (writes_ok f w1);
    let respects_flows_lemma (from to:_)
      : Lemma 
        (requires ~(has_flow from to fs1) /\ from<>to)
        (ensures (no_leakage f from to))
        [SMTPat(no_leakage f from to)]
      = assert (no_leakage forig from to)
    in
    assert (respects_flows f fs1);
    f

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  IST : a:Type ->
        writes:label ->
        reads:label ->
        flows:flows ->
        p:pre ->
        q:(store -> a -> store -> Type0) ->
        Effect
  with
    repr = ist;
    return = return;
    bind = bind;
    subcomp = subcomp
}
let read (l:loc) 
  : IST int bot (single l) []
    (requires fun _ -> True)
    (ensures fun s0 x s1 -> x == sel s0 l)
  = IST?.reflect (iread l)
let write (l:loc) (x:int) 
  : IST unit (single l) bot []
    (requires fun _ -> True)
    (ensures fun _ _ s1 -> sel s1 l == x)
  = IST?.reflect (iwrite l x)

let u : Type = unit
let lift_pure (a:Type) (x:u -> Tot a)
  : ist a bot bot [] (fun _ -> True) (fun s0 v s1 -> s0 == s1 /\ v == x())
  = return a (x())

sub_effect PURE ~> IST = lift_pure


let refine_flow #a #w #r #f #fs #p #q
                ($c: unit -> IST a w r (f::fs) p q)
  : Pure (unit -> IST a w r fs p q)
         (requires 
           (forall from to v. 
             has_flow_1 from to f /\
             from <> to ==>
             (forall s0 x x' s1 s1'. 
               p s0 /\
               p (havoc s0 from v) /\
               q s0 x s1 /\
               modifies w s0 s1 /\
               q (havoc s0 from v) x' s1' /\
               modifies w (havoc s0 from v) s1' ==>
               sel s1 to == sel s1' to)))
         (ensures fun _ -> True)
  =  (fun () -> IST?.reflect (refine_flow_ist (reify (c()))))

let ref (l:label) = r:loc {r `Set.mem` l}
assume val high : label
let low : label = Set.complement high
let lref = ref low
let href = ref high


let test (l:lref) (h:href)
  : IST unit (union bot (single h))
             (union (single l) bot)
             (add_source (single l) [bot, single h])
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = let x = read l in
    write h x

let test2 (l:lref) (h:href)
  : IST unit (single h)
             (single l)
             [single l, single h]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = let x = read l in
    write h x

let test3 (l:lref) (h:href)
  : IST unit (single h)
             (single l)
             [single l, single h]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = write h (read l)

let test3_lab (l:lref) (h:href)
  : IST unit high low [low, high]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = write h (read l)

let test3_1 (l:lref) (h:href) (x:int)
  : IST int (single h)
          (single l)
          []
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 h == 0 /\ r == sel s1 l)
  = write h 0;
    read l

effect ISTT (a:Type) (w r:label) (fs:flows) = IST a w r fs (fun _ -> True) (fun _ _ _ -> True)
let test4 (l:lref) (h:href) (x:int)
  : IST int (single l)
          (single h)
          [single h, bot]
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 l == x /\ r == sel s1 h)
  = write l x;
    read h

let test5 (l:lref) (h:href) (x:int)
  : IST int (single l)
           (single h)
           []
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 l == x /\ r == sel s1 h)
  = write l x;
    read h

let test6 (l:lref) (h:href)
  : IST unit high low [low, high]
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 h == sel s0 l)
  = let x = read l in
    write h x

//This leaks the contents of the href
let test7 (l:lref) (h:href)
  : IST unit (single l)
             (single h)
             [high, low]
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 l == sel s0 h)
  = let x = read h in
    write l x

//But, label-based IFC is inherently imprecise
//This one reports a leakage, even though it doesn't really leak h
let test8 (l:lref) (h:href)
  : IST unit (single l)
             (union (single h) (single l))
             [(single h, single l)]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 l == sel s0 l + 1)
  = let x0 = read h in
    let x = read l in
    write l (x + 1)

//But, using the Hoare refinements, we can recover precision and remove
//the spurious flow from h to l
let refine_test8 (l:lref) (h:href)
  : unit -> IST unit (single l)
             (union (single h) (single l))
             []
             (requires fun _ -> True)
             (ensures fun s0 _ s1 -> sel s1 l == sel s0 l + 1)
  = refine_flow (fun () -> test8 l h)

//But, label-based IFC is inherently imprecise
//This one still reports a leakage, even though it doesn't really leak h
let test9 (l:lref) (h:href)
  : IST unit (single l)
             (union (single h) (single l))
             [(single l `union` single h, single l)]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 l == sel s0 l)
  = let x= (let x0 = read h in
            read l)
    in
    write l x

let refine_test9 (l:lref) (h:href)
  : (unit -> IST unit (single l)
                     (union (single h) (single l))
                     []
                     (requires fun _ -> True)
                     (ensures fun s0 _ s1 -> sel s1 l == sel s0 l))
  = refine_flow (fun () -> test9 l h)


assume
val cw0 : label
assume
val cr0 : label
assume
val c0 (_:unit) : ISTT unit cw0 cr0 []


assume
val cw1 : label
assume
val cr1 : label
assume
val c1 (_:unit) : ISTT unit cw1 cr1 []

assume
val cw2 : label
assume
val cr2 : label
assume
val c2 (_:unit) : ISTT unit cw2 cr2 []

let test10 ()
  : ISTT unit (union cw0 (union cw1 cw2))
             (union cr0 (union cr1 cr2))
             (add_source cr0
               ((bot, union cw1 cw2)::
                (add_source cr1 [bot, cw2])))
  = c0 (); (c1();c2())


let test12 ()
  : ISTT unit (union cw0 (union cw1 cw2))
             (union cr0 (union cr1 cr2))
             [(cr0, union cw1 cw2);
              (union cr0 cr1, cw2)]
  = c0 (); (c1();c2())

let test12_1 ()
  : ISTT unit (union cw0 (union cw1 cw2))
             (union cr0 (union cr1 cr2))
             [(cr0, cw1);
              (union cr0 cr1, cw2)]
  = c0 (); (c1();c2())


let test13 ()
  : ISTT unit (union (union cw0 cw1) cw2)
             (union (union cr0 cr1) cr2)
             (add_source cr0 [bot, cw1] @
              add_source (union cr0 cr1) [bot, cw2])
  = (c0 (); c1());c2()

let test14 ()
  : ISTT unit (union (union cw0 cw1) cw2)
             (union (union cr0 cr1) cr2)
             ([cr0, cw1;
               union cr0 cr1, cw2])
  = (c0 (); c1()); c2()

let test15 (l:lref)
  : IST unit (single l) (single l) []
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s0 l == sel s1 l)
  = write l (read l)

let ist_exn a w r fs (p:pre) (q:post a) =
    unit -> IST (option a) w r fs p 
               (fun s0 x s1 ->
                 match x with
                 | None -> True
                 | Some x -> q s0 x s1)

#push-options "--error_contexts true --print_implicits --print_bound_var_types --debug Sec2.IFCHoare --debug_level ExplainRel"
// let ist_exn_return (a:Type) (x:a) (_:unit)
//   : IST (option a) bot bot [] 
//         (fun _ -> True)
//         (fun s0 r s1 -> match r with | None -> True | Some r -> s0 == s1 /\ r == x)
//   = Some x

// let ist_return 
// let ifc_exn 
