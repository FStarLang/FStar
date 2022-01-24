module Sec2.HIFC
open FStar.List.Tot
open FStar.Map
let loc = int
type store = m:Map.t loc int{forall l. contains m l}
let upd (s:store) (l:loc) (x:int) : store = Map.upd s l x
let sel (s:store) (l:loc) : int = Map.sel s l
open FStar.Set

(*** A basic Hoare state monad ***)
let pre = store -> Type0
let post a = store -> a -> store -> Type0
let hst a (p:pre) (q:post a) = s0:store{p s0} -> r:(a & store){q s0 (fst r) (snd r)}

let return_hst a (x:a) : hst a (fun _ -> True) (fun s0 r s1 -> s0 == s1 /\ r == x) = fun s -> x,s
let bind_hst (a b:Type)
             p q r s
             (x:hst a p q)
             (y: (x:a -> hst b (r x) (s x)))
  : hst b (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1))
           (fun s0 r s2 -> (exists x s1. q s0 x s1 /\ s x s1 r s2))
  = fun s0 -> let v, s1 = x s0 in y v s1

layered_effect {
  HST : a:Type -> p:pre -> q:post a -> Effect
  with
    repr = hst;
    return = return_hst;
    bind = bind_hst
}

(*** Now, HIFC ***)

(* Some basic definitions of labels and sets *)
let label = Set.set loc
let label_inclusion (l0 l1:label) = Set.subset l0 l1
let bot : label = Set.empty
let single (l:loc) : label = Set.singleton l
let union (l0 l1:label) = Set.union l0 l1
let is_empty #a (s:Set.set a) = forall (x:a). ~ (Set.mem x s)

(* The write effect of a computation *)
let modifies (w:label) (s0 s1:store) = (forall l.{:pattern (sel s1 l)} ~(Set.mem l w) ==> sel s0 l == sel s1 l)
let writes #a #p #q (f:hst a p q) (writes:label) =
    forall (s0:store{p s0}). let x1, s0' = f s0 in modifies writes s0 s0'

(* The read effect of a computation *)
let agree_on (reads:label) (s0 s1: store) = forall l. Set.mem l reads ==> sel s0 l == sel s1 l
let related_runs #a #p #q (f:hst a p q) (s0:store{p s0}) (s0':store{p s0'}) =
      (let x1, s1 = f s0 in
       let x1', s1' = f s0' in
       x1 == x1' /\
       (forall (l:loc). (sel s1 l == sel s1' l \/ (sel s1 l == sel s0 l /\ sel s1' l == sel s0' l))))
let reads #a #p #q (f:hst a p q) (reads:label) =
    forall (s0:store{p s0}) (s0':store{p s0'}). agree_on reads s0 s0' ==> related_runs f s0 s0'

(* The respects flows refinement *)
let flow = label & label //from, to
let flows = list flow
let has_flow_1 (from to:loc) (f:flow) = from `Set.mem` fst f /\ to `Set.mem` snd f
let has_flow (from to:loc) (fs:flows) = (exists rs. rs `List.Tot.memP` fs /\ has_flow_1 from to rs)
let no_leakage_k #a #p #q (f:hst a p q) (from to:loc) (k:int) =
  forall (s0:store{p s0}).{:pattern (upd s0 from k)}
    p (upd s0 from k) ==>
    sel (snd (f s0)) to == (sel (snd (f (upd s0 from k))) to)
let no_leakage #a #p #q (f:hst a p q) (from to:loc) = forall k. no_leakage_k f from to k
let respects #a #p #q (f:hst a p q) (fs:flows) =
    (forall from to. {:pattern (no_leakage f from to)} ~(has_flow from to fs) /\ from<>to ==> no_leakage f from to)

(** Representation type for the HIFC effect
     You should convince yourself that `reads`, `writes` and `respects`
     really capture the intended semantics of read effects, write effects, and IFC **)
let hifc a (r:label) (w:label) (fs:flows) (p:pre) (q:post a) =
  f:hst a p q {
    reads f r /\
    writes f w  /\
    respects f fs
  }

(** returning a pure value `x` into hifc **)
let return (a:Type) (x:a) : hifc a bot bot [] (fun _ -> True) (fun s0 r s1 -> s0 == s1 /\ r == x) =
  let f : hst a (fun _ -> True) (fun s0 r s1 -> s0 == s1 /\ r == x) = fun s -> x,s in
  f

(** reading a loc `l` *)
let iread (l:loc) : hifc int (single l) bot [] (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == sel s0 l) =
  let f : hst int (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == sel s0 l) = fun s -> sel s l, s in
  f

(** writing a loc `l` *)
let iwrite (l:loc) (x:int) : hifc unit bot (single l) [] (fun _ -> True) (fun s0 _ s1 -> s1 == upd s0 l x) =
  let f : hst unit (fun _ -> True) (fun s0 _ s1 -> s1 == upd s0 l x) = fun s -> (), upd s l x in
  f

(** Now, a lot of what follows is proofs that allow us to define 
    return, bind, subsumption, and other combinators *)
let does_not_read_loc_v #a #p #q (f:hst a p q)
                        (reads:label)
                        (l:loc)
                        (s0:store{p s0})
                        v =
    let s0' = upd s0 l v in
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

let does_not_read_loc #a #p #q (f:hst a p q) (reads:label) (l:loc) (s0:store{p s0}) =
  forall v. does_not_read_loc_v f reads l s0 v

let reads_ok_preserves_equal_locs #a #p #q (f:hst a p q) (rds:label) (s0:store{p s0}) (s0':store{p s0'})
  : Lemma (requires agree_on rds s0 s0' /\ HIFC.reads f rds)
          (ensures (let x1, s1 = f s0 in
                    let x1', s1' = f s0' in
                    agree_on rds s1 s1'))
  = ()

let weaken_reads_ok #a #p #q (f:hst a p q) (rds rds1:label)
  : Lemma (requires reads f rds /\
                    label_inclusion rds rds1)
          (ensures reads f rds1)
  = let aux s0 s0'
    : Lemma (requires p s0 /\ p s0' /\ agree_on rds1 s0 s0')
            (ensures agree_on rds s0 s0')
            [SMTPat(agree_on rds1 s0 s0')]
    = ()
    in
    ()

let reads_ok_does_not_read_loc #a #p #q (f:hst a p q) (reads:label) (l:loc{~(Set.mem l reads)}) (s0:store{p s0})
  : Lemma
    (requires HIFC.reads f reads)
    (ensures does_not_read_loc f reads l s0)
  = let aux (v:int)
      : Lemma (requires p (upd s0 l v))
              (ensures does_not_read_loc_v f reads l s0 v)
              [SMTPat ((upd s0 l v))]
      = assert (agree_on reads s0 (upd s0 l v));
        ()
    in
    ()

let add_source (r:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> union r r0, w0) fs
let add_sink (w:label) (fs:flows) : flows = List.Tot.map (fun (r0, w0) -> r0, union w w0) fs

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

(* The computation behavior of sequential composition of HIFC
   is the same as HST.
   This is a step towards defining bind_hifc ... we will
   need several lemmas to give the result the hifc type we want *)
let bind_ifc' (#a #b:Type)
              (#w0 #r0 #w1 #r1:label)
              (#fs0 #fs1:flows)
              #p #q #r #s
              (x:hifc a r0 w0 fs0 p q)
              (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
  : hst b (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1))
          (fun s0 r s2 -> (exists x s1. q s0 x s1 /\ s x s1 r s2))
  = bind_hst _ _ _ _ _ _ x y

(* bind_ifc' reads the union of the read labels *)
let bind_ifc_reads_ok (#a #b:Type)
                      (#w0 #r0 #w1 #r1:label)
                      (#fs0 #fs1:flows)
                      #p #q #r #s
                      (x:hifc a r0 w0 fs0 p q)
                      (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
  : Lemma (HIFC.reads (bind_ifc' x y) (union r0 r1))
  = let f = bind_ifc' x y in
    let p_f = (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1)) in
    let reads = union r0 r1 in
    let f_reads_ok (s0:store{p_f s0}) (s0':store{p_f s0'})
      : Lemma
        (requires agree_on reads s0 s0')
        (ensures  related_runs f s0 s0')
        [SMTPat(agree_on reads s0 s0')]
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

(* bind_ifc' writes the union of the write labels *)
let bind_ifc_writes_ok (#a #b:Type)
                        (#w0 #r0 #w1 #r1:label)
                        (#fs0 #fs1:flows)
                        #p #q #r #s
                        (x:hifc a r0 w0 fs0 p q)
                        (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
  : Lemma (writes (bind_ifc' x y) (union w0 w1))
  = ()

(* Now the harder part: Showing that bind_ifc respects a flows set 
   See bind_ifc_flows_ok several lines below *)
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
  = let aux (rs:_)
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

let has_flow_soundness #a #r #w #fs #p #q (f:hifc a r w fs p q)
                       (from to:loc) (s:store{p s}) (k:int{p (upd s from k)})
    : Lemma (requires
              (let x, s1 = f s in
               let _, s1' = f (upd s from k) in
               from <> to /\
               sel s1 to <> sel s1' to))
            (ensures has_flow from to fs)
    = let aux ()
       : Lemma (requires (~(has_flow from to fs)))
               (ensures False)
               [SMTPat ()]
       = assert (respects f fs);
         assert (no_leakage f from to)
      in
      ()

let bind_hst_no_leakage (#a #b:Type)
                         (#w0 #r0 #w1 #r1:label)
                         (#fs0 #fs1:flows)
                         #p #q #r #s
                         (x:hifc a r0 w0 fs0 p q)
                         (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
                         (from to:loc)
                         (s0:store) (k:_)
    : Lemma
      (requires (
        let p_f = (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1)) in
        let s0' = upd s0 from k in
        p_f s0 /\
        p_f s0' /\
        from <> to /\
        ~(has_flow from to (fs0 @ add_source r0 ((bot, w1)::fs1)))))
      (ensures (let f = bind_ifc' x y in
                let s0' = upd s0 from k in
                let _, s2 = f s0 in
                let _, s2' = f s0' in
                sel s2 to == sel s2' to))
    = let f = bind_ifc' x y in
      assert (reads x r0);
      let s0' = upd s0 from k in
      let _, s2f = f s0 in
      let _, s2f' = f s0' in
      let flows = (fs0 @ add_source r0 ((r1, w1)::fs1)) in
      let v0, s1 = x s0 in
      let v0', s1' = x s0' in
      elim_has_flow_seq from to r0 r1 w1 fs0 fs1;
      assert (~(has_flow from to fs0));
      assert (respects x fs0);
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
           //     s1' = upd from s1 k
           //     s2 to = s2' to
      if Set.mem to w1
      then begin
        assert (~(Set.mem from r0));
        assert (reads x r0);
        reads_ok_does_not_read_loc x r0 from s0;
        assert (does_not_read_loc x r0 from s0);
        assert (does_not_read_loc_v x r0 from s0 k);
        assert (v0 == v0');
        assert (forall l. l <> from ==> sel s1 l == sel s1' l);
        assert (Map.equal s1' (upd s1 from k) \/ Map.equal s1' s1);
        if (sel s1 from = sel s1' from)
        then begin
          assert (Map.equal s1 s1')
          end
        else begin
          assert (Map.equal s1' (upd s1 from k));
          assert (reads (y v0) r1);
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

(* bind_ifc' has flows corresponding to the flows of
     -- `x` the first computation, i.e., fs0
     -- `y` the second computation ((bot, w1)::fs1)
         augmented with the reads of `x`, since the
         result of `x` is tainted by its reads *)
let bind_ifc_flows_ok (#a #b:Type)
                       (#w0 #r0 #w1 #r1:label)
                       (#fs0 #fs1:flows)
                       #p #q #r #s
                       (x:hifc a r0 w0 fs0 p q)
                       (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
  : Lemma (respects (bind_ifc' x y) (fs0 @ add_source r0 ((bot, w1)::fs1)))
  = let f = bind_ifc' x y in
    let p_f = (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1)) in
    let flows = (fs0 @ add_source r0 ((bot, w1)::fs1)) in
    let respects_flows_lemma (from to:loc)
      : Lemma (requires from <> to /\ ~(has_flow from to flows))
              (ensures no_leakage f from to)
              [SMTPat (has_flow from to flows)]
      = let aux (s0:store{p_f s0}) (k:_{p_f (upd s0 from k)})
         : Lemma (let s0' = upd s0 from k in
                  let _, s2 = f s0 in
                  let _, s2' = f s0' in
                  sel s2 to == sel s2' to)
                 [SMTPat (upd s0 from k)]
         = bind_hst_no_leakage x y from to s0 k
        in
        ()
    in
    ()

(* Getting there: pre_bind is a valid bind for hifc.
   But, we can do a bit better by integrating framing into it ... see below *)
let pre_bind (a b:Type)
         (w0 r0 w1 r1:label) (fs0 fs1:flows)
         #p #q #r #s
         (x:hifc a r0 w0 fs0 p q)
         (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
  : hifc b (union r0 r1) (union w0 w1) (fs0 @ add_source r0 ((bot, w1)::fs1))
          (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 ==> r x s1))
          (fun s0 r s2 -> (exists x s1. q s0 x s1 /\ s x s1 r s2))
  = let f = bind_ifc' x y in
    bind_ifc_reads_ok x y;
    bind_ifc_writes_ok x y;
    bind_ifc_flows_ok x y;
    f

(* Incidentially, The IFC indexing structure is a monoid 
   under the label_equiv equivalence relation, making
   hifc a graded Hoare monad
*)
let triple = label & label & flows
let unit_triple = bot, bot, []
let ifc_triple (w0, r0, fs0) (w1, r1, fs1) = (union w0 w1, union r0 r1, (fs0 @ add_source r0 ((bot, w1)::fs1)))

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

(* monoid laws for ifc_triple *)
let left_unit (w, r, f) =
  assert (Set.equal (union bot bot) bot);
  add_source_bot f;
  assert (ifc_triple unit_triple (w, r, f) `triple_equiv` (w, r, f))
let right_unit (w, r, f) =
  calc (==) {
    ifc_triple (w, r, f) unit_triple;
    (==) { }
    (w `union` bot, r `union` bot, f @ add_source r ((bot, bot)::[]));
  };
  assert (flows_equiv (add_source r [(bot, bot)]) []);
  flows_equiv_append f (add_source r [(bot, bot)]) f [];
  append_nil_r f;
  assert (ifc_triple (w, r, f) unit_triple  `triple_equiv` (w, r, f))
open FStar.Calc
let assoc_hst (w0, r0, fs0) (w1, r1, fs1) (w2, r2, fs2) =
  calc (==) {
    ifc_triple (w0, r0, fs0) (ifc_triple (w1, r1, fs1) (w2, r2, fs2)) ;
    (==) { }
    ifc_triple (w0, r0, fs0) (union w1 w2, union r1 r2, (fs1 @ add_source r1 ((bot, w2)::fs2)));
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
    ifc_triple (ifc_triple (w0, r0, fs0) (w1, r1, fs1)) (w2, r2, fs2);
    (==) { }
    ifc_triple (union w0 w1, union r0 r1, (fs0 @ add_source r0 ((bot, w1)::fs1))) (w2, r2, fs2);
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

(* Adding a frame combinator, refining the Hoare postcondition with 
   the interpretation of the write index *)
let frame (a:Type) (r w:label) (fs:flows) #p #q (f:hifc a r w fs p q)
  : hifc a r w fs p (fun s0 x s1 -> q s0 x s1 /\ modifies w s0 s1)
  = let aux (s0:store{p s0}) (l:loc{~(Set.mem l w)})
      : Lemma (let x, s1 = f s0 in
               sel s0 l == sel s1 l)
               [SMTPat()]

      = ()
    in
    let g : hst a p (fun s0 x s1 -> q s0 x s1 /\ modifies w s0 s1) = fun s0 -> f s0 in
    assert (HIFC.reads f r);
    let read_ok_lem (l:loc) (s:store{p s})
      : Lemma (requires (~(Set.mem l r)))
              (ensures (does_not_read_loc g r l s))
              [SMTPat(does_not_read_loc g r l s)]
      = reads_ok_does_not_read_loc g r l s;
        assert (does_not_read_loc f r l s)
    in
    assert (HIFC.reads g r);
    assert (writes g w);
    let respects_flows_lemma (from to:_)
      : Lemma
        (requires ~(has_flow from to fs) /\ from<>to)
        (ensures (no_leakage g from to))
        [SMTPat(has_flow from to fs)]
      = assert (no_leakage f from to)
    in
    assert (respects g fs);
    g


(*** And there we have our bind for hifc ***)
(* It is similar to pre_bind, but we integrate the use of `frame`
   so that all HIFC computations are auto-framed *)
let bind (a b:Type)
         (r0 w0 r1 w1:label) (fs0 fs1:flows)
         #p #q #r #s
         (x:hifc a r0 w0 fs0 p q)
         (y: (x:a -> hifc b r1 w1 fs1 (r x) (s x)))
  : hifc b (union r0 r1) (union w0 w1) (fs0 @ add_source r0 ((bot, w1)::fs1))
          (fun s0 -> p s0 /\ (forall x s1. q s0 x s1 /\ modifies w0 s0 s1 ==> r x s1))
          (fun s0 r s2 -> (exists x s1. (q s0 x s1 /\ modifies w0 s0 s1) /\ (s x s1 r s2 /\ modifies w1 s1 s2)))
  = (pre_bind _ _ _ _ _ _ _ _ (frame _ _ _ _ x) (fun a -> frame _ _ _ _ (y a)))


(** This one lets you drop a flow `f` from the flow set
    if the Hoare spec lets you prove that *)
let refine_flow_hifc #a #w #r #f #fs #p #q
                (c: hifc a r w (f::fs) p q)
  : Pure (hifc a r w fs p q)
         (requires
           (forall from to v.
             has_flow_1 from to f /\
             from <> to ==>
             (forall s0 x x' s1 s1'.
               p s0 /\
               p (upd s0 from v) /\
               q s0 x s1 /\
               modifies w s0 s1 /\
               q (upd s0 from v) x' s1' /\
               modifies w (upd s0 from v) s1' ==>
               sel s1 to == sel s1' to)))
         (ensures fun _ -> True)
  = c

(** Classic Hoare rule of consequence *)
let consequence (a:Type) (r0 w0:label) p q p' q' (fs0:flows) (f:hifc a r0 w0 fs0 p q)
  : Pure (hst a p' q')
    (requires (forall s. p' s ==> p s) /\
              (forall s0 x s1. p' s0 /\ q s0 x s1 ==> q' s0 x s1))
    (fun _ -> True)
  = let g : hst a p' q' = fun s -> f s in
    g

(* A couple of utils *)
let norm_spec (p:Type)
  : Lemma (requires (norm [delta;iota;zeta] p))
          (ensures p)
  = ()
let norm_spec_inv (p:Type)
  : Lemma (requires p)
          (ensures (norm [delta;iota;zeta] p))
  = ()

(* A subsumption rule for hifc *)
let sub_hifc (a:Type) (r0 w0 r1 w1:label) #p #q #p' #q' (fs0 fs1:flows) 
             (f:hifc a r0 w0 fs0 p q)
  : Pure (hifc a r1 w1 fs1 p' q')
         (requires
               label_inclusion r0 r1 /\
               label_inclusion w0 w1 /\
               (norm [delta;iota;zeta] (fs0 `flows_included_in` fs1)) /\
               (forall s. p' s ==> p s) /\
               (forall s0 x s1. p' s0 /\ q s0 x s1 ==> q' s0 x s1))
         (ensures fun _ -> True)
  = let forig = f in
    norm_spec (fs0 `flows_included_in` fs1);
    assert ((fs0 `flows_included_in` fs1));
    let f : hst a p' q' = consequence a r0 w0 p q p' q' fs0 f in
    weaken_reads_ok f r0 r1;
    assert (reads f r1);
    assert (writes f w1);
    let respects_flows_lemma (from to:_)
      : Lemma
        (requires ~(has_flow from to fs1) /\ from<>to)
        (ensures (no_leakage f from to))
        [SMTPat(no_leakage f from to)]
      = assert (no_leakage forig from to)
    in
    assert (respects f fs1);
    f

(* A conditional rule for hifc *)
let if_then_else (a:Type) r0 w0 f0 p0 q0
                          r1 w1 f1
                          p1 q1
                          (c_then:hifc a r0 w0 f0 p0 q0)
                          (c_else:hifc a r1 w1 f1 p1 q1)
                          (b:bool)
   = hifc a (r0 `union` r1) (w0 `union` w1) (f0 @ f1)
            (fun s -> if b then p0 s else p1 s)
            (fun s0 x s1 -> if b then q0 s0 x s1 else q1 s0 x s1)

let rec append_memP #a (x:a) (l0 l1:list a)
    : Lemma (List.Tot.memP x (l0 @ l1) <==> (List.Tot.memP x l0 \/ List.Tot.memP x l1))
      = match l0 with
        | [] -> ()
        | hd::tl -> append_memP x tl l1

    
(* An auxiliary lemma needed to prove if_then_else sound *)
let weaken_flows_append (fs fs':flows)
  : Lemma (ensures (norm [delta;iota;zeta] (fs `flows_included_in` (fs @ fs')) /\
                   (norm [delta;iota;zeta] (fs' `flows_included_in` (fs @ fs')))))
          [SMTPat  ()]
  = let aux (f0:flow)
      : Lemma
        (requires f0 `List.Tot.memP` fs)
        (ensures  f0 `List.Tot.memP` (fs @ fs'))
        [SMTPat(f0 `List.Tot.memP` (fs @ fs'))]
      = append_memP f0 fs fs'
    in
    let aux (f0:flow)
      : Lemma
        (requires f0 `List.Tot.memP` fs')
        (ensures  f0 `List.Tot.memP` (fs @ fs'))
        [SMTPat(f0 `List.Tot.memP` (fs @ fs'))]
      = append_memP f0 fs fs'
    in
    norm_spec_inv (fs `flows_included_in` (fs @ fs'));
    norm_spec_inv (fs' `flows_included_in` (fs @ fs'))

(*** We now create our HIFC effect *)
[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  HIFC : a:Type ->
        reads:label ->
        writes:label ->
        flows:flows ->
        p:pre ->
        q:(store -> a -> store -> Type0) ->
        Effect
  with
    repr = hifc;
    return = return;
    bind = bind;
    subcomp = sub_hifc;
    if_then_else = if_then_else
}

(* reflecting actions into it *)
let read (l:loc)
  : HIFC int (single l) bot []
    (requires fun _ -> True)
    (ensures fun s0 x s1 -> x == sel s0 l)
  = HIFC?.reflect (iread l)
let write (l:loc) (x:int)
  : HIFC unit bot (single l) []
    (requires fun _ -> True)
    (ensures fun _ _ s1 -> sel s1 l == x)
  = HIFC?.reflect (iwrite l x)

(* This is a technical bit to lift the F*'s WP-calculus of PURE
   computations into the Hoare types of HIFC *)
let u : Type = unit
let lift_PURE_HIFC (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
  : Pure (hifc a bot bot [] (fun _ -> True) (fun s0 _ s1 -> s0 == s1))
      (requires wp (fun _ -> True))
      (ensures fun _ -> True)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    return a (f ())
sub_effect PURE ~> HIFC = lift_PURE_HIFC

(* reflecting the flow refinement into the effect *)
let refine_flow #a #w #r #f #fs #p #q
                ($c: unit -> HIFC a r w (f::fs) p q)
  : Pure (unit -> HIFC a r w fs p q)
         (requires
           (forall from to v.
             has_flow_1 from to f /\
             from <> to ==>
             (forall s0 x x' s1 s1'.
               p s0 /\
               p (upd s0 from v) /\
               q s0 x s1 /\
               modifies w s0 s1 /\
               q (upd s0 from v) x' s1' /\
               modifies w (upd s0 from v) s1' ==>
               sel s1 to == sel s1' to)))
         (ensures fun _ -> True)
  =  (fun () -> HIFC?.reflect (refine_flow_hifc (reify (c()))))

(* Now for some examples *)

let ref (l:label) = r:loc {r `Set.mem` l}
assume val high : label
let low : label = Set.complement high
let lref = ref low
let href = ref high

let test (l:lref) (h:href)
  : HIFC unit (union (single l) bot)
              (union bot (single h))
              (add_source (single l) [bot, single h])
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = let x = read l in
    write h x

let test2 (l:lref) (h:href)
  : HIFC unit (single l)
              (single h)
              [single l, single h]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = let x = read l in
    write h x

let test3 (l:lref) (h:href)
  : HIFC unit (single l)
              (single h)
              [single l, single h]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = write h (read l)

let test3_lab (l:lref) (h:href)
  : HIFC unit low high [low, high]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 h == sel s0 l)
  = write h (read l)

let test3_1 (l:lref) (h:href) (x:int)
  : HIFC int (single l) (single h) []
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 h == 0 /\ r == sel s1 l)
  = write h 0;
    read l


let test4 (l:lref) (h:href) (x:int)
  : HIFC int (single h) (single l) [single h, bot]
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 l == x /\ r == sel s1 h)
  = write l x;
    read h

let test5 (l:lref) (h:href) (x:int)
  : HIFC int (single h) (single l) []
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 l == x /\ r == sel s1 h)
  = write l x;
    read h

let test6 (l:lref) (h:href)
  : HIFC unit low high [low, high]
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 h == sel s0 l)
  = let x = read l in
    write h x

//This leaks the contents of the href
let test7 (l:lref) (h:href)
  : HIFC unit (single h) (single l) [high, low]
    (requires fun _ -> True)
    (ensures fun s0 r s1 -> sel s1 l == sel s0 h)
  = let x = read h in
    write l x

//But, label-based IFC is inherently imprecise
//This one reports a leakage, even though it doesn't really leak h
let test8 (l:lref) (h:href)
  : HIFC unit (union (single h) (single l)) (single l)  [(single h, single l)]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 l == sel s0 l + 1)
  = let x0 = read h in
    let x = read l in
    write l (x + 1)

effect IFC (a:Type) (w r:label) (fs:flows) = HIFC a w r fs (fun _ -> True) (fun _ _ _ -> True)
let test_cond (l:lref) (h:href) (b:bool)
  : IFC unit (union (single h) (single l)) (single l) [single h, single l]
  = if b then write l (read h) else write l (read l + 1)

//But, using the Hoare refinements, we can recover precision and remove
//the spurious flow from h to l
let refine_test8 (l:lref) (h:href)
  : unit -> HIFC unit (union (single h) (single l)) (single l) []
             (requires fun _ -> True)
             (ensures fun s0 _ s1 -> sel s1 l == sel s0 l + 1)
  = refine_flow (fun () -> test8 l h)

//But, label-based IFC is inherently imprecise
//This one still reports a leakage, even though it doesn't really leak h
let test9 (l:lref) (h:href)
  : HIFC unit (union (single h) (single l)) (single l)
             [(single l `union` single h, single l)]
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s1 l == sel s0 l)
  = let x= (let x0 = read h in
            read l)
    in
    write l x

let refine_test9 (l:lref) (h:href)
  : (unit -> HIFC unit (union (single h) (single l))
                      (single l)
                      []
                      (requires fun _ -> True)
                      (ensures fun s0 _ s1 -> sel s1 l == sel s0 l))
  = refine_flow (fun () -> test9 l h)


assume
val cw0 : label
assume
val cr0 : label
assume
val c0 (_:unit) : IFC unit cr0 cw0 []


assume
val cw1 : label
assume
val cr1 : label
assume
val c1 (_:unit) : IFC unit cr1 cw1 []

assume
val cw2 : label
assume
val cr2 : label
assume
val c2 (_:unit) : IFC unit cr2 cw2 []

let test10 ()
  : IFC unit (union cr0 (union cr1 cr2))
             (union cw0 (union cw1 cw2))
             (add_source cr0
               ((bot, union cw1 cw2)::
                (add_source cr1 [bot, cw2])))
  = c0 (); (c1();c2())


let test12 ()
  : IFC unit (union cr0 (union cr1 cr2))
              (union cw0 (union cw1 cw2))
              [(cr0, union cw1 cw2);
              (union cr0 cr1, cw2)]
  = c0 (); (c1();c2())

let test12_1 ()
  : IFC unit (union cr0 (union cr1 cr2))
              (union cw0 (union cw1 cw2))
              [(cr0, cw1); (union cr0 cr1, cw2)]
  = c0 (); (c1();c2())


let test13 ()
  : IFC unit (union (union cr0 cr1) cr2)
             (union (union cw0 cw1) cw2)
             (add_source cr0 [bot, cw1] @
              add_source (union cr0 cr1) [bot, cw2])
  = (c0 (); c1());c2()

let test14 ()
  : IFC unit (union (union cr0 cr1) cr2)
             (union (union cw0 cw1) cw2)
             ([cr0, cw1;
               union cr0 cr1, cw2])
  = (c0 (); c1()); c2()

let test15 (l:lref)
  : HIFC unit (single l) (single l) []
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> sel s0 l == sel s1 l)
  = write l (read l)

let ist_exn a w r fs (p:pre) (q:post a) =
    unit -> HIFC (option a) w r fs p
               (fun s0 x s1 ->
                 match x with
                 | None -> True
                 | Some x -> q s0 x s1)


let lift_ist_hst a w r fs p q (x:hifc a r w fs p q) 
  : hst a p (fun s0 x s1 -> q s0 x s1 /\ modifies w s0 s1) 
  = frame _ _ _ _ x
sub_effect HIFC ~> HST = lift_ist_hst
