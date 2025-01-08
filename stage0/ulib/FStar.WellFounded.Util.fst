module FStar.WellFounded.Util
open FStar.WellFounded

#set-options "--warn_error -242" //inner let recs not encoded to SMT; ok

let intro_lift_binrel (#a:Type) (r:binrel a) (y:a) (x:a)
  : Lemma
    (requires r y x)
    (ensures lift_binrel r (| a, y |) (| a, x |))
  = let t0 : top = (| a, y |) in
    let t1 : top = (| a, x |) in
    let pf1 : squash (dfst t0 == a /\ dfst t1 == a) = () in
    let pf2 : squash (r (dsnd t0) (dsnd t1)) = () in
    let pf : squash (lift_binrel r t0 t1) =
      FStar.Squash.bind_squash pf1 (fun (pf1: (dfst t0 == a /\ dfst t1 == a)) ->
      FStar.Squash.bind_squash pf2 (fun (pf2: (r (dsnd t0) (dsnd t1)))  ->
      let p : lift_binrel r t0 t1 = (| pf1, pf2 |) in
      FStar.Squash.return_squash p))
    in
    ()

let elim_lift_binrel (#a:Type) (r:binrel a) (y:top) (x:a)
  : Lemma
    (requires lift_binrel r y (| a, x |))
    (ensures dfst y == a /\ r (dsnd y) x)
  = let s : squash (lift_binrel r y (| a, x |)) = FStar.Squash.get_proof (lift_binrel r y (| a, x |)) in
    let s : squash (dfst y == a /\ r (dsnd y) x) = FStar.Squash.bind_squash s (fun (pf:lift_binrel r y (|a, x|)) ->
      let p1 : (dfst y == a /\ a == a) = dfst pf in
      let p2 : r (dsnd y) x = dsnd pf in
      introduce dfst y == a /\ r (dsnd y) x
      with eliminate dfst y == a /\ a == a
           returns _
           with l r. l
      and  FStar.Squash.return_squash p2)
    in
    ()

let lower_binrel (#a:Type)
                 (#r:binrel a)
                 (x y:top)
                 (p:lift_binrel r x y)
  : r (dsnd x) (dsnd y)
  = dsnd p


let lift_binrel_well_founded (#a:Type u#a)
                             (#r:binrel u#a u#r a)
                             (wf_r:well_founded r)
  : well_founded (lift_binrel r)
  = let rec aux (y:top{dfst y == a})
                (pf:acc r (dsnd y))
        : Tot (acc (lift_binrel r) y)
              (decreases pf)
        = AccIntro (fun (z:top) (p:lift_binrel r z y) ->
            aux z (pf.access_smaller (dsnd z) (lower_binrel z y p)))
    in
    let aux' (y:top{dfst y =!= a})
        : acc (lift_binrel r) y
        = AccIntro (fun y p -> false_elim ())
    in
    fun (x:top) ->
      let b = FStar.StrongExcludedMiddle.strong_excluded_middle (dfst x == a) in
      if b
      then aux x (wf_r (dsnd x))
      else aux' x

let lower_binrel_squashed (#a:Type u#a)
                          (#r:binrel u#a u#r a)
                          (x y:top u#a)
                          (p:lift_binrel_squashed r x y)
  : squash (r (dsnd x) (dsnd y))
  = assert (dfst x==a /\ dfst y==a /\ squash (r (dsnd x) (dsnd y)))
        by FStar.Tactics.(exact (quote (FStar.Squash.return_squash p)))


let lift_binrel_squashed_well_founded (#a:Type u#a)
                                      (#r:binrel u#a u#r a)
                                      (wf_r:well_founded (squash_binrel r))
  : well_founded (lift_binrel_squashed r)
  = let rec aux (y:top{dfst y == a})
                (pf:acc (squash_binrel r) (dsnd y))
        : Tot (acc (lift_binrel_squashed r) y)
              (decreases pf)
        = AccIntro (fun (z:top) (p:lift_binrel_squashed r z y) ->
                let p =  lower_binrel_squashed z y p in
                aux z (pf.access_smaller (dsnd z) (FStar.Squash.join_squash p)))
    in
    let aux' (y:top{dfst y =!= a})
        : acc (lift_binrel_squashed r) y
        = AccIntro (fun y p -> false_elim ())
    in
    fun (x:top) ->
      let b = FStar.StrongExcludedMiddle.strong_excluded_middle (dfst x == a) in
      if b
      then aux x (wf_r (dsnd x))
      else aux' x

let lift_binrel_squashed_intro (#a:Type) (#r:binrel a)
                               (wf_r:well_founded (squash_binrel r))
                               (x y:a)
                               (sqr:squash (r x y))
  : Lemma
    (ensures lift_binrel_squashed r (|a, x|) (|a, y|))
  = assert (lift_binrel_squashed r (| a, x |) (| a , y |))
        by FStar.Tactics.(
            norm [delta_only [`%lift_binrel_squashed]];
            split(); split(); trefl(); trefl();
            mapply (`FStar.Squash.join_squash)
           )

let unsquash_well_founded (#a:Type u#a) (r:binrel u#a u#r a) (wf_r:well_founded (squash_binrel r))
  : well_founded u#a u#r r
  = let rec f (x:a)
      : Tot (acc r x)
            (decreases {:well-founded (lift_binrel_squashed_as_well_founded_relation wf_r) (| a, x |)})
      = AccIntro (let g_smaller (y: a) (u: r y x) : acc r y =
                      lift_binrel_squashed_intro wf_r y x (FStar.Squash.return_squash u);
                      f y
                  in g_smaller)
    in
    f
