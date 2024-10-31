module PulseCore.IndirectionTheoryActions
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt
module HST = PulseCore.HoareStateMonad
open FStar.Ghost

let pm_sep_laws () : squash (
  PulseCore.Semantics.(
    associative PM.star /\
    commutative PM.star /\
    is_unit PM.emp PM.star
  )
) 
= introduce forall p q. PM.equiv p q ==> p == q
  with introduce _ ==> _
  with _ . (
    PM.slprop_extensionality p q
  );
  let open PM in
  FStar.Classical.(
    forall_intro_2 star_commutative;
    forall_intro_3 star_associative;
    forall_intro emp_unit
  )
  
let pm_sep : PulseCore.HeapSig.separable pulse_mem = PM.pulse_heap_sig.sep
let pm_core_of (m:pulse_mem) : pulse_core_mem = PM.pulse_heap_sig.sep.core_of m

let split_mem (p:slprop) (q:slprop) (m:erased core_mem { interp (p `star` q) m })
: res:(erased core_mem & erased core_mem) {
    let l, r = res in
    disjoint l r /\
    reveal m == join l r /\
    interp p l /\
    interp q r
  }
= star_equiv p q m;
  let m1 : erased (core_mem) =
    FStar.IndefiniteDescription.indefinite_description_tot
      core_mem
      (fun m1 -> 
        exists m2. 
          disjoint m1 m2 /\
          reveal m == join m1 m2 /\
          interp p m1 /\
          interp q m2)
  in
  let m2 : erased (core_mem) =
    FStar.IndefiniteDescription.indefinite_description_tot
        core_mem
        (fun m2 -> 
            disjoint m1 m2 /\
            reveal m == join m1 m2 /\
            interp p m1 /\
            interp q m2)
  in
  m1, m2

let split_mem3 (pp qq rr:slprop) (s:erased core_mem { interp (pp `star` qq `star` rr) s })
: res:(erased core_mem & erased core_mem & erased core_mem) {
    let l, m, r = res in
    // disjoint l m /\
    disjoint m r /\
    disjoint l (join m r) /\
    reveal s == join l (join m r) /\
    interp pp l /\
    interp qq m /\
    interp rr r
}
= sep_laws();
  let m1, m2 = split_mem pp (qq `star` rr) s in
  let lr :erased (erased core_mem & erased core_mem) = hide (split_mem qq rr m2) in
  let l, m, r = m1, fst <| reveal lr, snd <| reveal lr in
  l, m, r


let pin_frame (p:pm_slprop) (frame:slprop) 
              (w:mem { interpret (lift p `star` frame) w })
: frame':pm_slprop { PM.interp (p `PM.star` frame')  w.pulse_mem } &
  (q:pm_slprop -> m':pulse_mem ->
    Lemma 
      (requires PM.interp (q `PM.star` frame') m')
      (ensures interpret (lift q `star` frame) { w with pulse_mem = m'}))
= let c = core_of w in
  let { pulse_mem; istore } = w in
  let m0, m1 = split_mem (lift p) frame c in
  star_equiv (lift p) frame c;
  let fr (pm:pulse_core_mem)  
    : prop
    = interp frame { pulse_mem=pm; istore=m1.istore }
  in
  let fr_affine ()
  : Lemma (HeapSig.is_affine_mem_prop pm_sep fr)
  = introduce forall s0 s1.
      fr s0 /\ pm_sep.disjoint s0 s1 ==> fr (pm_sep.join s0 s1)
    with introduce _ ==> _
    with _. ( 
      let left = { pulse_mem = s0; istore = m1.istore } in
      let right = { pulse_mem = s1; istore = clear_credits m1.istore } in
      istore_join_refl m1.istore;
      assert (disjoint left right);
      assert (join left right == { pulse_mem = pm_sep.join s0 s1; istore=m1.istore })
    )
  in
  fr_affine();
  let frame' = PM.pulse_heap_sig.as_slprop fr in
  lift_eq p;
  assert (PM.pulse_heap_sig.interp p m0.pulse_mem);
  assert (fr m1.pulse_mem);
  PM.pulse_heap_sig.interp_as fr;
  assert (PM.pulse_heap_sig.interp frame' m1.pulse_mem);
  assert (pm_sep.disjoint m0.pulse_mem m1.pulse_mem);
  assert (pm_sep.join m0.pulse_mem m1.pulse_mem == c.pulse_mem);
  PM.pulse_heap_sig.star_equiv p frame' c.pulse_mem;
  assert (PM.interp (p `PM.star` frame') pulse_mem);
  introduce forall (q:PM.slprop) (m':_).
      PM.interp (q `PM.star` frame') m' ==>
      interpret (lift q `star` frame) { w with pulse_mem=m'}
  with introduce _ ==> _
  with _ . (
    PM.pulse_heap_sig.star_equiv q frame' (pm_core_of m');
    eliminate exists (m0' m1':pulse_core_mem).
        pm_sep.disjoint m0' m1' /\
        pm_core_of m' == pm_sep.join m0' m1' /\
        PM.pulse_heap_sig.interp q m0' /\
        PM.pulse_heap_sig.interp frame' m1'
    returns _
    with _ . ( 
      assert (fr m1');
      let mres = core_of { w with pulse_mem = m'} in
      introduce exists (ml mr:core_mem).
        disjoint ml mr /\
        mres == join ml mr /\
        interp (lift q) ml /\
        interp frame mr
      with ({ pulse_mem=m0'; istore=m0.istore})
            ({ pulse_mem=m1'; istore=m1.istore })
      and  (
        let ml = { pulse_mem=m0'; istore=m0.istore } in
        let mr = { pulse_mem=m1'; istore=m1.istore } in
        assert (pm_sep.disjoint m0' m1');
        assert (pm_sep.join m0' m1' == pm_core_of m');
        assert (istore_disjoint m0.istore m1.istore);
        assert (istore_join m0.istore m1.istore == c.istore);
        assert (c.istore == mres.istore);
        assert (interp frame mr);
        lift_eq q;
        assert (interp (lift q) ml)
      );
      star_equiv (lift q) frame mres;
      assert (interp (lift q `star` frame) mres)
    )
  );
  let frame' =
    FStar.IndefiniteDescription.indefinite_description_tot 
      PM.slprop
      (fun frame' ->
       PM.interp (p `PM.star` frame') pulse_mem /\
        (forall (q:PM.slprop) (m':_).
          PM.interp (q `PM.star` frame') m' ==>
          interpret (lift q `star` frame) { w with pulse_mem=m'}))
  in
  let frame' : PM.slprop = PM.pulse_heap_sig.non_info_slprop frame' in
  (| frame', (fun q m' -> ())|)

let is_ghost_action_istore_refl (i:istore)
: Lemma (is_ghost_action_istore i i)
= assert (FStar.Preorder.reflexive is_ghost_action_istore)

let is_ghost_action_refl (m:mem)
: Lemma (is_ghost_action m m)
= is_ghost_action_istore_refl m.istore;
  PM.ghost_action_preorder ()

let is_ghost_action_trans (m0 m1 m2:mem)
: Lemma 
  (requires is_ghost_action m0 m1 /\ is_ghost_action m1 m2)
  (ensures is_ghost_action m0 m2)
= assert (FStar.Preorder.transitive is_ghost_action_istore);
  PM.ghost_action_preorder ()

let lift_mem_action #a #mg #ex #pre #post
                   (pm_act:PM._pst_action_except a mg (lower_inames ex) pre post)
: _act_except a (if mg then GHOST else ATOMIC) ex (lift pre) (fun x -> lift (post x))
= fun frame 
      (w0:mem {
        inames_ok ex w0 /\
        is_full w0 /\
        interpret (lift pre `star` frame `star` mem_invariant ex w0) w0
      }) -> 
    let { pulse_mem; istore } = w0 in
    calc (==) {
      lift pre `star` frame `star` mem_invariant ex w0;
    (==) { }
      lift pre `star` frame `star` (lift (PM.mem_invariant (lower_inames ex) pulse_mem) `star`
                                    istore_invariant ex istore);
    (==) { sep_laws () }
      (lift pre `star` lift (PM.mem_invariant (lower_inames ex) pulse_mem)) `star`
      (frame `star` istore_invariant ex istore);
    (==) { lift_star_eq pre (PM.mem_invariant (lower_inames ex) pulse_mem) }
      lift (pre `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem) `star`
      (frame `star` istore_invariant ex istore);
    };
    let (| frame', restore |) = 
      pin_frame (pre `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem)
                (frame `star` istore_invariant ex istore)
                w0
    in
    calc (==) {
      pre `PM.star`
      PM.mem_invariant (lower_inames ex) pulse_mem `PM.star`
      frame';
    (==) { pm_sep_laws () }
      pre `PM.star` frame' `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem;
    };
    let x, pulse_mem' = pm_act frame' pulse_mem in
    calc (==) {
      (post x `PM.star` frame' `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem');
    (==) { pm_sep_laws () }
      (post x `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem') `PM.star` frame';
    };
    restore (post x `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem') pulse_mem';
    let w1 =  { w0 with pulse_mem = pulse_mem' } in
    calc (==) {
      lift (post x `PM.star` PM.mem_invariant (lower_inames ex) pulse_mem') `star`
      (frame `star` istore_invariant ex istore);
    (==) { lift_star_eq (post x) (PM.mem_invariant (lower_inames ex) pulse_mem');
           sep_laws () }
      lift (post x) `star`
      frame `star`
      (lift (PM.mem_invariant (lower_inames ex) pulse_mem') `star` istore_invariant ex istore);
    (==) { }
      lift (post x) `star`
      frame `star`
      (mem_invariant ex w1);
    };
    is_ghost_action_istore_refl w0.istore;
    (x, w1)


let intro_star (p q:slprop) (m0 m1:core_mem)
: Lemma
  (requires disjoint m0 m1 /\ interp p m0 /\ interp q m1)
  (ensures interp (p `star` q) (join m0 m1))
= star_equiv p q (join m0 m1)


let later_elim (e:inames) (p:slprop) 
: ghost_act unit e (later p `star` later_credit 1) (fun _ -> p)
= fun frame s0 ->
    let open FStar.Ghost in
    sep_laws();
    let m1, m2, m3 = split_mem3 (later_credit 1) (later p) (frame `star` mem_invariant e s0) (core_of s0) in
    interp_later_credit 1 m1;
    assert (interp (later_credit 1) m1);
    disjoint_join_levels m2 m3;
    disjoint_join_levels m1 (join m2 m3);
    assert (level m1 > 0 /\ level m2 > 0);
    let m1' : erased core_mem = age1 m1 in
    let m2' : erased core_mem = age1 m2 in
    let m31, m32 = split_mem frame (mem_invariant e s0) m3 in
    let m31' : erased core_mem = age1 m31 in
    age_hereditary frame m31;
    let m32' : erased core_mem = age1 m32 in
    disjoint_join_levels m1 (join m2 m3);
    disjoint_join_levels m2 m3;
    disjoint_join_levels m31 m32;
    assert (level m32 == level m3);
    assert (level m32 == level m1);
    assert (level m1 == level (core_of s0));
    assert (level m1 > 1);
    mem_invariant_age e s0 m32;
    age_disjoint m31 m32;
    intro_star frame (mem_invariant e (age_mem s0)) m31' m32';
    let m3' : erased core_mem = age1 m3 in
    assert (interp (frame `star` mem_invariant e (age_mem s0)) m3');
    age_later p m2;
    assert (interp p m2');
    age_level m1;
    assert (level m1' == level (core_of s0) - 1);
    assert (credits m1' > 0);
    let m1'' : erased core_mem = spend m1' in
    age_disjoint m2 m3;
    age_disjoint m1 (join m2 m3);
    spend_disjoint m1' (join m2' m3');
    let m : erased core_mem = join m1'' (join m2' m3') in
    intro_star p (frame `star` mem_invariant e (age_mem s0)) m2' m3';
    emp_equiv m1'';
    intro_star emp (p `star` (frame `star` mem_invariant e (age_mem s0))) m1'' (join m2' m3');
    assert (interp (p `star` (frame `star` mem_invariant e (age_mem s0))) m);
    calc (==) {
      level m;
    (==) { disjoint_join_levels m1'' (join m2' m3') }
      level m1'';
    (==) { spend_lemma m1' }
      level m1';
    (==) { }
      level (core_of s0) - 1;
    };
    calc (==) {
      credits m;
    (==) { disjoint_join_levels m1'' (join m2' m3') }
      credits m1'' + credits (join m2' m3');
    (==) { spend_lemma m1' }
      credits m1' - 1 + credits (join m2' m3');
    (==) { age_level m1 }
      credits m1 + credits (join m2' m3') - 1;
    (==) { 
         calc (==) {
            credits (join m2' m3');
          (==) {disjoint_join_levels m2' m3'}
            credits m2' + credits m3';
          (==) {age_level m2; age_level m3}
            credits m2 + credits m3;
          (==) {disjoint_join_levels m2 m3}
            credits (join m2 m3);
          }
        }
      credits m1 + credits (join m2 m3) - 1;
    (==) {}
      credits (core_of s0) - 1;
    };
    assert (reveal m == spend (age1 (core_of s0)));
    let s1 = age_mem s0 in
    let s2 = spend_mem s1 in
    assert (reveal m == core_of s2);
    is_ghost_action_trans s0 s1 s2;
    assert (is_ghost_action s0 s2);
    mem_invariant_spend e s1;
    inames_ok_update e s0 s2;
    assert (inames_ok e s0 <==> inames_ok e s2);
    assert (level_decreases_by_spent_credits s0 s2);
    assert (is_full s2);
    (), s2

let buy (e:inames) (n:FStar.Ghost.erased nat)
: buy_act unit e emp (fun _ -> later_credit n)
= fun frame s0 ->
    sep_laws();
    let m0, m1 = split_mem emp (frame `star` mem_invariant e s0) (core_of s0) in
    let m0' : erased core_mem = buy n m0 in
    buy_lemma n m0;
    interp_later_credit n m0';
    assert (interp (later_credit n) m0');
    buy_disjoint n m0 m1;
    assert (disjoint m0' m1);
    intro_star (later_credit n) (frame `star` mem_invariant e s0) m0' m1;
    let m' : erased core_mem = join m0' m1 in
    let s1 = buy_mem n s0 in
    assert (reveal m' == core_of s1);
    mem_invariant_buy e n s0;
    inames_ok_update e s0 s1;
    (), s1


let dup_inv (e:inames) (i:iref) (p:slprop)
: ghost_act unit e 
    (inv i p) 
    (fun _ -> inv i p `star` inv i p)
= fun frame s0 ->
    sep_laws();
    dup_inv_equiv i p;
    is_ghost_action_refl s0;
    (), s0

let intro_read_inv (i:iref) (p frame:slprop) (m:core_mem)
: Lemma
  (requires 
    iname_ok i m /\
    level m > 0 /\
    interp (inv i p `star` later p `star` frame) m)
  (ensures interp (inv i p `star` later (read_inv i m) `star` frame) m)
= sep_laws();
  dup_inv_equiv i p;
  let sl, sr = split_mem (later p `star` inv i p) (inv i p `star` frame) m in
  disjoint_join_levels sl sr;
  destruct_star (later p) (inv i p) sl;
  inames_ok_single i p sl;
  read_inv_equiv i sl p;
  assert (interp (later (read_inv i sl)) sl);
  read_inv_disjoint i sl sr;
  intro_star (later (read_inv i m)) (inv i p `star` frame) sl sr

let elim_read_inv (i:iref) (p frame:slprop) (m:core_mem)
: Lemma
  (requires 
    iname_ok i m /\
    level m > 0 /\
    interp (inv i p `star` later (read_inv i m) `star` frame) m)
  (ensures interp (inv i p `star` later p `star` frame) m)
= sep_laws();
  dup_inv_equiv i p;
  let sl, sr = split_mem (later (read_inv i m) `star` inv i p) (inv i p `star` frame) m in
  disjoint_join_levels sl sr;
  destruct_star (later (read_inv i m)) (inv i p) sl;
  inames_ok_single i p sl;
  read_inv_disjoint i sl sr;
  assert (interp (later (read_inv i sl) `star` inv i p) sl);
  destruct_star (later (read_inv i m)) (inv i p) sl;
  read_inv_equiv i sl p;
  assert (interp (later p) sl);
  intro_star (later p) (inv i p `star` frame) sl sr

let intro_read_inv_later (i:iref) (p frame:slprop) (m:core_mem)
: Lemma
  (requires 
    iname_ok i m /\
    level m > 0 /\
    interp (inv i p `star` p `star` frame) m)
  (ensures interp (inv i p `star` later (read_inv i m) `star` frame) m)
= sep_laws();
  let s1, s2, s3 = split_mem3 (inv i p) p frame m in
  intro_later p s2;
  intro_star (later p) frame s2 s3;
  intro_star (inv i p) (later p `star` frame) s1 (join s2 s3);
  intro_read_inv i p frame m

let fresh_invariant (e:inames) (p:slprop) (ctx:FStar.Ghost.erased (list iref))
: ghost_act (i:iref{fresh_wrt ctx i}) e p (fun i -> inv i p)
= fun frame s0 ->
    let (| i, s0' |) = fresh_inv p s0 ctx in
    let s1 = join_mem s0 s0' in
    disjoint_join_levels (core_of s0) (core_of s0');
    mem_invariant_disjoint e (single i) (p `star` frame) (inv i p) s0 s0';
    assert (interp 
              ((p `star` frame) `star` inv i p `star`
                (mem_invariant (GhostSet.union e (single i)) s1))
              (core_of s1));
    sep_laws ();
    assert (GhostSet.union e (single i) `GhostSet.equal` (add_inv e i));
    inames_ok_istore_dom e s0;
    inames_ok_istore_dom (single i) s0';
    assert (~(mem_inv e i));
    assert (interp 
              (inv i p `star`
              (frame `star` p `star` mem_invariant (add_inv e i) s1))
              (core_of s1));
    destruct_star_l (inv i p)
                    (frame `star` p `star` mem_invariant (add_inv e i) s1)
                    (core_of s1);
    inames_ok_single i p (core_of s1);
    assert (iname_ok i (core_of s1));
    intro_read_inv_later i p (frame `star` mem_invariant (add_inv e i) s1) (core_of s1);
    assert (interp (inv i p `star`
                    frame `star`
                    (mem_invariant (add_inv e i) s1 `star`
                    later (read_inv i (core_of s1)))) (core_of s1));
    mem_invariant_equiv e s1 i;
    assert (interp (inv i p `star` frame `star` mem_invariant e s1) (core_of s1));    
    assert (is_ghost_action s0 s1);
    inames_ok_disjoint e (single i) s0 s0';
    inames_ok_union e (single i) s1;
    assert (inames_ok e s1);
    assert (is_full s1);
    disjoint_join_levels (core_of s0) (core_of s0');
    assert (level (core_of s0) == level (core_of s0'));
    assert (level_decreases_by_spent_credits s0 s1);
    i, s1

let new_invariant (e:inames) (p:slprop)
: ghost_act iref e p (fun i -> inv i p)
= fresh_invariant e p []

let iname_ok_frame (i:iref) (p:slprop) (frame:slprop) (m:core_mem)
: Lemma
  (requires interp (inv i p `star` frame) m)
  (ensures iname_ok i m)
= destruct_star_l (inv i p) frame m;
  inames_ok_single i p m

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (#ak:action_kind {not (BUY? ak)})
                   (i:iref{not (mem_inv opened_invariants i)})
                   (f:_act_except a ak
                        (add_inv opened_invariants i) 
                        (later p `star` fp)
                        (fun x -> later p `star` fp' x))
: _act_except a ak opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)
= fun frame s0 ->
    sep_laws();
    iname_ok_frame i p (fp `star` frame `star` mem_invariant opened_invariants s0) (core_of s0);
    assert (iname_ok i (core_of s0));
    assert (inames_ok (single i) s0);
    mem_invariant_equiv opened_invariants s0 i;
    assert (interp (inv i p `star` fp `star` frame `star` 
              (mem_invariant (add_inv opened_invariants i) s0 `star` later (read_inv i (core_of s0)))) (core_of s0));
    elim_read_inv i p (fp `star` frame `star` mem_invariant (add_inv opened_invariants i) s0) (core_of s0);
    inames_ok_union (single i) opened_invariants s0;
    assert (inames_ok (add_inv opened_invariants i) s0);
    assert (interp ((later p `star` fp) 
                    `star` (frame `star` inv i p)
                    `star` mem_invariant (add_inv opened_invariants i) s0)
                    (core_of s0));
    let x, s1 = f (frame `star` inv i p) s0 in
    inames_ok_union (single i) opened_invariants s1;
    assert (inames_ok (single i) s1);
    assert (iname_ok i (core_of s1));
    intro_read_inv i p (fp' x `star` frame `star` mem_invariant (add_inv opened_invariants i) s1) (core_of s1);
    assert (interp ((inv i p `star` fp' x) 
                    `star` frame
                    `star` (mem_invariant (add_inv opened_invariants i) s1 `star` later (read_inv i (core_of s1))))
                    (core_of s1));
    mem_invariant_equiv opened_invariants s1 i;
    assert (interp ((inv i p `star` fp' x) 
                    `star` frame
                    `star` mem_invariant opened_invariants s1)
                    (core_of s1));
    inames_ok_union (single i) opened_invariants s1;
    x, s1


let frame (#a:Type)
          (#ak:action_kind)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:_act_except a ak opened_invariants pre post)
: _act_except a ak opened_invariants (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> sep_laws (); f (frame `star` frame')

let witness_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: ghost_act (erased a) opened_invariants
           (op_exists_Star p)
           (fun x -> p x)
= fun frame s0 ->
    sep_laws();
    let m1, m2 = split_mem (op_exists_Star p) (frame `star` mem_invariant opened_invariants s0) (core_of s0) in 
    interp_exists p;
    eliminate exists x. interp (p x) m1
    returns exists x. interp (p x `star` (frame `star` mem_invariant opened_invariants s0)) (core_of s0)
    with _. (
        star_equiv (p x) (frame `star` mem_invariant opened_invariants s0) (core_of s0)
    );
    let x =
      FStar.IndefiniteDescription.indefinite_description_tot
        a 
        (fun x -> interpret (p x `star` (frame `star` mem_invariant opened_invariants s0)) s0)
    in
    is_ghost_action_refl s0;
    x, s0

let intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
: ghost_act unit opened_invariants
  (p x)
  (fun _ -> op_exists_Star p)
= fun frame s0 ->
    sep_laws();
    let m1, m2 = split_mem (p x) (frame `star` mem_invariant opened_invariants s0) (core_of s0) in
    interp_exists p;
    star_equiv (op_exists_Star p) (frame `star` mem_invariant opened_invariants s0) (core_of s0);
    is_ghost_action_refl s0;
    (), s0

let raise_exists (#opened_invariants:_) (#a:Type u#a) (p:a -> slprop)
: ghost_act unit opened_invariants
    (op_exists_Star p)
    (fun _a -> op_exists_Star #(U.raise_t u#a u#b a) (U.lift_dom u#a u#_ u#b p))
= fun frame s0 ->
    let x, s1 = witness_exists #opened_invariants #a p frame s0 in
    sep_laws();
    let m1, m2 = split_mem (p x) (frame `star` mem_invariant opened_invariants s1) (core_of s1) in
    assert (interp ((U.lift_dom p) (U.raise_val u#a u#b (reveal x))) m1);
    interp_exists (U.lift_dom u#a u#_ u#b p);
    assert (interp (op_exists_Star #(U.raise_t u#a u#b a) (U.lift_dom p)) m1);
    star_equiv (op_exists_Star #(U.raise_t u#a u#b a) (U.lift_dom p)) (frame `star` mem_invariant opened_invariants s1) (core_of s1);
    (), s1

let elim_pure (#opened_invariants:_) (p:prop)
: ghost_act (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)
= fun frame s0 ->
    sep_laws();
    let m1, m2 = split_mem (pure p) (frame `star` mem_invariant opened_invariants s0) (core_of s0) in
    interp_pure p m1;
    emp_equiv m1;
    star_equiv emp (frame `star` mem_invariant opened_invariants s0) (core_of s0);
    is_ghost_action_refl s0;
    (), s0

let intro_pure (#opened_invariants:_) (p:prop) (_:squash p)
: ghost_act unit opened_invariants emp (fun _ -> pure p)
= fun frame s0 -> 
    sep_laws();
    let m1, m2 = split_mem emp (frame `star` mem_invariant opened_invariants s0) (core_of s0) in
    interp_pure p m1;
    star_equiv (pure p) (frame `star` mem_invariant opened_invariants s0) (core_of s0);
    is_ghost_action_refl s0;
    (), s0

let drop (#opened_invariants:_) (p:slprop)
: ghost_act unit opened_invariants p (fun _ -> emp)
= fun frame s0 -> 
    sep_laws();
    let m1, m2 = split_mem p (frame `star` mem_invariant opened_invariants s0) (core_of s0) in
    emp_equiv m1;
    star_equiv emp (frame `star` mem_invariant opened_invariants s0) (core_of s0);
    is_ghost_action_refl s0;
    (), s0

let lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:HeapSig.non_info a)
      (f:erased (ghost_act a opened_invariants p q))
: ghost_act a opened_invariants p q
= fun frame s0 ->
    let result : erased (a & full_mem) = hide ((reveal f) frame s0) in
    let res : a = ni_a (hide (fst result)) in
    let s1 : full_mem = update_ghost s0 (hide (snd result)) in
    res, s1