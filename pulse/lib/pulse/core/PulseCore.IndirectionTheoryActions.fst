module PulseCore.IndirectionTheoryActions
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt
module HST = PulseCore.HoareStateMonad

assume
val pm_sep_laws () : squash (
  PulseCore.Semantics.(
    associative PM.star /\
    commutative PM.star /\
    is_unit PM.emp PM.star
  )
)

let pm_sep : PulseCore.HeapSig.separable pulse_mem = PM.pulse_heap_sig.sep
let pm_core_of (m:pulse_mem) : pulse_core_mem = PM.pulse_heap_sig.sep.core_of m


let pin_frame (p:pm_slprop) (frame:slprop) 
              (w:mem { interpret (lift p `star` frame) w })
: frame':pm_slprop { PM.interp (p `PM.star` frame')  w.pulse_mem } &
  (q:pm_slprop -> m':pulse_mem ->
    Lemma 
      (requires PM.interp (q `PM.star` frame') m')
      (ensures interpret (lift q `star` frame) { w with pulse_mem = m'}))
= let c = core_of w in
  let { pulse_mem; istore } = w in
  star_equiv (lift p) frame c;
  eliminate exists m0 m1.
      disjoint m0 m1 /\
      c == join m0 m1 /\
      interp (lift p) m0 /\
      interp frame m1
  returns
    exists frame'. 
      PM.interp (p `PM.star` frame') pulse_mem /\
      (forall (q:PM.slprop) (m':_).
        PM.interp (q `PM.star` frame') m' ==>
        interpret (lift q `star` frame) { w with pulse_mem=m'})
  with _ . (
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
        let right = { pulse_mem = s1; istore = m1.istore } in
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

let lift_mem_action #a #mg #ex #pre #post
                   (pm_act:PM._pst_action_except a mg (lower_inames ex) pre post)
: _act_except a mg ex (lift pre) (fun x -> lift (post x))
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

let later_elim (e:inames) (p:slprop) 
: ghost_act unit e (later p `star` later_credit 1) (fun _ -> p)
= admit()

let buy (e:inames) (n:nat)
: act unit e emp (fun _ -> later_credit n)
= admit()

let is_ghost_action_refl (m:mem)
: Lemma (is_ghost_action m m)
= is_ghost_action_istore_refl m.istore;
  PM.ghost_action_preorder ()

let dup_inv (e:inames) (i:iref) (p:slprop)
: ghost_act unit e 
    (inv i p) 
    (fun _ -> inv i p `star` inv i p)
= fun frame s0 ->
    sep_laws();
    dup_inv_equiv i p;
    is_ghost_action_refl s0;
    (), s0

let new_invariant (e:inames) (p:slprop)
: ghost_act iref e p (fun i -> inv i p)
= admit()

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (#maybe_ghost:bool)
                   (i:iref{not (mem_inv opened_invariants i)})
                   (f:_act_except a maybe_ghost
                        (add_inv opened_invariants i) 
                        (later p `star` fp)
                        (fun x -> later p `star` fp' x))
: _act_except a maybe_ghost opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)
= fun frame s0 ->
    sep_laws();
    destruct_star_l (inv i p) (fp `star` frame `star` mem_invariant opened_invariants s0) (core_of s0);
    mem_invariant_equiv opened_invariants s0 i p;
    inames_ok_union (single i) opened_invariants s0;
    let x, s1 = f (frame `star` inv i p) s0 in
    destruct_star_l (inv i p) (later p `star` fp' x `star` frame `star` mem_invariant (add_inv opened_invariants i) s1) (core_of s1);
    inames_ok_union (single i) opened_invariants s1;
    mem_invariant_equiv opened_invariants s1 i p;
    x, s1


let frame (#a:Type)
          (#maybe_ghost:bool)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:_act_except a maybe_ghost opened_invariants pre post)
: _act_except a maybe_ghost opened_invariants (pre `star` frame) (fun x -> post x `star` frame)
= fun frame' -> sep_laws (); f (frame `star` frame')

val witness_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: ghost_act (erased a) opened_invariants
           (op_exists_Star p)
           (fun x -> p x)

val intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
: ghost_act unit opened_invariants
  (p x)
  (fun _ -> op_exists_Star p)

val raise_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: ghost_act unit opened_invariants
    (op_exists_Star p)
    (fun _a -> op_exists_Star #(U.raise_t a) (U.lift_dom p))

val elim_pure (#opened_invariants:_) (p:prop)
: ghost_act (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)

val intro_pure (#opened_invariants:_) (p:prop) (_:squash p)
: ghost_act unit opened_invariants emp (fun _ -> pure p)

val drop (#opened_invariants:_) (p:slprop)
: ghost_act unit opened_invariants p (fun _ -> emp)

let non_info a = x:erased a -> y:a { reveal x == y}

val lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:non_info a)
      (f:erased (ghost_act a opened_invariants p q))
: ghost_act a opened_invariants p q