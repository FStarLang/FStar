module Steel.C.Ref
open FStar.PCM
open FStar.FunctionalExtensionality
open Steel.C.PCM
open Steel.C.Connection

#push-options "--print_universes"

noeq type ref (a: Type u#1) #b (q: pcm b): Type = {
  p: pcm a;
  pl: connection p q;
  r: Steel.Memory.ref a p;
}

let mpts_to (#p: pcm 'a) (r: Steel.Memory.ref 'a p) = Steel.PCMReference.pts_to r

open Steel.Effect

val pts_to
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p) ([@@@smt_fallback] v: Ghost.erased b)
: vprop

let ref_focus
  (#a:Type) (#b:Type) (#c:Type) (#p: pcm b)
  (r: ref a p) (#q: pcm c) (l: connection p q)
: ref a q
= {p = r.p; pl = connection_compose r.pl l; r = r.r}

let ref_focus_comp (r: ref 'a 'p) (l: connection 'p 'q) (m: connection 'q 'r)
: Lemma (ref_focus (ref_focus r l) m == ref_focus r (l `connection_compose` m))
  [SMTPatOr [
    [SMTPat (ref_focus (ref_focus r l) m)]; 
    [SMTPat (ref_focus r (l `connection_compose` m))]]]
= connection_eq
    ((r.pl `connection_compose` l) `connection_compose` m)
    (r.pl `connection_compose` (l `connection_compose` m))

module A = Steel.Effect.Atomic

val focus (#p: pcm 'b) (r: ref 'a p)
  (#q: pcm 'c)
  (l: connection p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: Steel (ref 'a q)
    (r `pts_to` s)
    (fun r' -> r' `pts_to` x)
    (fun _ -> Ghost.reveal s == l.conn_small_to_large.morph x)
    (fun _ r' _ -> r' == ref_focus r l)

module M = Steel.Memory

val unfocus (#opened:M.inames)
  (#p: pcm 'b)
  (#q: pcm 'c)
  (r: ref 'a q) (r': ref 'a p)
  (l: connection p q) (x: Ghost.erased 'c)
: A.SteelGhost unit opened
    (r `pts_to` x)
    (fun _ -> r' `pts_to` l.conn_small_to_large.morph x)
    (requires fun _ -> r == ref_focus r' l)
    (ensures fun _ _ _ -> True)

val split (#a:Type) (#b:Type) (#p: pcm b) (r: ref a p) (xy x y: Ghost.erased b)
: Steel unit
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> composable p x y /\ xy == Ghost.hide (op p x y))
    (fun _ _ _ -> True)

val gather (#a:Type) (#b:Type) (#p: pcm b) (r: ref a p) (x y: Ghost.erased b)
: SteelT (_:unit{composable p x y})
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op p x y)

val ref_read
  (#a:Type) (#b:Type) (#p: pcm b) (#x: Ghost.erased b) (r: ref a p)
: Steel b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> compatible p x x')

val ref_upd
  (#a:Type) (#b:Type) (#p: pcm b)
  (r: ref a p) (x: Ghost.erased b { ~ (Ghost.reveal x == one p) }) (y: Ghost.erased b) (f: frame_preserving_upd p x y)
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)

let is_unit (#a: Type u#a) (p:pcm a) 
  (x:a)
:  Lemma (composable p x p.FStar.PCM.p.one /\
         op p x p.FStar.PCM.p.one == x)
= p.is_unit x

let base_fpu
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a)
  (y: a)
: Pure (frame_preserving_upd p x y)
  (requires (exclusive p x /\ p.refine y))
  (ensures (fun _ -> True))
= fun _ ->
  Classical.forall_intro (is_unit p);
  compatible_refl p y;
  y

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

let opt_comp (x y: option 'a): prop = match x, y with
  | None, _ | _, None -> True
  | _, _ -> False

let opt_op (x: option 'a) (y: option 'a{opt_comp x y}): option 'a = match x, y with
  | None, z | z, None -> z

let opt_pcm #a : pcm (option a) = {
  FStar.PCM.p = {composable = opt_comp; op = opt_op; one = None};
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> Some? x == true);
}

let exclusive_opt
  (#a: Type)
  (x: option a)
: Lemma
  (exclusive opt_pcm x <==> ((exists (y: a) . True) ==> Some? x))
=
  match x with
  | None ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (y: a). True)
    then begin
      let y = FStar.IndefiniteDescription.indefinite_description_ghost a (fun _ -> True) in
      assert (composable opt_pcm x (Some y))
    end else begin
      let phi
        (frame: option a)
      : Lemma
        (frame == None)
      = match frame with
        | None -> ()
        | Some z -> assert (exists (y: a) . True)
      in
      Classical.forall_intro phi
    end
  | Some _ -> ()

let opt_pcm_fpu
  (#a: Type)
  (x: Ghost.erased (option a) { ~ (Ghost.reveal x == one opt_pcm) })
  (y: a)
: Tot (frame_preserving_upd opt_pcm x (Some y))
= base_fpu opt_pcm x (Some y)

let opt_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some y)
  (requires (fun _ -> Some? x))
  (ensures (fun _ _ _ -> True))

//let opt_pcm_write r x y
= ref_upd r x (Some y) (opt_pcm_fpu x y)

let opt_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Ghost.reveal x == Some y))

//let opt_pcm_read r x
= let y' = ref_read r in
  assert (Ghost.reveal x == y');
  Some?.v y'
  
/// Fractional permissions: from Steel.HigherReference
open Steel.FractionalPermission

let fractional (a:Type u#1) = option (a & perm)

let fractional_composable #a : symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ sum_perm p0 p1 `lesser_equal_perm` full_perm

let fractional_compose #a (f0:fractional a) (f1:fractional a{fractional_composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, sum_perm p0 p1)

let pcm_frac #a : pcm (fractional a) = {
  FStar.PCM.p = {
         composable = fractional_composable;
         op = fractional_compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> Some? x /\ snd (Some?.v x) == full_perm)
}

let frac_pcm_fpu
  (#a: Type)
  (x: Ghost.erased (fractional a) { Some? x /\ snd (Some?.v x) == full_perm })
  (y: a)
: Tot (frame_preserving_upd pcm_frac x (Some (y, full_perm)))
= base_fpu pcm_frac x (Some (y, full_perm))

let frac_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some (y, full_perm))
  (requires (fun _ -> Some? x /\ snd (Some?.v x) == full_perm))
  (ensures (fun _ _ _ -> True))

//let frac_pcm_write r x y
= ref_upd r x (Some (y, full_perm)) (frac_pcm_fpu x y)

let frac_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Some? x /\ y == fst (Some?.v (Ghost.reveal x))))

//let frac_pcm_read r x
= let y' = ref_read r in
  assert (Some? y' /\ fst (Some?.v (Ghost.reveal x)) == fst (Some?.v y'));
  fst (Some?.v y')

let exclusive_frac
  (#a: Type)
  (x: option (a & perm))
: Lemma
  (exclusive pcm_frac x <==> ((exists (y: a) . True) ==> (Some? x /\ full_perm `lesser_equal_perm` snd (Some?.v x))))
= match x with
  | None ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (y: a). True)
    then begin
      let y = FStar.IndefiniteDescription.indefinite_description_ghost a (fun _ -> True) in
      let frame = Some (y, full_perm) in
      assert (~ (frame == one pcm_frac));
      assert (composable pcm_frac x frame)
    end else begin
      let phi
        (frame: option (a & perm))
      : Lemma
        (frame == None)
      = match frame with
        | None -> ()
        | Some (z, _) -> assert (exists (y: a) . True)
      in
      Classical.forall_intro phi
    end
  | Some (y, p) ->
    assert (exists (z: a) . True);
    if FStar.StrongExcludedMiddle.strong_excluded_middle (full_perm `lesser_equal_perm` p)
    then ()
    else begin
      let frame = Some (y, MkPerm (let open FStar.Real in one -. p.v)) in
      assert (composable pcm_frac x frame);
      assert (~ (frame == one pcm_frac))
    end

/// Uninitialized

noeq
type uninit_t (a: Type)
= | Uninitialized
  | InitOrUnit: a -> uninit_t a

let uninit_composable
  (#a: Type)
  (p: pcm a)
: Tot (symrel (uninit_t a))
= fun u1 u2 ->
  match u1, u2 with
  | Uninitialized, InitOrUnit x
  | InitOrUnit x, Uninitialized
    -> x == one p
  | InitOrUnit x1, InitOrUnit x2
    -> composable p x1 x2
  | _ -> False

let uninit_compose
  (#a: Type)
  (p: pcm a)
  (u1: uninit_t a)
  (u2: uninit_t a { uninit_composable p u1 u2 })
: Tot (uninit_t a)
= match u1, u2 with
  | Uninitialized, _
  | _, Uninitialized
    -> Uninitialized
  | InitOrUnit x1, InitOrUnit x2
    -> InitOrUnit (op p x1 x2)

let uninit_refine
  (#a: Type)
  (p: pcm a)
  (x: uninit_t a)
: Tot prop
= match x with
  | Uninitialized -> True
  | InitOrUnit y -> p.refine y

let pcm_uninit #a (p: pcm a) : pcm (uninit_t a) = {
  FStar.PCM.p = {
         composable = uninit_composable p;
         op = uninit_compose p;
         one = InitOrUnit (one p);
      };
  comm = (fun _ _ ->
    Classical.forall_intro_2 p.comm
  );
  assoc = (fun x1 x2 x3 ->
    Classical.forall_intro_3 p.assoc;
    Classical.forall_intro (is_unit p)
  );
  assoc_r = (fun _ _ _ -> 
    Classical.forall_intro_3 p.assoc_r;
    Classical.forall_intro (is_unit p)
  );
  is_unit = (fun _ -> Classical.forall_intro (is_unit p));
  refine = uninit_refine p;
}

let value_to_uninit
  (#a: Type)
  (p: pcm a)
: Tot (morphism p (pcm_uninit p))
= mkmorphism
    (fun x -> InitOrUnit x)
    ()
    (fun _ _ -> ())

let uninit_to_value
  (#a: Type)
  (p: pcm a)
: Tot (morphism (pcm_uninit p) p)
= mkmorphism
    (fun x -> match x with InitOrUnit y -> y | _ -> one p)
    ()
    (fun _ _ -> Classical.forall_intro (is_unit p))

let uninit_conn_fpu'
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a { ~ (Ghost.reveal x == one p) })
  (y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
  (v: uninit_t a {
    (pcm_uninit p).refine v /\
    compatible (pcm_uninit p) ((value_to_uninit p).morph x) v
  })
: Tot (uninit_t a)
=
  let InitOrUnit x' = v in
  InitOrUnit (f x')

let uninit_conn_fpu_prop
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a { ~ (Ghost.reveal x == one p) })
  (y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
  (v: uninit_t a {
    (pcm_uninit p).refine v /\
    compatible (pcm_uninit p) ((value_to_uninit p).morph x) v
  })
: Lemma
  (let v_new = uninit_conn_fpu' p x y f v in
    (pcm_uninit p).refine v_new /\
    compatible (pcm_uninit p) ((value_to_uninit p).morph y) v_new /\
    (forall (frame:_{composable (pcm_uninit p) ((value_to_uninit p).morph x) frame}).
       composable (pcm_uninit p) ((value_to_uninit p).morph y) frame /\
       (op (pcm_uninit p) ((value_to_uninit p).morph x) frame == v ==> op (pcm_uninit p) ((value_to_uninit p).morph y) frame == v_new))
  )
= Classical.forall_intro (is_unit p);
  let y' = (value_to_uninit p).morph y in
  let InitOrUnit x' = v in
  let v_new = uninit_conn_fpu' p x y f v in
  let frame : a = compatible_elim p y (f x') in
  let frame' : uninit_t a = InitOrUnit frame in
  assert (composable (pcm_uninit p) y' frame');
  assert (op (pcm_uninit p) frame' y' == v_new);
  compatible_intro (pcm_uninit p) y' v_new frame';
  assert (forall (frame:_{composable (pcm_uninit p) ((value_to_uninit p).morph x) frame}).
       composable (pcm_uninit p) ((value_to_uninit p).morph y) frame /\
       (op (pcm_uninit p) ((value_to_uninit p).morph x) frame == v ==> op (pcm_uninit p) ((value_to_uninit p).morph y) frame == v_new));
  ()

let uninit_conn_fpu
  (#a: Type)
  (p: pcm a)
  (x: Ghost.erased a { ~ (Ghost.reveal x == one p) })
  (y: Ghost.erased a)
  (f: frame_preserving_upd p x y)
: Tot (frame_preserving_upd (pcm_uninit p) ((value_to_uninit p).morph x) ((value_to_uninit p).morph y))
=
  fun v ->
    uninit_conn_fpu_prop p x y f v;
    uninit_conn_fpu' p x y f v

let uninit_conn
  (#a: Type)
  (p: pcm a)
: Tot (connection (pcm_uninit p) p)
= mkconnection
    (value_to_uninit p)
    (uninit_to_value p)
    ()
    (uninit_conn_fpu p)

let exclusive_uninit
  (#a: Type)
  (p: pcm a)
  (x: uninit_t a)
: Lemma
  (exclusive (pcm_uninit p) x <==> begin match x with
  | Uninitialized -> True
  | InitOrUnit z -> exclusive p z /\ (~ (z == one p))
  end)
= match x with
  | Uninitialized -> ()
  | InitOrUnit z ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (z == one p)
    then begin
      assert (composable (pcm_uninit p) x Uninitialized)
    end else
      let phi2
        frame
      : Lemma
        (requires (exclusive (pcm_uninit p) x /\ composable p z frame))
        (ensures (frame == one p))
        [SMTPat (composable p z frame)]
      = assert (composable (pcm_uninit p) x (InitOrUnit frame))
      in
      ()

let refine (a: Type) (p: (a -> Tot prop)) : Tot Type =
  (x: a { p x })

noeq
type sel_view
  (#carrier: Type u#a)
  (p: pcm carrier)
  (view: Type u#b)
= {
  to_view_prop: (carrier -> Tot prop);
  to_view: (refine carrier to_view_prop -> GTot view);
  to_carrier: (view -> GTot (refine carrier to_view_prop));
  to_carrier_not_one:
    (x: view) ->
    Lemma
    (~ (to_carrier x == one p));
  to_view_frame:
    (x: view) ->
    (frame: carrier) ->
    Lemma
    (requires (composable p (to_carrier x) frame))
    (ensures (to_view_prop (op p (to_carrier x) frame) /\ to_view (op p (to_carrier x) frame) == x));
}

let g_is_inverse_of (#a #b: Type) (g: (b -> GTot a)) (f: (a -> GTot b)) : Tot prop =
  (forall x . {:pattern (g (f x))} g (f x) == x)

let sel_view_inv
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type u#b)
  (vw: sel_view p view)
: Lemma
  (vw.to_view `g_is_inverse_of` vw.to_carrier)
  [SMTPat (has_type vw (sel_view p view))]
= let aux
    (x: view)
  : Lemma
    (vw.to_view (vw.to_carrier x) == x)
    [SMTPat (vw.to_view (vw.to_carrier x))]
  = is_unit p (vw.to_carrier x);
    vw.to_view_frame x (one p)
  in
  ()

let pts_to_view_explicit
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (vw: sel_view p c)
  (v: Ghost.erased c)
: Tot M.slprop
= hp_of (pts_to r (vw.to_carrier v))

val pts_to_view_explicit_witinv
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (vw: sel_view p c)
: Lemma
  (M.is_witness_invariant (pts_to_view_explicit r vw))

let pts_to_view_sl
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (vw: sel_view p c)
: Tot M.slprop
= M.h_exists (pts_to_view_explicit r vw)

let pts_to_view_sel'
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
: Tot (selector' c (pts_to_view_sl r vw))
= fun h ->
  let x = M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) h in
  Ghost.reveal (Ghost.reveal x)

let pts_to_view_depends_only_on
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
  (m0:M.hmem (pts_to_view_sl r vw)) (m1:M.mem{M.disjoint m0 m1})
: Lemma (pts_to_view_sel' r vw m0 == pts_to_view_sel' r vw (M.join m0 m1))
= let x = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) m0) in
  let y = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) (M.join m0 m1)) in
  pts_to_view_explicit_witinv r vw;
  M.elim_wi (pts_to_view_explicit r vw) x y (M.join m0 m1)

let pts_to_view_depends_only_on_core
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
  (m0:M.hmem (pts_to_view_sl r vw))
: Lemma (pts_to_view_sel' r vw m0 == pts_to_view_sel' r vw (M.core_mem m0))
= let x = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) m0) in
  let y = Ghost.reveal (M.id_elim_exists #(Ghost.erased c) (pts_to_view_explicit r vw) (M.core_mem m0)) in
  pts_to_view_explicit_witinv r vw;
  M.elim_wi (pts_to_view_explicit r vw) x y (M.core_mem m0)

let pts_to_view_sel
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
: Tot (selector c (pts_to_view_sl r vw))
= Classical.forall_intro_2 (pts_to_view_depends_only_on r vw);
  Classical.forall_intro (pts_to_view_depends_only_on_core r vw);
  pts_to_view_sel' r vw

[@@__steel_reduce__]
let pts_to_view'
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
: Tot vprop'
= {
  hp = pts_to_view_sl r vw;
  t = c;
  sel = pts_to_view_sel r vw;
}

[@@__steel_reduce__]
let pts_to_view 
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
: Tot vprop
= VUnit (pts_to_view' r vw)

let pts_to_view_intro_lemma
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (x: Ghost.erased b)
  (#c: Type0)
  (vw: sel_view p c)
  (y: Ghost.erased c) // necessary because to_view may erase information from x
  (m: M.mem)
: Lemma
  (requires (M.interp (hp_of (pts_to r x)) m) /\ vw.to_carrier y == Ghost.reveal x)
  (ensures (
    M.interp (pts_to_view_sl r vw) m /\
    pts_to_view_sel r vw m == Ghost.reveal y
  )) 
=
  M.intro_h_exists y (pts_to_view_explicit r vw) m;
  pts_to_view_explicit_witinv r vw

let pts_to_view_intro
  (#invs: _)
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (x: Ghost.erased b)
  (#c: Type0)
  (vw: sel_view p c)
  (y: Ghost.erased c) // necessary because to_view may erase information from x
: A.SteelGhost unit invs
    (pts_to r x)
    (fun _ -> pts_to_view r vw)
    (fun _ -> vw.to_carrier y == Ghost.reveal x)
    (fun _ _ h' ->
      h' (pts_to_view r vw) == Ghost.reveal y
    )
= A.change_slprop_2
    (pts_to r x)
    (pts_to_view r vw)
    y
    (fun m ->
      pts_to_view_intro_lemma r x vw y m
    )

let pts_to_view_elim_lemma
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
  (m: M.mem)
: Lemma
  (requires (M.interp (pts_to_view_sl r vw) m))
  (ensures (
    M.interp (hp_of (pts_to r (vw.to_carrier (pts_to_view_sel r vw m)))) m
  ))
=
  M.elim_h_exists (pts_to_view_explicit r vw) m;
  pts_to_view_explicit_witinv r vw

/// Introducing a dependent star for [v] and [q]
let intro_vdep2 (#opened:_)
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
  (x: t_of v)
: A.SteelGhost unit opened
    (v `star` q)
    (fun _ -> vdep v p)
    (requires (fun h -> h v == x /\ q == p x))
    (ensures (fun h _ h' ->
      let x2 = h' (vdep v p) in
      q == p (h v) /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    ))
=
  A.intro_vdep v q p

let pts_to_view_elim
  (#invs: _)
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type0)
  (vw: sel_view p c)
: A.SteelGhost (Ghost.erased b) invs
    (pts_to_view r vw)
    (fun res -> pts_to r res)
    (fun _ -> True)
    (fun h res _ ->
      Ghost.reveal res == vw.to_carrier (h (pts_to_view r vw))
    )
=
  let g : Ghost.erased c = A.gget (pts_to_view r vw) in
  let res : Ghost.erased b = Ghost.hide (vw.to_carrier g) in
  A.intro_pure (vw.to_carrier (Ghost.reveal g) == Ghost.reveal res);
  let f (x: t_of (pts_to_view r vw)) : Tot vprop = pure (vw.to_carrier x == Ghost.reveal res) in
  intro_vdep2
    (pts_to_view r vw)
    (pure (vw.to_carrier (Ghost.reveal g) == Ghost.reveal res))
    f
    (Ghost.reveal g);
  A.rewrite_slprop
    (vdep (pts_to_view r vw) f)
    (pts_to r res)
    (fun m ->
      interp_vdep_hp (pts_to_view r vw) f m;
      M.interp_star (hp_of (pts_to_view r vw)) (hp_of (f (sel_of (pts_to_view r vw) m))) m;
      M.pure_interp (vw.to_carrier (sel_of (pts_to_view r vw) m) == Ghost.reveal res) m;
      pts_to_view_elim_lemma r vw m
    );
  res

let opt_view
  (a: Type)
: Tot (sel_view (opt_pcm #a) a)
= {
  to_view_prop = (fun x -> Some? x == true);
  to_view = (fun x -> Some?.v x);
  to_carrier = (fun z  -> Some z);
  to_carrier_not_one = (fun _ -> ());
  to_view_frame = (fun x frame -> ());
}

let frac_view
  (a: Type)
  (p: perm)
: Tot (sel_view (pcm_frac #a) a)
= {
  to_view_prop = (fun x -> Some? x == true);
  to_view = (fun x -> let Some (v, _) = x in v);
  to_carrier = (fun v -> Some (v, p));
  to_carrier_not_one = (fun _ -> ());
  to_view_frame = (fun v frame -> ());
}

let uninit_view
  (#a: Type)
  (#p: pcm a)
  (#b: Type)
  (w: sel_view p b)
: Tot (sel_view #(uninit_t a) (pcm_uninit p) (uninit_t b))
= {
  to_view_prop = (fun x -> match x with
  | Uninitialized -> True
  | InitOrUnit x' -> w.to_view_prop x'
  );
  to_view = (fun x -> match x with
  | Uninitialized -> Uninitialized
  | InitOrUnit x' -> InitOrUnit (w.to_view x')
  );
  to_carrier = (fun v -> match v with
  | Uninitialized -> Uninitialized
  | InitOrUnit v' -> w.to_carrier_not_one v'; InitOrUnit (w.to_carrier v')
  );
  to_carrier_not_one = (fun v -> match v with
  | Uninitialized -> ()
  | InitOrUnit v' -> w.to_carrier_not_one v'
  );
  to_view_frame = (fun v frame -> match v with
  | Uninitialized -> ()
  | InitOrUnit v' -> w.to_carrier_not_one v'; let InitOrUnit frame' = frame in w.to_view_frame v' frame'
  );
}

let uninit_view_initialized
  (#a: Type)
  (#p: pcm a)
  (#b: Type)
  (w: sel_view p b)
: Tot (sel_view #(uninit_t a) (pcm_uninit p) b)
= {
  to_view_prop = (fun x -> match x with
  | Uninitialized -> False
  | InitOrUnit x' -> w.to_view_prop x'
  );
  to_view = (fun x -> match x with
  | InitOrUnit x' -> w.to_view x'
  );
  to_carrier = (fun v' -> w.to_carrier_not_one v'; InitOrUnit (w.to_carrier v'));
  to_carrier_not_one = (fun v -> w.to_carrier_not_one v);
  to_view_frame = (fun v frame ->
    w.to_carrier_not_one v; let InitOrUnit frame' = frame in w.to_view_frame v frame'
  );
}
