module Steel.C.PCM
open FStar.PCM

#push-options "--print_universes"

unfold
let one (#a: Type) (p: pcm a) = p.p.one

let pcm (a: Type) : Tot Type =
  (p: FStar.PCM.pcm a {
    (forall (x:a) (y:a{composable p x y}).{:pattern (composable p x y)}
      op p x y == one p ==> x == one p /\ y == one p) // /\ // necessary to lift frame-preserving updates to unions
    //(forall (x:a) . {:pattern (p.refine x)} p.refine x ==> exclusive p x) /\ // nice to have, but not used yet
    //(~ (p.refine (one p))) // necessary to maintain (refine ==> exclusive) for uninit
  })

noeq
type morphism (#a #b: Type) (pa: pcm a) (pb: pcm b) = {
  morph: (a -> Tot b);
  morph_unit: squash (morph pa.p.one == pb.p.one);
  morph_compose:
    (x1: a) ->
    (x2: a) ->
    Lemma
    (requires (composable pa x1 x2))
    (ensures (composable pb (morph x1) (morph x2) /\ morph (x1 `pa.p.op` x2) == morph x1 `pb.p.op` morph x2));
}

let morphism_morph_compose
  (#a #b: Type) (#pa: pcm a) (#pb: pcm b) (m: morphism pa pb)
  (x1: a)
  (x2: a)
: Lemma
  (requires (composable pa x1 x2))
  (ensures (composable pb (m.morph x1) (m.morph x2) /\ m.morph (x1 `pa.p.op` x2) == m.morph x1 `pb.p.op` m.morph x2))
  [SMTPat (composable pb (m.morph x1) (m.morph x2))]
= m.morph_compose x1 x2

let morphism_compose (#a #b #c: Type) (#pa: pcm a) (#pb: pcm b) (#pc: pcm c) (fab: morphism pa pb) (fbc: morphism pb pc) : Tot (morphism pa pc) = {
  morph = (fun x -> fbc.morph (fab.morph x));
  morph_unit = ();
  morph_compose = begin fun x1 x2 ->
    fab.morph_compose x1 x2;
    fbc.morph_compose (fab.morph x1) (fab.morph x2)
  end;
}

let injective (#a #b: Type) (f: (a -> Tot b)) : Tot prop =
  (forall x1 x2 . {:pattern f x1; f x2} f x1 == f x2 ==> x1 == x2)

let is_inverse_of (#a #b: Type) (g: (b -> Tot a)) (f: (a -> Tot b)) : Tot prop =
  (forall x . {:pattern (g (f x))} g (f x) == x)

let is_inverse_of_injective (#a #b: Type) (g: (b -> Tot a)) (f: (a -> Tot b))
  x1 x2
: Lemma
  (requires (g `is_inverse_of` f /\ f x1 == f x2))
  (ensures (x1 == x2))
  [SMTPat (g `is_inverse_of` f); SMTPat (f x1); SMTPat (f x2)]
= assert (g (f x1) == g (f x2))

noeq
type connection (#t_large #t_small: Type) (p_large: pcm t_large) (p_small: pcm t_small) = {
  conn_small_to_large: morphism p_small p_large;
  conn_large_to_small: morphism p_large p_small;
  conn_small_to_large_inv: squash (conn_large_to_small.morph `is_inverse_of` conn_small_to_large.morph);
  conn_lift_frame_preserving_upd:
    (x: Ghost.erased t_small { ~ (Ghost.reveal x == p_small.p.one) }) -> // validity condition, e.g. union cases
    (y: Ghost.erased t_small) ->
    (f: frame_preserving_upd p_small x y) ->
    Tot (frame_preserving_upd p_large (conn_small_to_large.morph x) (conn_small_to_large.morph y));
}

let connection_compose (#a #b #c: Type) (#pa: pcm a) (#pb: pcm b) (#pc: pcm c) (fab: connection pa pb) (fbc: connection pb pc) : Tot (connection pa pc) = {
  conn_small_to_large = fbc.conn_small_to_large `morphism_compose` fab.conn_small_to_large;
  conn_large_to_small = fab.conn_large_to_small `morphism_compose` fbc.conn_large_to_small;
  conn_small_to_large_inv = ();
  conn_lift_frame_preserving_upd = begin fun xc yc f ->
    let xb = Ghost.hide (fbc.conn_small_to_large.morph xc) in
    let yb = Ghost.hide (fbc.conn_small_to_large.morph yc) in
    let xa = Ghost.hide (fab.conn_small_to_large.morph xb) in
    let ya = Ghost.hide (fab.conn_small_to_large.morph yb) in
    fab.conn_lift_frame_preserving_upd _ _ (fbc.conn_lift_frame_preserving_upd _ _ f)
  end;
}

noeq type ref (a: Type u#1) #b (q: pcm b): Type = {
  p: pcm a;
  pl: connection p q;
  r: Steel.Memory.ref a p;
}

let mpts_to (#p: pcm 'a) (r: Steel.Memory.ref 'a p) = Steel.PCMReference.pts_to r

open Steel.Effect

//val pts_to
//  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
//  (r: ref a p) ([@@@smt_fallback] v: Ghost.erased b)
//: vprop

val pts_to
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p) ([@@@smt_fallback] v: Ghost.erased b)
: vprop

let pts_to r v =
  r.r `mpts_to` r.pl.conn_small_to_large.morph v

val ref_focus
  (#a:Type) (#b:Type) (#c:Type) (#p: pcm b)
  (r: ref a p) (#q: pcm c) (l: connection p q)
: ref a q

let ref_focus #a #b #c #p r #q l =
  {p = r.p; pl = connection_compose r.pl l; r = r.r}

module A = Steel.Effect.Atomic

let focus (r: ref 'a 'p)
  (#q: pcm 'c)
  (l: connection 'p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: Steel (ref 'a q)
    (r `pts_to` s)
    (fun r' -> r' `pts_to` x)
    (fun _ -> Ghost.reveal s == l.conn_small_to_large.morph x)
    (fun _ r' _ -> r' == ref_focus r l)
= let r' = ref_focus r l in
  A.change_slprop_rel  
    (r `pts_to` s)
    (r' `pts_to` x)
    (fun _ _ -> True)
    (fun m -> ());
  A.return r'

let unfocus #inames
  (#p: pcm 'b)
  (#q: pcm 'c)
  (r: ref 'a q) (r': ref 'a p)
  (l: connection p q) (x: Ghost.erased 'c)
: A.SteelGhost unit inames
    (r `pts_to` x)
    (fun _ -> r' `pts_to` l.conn_small_to_large.morph x)
    (requires fun _ -> r == ref_focus r' l)
    (ensures fun _ _ _ -> True)
= A.change_slprop_rel  
    (r `pts_to` x)
    (r' `pts_to` l.conn_small_to_large.morph x)
    (fun _ _ -> True)
    (fun m -> ())

val split (#a:Type) (#b:Type) (#p: pcm b) (r: ref a p) (xy x y: Ghost.erased b)
: Steel unit
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> composable p x y /\ xy == Ghost.hide (op p x y))
    (fun _ _ _ -> True)

let split r xy x y =
  A.change_equal_slprop
    (r `pts_to` xy)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph xy)));
  Steel.PCMReference.split r.r
    (r.pl.conn_small_to_large.morph xy)
    (r.pl.conn_small_to_large.morph x)
    (r.pl.conn_small_to_large.morph y);
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph x)))
    (r `pts_to` x);
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph y)))
    (r `pts_to` y)

let mgather
  (#a:Type) (#p:pcm a)
  (r:Steel.Memory.ref a p) (v0:Ghost.erased a) (v1:Ghost.erased a)
: SteelT (_:unit{composable p v0 v1})
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (op p v0 v1))
= Steel.PCMReference.gather r v0 v1

val gather (#a:Type) (#b:Type) (#p: pcm b) (r: ref a p) (x y: Ghost.erased b)
: SteelT (_:unit{composable p x y})
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op p x y)

let gather #a #b #p r x y =
  A.change_equal_slprop
    (r `pts_to` x)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph x)));
  A.change_equal_slprop
    (r `pts_to` y)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (r.pl.conn_small_to_large.morph y)));
  mgather r.r
    (r.pl.conn_small_to_large.morph x)
    (r.pl.conn_small_to_large.morph y);
  assert (
    let x1 = r.pl.conn_small_to_large.morph x in
    let y1 = r.pl.conn_small_to_large.morph y in
    let x2 = r.pl.conn_large_to_small.morph x1 in
    let y2 = r.pl.conn_large_to_small.morph y1 in
    Ghost.reveal x == x2 /\ Ghost.reveal y == y2
  );
  A.change_equal_slprop _ (r `pts_to` op p x y)

val ref_read
  (#a:Type) (#b:Type) (#p: pcm b) (#x: Ghost.erased b) (r: ref a p)
: Steel b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> compatible p x x')

let ref_read (#p: pcm 'b) (#x: Ghost.erased 'b) (r: ref 'a p)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> compatible p x x')
= let w = Ghost.hide (r.pl.conn_small_to_large.morph x) in
  A.change_equal_slprop (r `pts_to` x) (r.r `mpts_to` w);
  let w' = Steel.PCMReference.read r.r w in
  A.change_equal_slprop (r.r `mpts_to` w) (r `pts_to` x);
  let x' = r.pl.conn_large_to_small.morph w' in
  assert (forall frame . (composable r.p w frame /\ op r.p frame w == w') ==> (
    let sw = r.pl.conn_large_to_small.morph w in
    let sw' = r.pl.conn_large_to_small.morph w' in
    let sframe = r.pl.conn_large_to_small.morph frame in
    (composable p sw sframe /\ op p sframe sw == sw')
  ));
  A.return x'

module M = Steel.Memory

let ref_upd_act (r: ref 'a 'p) (x: Ghost.erased 'b { ~ (Ghost.reveal x == one 'p) }) (y: Ghost.erased 'b) (f: frame_preserving_upd 'p x y)
: Tot (M.action_except unit Set.empty (hp_of (r `pts_to` x)) (fun _ -> hp_of (r `pts_to` y)))
= M.upd_gen Set.empty r.r  (Ghost.hide (r.pl.conn_small_to_large.morph x)) (Ghost.hide (r.pl.conn_small_to_large.morph y)) (r.pl.conn_lift_frame_preserving_upd x y f)

let as_action (#p:vprop)
              (#q:vprop)
              (f:M.action_except unit Set.empty (hp_of p) (fun _ -> hp_of q))
: SteelT unit p (fun x -> q)
= A.change_slprop_rel p (to_vprop (hp_of p)) (fun _ _ -> True) (fun m -> ());
  let x = Steel.Effect.as_action f in
  A.change_slprop_rel (to_vprop (hp_of q)) q (fun _ _ -> True) (fun m -> ());
  A.return x

val ref_upd
  (#a:Type) (#b:Type) (#p: pcm b)
  (r: ref a p) (x: Ghost.erased b { ~ (Ghost.reveal x == one p) }) (y: Ghost.erased b) (f: frame_preserving_upd p x y)
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)

let ref_upd r x y f = as_action (ref_upd_act r x y f)

(** A PCM for structs *)

/// We can generalize to 'a-ary products (k:'a -> 'b k), given a PCM for each k:

open FStar.FunctionalExtensionality
open FStar.Classical
let ext (f g: restricted_t 'a 'b) (fg:(x:'a -> Lemma (f x == g x))) : Lemma (f == g) =
  extensionality 'a 'b f g;
  forall_intro fg

let prod_comp (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b): prop =
  forall k. composable (p k) (x k) (y k)

let prod_op (p:(k:'a -> pcm ('b k)))
  (x: restricted_t 'a 'b) (y: restricted_t 'a 'b{prod_comp p x y})
: restricted_t 'a 'b
= on_domain 'a (fun k -> op (p k) (x k) (y k))

let prod_one (p:(k:'a -> pcm ('b k))): restricted_t 'a 'b =
  on_domain 'a (fun k -> one (p k))

let prod_comm (p:(k:'a -> pcm ('b k)))
  (x: restricted_t 'a 'b) (y: restricted_t 'a 'b{prod_comp p x y})
: Lemma (prod_op p x y == prod_op p y x)
= ext (prod_op p x y) (prod_op p y x) (fun k -> (p k).comm (x k) (y k))

let prod_assoc (p:(k:'a -> pcm ('b k)))
  (x y: restricted_t 'a 'b)
  (z: restricted_t 'a 'b{prod_comp p y z /\ prod_comp p x (prod_op p y z)})
: Lemma (prod_comp p x y /\
         prod_comp p (prod_op p x y) z /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
= let aux k
  : Lemma (composable (p k) (x k) (y k) /\
           composable (p k) (op (p k) (x k) (y k)) (z k)) 
    [SMTPat (p k)]
  = (p k).assoc (x k) (y k) (z k)
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> (p k).assoc (x k) (y k) (z k))

let prod_assoc_r (p:(k:'a -> pcm ('b k)))
  (x y: restricted_t 'a 'b)
  (z: restricted_t 'a 'b{prod_comp p x y /\ prod_comp p (prod_op p x y) z})
: Lemma (prod_comp p y z /\
         prod_comp p x (prod_op p y z) /\
         prod_op p x (prod_op p y z) == prod_op p (prod_op p x y) z)
= let aux k
  : Lemma (composable (p k) (y k) (z k) /\
           composable (p k) (x k) (op (p k) (y k) (z k)))
    [SMTPat (p k)]
  = (p k).assoc_r (x k) (y k) (z k)
  in
  ext (prod_op p x (prod_op p y z)) (prod_op p (prod_op p x y) z)
    (fun k -> (p k).assoc (x k) (y k) (z k))

let prod_is_unit (p:(k:'a -> pcm ('b k))) (x: restricted_t 'a 'b)
: Lemma (prod_comp p x (prod_one p) /\
         prod_op p x (prod_one p) == x)
= let is_unit k
  : Lemma (composable (p k) (x k) (prod_one p k))
    [SMTPat (p k)]
  = (p k).is_unit (x k)
  in ext (prod_op p x (prod_one p)) x (fun k -> (p k).is_unit (x k))

let prod_refine (p:(k:'a -> pcm ('b k))) (x: restricted_t 'a 'b): prop =
  (exists (k: 'a). True) /\ (forall k. (p k).refine (x k))

let prod_pcm' (p:(k:'a -> pcm ('b k))): FStar.PCM.pcm (restricted_t 'a 'b) = {
  comm = prod_comm p;
  FStar.PCM.p = {composable = prod_comp p; op = prod_op p; one = prod_one p};
  assoc = prod_assoc p;
  assoc_r = prod_assoc_r p;
  is_unit = prod_is_unit p;
  refine = prod_refine p
}

let prod_pcm (p:(k:'a -> pcm ('b k))): pcm (restricted_t 'a 'b) =
  let p' = prod_pcm' p in
  assert (forall x y . (composable p' x y /\ op p' x y == one p') ==> (
    x `feq` one p' /\ y `feq` one p'
  ));
  //assert (forall x frame . (prod_refine p x /\ prod_comp p x frame) ==> frame `feq` prod_one p);
  p'

let prod_pcm_composable_intro (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b)
  (h:(k:'a -> Lemma (composable (p k) (x k) (y k))))
: Lemma (composable (prod_pcm p) x y) = FStar.Classical.forall_intro h

let field_to_struct_f
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: b k)
: Pure (restricted_t a b)
  (requires True)
  (ensures (fun y -> forall k' . y k' == (if k' = k then (x <: b k') else one (p k'))))
= on_dom a (fun k' -> if k' = k then (x <: b k') else one (p k'))

let is_unit (#a: Type u#a) (p:pcm a) 
  (x:a)
:  Lemma (composable p x p.FStar.PCM.p.one /\
         op p x p.FStar.PCM.p.one == x)
= p.is_unit x

let field_to_struct
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (morphism (p k) (prod_pcm p))
= {
  morph = field_to_struct_f p k;
  morph_unit = assert (field_to_struct_f p k (one (p k)) `feq` one (prod_pcm p));
  morph_compose = (fun x1 x2 ->
    Classical.forall_intro_2 (fun k -> is_unit (p k));
    assert (prod_op p (field_to_struct_f p k x1) (field_to_struct_f p k x2) `feq` field_to_struct_f p k (op (p k) x1 x2));
      ()
  );
}

let struct_to_field_f
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: restricted_t a b)
: Tot (b k)
= x k

let struct_to_field
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (morphism (prod_pcm p) (p k))
= {
  morph = struct_to_field_f p k;
  morph_unit = ();
  morph_compose = (fun x1 x2 -> ());
}

let struct_field_lift_fpu'
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: restricted_t a b {
    (prod_pcm p).refine v /\
    compatible (prod_pcm p) ((field_to_struct p k).morph x) v
  })
: Tot (restricted_t a b)
= 
    on_dom a (fun k' ->
      if k' = k
      then f (v k) <: b k'
      else v k'
    )

let struct_field_lift_fpu_prf
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: restricted_t a b {
    (prod_pcm p).refine v /\
    compatible (prod_pcm p) ((field_to_struct p k).morph x) v
  })
: Lemma
  (let v_new = struct_field_lift_fpu' p k x y f v in
    (prod_pcm p).refine v_new /\
    compatible (prod_pcm p) ((field_to_struct p k).morph y) v_new /\
    (forall (frame:_{composable (prod_pcm p) ((field_to_struct p k).morph x) frame}).
       composable (prod_pcm p) ((field_to_struct p k).morph y) frame /\
       (op (prod_pcm p) ((field_to_struct p k).morph x) frame == v ==> op (prod_pcm p) ((field_to_struct p k).morph y) frame == v_new))
  )
=
  let y' = (field_to_struct p k).morph y in
  let v_new = struct_field_lift_fpu' p k x y f v in
  Classical.forall_intro_2 (fun k -> is_unit (p k));
  assert (forall (frame: b k) .
    (composable (p k) y frame /\ op (p k) frame y == f (v k)) ==> (
    let frame' : restricted_t a b = on_dom a (fun k' -> if k' = k then (frame <: b k') else v_new k') in
    composable (prod_pcm p) y' frame' /\
    op (prod_pcm p) frame' y' `feq` v_new
  ));
  assert (compatible (prod_pcm p) y' v_new);
  assert (forall (frame:_{composable (prod_pcm p) ((field_to_struct p k).morph x) frame}).
       composable (prod_pcm p) ((field_to_struct p k).morph y) frame /\
       (op (prod_pcm p) ((field_to_struct p k).morph x) frame == v ==> op (prod_pcm p) ((field_to_struct p k).morph y) frame `feq` v_new));
  ()

let struct_field_lift_fpu
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
: Tot (frame_preserving_upd (prod_pcm p) ((field_to_struct p k).morph x) ((field_to_struct p k).morph y))
= fun v ->
    struct_field_lift_fpu_prf p k x y f v;
    struct_field_lift_fpu' p k x y f v

let struct_field
  (#a: eqtype)
  (#b: a -> Type u#b)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (connection (prod_pcm p) (p k))
= {
  conn_small_to_large = field_to_struct p k;
  conn_large_to_small = struct_to_field p k;
  conn_small_to_large_inv = ();
  conn_lift_frame_preserving_upd = struct_field_lift_fpu p k;
}

let struct_without_field (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (xs: restricted_t a b)
: restricted_t a b
= on_dom a (fun k' -> if k' = k then one (p k) else xs k')

let struct_peel (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (xs: restricted_t a b)
: Lemma (
    composable (prod_pcm p) (struct_without_field p k xs) (field_to_struct_f p k (xs k)) /\
    xs == op (prod_pcm p) (struct_without_field p k xs) (field_to_struct_f p k (xs k)))
= Classical.forall_intro_2 (fun k -> is_unit (p k));
  Classical.forall_intro_3 (fun k -> (p k).comm);
  assert (xs `feq` op (prod_pcm p) (struct_without_field p k xs) (field_to_struct_f p k (xs k)))
  
let addr_of_struct_field
  #base (#a:eqtype) #b (#p:(k:a -> pcm (b k)))
  (r: ref base (prod_pcm p)) (k:a)
  (xs: Ghost.erased (restricted_t a b))
: Steel (ref base (p k))
    (r `pts_to` xs)
    (fun s ->
      (r `pts_to` struct_without_field p k xs) `star` 
      (s `pts_to` Ghost.reveal xs k))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r (struct_field p k))
= struct_peel p k xs;
  split r xs (struct_without_field p k xs) (field_to_struct_f p k (Ghost.reveal xs k));
  let r = focus r (struct_field p k) (field_to_struct_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  A.return r

let struct_with_field (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (x:b k) (xs: restricted_t a b)
: restricted_t a b
= on_dom a (fun k' -> if k' = k then x else xs k')

let struct_unpeel (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (x: b k) (xs: restricted_t a b)
: Lemma
    (requires xs k == one (p k))
    (ensures
      composable (prod_pcm p) xs (field_to_struct_f p k x) /\
      struct_with_field p k x xs == op (prod_pcm p) xs (field_to_struct_f p k x))
= Classical.forall_intro_2 (fun k -> is_unit (p k));
  Classical.forall_intro_3 (fun k -> (p k).comm);
  assert (struct_with_field p k x xs `feq` op (prod_pcm p) xs (field_to_struct_f p k x))

let unaddr_of_struct_field
  #base (#a:eqtype) #b (#p:(k:a -> pcm (b k))) (k:a)
  (r': ref base (p k)) (r: ref base (prod_pcm p))
  (xs: Ghost.erased (restricted_t a b)) (x: Ghost.erased (b k))
: Steel unit
    ((r `pts_to` xs) `star` (r' `pts_to` x))
    (fun s -> r `pts_to` struct_with_field p k x xs)
    (requires fun _ -> r' == ref_focus r (struct_field p k) /\ Ghost.reveal xs k == one (p k))
    (ensures fun _ _ _ -> True)
= unfocus r' r (struct_field p k) x;
  gather r xs (field_to_struct_f p k x);
  struct_unpeel p k x xs;
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  A.return ()

let exclusive_struct_intro
  (#a: Type)
  (#b: _)
  (p:(k: a -> pcm (b k)))
  (x: restricted_t a b)
: Lemma
  (requires (
    forall k . exclusive (p k) (struct_to_field_f p k x)
  ))
  (ensures (
    exclusive (prod_pcm p) x
  ))
  [SMTPat (exclusive (prod_pcm p) x)]
=
  assert (forall frame . prod_comp p x frame ==> frame `feq` prod_one p)

let exclusive_struct_elim
  (#a: eqtype)
  (#b: _)
  (p:(k: a -> pcm (b k)))
  (x: restricted_t a b)
  (k: a)
: Lemma
  (requires (exclusive (prod_pcm p) x))
  (ensures (exclusive (p k) (struct_to_field_f p k x)))
=
  let phi
    frame
  : Lemma
    (requires (composable (p k) (struct_to_field_f p k x) frame))
    (ensures (composable (prod_pcm p) x (field_to_struct_f p k frame)))
    [SMTPat (composable (p k) (struct_to_field_f p k x) frame)]
  = let x' = struct_to_field_f p k x in
    let f' = field_to_struct_f p k frame in
    let psi
      k'
    : Lemma
      (composable (p k') (x k') (f' k'))
      [SMTPat (composable (p k') (x k') (f' k'))]
    = if k' = k
      then ()
      else is_unit (p k') (x k')
    in
    ()
  in
  ()

(** A PCM for unions TODO move to proper place *)

open FStar.FunctionalExtensionality

let case_refinement_f (p:(k:'a -> pcm ('b k))) (k:'a) (f: restricted_t 'a 'b): prop =
  forall k'. ~ (k == k') ==> f k' == one (p k')

let case_refinement_f_intro (p:(k:'a -> pcm ('b k))) (k:'a) (f: restricted_t 'a 'b)
  (h:(k':'a{~ (k == k')} -> Lemma (f k' == one (p k'))))
: Lemma (case_refinement_f p k f) = FStar.Classical.forall_intro h

let case_refinement_f_uniq (p:(k:'a -> pcm ('b k))) (j k:'a) (f: restricted_t 'a 'b)
: Lemma
    (requires case_refinement_f p j f /\ case_refinement_f p k f /\ ~ (j == k))
    (ensures f == one (prod_pcm p))
= ext f (one (prod_pcm p)) (fun k -> ())

let is_union (p:(k:'a -> pcm ('b k))) (f: restricted_t 'a 'b) =
  (exists (k:'a). True) ==> (exists k. case_refinement_f p k f)
  (** precondition is there because we don't care if 'a is inhabited *)

let union (p:(k:'a -> pcm ('b k))) = f:restricted_t 'a 'b{is_union p f}

let union_elim (p:(k:'a -> pcm ('b k))) (f: union p) (goal:Type)
  (cont:(k:'a -> Lemma (requires case_refinement_f p k f) (ensures goal)
    [SMTPat (case_refinement_f p k f)]))
: Lemma (forall (j:'a). goal)
= let _ = cont in ()

let is_union_intro (p:(k:'a -> pcm ('b k))) (f: restricted_t 'a 'b)
  (k:'a{case_refinement_f p k f})
: Lemma (is_union p f)
= ()

let union_comp (p:(k:'a -> pcm ('b k))): symrel (union p) = fun f g ->
  forall j k.
  ~ (f j == one (p j)) /\ ~ (g k == one (p k)) ==>
  j == k /\ composable (p k) (f k) (g k)

let union_comp_intro (p:(k:'a -> pcm ('b k))) (f g: union p)
  (h:(j:'a -> k:'a ->
    Lemma
      (requires ~ (f j == one (p j)) /\ ~ (g k == one (p k)))
      (ensures j == k /\ composable (p k) (f k) (g k))
      [SMTPat (f j); SMTPat (g k)]))
: Lemma (union_comp p f g)
= let _ = h in ()

let union_comp_prod_comp (p:(k:'a -> pcm ('b k))) (f g: union p)
: Lemma
    (requires union_comp p f g)
    (ensures prod_comp p f g)
    [SMTPat (union_comp p f g)]
= prod_pcm_composable_intro p f g (fun k -> (p k).is_unit (f k); (p k).is_unit (g k))

let case_refinement_f_one (p:(k:'a -> pcm ('b k))) (k:'a) (f: restricted_t 'a 'b)
: Lemma
    (requires case_refinement_f p k f /\ f k == one (p k))
    (ensures f == one (prod_pcm p))
    [SMTPat (case_refinement_f p k f); SMTPat (f k == one (p k))]
= ext f (one (prod_pcm p)) (fun _ -> ())

let case_refinement_f_op (p:(k:'a -> pcm ('b k))) (j k:'a) (f g: restricted_t 'a 'b)
: Lemma
    (requires case_refinement_f p j f /\ case_refinement_f p k g /\ union_comp p f g)
    (ensures
      f == one (prod_pcm p) \/
      g == one (prod_pcm p) \/ 
      case_refinement_f p k (prod_op p f g))
    [SMTPat (case_refinement_f p j f); SMTPat (case_refinement_f p k g)]
= let fj_or_gk_one
  : squash
      (f j == one (p j) \/ g k == one (p k) ==>
       feq f (one (prod_pcm p)) \/ feq g (one (prod_pcm p)))
  = ()
  in let fj_gk_both_not_one ()
  : Lemma
      (requires ~ (f j == one (p j)) /\ ~ (g k == one (p k)))
      (ensures case_refinement_f p k (prod_op p f g))
  = case_refinement_f_intro p k (prod_op p f g) (fun k' -> (p k').is_unit (g k'))
  in
  move_requires fj_gk_both_not_one ();
  assert
   ((f j == one (p j) \/ g k == one (p k)) ==>
    f == one (prod_pcm p) \/
    g == one (prod_pcm p) \/ 
    case_refinement_f p k (prod_op p f g))

let union_op (p:(k:'a -> pcm ('b k))) (f: union p) (g: union p{union_comp p f g}): union p =
  let h = prod_op p f g in
  let goal = is_union p h in
  union_elim p f goal (fun j ->
  union_elim p g goal (fun k ->
  case_refinement_f_op p j k f g;
  (prod_pcm p).is_unit g));
  h

let union_one (p:(k:'a -> pcm ('b k))): union p = prod_one p
let union_refine (p:(k:'a -> pcm ('b k))) = prod_refine p

let union_assoc (p:(k:'a -> pcm ('b k)))
  (x y: union p)
  (z: union p{union_comp p y z /\ union_comp p x (union_op p y z)})
: Lemma (union_comp p x y /\
         union_comp p (union_op p x y) z /\
         union_op p x (union_op p y z) == union_op p (union_op p x y) z)
= prod_assoc p x y z;
  union_comp_intro p x y (fun j k -> (prod_pcm p).is_unit y);
  union_comp_intro p (union_op p x y) z (fun j k -> ())

#restart-solver
#push-options "--query_stats --z3rlimit 32"

let union_assoc_r (p:(k:'a -> pcm ('b k)))
  (x y: union p)
  (z: union p{union_comp p x y /\ union_comp p (union_op p x y) z})
: Lemma (union_comp p y z /\
         union_comp p x (union_op p y z) /\
         union_op p x (union_op p y z) == union_op p (union_op p x y) z)
= prod_assoc_r p x y z;
  union_comp_intro p x y (fun j k -> (prod_pcm p).is_unit y);
  union_comp_intro p (union_op p x y) z (fun j k -> ())

#pop-options

let union_is_unit (p:(k:'a -> pcm ('b k))) (x: union p)
: Lemma (union_comp p x (union_one p) /\
         union_op p x (union_one p) == x)
= (prod_pcm p).is_unit x

let union_pcm (p:(k:'a -> pcm ('b k))): pcm (union p) =
  let p' = {
    FStar.PCM.p = {composable = union_comp p; op = union_op p; one = union_one p};
    comm = (fun x y -> prod_comm p x y);
    assoc = union_assoc p;
    assoc_r = union_assoc_r p;
    is_unit = union_is_unit p;
    refine = union_refine p;
  } in
  let aux (x:union p) (y:union p{composable p' x y})
  : Lemma (requires op p' x y == one p') (ensures x == one p' /\ y == one p')
    [SMTPat (op p' x y)]
  = ext x (one p') (fun k -> let _ = p k in ());
    ext y (one p') (fun k -> let _ = p k in ())
  in
  //assert (forall x frame . (union_refine p x /\ union_comp p x frame) ==> frame `feq` union_one p);
  p'

let field_to_union_f
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: b k)
: Pure (union p)
  (requires True)
  (ensures (fun y -> forall k' . y k' == (if k' = k then (x <: b k') else one (p k'))))
= on_dom a (fun k' -> if k' = k then (x <: b k') else one (p k'))

let field_to_union
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (morphism (p k) (union_pcm p))
= {
  morph = field_to_union_f p k;
  morph_unit = assert (field_to_union_f p k (one (p k)) `feq` one (union_pcm p));
  morph_compose = (fun x1 x2 ->
    Classical.forall_intro_2 (fun k -> is_unit (p k));
    assert (union_op p (field_to_union_f p k x1) (field_to_union_f p k x2) `feq` field_to_union_f p k (op (p k) x1 x2));
      ()
  );
}

let union_to_field_f
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: union p)
: Tot (b k)
= x k

let union_to_field
  (#a: Type)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (morphism (union_pcm p) (p k))
= {
  morph = union_to_field_f p k;
  morph_unit = ();
  morph_compose = (fun x1 x2 -> ());
}

let union_field_lift_fpu'
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: union p {
    (union_pcm p).refine v /\
    compatible (union_pcm p) ((field_to_struct p k).morph x) v
  })
: Tot (union p)
= 
    on_dom a (fun k' ->
      if k' = k
      then f (v k) <: b k'
      else one (p k')
    )

let compatible_intro
  (#a: Type u#a)
  (pcm: pcm a)
  (x y: a)
  (frame: a)
: Lemma
  (requires (composable pcm x frame /\ op pcm frame x == y))
  (ensures (compatible pcm x y))
= ()

let compatible_elim
  (#a: Type u#a)
  (pcm: pcm a)
  (x y: a)
: Ghost a
  (requires (compatible pcm x y))
  (ensures (fun frame ->
    composable pcm x frame /\
    op pcm frame x == y
  ))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun frame -> 
    composable pcm x frame /\
    op pcm frame x == y
  )

#restart-solver
#push-options "--z3rlimit 32 --query_stats"

let union_field_lift_fpu_prf
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: union p {
    (union_pcm p).refine v /\
    compatible (union_pcm p) ((field_to_union p k).morph x) v
  })
: Lemma
  (let v_new = union_field_lift_fpu' p k x y f v in
    (union_pcm p).refine v_new /\
    compatible (union_pcm p) ((field_to_union p k).morph y) v_new /\
    (forall (frame:_{composable (union_pcm p) ((field_to_union p k).morph x) frame}).
       composable (union_pcm p) ((field_to_union p k).morph y) frame /\
       (op (union_pcm p) ((field_to_union p k).morph x) frame == v ==> op (union_pcm p) ((field_to_union p k).morph y) frame == v_new))
  )
=
  let y' = (field_to_union p k).morph y in
  let v_new = union_field_lift_fpu' p k x y f v in
  Classical.forall_intro_2 (fun k -> is_unit (p k));
  let frame : b k = compatible_elim (p k) y (f (v k)) in
  let frame' : union p = on_dom a (fun k' -> if k' = k then (frame <: b k') else one (p k')) in
  assert (composable (union_pcm p) y' frame');
  assert (op (union_pcm p) frame' y' `feq` v_new);
  compatible_intro (union_pcm p) y' v_new frame';
  assert (forall (frame:_{composable (union_pcm p) ((field_to_union p k).morph x) frame}).
       composable (union_pcm p) ((field_to_union p k).morph y) frame /\
       (op (union_pcm p) ((field_to_union p k).morph x) frame == v ==> op (union_pcm p) ((field_to_union p k).morph y) frame `feq` v_new));
  ()

#pop-options

let union_field_lift_fpu
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
: Tot (frame_preserving_upd (union_pcm p) ((field_to_union p k).morph x) ((field_to_union p k).morph y))
= fun v ->
    union_field_lift_fpu_prf p k x y f v;
    union_field_lift_fpu' p k x y f v

let union_field
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (connection (union_pcm p) (p k))
= {
  conn_small_to_large = field_to_union p k;
  conn_large_to_small = union_to_field p k;
  conn_small_to_large_inv = ();
  conn_lift_frame_preserving_upd = union_field_lift_fpu p k;
}

let union_without_field (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (xs: union p)
: union p
= on_dom a (fun k' -> if k' = k then one (p k) else xs k')

let union_peel (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (xs: union p)
: Lemma (
    composable (prod_pcm p) (union_without_field p k xs) (field_to_union_f p k (xs k)) /\
    xs == op (prod_pcm p) (union_without_field p k xs) (field_to_union_f p k (xs k)))
= Classical.forall_intro_2 (fun k -> is_unit (p k));
  Classical.forall_intro_3 (fun k -> (p k).comm);
  assert (xs `feq` op (prod_pcm p) (union_without_field p k xs) (field_to_union_f p k (xs k)))

let addr_of_union_field
  #base (#a:eqtype) #b (#p:(k:a -> pcm (b k)))
  (r: ref base (union_pcm p)) (k:a)
  (xs: Ghost.erased (union p))
: Steel (ref base (p k))
    (r `pts_to` xs)
    (fun s ->
      (r `pts_to` union_without_field p k xs) `star` 
      (s `pts_to` Ghost.reveal xs k))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r (union_field p k))
= union_peel p k xs;
  split r xs (union_without_field p k xs) (field_to_union_f p k (Ghost.reveal xs k));
  let r = focus r (union_field p k) (field_to_union_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  A.return r

let union_with_field (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (x:b k) (xs: union p{xs == one (union_pcm p)})
: union p
= on_dom a (fun k' -> if k' = k then x else xs k')

let union_unpeel (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (x: b k) (xs: union p{xs == one (union_pcm p)})
: Lemma
    (requires xs k == one (p k))
    (ensures
      composable (union_pcm p) xs (field_to_union_f p k x) /\
      union_with_field p k x xs == op (union_pcm p) xs (field_to_union_f p k x))
= Classical.forall_intro_2 (fun k -> is_unit (p k));
  Classical.forall_intro_3 (fun k -> (p k).comm);
  assert (union_with_field p k x xs `feq` op (union_pcm p) xs (field_to_union_f p k x))

let unaddr_of_union_field
  (#opened:M.inames) #base (#a:eqtype) #b (#p:(k:a -> pcm (b k))) (k:a)
  (r': ref base (p k)) (r: ref base (union_pcm p))
  (x: Ghost.erased (b k))
: A.SteelGhost unit opened
    (r' `pts_to` x)
    (fun s -> r `pts_to` field_to_union_f p k x)
    (requires fun _ -> r' == ref_focus r (union_field p k))
    (ensures fun _ _ _ -> True)
= unfocus r' r (union_field p k) x

let exclusive_union_intro
  (#a: Type)
  (#b: _)
  (p:(k: a -> pcm (b k)))
  (x: union p)
  (k: a)
: Lemma
  (requires (exclusive (p k) (x k) /\ (~ (x k == one (p k)))))
  (ensures (exclusive (union_pcm p) x))
= let phi
    (frame: union p)
  : Lemma
    (requires (composable (union_pcm p) x frame))
    (ensures (frame `feq` union_one p))
    [SMTPat (composable (union_pcm p) x frame)]
  = ()
  in
  ()

let exclusive_union_elim
  (#a: eqtype)
  (#b: _)
  (p: (k: a -> pcm (b k)))
  (x: union p)
  (k: a)
: Lemma
  (requires (exclusive (union_pcm p) x))
  (ensures (x k == one (p k) \/ exclusive (p k) (x k)))
= if FStar.StrongExcludedMiddle.strong_excluded_middle (x k == one (p k))
  then ()
  else
    let phi
      (frame: b k)
    : Lemma
      (requires (composable (p k) (x k) frame))
      (ensures (frame == one (p k)))
      [SMTPat (composable (p k) (x k) frame)]
    = let frame' = field_to_union_f p k frame in
      ()
    in
    ()

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

val opt_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some y)
  (requires (fun _ -> Some? x))
  (ensures (fun _ _ _ -> True))

let opt_pcm_write
  r x y
= ref_upd r x (Some y) (opt_pcm_fpu x y)

val opt_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Ghost.reveal x == Some y))

let opt_pcm_read
  r x
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

val frac_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some (y, full_perm))
  (requires (fun _ -> Some? x /\ snd (Some?.v x) == full_perm))
  (ensures (fun _ _ _ -> True))

let frac_pcm_write
  r x y
= ref_upd r x (Some (y, full_perm)) (frac_pcm_fpu x y)

val frac_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (pcm_frac #b)) (x: Ghost.erased (fractional b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Some? x /\ y == fst (Some?.v (Ghost.reveal x))))

let frac_pcm_read
  r x
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
= {
  morph = (fun x -> InitOrUnit x);
  morph_unit = ();
  morph_compose = (fun _ _ -> ());
}

let uninit_to_value
  (#a: Type)
  (p: pcm a)
: Tot (morphism (pcm_uninit p) p)
= {
  morph = (fun x -> match x with InitOrUnit y -> y | _ -> one p);
  morph_unit = ();
  morph_compose = (fun _ _ -> Classical.forall_intro (is_unit p));
}

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
= {
  conn_small_to_large = value_to_uninit p;
  conn_large_to_small = uninit_to_value p;
  conn_small_to_large_inv = ();
  conn_lift_frame_preserving_upd = uninit_conn_fpu p;
}

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

let pts_to_view_explicit_witinv
  (#a: Type u#1) (#b: Type u#b) (#p: pcm b)
  (r: ref a p)
  (#c: Type u#c)
  (vw: sel_view p c)
: Lemma
  (M.is_witness_invariant (pts_to_view_explicit r vw))
= 
  let aux (x y : Ghost.erased c) (m:M.mem)
  : Lemma
    (requires (M.interp (pts_to_view_explicit r vw x) m /\ M.interp (pts_to_view_explicit r vw y) m))
    (ensures  (x == y))
  =
    let x_ = vw.to_carrier x in
    let y_ = vw.to_carrier y in
    let x' = r.pl.conn_small_to_large.morph x_ in
    let y' = r.pl.conn_small_to_large.morph y_ in
    M.pts_to_join r.r x' y' m;
    let z' = FStar.IndefiniteDescription.indefinite_description_ghost a (fun z' -> compatible r.p x' z' /\ compatible r.p y' z') in
    let frame_x' = FStar.IndefiniteDescription.indefinite_description_ghost a (fun frame_x' -> composable r.p x' frame_x' /\ op r.p frame_x' x' == z') in
    let frame_y' = FStar.IndefiniteDescription.indefinite_description_ghost a (fun frame_y' -> composable r.p y' frame_y' /\ op r.p frame_y' y' == z') in
    let frame_x_ = r.pl.conn_large_to_small.morph frame_x' in
    let frame_y_ = r.pl.conn_large_to_small.morph frame_y' in
    r.p.comm x' frame_x';
    r.pl.conn_large_to_small.morph_compose x' frame_x';
    vw.to_view_frame x (r.pl.conn_large_to_small.morph frame_x');
    r.p.comm y' frame_y';
    r.pl.conn_large_to_small.morph_compose y' frame_y';
    vw.to_view_frame y (r.pl.conn_large_to_small.morph frame_y');
    ()
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

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
