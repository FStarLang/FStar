module Steel.C.Model.Union

module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.C.Model.Ref
open Steel.C.Model.Struct
open Steel.Effect
module A = Steel.Effect.Atomic

(** A PCM for unions *)

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

let is_union (#a:Type) (#b:a->Type) (p:(k:a -> pcm (b k))) (f: restricted_t a b) =
  (exists (k:a). True) ==> (exists k. case_refinement_f p k f)
  (** precondition is there because we don't care if 'a is inhabited *)

let union (#a:Type) (#b:a->Type) (p:(k:a -> pcm (b k))) = f:restricted_t a b{is_union p f}

let union_elim (p:(k:'a -> pcm ('b k))) (f: union p) (goal:Type)
  (cont:(k:'a -> Lemma (requires case_refinement_f p k f) (ensures goal)
    [SMTPat (case_refinement_f p k f)]))
: Lemma (forall (j:'a). goal)
= let _ = cont in ()

let is_union_intro (p:(k:'a -> pcm ('b k))) (f: restricted_t 'a 'b)
  (k:'a{case_refinement_f p k f})
: Lemma (is_union p f)
= ()

let union_comp0 (p:(k:'a -> pcm ('b k))) (f g: union p) : Tot prop =
  forall j k.
  ~ (f j == one (p j)) /\ ~ (g k == one (p k)) ==>
  j == k /\ composable (p k) (f k) (g k)

let union_comp (p:(k:'a -> pcm ('b k))) : Tot (P.symrel (union p)) =
  union_comp0 p

let union_comp_intro (p:(k:'a -> pcm ('b k))) (f g: union p)
  (h:(j:'a -> k:'a ->
    Lemma
      (requires ~ (f j == one (p j)) /\ ~ (g k == one (p k)))
      (ensures j == k /\ composable (p k) (f k) (g k))
      [SMTPat (f j); SMTPat (g k)]))
: Lemma (union_comp p f g)
= let _ = h in ()

let union_comp_elim (p:(k:'a -> pcm ('b k))) (f g: union p)
  (j:'a) (k:'a)
: Lemma
  (requires (union_comp p f g /\ ~ (f j == one (p j)) /\ ~ (g k == one (p k))))
  (ensures j == k /\ composable (p k) (f k) (g k))
= ()

let union_comp_prod_comp (p:(k:'a -> pcm ('b k))) (f g: union p)
: Lemma
    (requires union_comp p f g)
    (ensures prod_comp p f g)
    [SMTPat (union_comp p f g)]
= prod_pcm_composable_intro p f g (fun k -> is_unit (p k) (f k); is_unit (p k) (g k))

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
  = case_refinement_f_intro p k (prod_op p f g) (fun k' -> is_unit (p k') (g k'))
  in
  FStar.Classical.move_requires fj_gk_both_not_one ();
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
  is_unit (prod_pcm p) g));
  h

let union_one (p:(k:'a -> pcm ('b k))): union p = prod_one p

let union_refine (p:(k:'a -> pcm ('b k))) (u: union p): Tot prop = exists k. p_refine (p k) (u k)

let union_assoc (p:(k:'a -> pcm ('b k)))
  (x y: union p)
  (z: union p{union_comp p y z /\ union_comp p x (union_op p y z)})
: Lemma (union_comp p x y /\
         union_comp p (union_op p x y) z /\
         union_op p x (union_op p y z) == union_op p (union_op p x y) z)
= prod_assoc p x y z;
  union_comp_intro p x y (fun j k -> is_unit (prod_pcm p) y);
  union_comp_intro p (union_op p x y) z (fun j k -> ());
  assert (union_op p x (union_op p y z) `feq` union_op p (union_op p x y) z)

let union_assoc_r (p:(k:'a -> pcm ('b k)))
  (x y: union p)
  (z: union p{union_comp p x y /\ union_comp p (union_op p x y) z})
: Lemma (union_comp p y z /\
         union_comp p x (union_op p y z) /\
         union_op p x (union_op p y z) == union_op p (union_op p x y) z)
= prod_assoc_r p x y z;
  union_comp_intro p x y (fun j k -> is_unit (prod_pcm p) y);
  union_comp_intro p (union_op p x y) z (fun j k -> ());
  assert (union_op p x (union_op p y z) `feq` union_op p (union_op p x y) z)

let union_is_unit (p:(k:'a -> pcm ('b k))) (x: union p)
: Lemma (union_comp p x (union_one p) /\
         union_op p x (union_one p) == x)
= is_unit (prod_pcm p) x

let fstar_union_pcm (p:(k:'a -> pcm ('b k))): P.pcm (union p) = let open P in {
    FStar.PCM.p = {composable = union_comp p; op = union_op p; one = union_one p};
    comm = (fun x y -> prod_comm p x y);
    assoc = union_assoc p;
    assoc_r = union_assoc_r p;
    is_unit = union_is_unit p;
    refine = union_refine p;
  }

let union_pcm' (p:(k:'a -> pcm ('b k))): pcm0 (union p) = pcm_of_fstar_pcm (fstar_union_pcm p)

let union_pcm (p:(k:'a -> pcm ('b k))): pcm (union p) =
  let p' = union_pcm' p in
  let aux (x:union p) (y:union p{composable p' x y})
  : Lemma (requires op p' x y == one p') (ensures x == one p' /\ y == one p')
    [SMTPat (op p' x y)]
  = ext x (one p') (fun k -> let _ = p k in ());
    ext y (one p') (fun k -> let _ = p k in ())
  in
  assert (forall x frame . (union_refine p x /\ union_comp p x frame) ==> frame `feq` union_one p);
  union_pcm' p

let union_pcm_composable_intro0
  (p:(k:'a -> pcm ('b k)))
  (x y: union p)
: Lemma
  ((composable (union_pcm p) x y <==> union_comp p x y) /\
  (composable (union_pcm p) x y ==> op (union_pcm p) x y == union_op p x y))
  [SMTPat (composable (union_pcm p) x y)]
= ()

let union_comp_intro0 (p:(k:'a -> pcm ('b k))) (f g: union p)
  (h:(j:'a -> k:'a ->
    Lemma
      (requires ~ (f j == one (p j)) /\ ~ (g k == one (p k)))
      (ensures j == k /\ composable (p k) (f k) (g k))
      [SMTPat (f j); SMTPat (g k)]))
: Lemma (composable (union_pcm p) f g)
= let _ = h in ()

let union_comp_elim0 (p:(k:'a -> pcm ('b k))) (f g: union p)
  (j:'a) (k:'a)
: Lemma
  (requires (composable (union_pcm p) f g /\ ~ (f j == one (p j)) /\ ~ (g k == one (p k))))
  (ensures j == k /\ composable (p k) (f k) (g k))
= ()

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
= mkmorphism
    (field_to_union_f p k)
    (assert (field_to_union_f p k (one (p k)) `feq` one (union_pcm p)))
    (fun x1 x2 ->
      Classical.forall_intro_2 (fun k -> is_unit (p k));
      assert (union_op p (field_to_union_f p k x1) (field_to_union_f p k x2) `feq` field_to_union_f p k (op (p k) x1 x2));
        ())

let field_to_union_elim (#a: eqtype) (#b: a -> Type) (p: (k: a -> pcm (b k)))
  (k: a)
  (x: b k)
  (k': a)
: Lemma
  (requires (~ ((field_to_union p k).morph x k' == one (p k'))))
  (ensures (k == k'))
= ()

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
= mkmorphism
    (union_to_field_f p k) ()
    (fun x1 x2 -> ())

let union_field_lift_fpu'
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: frame_preserving_upd_dom (union_pcm p) ((field_to_struct p k).morph x))
: Tot (union p)
= 
    on_dom a (fun k' ->
      if k' = k
      then f (v k) <: b k'
      else one (p k')
    )

#restart-solver

#push-options "--z3rlimit 30 --query_stats --fuel 2 --ifuel 4"

let union_field_lift_fpu0_prf1
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: frame_preserving_upd_dom (union_pcm p) ((field_to_union p k).morph x))
: Lemma
  (frame_preserving_upd_goal1 (union_pcm p) ((field_to_union p k).morph x) ((field_to_union p k).morph y) (union_field_lift_fpu' p k x y f) v)
=
      let y' = (field_to_union p k).morph y in
      let v_new = union_field_lift_fpu' p k x y f v in
      assert (p_refine (union_pcm p) v_new);
      Classical.forall_intro_2 (fun k -> is_unit (p k));
      let frame : b k = compatible_elim (p k) y (f (v k)) in
      let frame' : union p = on_dom a (fun k' -> if k' = k then (frame <: b k') else one (p k')) in
      assert (composable (union_pcm p) y' frame');
      assert (op (union_pcm p) frame' y' `feq` v_new);
      compatible_intro (union_pcm p) y' v_new frame'

#pop-options

#restart-solver

#push-options "--query_stats --fuel 2 --ifuel 4 --z3rlimit 64"

let union_field_lift_fpu0_prf2
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: frame_preserving_upd_dom (union_pcm p) ((field_to_union p k).morph x))
  (frame: union p)
: Lemma
  (requires (
    frame_preserving_upd_goal2_pre (union_pcm p) ((field_to_union p k).morph x) ((field_to_union p k).morph y) (union_field_lift_fpu' p k x y f) v frame
  ))
  (ensures (
    frame_preserving_upd_goal2_post (union_pcm p) ((field_to_union p k).morph x) ((field_to_union p k).morph y) (union_field_lift_fpu' p k x y f) v frame
  ))
=
  union_comp_intro0
    p
    ((field_to_union p k).morph y)
    frame
    (fun j' k' ->
      field_to_union_elim p k y j';
      union_comp_elim0 p ((field_to_union p k).morph x) frame k k';
      let _ = f (v k) in
      assert (composable (p k) x (frame k));
      assert (composable (p k) y (frame k))
  )

#pop-options

#push-options "--query_stats --fuel 2 --ifuel 4 --z3rlimit 128"

#restart-solver

let union_field_lift_fpu0_prf3
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: frame_preserving_upd_dom (union_pcm p) ((field_to_union p k).morph x))
  (frame: union p)
: Lemma
  (requires (
    frame_preserving_upd_goal3_pre (union_pcm p) ((field_to_union p k).morph x) ((field_to_union p k).morph y) (union_field_lift_fpu' p k x y f) v frame
  ))
  (ensures (
    frame_preserving_upd_goal3_post (union_pcm p) ((field_to_union p k).morph x) ((field_to_union p k).morph y) (union_field_lift_fpu' p k x y f) v frame
  ))
=
  let w = op (union_pcm p) ((field_to_union p k).morph x) frame in
  union_pcm_composable_intro0 p ((field_to_union p k).morph x) frame;
  assert (w == union_op p ((field_to_union p k).morph x) frame);
  assert (w == prod_op p ((field_to_union p k).morph x) frame);
  assert (w k == op (p k) x (frame k));
  assert (w k == v k);
  let v'k = f (v k) in
  let w' = op (union_pcm p) ((field_to_union p k).morph y) frame in
  union_pcm_composable_intro0 p ((field_to_union p k).morph y) frame;
  assert (w' == union_op p ((field_to_union p k).morph y) frame);
  assert (w' == prod_op p ((field_to_union p k).morph y) frame);
  assert (w' k == op (p k) y (frame k));
  assert (w' k == v'k);
  assert (union_op p ((field_to_union p k).morph y) frame `feq` 
    union_field_lift_fpu' p k x y f v)

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
=
  let y' = Ghost.hide ((field_to_union p k).morph y) in
  frame_preserving_upd_intro
    (union_pcm p)
    ((field_to_union p k).morph x)
    ((field_to_union p k).morph y)
    (union_field_lift_fpu' p k x y f)
    (union_field_lift_fpu0_prf1 p k x y f)
    (union_field_lift_fpu0_prf2 p k x y f)
    (union_field_lift_fpu0_prf3 p k x y f)

let union_field
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
: Tot (connection (union_pcm p) (p k))
= mkconnection
    (field_to_union p k)
    (union_to_field p k)
    ()
    (union_field_lift_fpu p k)

module I = FStar.IndefiniteDescription
let case_of_union (p:(k:'a -> pcm ('b k))) (u: union p)
: GTot (k:option 'a{match k with Some k -> ~ (u k == one (p k)) | None -> u == one (union_pcm p)})
= if I.strong_excluded_middle (exists k. ~ (u k == one (p k))) then
    let k = I.indefinite_description_ghost 'a (fun k -> ~ (u k == one (p k))) in
    Some k
  else begin
    assert (u `feq` one (union_pcm p));
    None
  end

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
    
let union_peel (#a:eqtype) #b (p:(k:a -> pcm (b k))) (k:a)
  (xs: union p{~ (xs k == one (p k))})
: Lemma (xs == field_to_union_f p k (xs k))
= assert (xs `feq` field_to_union_f p k (xs k))

let addr_of_union_field
  (#a:eqtype) #b (#p:(k:a -> pcm (b k)))
  (r: ref (union_pcm p)) (k:a)
  (xs: Ghost.erased (union p))
: Steel (ref (p k))
    (r `pts_to` xs)
    (fun r' -> r' `pts_to` Ghost.reveal xs k)
    (requires fun _ -> ~ (Ghost.reveal xs k == one (p k)))
    (ensures fun _ r' _ -> r' == ref_focus r (union_field p k))
= union_peel p k xs;
  A.change_equal_slprop (r `pts_to` xs) (r `pts_to` _);
  let s = focus r (union_field p k) (field_to_union_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k) in
  A.change_equal_slprop (s `pts_to` _) (s `pts_to` _);
  A.return s

module M = Steel.Memory 
let unaddr_of_union_field
  (#opened:M.inames) (#a:eqtype) #b (#p:(k:a -> pcm (b k))) (k:a)
  (r': ref (p k)) (r: ref (union_pcm p))
  (x: Ghost.erased (b k))
: A.SteelGhost unit opened
    (r' `pts_to` x)
    (fun s -> r `pts_to` field_to_union_f p k x)
    (requires fun _ -> r' == ref_focus r (union_field p k))
    (ensures fun _ _ _ -> True)
= unfocus r' r (union_field p k) x

let union_view_to_view_prop
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
: union p -> Tot prop
= fun u ->
  u =!= one (union_pcm p) /\
  (forall k. case_refinement_f p k u ==> (case_view k).to_view_prop (u k))

let union_view_to_view
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
  (case_of:(u:union p -> k:a{case_refinement_f p k u}))
: refine (union p) (union_view_to_view_prop case_view) -> dtuple2 a view_t
= fun u -> let k = case_of u in (|k, (case_view k).to_view (u k)|)

let union_view_to_carrier
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
: dtuple2 a view_t -> refine (union p) (union_view_to_view_prop case_view)
= fun (|k, x|) -> field_to_union_f p k ((case_view k).to_carrier x)

let union_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
  (case_of:(u:union p -> k:a{case_refinement_f p k u}))
: Tot (sel_view (union_pcm p) (dtuple2 a view_t) false)
= {
  to_view_prop = union_view_to_view_prop case_view;
  to_view = union_view_to_view case_view case_of;
  to_carrier = union_view_to_carrier case_view;
  to_carrier_not_one = ();
  to_view_frame = (fun (|k, x|) u -> (case_view k).to_view_frame x (u k));
}
