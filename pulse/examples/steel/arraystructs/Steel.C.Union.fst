module Steel.C.Union

module P = FStar.PCM
open Steel.C.PCM
open Steel.C.Connection
open Steel.C.Ref
open Steel.C.Struct
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

let union_comp (p:(k:'a -> pcm ('b k))): P.symrel (union p) = fun f g ->
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
= mkmorphism
    (field_to_union_f p k)
    (assert (field_to_union_f p k (one (p k)) `feq` one (union_pcm p)))
    (fun x1 x2 ->
      Classical.forall_intro_2 (fun k -> is_unit (p k));
      assert (union_op p (field_to_union_f p k x1) (field_to_union_f p k x2) `feq` field_to_union_f p k (op (p k) x1 x2));
        ())

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

#push-options "--z3rlimit 32 --query_stats"

let union_field_lift_fpu'
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: union p {
    p_refine (union_pcm p) v /\
    compatible (union_pcm p) ((field_to_struct p k).morph x) v
  })
: Tot (union p)
= 
    on_dom a (fun k' ->
      if k' = k
      then f (v k) <: b k'
      else one (p k')
    )

#pop-options

#restart-solver

#push-options "--z3rlimit 64 --query_stats"

let union_field_lift_fpu_prf
  (#a: eqtype)
  (#b: a -> Type)
  (p:(k: a -> pcm (b k)))
  (k: a)
  (x: Ghost.erased (b k) { ~ (Ghost.reveal x == one (p k)) })
  (y: Ghost.erased (b k))
  (f: frame_preserving_upd (p k) x y)
  (v: union p {
    p_refine (union_pcm p) v /\
    compatible (union_pcm p) ((field_to_union p k).morph x) v
  })
: Lemma
  (let v_new = union_field_lift_fpu' p k x y f v in
    p_refine (union_pcm p) v_new /\
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
  let x = Ghost.reveal x in
  let aux (frame:_{composable (union_pcm p) ((field_to_union p k).morph x) frame})
  : Lemma (
      composable (union_pcm p) ((field_to_union p k).morph y) frame /\
      (op (union_pcm p) ((field_to_union p k).morph x) frame == v ==>
       op (union_pcm p) ((field_to_union p k).morph y) frame `feq` v_new))
  = assert (composable (union_pcm p) ((field_to_union p k).morph y) frame);
    assert_norm (
     union_op p ((field_to_union p k).morph x) frame k ==
     op (p k) x (frame k));
    assert (op (union_pcm p) ((field_to_union p k).morph x) frame == v ==>
       op (p k) x (frame k) == v k)
  in FStar.Classical.forall_intro aux; assume False

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

#pop-options

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
  #base (#a:eqtype) #b (#p:(k:a -> pcm (b k)))
  (r: ref base (union_pcm p)) (k:a)
  (xs: Ghost.erased (union p))
: Steel (ref base (p k))
    (r `pts_to` xs)
    (fun r' -> r' `pts_to` Ghost.reveal xs k)
    (requires fun _ -> ~ (Ghost.reveal xs k == one (p k)))
    (ensures fun _ r' _ -> r' == ref_focus r (union_field p k))
= union_peel p k xs;
  A.change_equal_slprop (r `pts_to` xs) (r `pts_to` _);
  focus r (union_field p k) (field_to_union_f p k (Ghost.reveal xs k)) (Ghost.reveal xs k)

module M = Steel.Memory 
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
