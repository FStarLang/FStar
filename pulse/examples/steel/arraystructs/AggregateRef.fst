module AggregateRef

open FStar.PCM
open FStar.PCM.Extras
open Lens
module P = FStar.PCM

open FStar.FunctionalExtensionality
open Steel.Effect

(** A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a.
    The base type of the lens, unlike the Steel.Memory.ref, is refined by a refinement re.
    This allows the reference to point to substructures of unions with known case. *)
noeq type ref a #b (q: refined_one_pcm b): Type = {
  p: refined_one_pcm a;
  re: pcm_refinement p;
  pl: pcm_lens (refined_pcm re) q;
  r: Steel.Memory.ref a p;
}

let mpts_to (#p: pcm 'a) (r: Steel.Memory.ref 'a p) = Steel.PCMReference.pts_to r

let pts_to r v = (* TODO unerase v, try [@@@smt_fallback] *)
  r.r `mpts_to` put r.pl v (one (refined_pcm r.re))

(** The refinement of a ref *)

let ref_refine (#a:Type) (#b:Type) (#p:refined_one_pcm b)
  (r: ref a p) (new_re: pcm_refinement p)
: ref a (refined_pcm new_re) = {
  p = r.p;
  re = {
    refi = conj_refinement r.re.refi (extend_refinement r.pl new_re.refi);
    u =
      conj_unrefinement r.re.refi (extend_refinement r.pl new_re.refi) r.re.u
        (extend_unrefinement r.pl new_re.refi new_re.u);
  };
  pl =
    pcm_iso_lens_comp
      (pcm_refinement'_conj_iso r.p r.re.refi (extend_refinement r.pl new_re.refi))
      (pcm_lens_refine r.pl new_re.refi);
  r = r.r
}

(** Fundamental operations on references *)

module M = Steel.Memory
module A = Steel.Effect.Atomic

let ref_focus #a #b #c #p r #q l =
  {p = r.p; re = r.re; pl = pcm_lens_comp r.pl l; r = r.r}

let focus (r: ref 'a 'p)
  (#q: refined_one_pcm 'c)
  (l: pcm_lens 'p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: Steel (ref 'a q)
    (r `pts_to` s)
    (fun r' -> r' `pts_to` x)
    (fun _ -> Ghost.reveal s == put l x (one 'p))
    (fun _ r' _ -> r' == ref_focus r l)
= let r' = ref_focus r l in
  A.change_slprop_rel  
    (r `pts_to` s)
    (r' `pts_to` x)
    (fun _ _ -> True)
    (fun m -> r.pl.get_morphism.f_one ());
  A.return r'

let unfocus #inames
  (#p: refined_one_pcm 'b)
  (#q: refined_one_pcm 'c)
  (r: ref 'a q) (r': ref 'a p)
  (l: pcm_lens p q) (x: Ghost.erased 'c)
: A.SteelGhost unit inames
    (r `pts_to` x)
    (fun _ -> r' `pts_to` put l x (one p))
    (requires fun _ -> r == ref_focus r' l)
    (ensures fun _ _ _ -> True)
= A.change_slprop_rel  
    (r `pts_to` x)
    (r' `pts_to` put l x (one p))
    (fun _ _ -> True)
    (fun m -> r'.pl.get_morphism.f_one ())

let split r xy x y =
  A.change_equal_slprop
    (r `pts_to` xy)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl xy (one (refined_pcm r.re)))));
  (refined_pcm r.re).is_unit (one (refined_pcm r.re));
  r.pl.put_morphism.f_op
    (Ghost.reveal x, one (refined_pcm r.re))
    (Ghost.reveal y, one (refined_pcm r.re));
  Steel.PCMReference.split r.r
    (put r.pl xy (one (refined_pcm r.re)))
    (put r.pl x (one (refined_pcm r.re)))
    (put r.pl y (one (refined_pcm r.re)));
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl x (one (refined_pcm r.re)))))
    (r `pts_to` x);
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl y (one (refined_pcm r.re)))))
    (r `pts_to` y)

let mgather
  (#a:Type) (#p:FStar.PCM.pcm a)
  (r:Steel.Memory.ref a p) (v0:Ghost.erased a) (v1:Ghost.erased a)
: SteelT (_:unit{composable p v0 v1})
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (op p v0 v1))
= Steel.PCMReference.gather r v0 v1

let gather #a #b #p r x y =
  A.change_equal_slprop
    (r `pts_to` x)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl x (one (refined_pcm r.re)))));
  A.change_equal_slprop
    (r `pts_to` y)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl y (one (refined_pcm r.re)))));
  mgather r.r
    (put r.pl x (one (refined_pcm r.re)))
    (put r.pl y (one (refined_pcm r.re)));
  r.pl.get_morphism.f_op
    (put r.pl x (one (refined_pcm r.re)))
    (put r.pl y (one (refined_pcm r.re)));
  (refined_pcm r.re).is_unit (one (refined_pcm r.re));
  r.pl.put_morphism.f_op
    (Ghost.reveal x, one (refined_pcm r.re))
    (Ghost.reveal y, one (refined_pcm r.re));
  A.change_equal_slprop _ (r `pts_to` op p x y)

let peel (#p: refined_one_pcm 'b) (r: ref 'a p) (#q: refined_one_pcm 'c)
  (l: pcm_lens p q) (x: Ghost.erased 'b)
: SteelT unit
    (r `pts_to` x)
    (fun _ ->
      (r `pts_to` put l (one q) x) `star` 
      (r `pts_to` put l (get l x) (one p)))
= q.is_unit (get l x);
  p.is_unit x;
  q.comm (get l x) (one q);
  l.put_morphism.f_op (one q, Ghost.reveal x) (get l (Ghost.reveal x), one p);
  split r x (put l (one q) x) (put l (get l x) (one p))

let addr_of_lens #a #b #c #p r l x =
  peel r l x;
  focus r l (put l (get l x) (one p)) (get l x)

let un_addr_of_lens #a #b #c #p #q r' r l x y =
  unfocus r' r l y;
  gather r x (put l y (one p));
  q.is_unit (Ghost.reveal y);
  p.is_unit (Ghost.reveal x);
  q.comm (get l x) y;
  l.put_morphism.f_op (get l x, Ghost.reveal x) (Ghost.reveal y, one p);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _)

val refine
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r: ref a p)
  (re: pcm_refinement p)
  (x: Ghost.erased b{refinement_f re x})
: Steel (ref a (refined_pcm re))
    (r `pts_to` x)
    (fun r' -> r' `pts_to` Ghost.reveal x)
    (fun _ -> True)
    (fun _ r' _ -> r' == ref_refine r re)
let refine r re x =
  let r' = ref_refine r re in
  A.change_equal_slprop (r `pts_to` x) (r' `pts_to` Ghost.reveal x);
  A.return r'

val unrefine
  (#opened:Steel.Memory.inames)
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r': ref a p)
  (re: pcm_refinement p)
  (r: ref a (refined_pcm re))
  (x: Ghost.erased b{refinement_f re x})
: A.SteelGhost unit opened
    (r `pts_to` Ghost.reveal x)
    (fun _ -> r' `pts_to` x)
    (fun _ -> r == ref_refine r' re)
    (fun _ _ _ -> True)
let unrefine #inames r' re r x =
  A.change_equal_slprop (r `pts_to` Ghost.reveal x) (r' `pts_to` x)

(*
val addr_of_union_lens
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b) (#q: refined_one_pcm c)
  (r: ref a p) (#re: pcm_refinement p) (l: pcm_lens (refined_pcm re) q)
  (x: Ghost.erased b{refinement_f re x})
: Steel (ref a q)
    (r `pts_to` x)
    (fun s ->
      (r `pts_to` put l (one q) x) `star` 
      (s `pts_to` get l x))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r l)

val un_addr_of_union_lens
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b) (#q: refined_one_pcm c)
  (r': ref a q) (r: ref a p) (l: pcm_lens p q)
  (x: Ghost.erased b) (y: Ghost.erased c)
: Steel unit
    ((r `pts_to` x) `star` (r' `pts_to` y))
    (fun s -> r `pts_to` put l y x)
    (requires fun _ -> r' == ref_focus r l /\ get l x == one q)
    (ensures fun _ _ _ -> True)
*)

let ref_read (#p: refined_one_pcm 'b) (#x: Ghost.erased 'b) (r: ref 'a p)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> ~ (Ghost.reveal x == one p))
    (ensures fun _ x' _ -> compatible p x x')
= let x' = Ghost.hide (put r.pl x (one (refined_pcm r.re))) in
  A.change_equal_slprop (r `pts_to` x) (r.r `mpts_to` x');
  let v = Steel.PCMReference.read r.r x' in
  pcm_refinement'_compatible_closed r.re.refi x' v;
  pcm_lens_compatible_get r.pl x' v;
  A.change_equal_slprop (r.r `mpts_to` x') (r `pts_to` x);
  A.return (get r.pl v)

let ref_frame_preserving_upd #a #b
  (#p: refined_one_pcm b) (r: ref a p) (x y: Ghost.erased b)
  (f: (b -> b){frame_pres p f x y})
: frame_preserving_upd r.p
    (put r.pl x (one (refined_pcm r.re)))
    (put r.pl y (one (refined_pcm r.re)))
= let x' = Ghost.hide (put r.pl x (one (refined_pcm r.re))) in
  let y' = Ghost.hide (put r.pl y (one (refined_pcm r.re))) in
  pcm_lens_frame_pres r.pl x' y f;
  r.re.u x' y' (frame_pres_mk_upd (refined_pcm r.re) x' y' (upd r.pl f))

let ref_upd_act (r: ref 'a 'p) (x y: Ghost.erased 'b) (f: ('b -> 'b){frame_pres 'p f x y})
: M.action_except unit Set.empty (hp_of (r `pts_to` x)) (fun _ -> hp_of (r `pts_to` y))
= M.upd_gen Set.empty r.r _ _ (ref_frame_preserving_upd r x y f)

let as_action (#p:vprop)
              (#q:vprop)
              (f:M.action_except unit Set.empty (hp_of p) (fun _ -> hp_of q))
: SteelT unit p (fun x -> q)
= A.change_slprop_rel p (to_vprop (hp_of p)) (fun _ _ -> True) (fun m -> ());
  let x = Steel.Effect.as_action f in
  A.change_slprop_rel (to_vprop (hp_of q)) q (fun _ _ -> True) (fun m -> ());
  A.return x

let ref_upd r x y f = as_action (ref_upd_act r x y f)

let frame_preserving_upd_valid_write (p: pcm 'a)
  (x:Ghost.erased 'a) (y:'a{valid_write p x y})
: f:('a -> 'a){frame_pres p f x y}
= let f = fun v -> y in
  frame_pres_intro p f x y (fun v ->
    compatible_refl p y;
    let aux (frame:'a{composable p x frame})
    : Lemma (
       composable p y frame /\
       (op p x frame == v ==> op p y frame == y))
    = assert (op p frame x == Ghost.reveal x);
      assert (op p frame y == y);
      p.comm frame x; p.comm frame y
    in FStar.Classical.forall_intro aux);
  f

let ref_write (r: ref 'a 'p) (#x: Ghost.erased 'b) (y: 'b{valid_write 'p x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
= ref_upd r x y (frame_preserving_upd_valid_write 'p x y)
