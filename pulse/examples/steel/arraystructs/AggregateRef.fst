module AggregateRef

open FStar.PCM
module P = FStar.PCM

let frame_pres_intro p f x y g =
  let _ = g in ()

(** PCM morphisms *)

let pcm_morphism_id #a #p = {
  f_refine = (fun _ -> ());
  f_one = (fun _ -> ());
  f_op = (fun _ _ -> ());
}

let pcm_morphism_comp #a #b #c #p #q #r #f #g mf mg = {
  f_refine = (fun x -> mg.f_refine x; mf.f_refine (g x));
  f_one = (fun () -> mg.f_one (); mf.f_one ());
  f_op = (fun x y -> mg.f_op x y; mf.f_op (g x) (g y));
}

open Aggregates
let pcm_morphism_both #a #b #c #p #q #r #s #f #g mf mg = {
  f_refine = (fun (x, y) -> mf.f_refine x; mg.f_refine y);
  f_one = (fun () -> mg.f_one (); mf.f_one ());
  f_op = (fun (x, y) (z, w) -> mf.f_op x z; mg.f_op y w);
}

let pcm_refinement'_comp_new_one #a #p re x y =
  re.new_one_is_refined_unit x;
  p.assoc_r x re.new_one y;
  re.f_closed_comp re.new_one y

let pcm_refinement'_compatible_closed #a #p re x y =
  let p' = refined_pcm re in
  compatible_elim p x y (re.f y) (fun frame ->
   re.f_closed_comp x frame; p.comm frame x);
  compatible_elim p x y (compatible p' x y) (fun frame_x ->
    pcm_refinement'_comp_new_one re x frame_x;
    let frame = op p re.new_one frame_x in
    re.new_one_is_refined_unit x;
    p.comm x frame_x;
    p.assoc x re.new_one frame_x;
    p.comm x (op p re.new_one frame_x);
    compatible_intro p' x y (op p re.new_one frame_x))

(** Lenses *)

let lens_upd l f s = l.put (f (l.get s)) s

(** The identity lens *)
let const (x: 'a) (b: 'b): 'a = x
let lens_id #a = {
  get = id;
  put = const;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

(** Lens composition *)
let get_comp (l: lens 'a 'b) (m: lens 'b 'c) (s: 'a): 'c = m.get (l.get s)
let put_comp (l: lens 'a 'b) (m: lens 'b 'c) (v: 'c) (s: 'a): 'a =
  lens_upd l (m.put v) s
let lens_comp l m = {
  get = get_comp l m;
  put = put_comp l m;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

(** PCM lenses *)

let compatible_pcm_morphism #a #b #p #q f m x y =
  compatible_elim p x y (compatible q (f x) (f y)) (fun frame_x ->
  let _ = m.f_op frame_x x in
  compatible_intro q (f x) (f y) (f frame_x))

let pcm_lens_compatible_get #a #b #p #q l x y =
  compatible_pcm_morphism l.l.get l.get_morphism x y
    
let pcm_lens_frame_pres #a #b #p #q l s v f =
  frame_pres_intro p (upd l f) s (put l v s) (fun full ->
    let _ = l.get_morphism.f_refine in
    pcm_lens_compatible_get l s full;
    l.put_morphism.f_refine (f (get l full), full);
    let goal = frame_pres_on p (upd l f) s (put l v s) full in
    compatible_elim p s full goal (fun frame_s ->
    compatible_elim q v (f (get l full)) goal (fun frame_v ->
    let frame_vs: a = put l frame_v frame_s in
    l.put_morphism.f_op (v, s) (frame_v, frame_s);
    p.comm frame_vs (put l v s);
    q.comm v frame_v;
    p.comm s frame_s;
    compatible_intro p (put l v s) (upd l f full) frame_vs;
    let aux (frame:a{composable p s frame})
    : Lemma (composable p (put l v s) frame /\
             (op p s frame == full ==> op p (put l v s) frame == upd l f full))
    = l.get_morphism.f_op s frame;
      l.put_morphism.f_op (v, s) (get l frame, frame);
      let aux ()
      : Lemma (requires op p s frame == full) 
              (ensures op p (put l v s) frame == upd l f full)
      = () in ()
    in FStar.Classical.forall_intro aux)))

let pcm_lens_id (#p: pcm 'a) = {
  l = lens_id; 
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

let pcm_lens_comp #a #b #c #p #q #r l m = {
  l = lens_comp l.l m.l;
  get_morphism = {
    f_refine = (fun _ ->
      let _ = l.get_morphism.f_refine in
      let _ = m.get_morphism.f_refine in ());
    f_one = (fun _ -> l.get_morphism.f_one (); m.get_morphism.f_one ());
    f_op = (fun s t ->
      l.get_morphism.f_op s t;
      m.get_morphism.f_op (get l s) (get l t));
  };
  put_morphism = {
    f_refine = (fun (v, s) ->
      l.get_morphism.f_refine s;
      m.put_morphism.f_refine (v, get l s);
      l.put_morphism.f_refine (put m v (get l s), s));
    f_one = (fun _ -> l.put_morphism.f_one (); m.put_morphism.f_one ());
    f_op = (fun (v, s) (w, t) ->
      l.get_morphism.f_op s t;
      m.put_morphism.f_op (v, get l s) (w, get l t);
      l.put_morphism.f_op (put m v (get l s), s) (put m w (get l t), t));
  };
}

open FStar.FunctionalExtensionality
open Steel.Effect

(** Basic lenses *)

let lens_fst_put (x:'a) (xy: 'a & 'b): 'a & 'b = (x, snd xy)
let lens_fst #a #b : lens (a & b) a = {
  get = fst;
  put = lens_fst_put;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

let pcm_lens_fst #a #b (p: pcm a) (q: pcm b): pcm_lens (p `pcm_times` q) p = {
  l = lens_fst;
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

(** We can create lenses for unions if we know which case of the union we are in: *)

let either_l a b = x:either a b{Inl? x}
let lens_left_put (y: 'a) (x:either_l 'a 'b): either_l 'a 'b =
  Inl y
let lens_left #a #b : lens (either_l a b) a = {
  get = Inl?.v;
  put = lens_left_put;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

let lens_left_fst #a #b #c: lens (either_l (a & b) c) a = lens_comp lens_left lens_fst
let lens_fst_left #a #b #c: lens ((either_l a b) & c) a = lens_comp lens_fst lens_left

(** A PCM for binary sums *)

let either_composable (p: pcm 'a) (q: pcm 'b): symrel (option (either 'a 'b)) =
  fun x y -> match x, y with
    | None, _ | _, None -> True
    | Some (Inl x), Some (Inl y) -> composable p x y
    | Some (Inr x), Some (Inr y) -> composable q x y
    | _, _ -> False
let either_op (p: pcm 'a) (q: pcm 'b) (x: option (either 'a 'b))
  (y: option (either 'a 'b){either_composable p q x y})
: option (either 'a 'b) = match x, y with
  | None, z | z, None -> z
  | Some (Inl x), Some (Inl y) -> Some (Inl (op p x y))
  | Some (Inr x), Some (Inr y) -> Some (Inr (op q x y))
    
let either_pcm (p: pcm 'a) (q: pcm 'b): pcm (option (either 'a 'b)) = P.({
  p = {composable = either_composable p q; op = either_op p q; one = None};
  comm = (fun x y -> match x, y with
    | None, _ | _, None -> ()
    | Some (Inl x), Some (Inl y) -> p.comm x y
    | Some (Inr x), Some (Inr y) -> q.comm x y);
  assoc = (fun x y z -> match x, y, z with
    | Some (Inl x), Some (Inl y), Some (Inl z) -> p.assoc x y z
    | Some (Inr x), Some (Inr y), Some (Inr z) -> q.assoc x y z
    | _, _, _ -> ());
  assoc_r = (fun x y z -> match x, y, z with
    | Some (Inl x), Some (Inl y), Some (Inl z) -> p.assoc_r x y z
    | Some (Inr x), Some (Inr y), Some (Inr z) -> q.assoc_r x y z
    | _, _, _ -> ());
  is_unit = (fun x -> ());
  refine = (fun x -> match x with
    | None -> True
    | Some (Inl x) -> p.refine x
    | Some (Inr x) -> q.refine x);
})

let inl_refinement (p: refined_one_pcm 'a) (q: pcm 'b): pcm_refinement' (either_pcm p q) = {
  f = (fun (x: option (either 'a 'b)) -> Some? x /\ Inl? (Some?.v x));
  f_closed_comp = (fun _ _ -> ());
  new_one = Some (Inl #_ #'b (one p));
  new_one_is_refined_unit = (fun (Some (Inl x)) -> p.is_unit x);
}

let mpts_to (#p: pcm 'a) (r: Steel.Memory.ref 'a p) = Steel.PCMReference.pts_to r

let pts_to r v = (* TODO unerase v, try [@@@smt_fallback] *)
  r.r `mpts_to` put r.pl v (one (refined_pcm r.re.refi))

(** Refining a pcm_lens *)

let extend_refinement_f (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement' q) (x: 'a): prop
= re.f (get l x)

let lens_refine_get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement' q) (s: refine_t (extend_refinement_f l re))
: refine_t re.f
= l.l.get s

let lens_refine_put (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement' q)
  (v: refine_t re.f) (s: refine_t (extend_refinement_f l re))
: refine_t (extend_refinement_f l re)
= l.l.put v s

let lens_refine (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (re: pcm_refinement' q)
: lens (refine_t (extend_refinement_f l re)) (refine_t re.f) = {
  get = lens_refine_get l re;
  put = lens_refine_put l re;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

let extend_refinement_f_closed (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement' q) (x: refine_t (extend_refinement_f l re))
  (y: 'a{composable p x y})
: Lemma (extend_refinement_f l re (op p x y))
= l.get_morphism.f_op x y;
  re.f_closed_comp (get l x) (get l y)

let extend_refinement_new_one (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: new_one:refine_t (extend_refinement_f l re){p.refine new_one}
= l.put_morphism.f_refine (re.new_one, one p); put l re.new_one (one p)

let extend_refinement_new_one_is_refined_unit
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement' q) (x: refine_t (extend_refinement_f l re))
: Lemma (composable p x (extend_refinement_new_one l re) /\
         op p x (extend_refinement_new_one l re) == x)
= re.new_one_is_refined_unit (get l x);
  p.is_unit x;
  l.put_morphism.f_op (get l x, x) (re.new_one, one p)
  
let extend_refinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: pcm_refinement' p = {
  f = extend_refinement_f l re;
  f_closed_comp = extend_refinement_f_closed l re;
  new_one = extend_refinement_new_one l re;
  new_one_is_refined_unit = extend_refinement_new_one_is_refined_unit l re;
}

let pcm_lens_refine_get_morphism_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_refine
    (refined_pcm (extend_refinement l re))
    (refined_pcm re)
    (lens_refine l re).get
= l.get_morphism.f_refine

let pcm_lens_refine_get_morphism_one
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_one
    (refined_pcm (extend_refinement l re))
    (refined_pcm re)
    (lens_refine l re).get
= l.get_morphism.f_one

let pcm_lens_refine_get_morphism_op
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_op
    (refined_pcm (extend_refinement l re))
    (refined_pcm re)
    (lens_refine l re).get
= l.get_morphism.f_op

let pcm_lens_refine_put_morphism_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_refine
    (refined_pcm re `pcm_times` refined_pcm (extend_refinement l re))
    (refined_pcm (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= fun (v, s) -> l.put_morphism.f_refine (v, s)

let pcm_lens_refine_put_morphism_one
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_one
    (refined_pcm re `pcm_times` refined_pcm (extend_refinement l re))
    (refined_pcm (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= l.put_morphism.f_one

let pcm_lens_refine_put_morphism_op
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_op
    (refined_pcm re `pcm_times` refined_pcm (extend_refinement l re))
    (refined_pcm (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= fun (v, s) (w, t) -> l.put_morphism.f_op (v, s) (w, t)

let pcm_lens_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: pcm_lens (refined_pcm (extend_refinement l re)) (refined_pcm re) = {
  l = lens_refine l re;
  get_morphism = {
    f_refine = pcm_lens_refine_get_morphism_refine l re;
    f_one = pcm_lens_refine_get_morphism_one l re;
    f_op = pcm_lens_refine_get_morphism_op l re;
  };
  put_morphism = {
    f_refine = pcm_lens_refine_put_morphism_refine l re;
    f_one = pcm_lens_refine_put_morphism_one l re;
    f_op = pcm_lens_refine_put_morphism_op l re;
  };
}
  
(** Isomorphisms *)

let iso_lens_comp_get (i: iso 'a 'b) (l: lens 'b 'c): 'a -> 'c = l.get `compose` i.fwd
let iso_lens_comp_put (i: iso 'a 'b) (l: lens 'b 'c) (v: 'c) (s: 'a): 'a = i.bwd (l.put v (i.fwd s))
let iso_lens_comp (i: iso 'a 'b) (l: lens 'b 'c): lens 'a 'c = {
  get = iso_lens_comp_get i l;
  put = iso_lens_comp_put i l;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

(** A refinement f of a refinement g of 'a is isomorphic to a refinement by conj f g *)

let refine_conj_iso_fwd (f: 'a -> prop) (g:(x:'a{f x} -> prop))
  (x: refine_t (conj f g))
: refine_t g
= x

let refine_conj_iso_bwd (f: 'a -> prop) (g:(x:'a{f x} -> prop))
  (x: refine_t g)
: refine_t (conj f g)
= x

let refine_conj_iso (f: 'a -> prop) (g:(x:'a{f x} -> prop))
: iso (refine_t #'a (conj #'a f g)) (refine_t #(x:'a{f x}) g) = {
  fwd = refine_conj_iso_fwd f g;
  bwd = refine_conj_iso_bwd f g;
  fwd_bwd = (fun _ -> ());
  bwd_fwd = (fun _ -> ());
}

(** PCM isomorphisms *)

let pcm_refinement'_conj_iso_i (p: pcm 'a)
  (re1: pcm_refinement' p)
  (re2: pcm_refinement' (refined_pcm re1))
: iso (refine_t #'a (conj #'a re1.f re2.f)) (refine_t #(x:'a{re1.f x}) re2.f) =
  refine_conj_iso re1.f re2.f

let pcm_iso_lens_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (i: pcm_iso p q) (l: pcm_lens q r)
: pcm_lens p r = {
  l = iso_lens_comp i.i l.l;
  get_morphism = pcm_morphism_comp l.get_morphism i.fwd_morphism;
  put_morphism = {
    f_refine = (fun (v, s) ->
      i.fwd_morphism.f_refine s; 
      l.put_morphism.f_refine (v, i.i.fwd s);
      i.bwd_morphism.f_refine (l.l.put v (i.i.fwd s)));
    f_one = (fun () ->
      i.fwd_morphism.f_one (); 
      l.put_morphism.f_one ();
      i.bwd_morphism.f_one ());
    f_op = (fun (v, s) (w, t) -> 
     i.fwd_morphism.f_op s t;
     l.put_morphism.f_op (v, i.i.fwd s) (w, i.i.fwd t);
     i.bwd_morphism.f_op (l.l.put v (i.i.fwd s)) (l.l.put w (i.i.fwd t)));
  }
}

(** The conjunction of two refinements *)

let conj_refinement_f (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
: 'a -> prop = conj #'a re1.f re2.f

let conj_refinement_f_closed (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
  (x: refine_t (conj_refinement_f re1 re2))
  (y: 'a{composable p x y})
: Lemma (conj_refinement_f re1 re2 (op p x y))
= pcm_refinement'_comp_new_one re1 x y;
  re1.f_closed_comp x (op p re1.new_one y);
  pcm_refinement'_comp_new_one re2 x (op p re1.new_one y);
  re2.f_closed_comp x (op p re2.new_one (op p re1.new_one y));
  p.assoc x re2.new_one (op p re1.new_one y);
  re2.new_one_is_refined_unit x;
  p.assoc x re1.new_one y;
  re1.new_one_is_refined_unit x

(* re1.new_one and re2.new_one both work; we go with re2 *)
let conj_refinement_new_one (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
: refine_t (conj_refinement_f re1 re2)
= re2.new_one

let conj_refinement_new_one_is_refined_unit (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
  (x: refine_t (conj_refinement_f re1 re2))
: Lemma (composable p x (conj_refinement_new_one re1 re2) /\
         op p x (conj_refinement_new_one re1 re2) == x)
= re2.new_one_is_refined_unit x

let conj_refinement (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
: pcm_refinement' p = {
  f = conj_refinement_f re1 re2;
  f_closed_comp = conj_refinement_f_closed re1 re2;
  new_one = conj_refinement_new_one re1 re2;
  new_one_is_refined_unit = conj_refinement_new_one_is_refined_unit re1 re2;
}

(** A refinement re1 of a refinement re2 of a PCM is isomorphic to a
    refinement by the conjunction of re1 and re2 *)
let pcm_refinement'_conj_iso (p: pcm 'a)
  (re1: pcm_refinement' p)
  (re2: pcm_refinement' (refined_pcm re1))
: pcm_iso (refined_pcm (conj_refinement re1 re2)) (refined_pcm re2) = {
  i = pcm_refinement'_conj_iso_i p re1 re2;
  fwd_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  bwd_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

let upd_across_pcm_iso (#p: pcm 'a) (#q: pcm 'b) (i: pcm_iso p q) (x y: Ghost.erased 'a)
: frame_pres_lift p x y q (i.i.fwd x) (i.i.fwd y)
= fun f v ->
  i.bwd_morphism.f_refine v;
  compatible_pcm_morphism i.i.bwd i.bwd_morphism (i.i.fwd x) v;
  let w = i.i.fwd (f (i.i.bwd v)) in
  i.fwd_morphism.f_refine (f (i.i.bwd v));
  compatible_pcm_morphism i.i.fwd i.fwd_morphism y (f (i.i.bwd v));
  let aux (frame:'b{composable q (i.i.fwd x) frame})
  : Lemma (composable q (i.i.fwd y) frame /\
           (op q (i.i.fwd x) frame == v ==>
            op q (i.i.fwd y) frame == w))
  = i.bwd_morphism.f_op (i.i.fwd x) frame;
    i.fwd_morphism.f_op y (i.i.bwd frame);
    i.fwd_morphism.f_op x (i.i.bwd frame)
  in FStar.Classical.forall_intro aux;
  w

let conj_unrefinement (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
  (h1: pcm_unrefinement re1) (h2: pcm_unrefinement re2)
: pcm_unrefinement (conj_refinement #'a re1 re2)
= fun x y ->
  h1 (Ghost.reveal x) (Ghost.reveal y) `compose`
  h2 (Ghost.reveal x) (Ghost.reveal y) `compose`
  upd_across_pcm_iso (pcm_refinement'_conj_iso p re1 re2) x y

let extend_unrefinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q) (u: pcm_unrefinement re)
: pcm_unrefinement (extend_refinement l re)
= fun x y f v ->
  let re' = extend_refinement l re in
  let p' = refined_pcm re' in
  pcm_refinement'_compatible_closed re' x v;
  pcm_lens_compatible_get l x v;
  let w = f v in
  let aux (frame:'a{composable p x frame})
  : Lemma (composable p y frame /\ (op p x frame == v ==> op p y frame == w))
  = pcm_refinement'_comp_new_one re' x frame;
    let frame' = op p re'.new_one frame in
    p.assoc y re'.new_one frame;
    re'.new_one_is_refined_unit y;
    p.assoc x re'.new_one frame;
    re'.new_one_is_refined_unit x
  in FStar.Classical.forall_intro aux;
  w

(** The refinement of a ref *)

let ref_refine (#a:Type) (#b:Type) (#p:refined_one_pcm b)
  (r: ref a p) (new_re: pcm_refinement p)
: ref a (refined_pcm new_re.refi) = {
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

let ref_focus r q l =
  {p = r.p; re = r.re; pl = pcm_lens_comp r.pl l; r = r.r}

let focus (r: ref 'a 'p)
  (#q: refined_one_pcm 'c)
  (l: pcm_lens 'p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: Steel (ref 'a q)
    (r `pts_to` s)
    (fun r' -> r' `pts_to` x)
    (fun _ -> Ghost.reveal s == put l x (one 'p))
    (fun _ r' _ -> r' == ref_focus r q l)
= let r' = ref_focus r q l in
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
    (requires fun _ -> r == ref_focus r' q l)
    (ensures fun _ _ _ -> True)
= A.change_slprop_rel  
    (r `pts_to` x)
    (r' `pts_to` put l x (one p))
    (fun _ _ -> True)
    (fun m -> r'.pl.get_morphism.f_one ())

let split r xy x y =
  A.change_equal_slprop
    (r `pts_to` xy)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl xy (one (refined_pcm r.re.refi)))));
  (refined_pcm r.re.refi).is_unit (one (refined_pcm r.re.refi));
  r.pl.put_morphism.f_op
    (Ghost.reveal x, one (refined_pcm r.re.refi))
    (Ghost.reveal y, one (refined_pcm r.re.refi));
  Steel.PCMReference.split r.r
    (put r.pl xy (one (refined_pcm r.re.refi)))
    (put r.pl x (one (refined_pcm r.re.refi)))
    (put r.pl y (one (refined_pcm r.re.refi)));
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl x (one (refined_pcm r.re.refi)))))
    (r `pts_to` x);
  A.change_equal_slprop
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl y (one (refined_pcm r.re.refi)))))
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
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl x (one (refined_pcm r.re.refi)))));
  A.change_equal_slprop
    (r `pts_to` y)
    (r.r `mpts_to` Ghost.reveal (Ghost.hide (put r.pl y (one (refined_pcm r.re.refi)))));
  mgather r.r
    (put r.pl x (one (refined_pcm r.re.refi)))
    (put r.pl y (one (refined_pcm r.re.refi)));
  r.pl.get_morphism.f_op
    (put r.pl x (one (refined_pcm r.re.refi)))
    (put r.pl y (one (refined_pcm r.re.refi)));
  (refined_pcm r.re.refi).is_unit (one (refined_pcm r.re.refi));
  r.pl.put_morphism.f_op
    (Ghost.reveal x, one (refined_pcm r.re.refi))
    (Ghost.reveal y, one (refined_pcm r.re.refi));
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

let refine r re x =
  let r' = ref_refine r re in
  A.change_equal_slprop (r `pts_to` x) (r' `pts_to` Ghost.reveal x);
  A.return r'

let unrefine #inames r' re r x =
  A.change_equal_slprop (r `pts_to` Ghost.reveal x) (r' `pts_to` x)

let ref_read (#p: refined_one_pcm 'b) (#x: Ghost.erased 'b) (r: ref 'a p)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> ~ (Ghost.reveal x == one p))
    (ensures fun _ x' _ -> compatible p x x')
= let x' = Ghost.hide (put r.pl x (one (refined_pcm r.re.refi))) in
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
    (put r.pl x (one (refined_pcm r.re.refi)))
    (put r.pl y (one (refined_pcm r.re.refi)))
= let x' = Ghost.hide (put r.pl x (one (refined_pcm r.re.refi))) in
  let y' = Ghost.hide (put r.pl y (one (refined_pcm r.re.refi))) in
  pcm_lens_frame_pres r.pl x' y f;
  r.re.u x' y' (frame_pres_mk_upd (refined_pcm r.re.refi) x' y' (upd r.pl f))

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
