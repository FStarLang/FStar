module AggregateRef

open FStar.PCM
module P = FStar.PCM

(** Misc. combinators *)
let compose (f: 'b -> 'c) (g: 'a -> 'b) (x: 'a): 'c = f (g x)
let both (f: 'a -> 'c) (g: 'b -> 'd) ((x, y): 'a & 'b): 'c & 'd = (f x, g y)
let uncurry (f: 'a -> 'b -> 'c) ((x, y): 'a & 'b): 'c = f x y
let conj (f: 'a -> prop) (g:(x:'a{f x} -> prop)) (x: 'a): prop = f x /\ g x
    
(** The non-computational part of frame_preserving_upd
    TODO: move this and lemmas about this to FStar.PCM.fst *)
let frame_pres_on (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a)
  (v:'a{p.refine v /\ compatible p x v})
= p.refine (f v) /\
  compatible p y (f v) /\
  (forall (frame:'a{composable p x frame}).{:pattern composable p x frame}
     composable p y frame /\
     (op p x frame == v ==> op p y frame == f v))
let frame_pres (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a) =
  forall (v:'a{p.refine v /\ compatible p x v}).{:pattern compatible p x v}
  frame_pres_on p f x y v

(** Every function satisfying frame_pres is a frame_preserving_upd *)
let frame_pres_mk_upd (p: pcm 'a) (x y: Ghost.erased 'a)
  (f:('a -> 'a){frame_pres p f x y})
  : frame_preserving_upd p x y
  = fun v -> f v
(** The converse is not true, because a frame_preserving_upd's domain
    is restricted to v:a{p.refine v /\ compatible p x v}. *)

let frame_pres_intro (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a)
  (g:(v:'a{p.refine v /\ compatible p x v} -> 
     Lemma (p.refine (f v) /\ compatible p y (f v) /\
            (forall (frame:'a{composable p x frame}).
              composable p y frame /\
              (op p x frame == v ==> op p y frame == f v)))
     [SMTPat (compatible p x v)]))
: Lemma (frame_pres p f x y) =
  let _ = g in ()

(** TODO move PCM morphisms and refinements to FStar.PCM.fst? *)

(** PCM morphisms *)

let morphism_refine (p: pcm 'a) (q: pcm 'b) (f: 'a -> 'b) =
  x:'a -> Lemma (requires p.refine x) (ensures q.refine (f x)) [SMTPat (p.refine x)]
let morphism_one (p: pcm 'a) (q: pcm 'b) (f: 'a -> 'b) =
  unit -> Lemma (f (one p) == one q)
let morphism_op (p: pcm 'a) (q: pcm 'b) (f: 'a -> 'b) =
  x:'a -> y:'a ->
    Lemma 
      (requires composable p x y) 
      (ensures composable q (f x) (f y) /\ f (op p x y) == op q (f x) (f y))
      [SMTPat (composable p x y)]

noeq type pcm_morphism #a #b (f: a -> b) (p: pcm a) (q: pcm b) = {
  f_refine: x:a -> Lemma (requires p.refine x) (ensures q.refine (f x)) [SMTPat (p.refine x)];
  f_one: morphism_one p q f;
  f_op: x:a -> y:a ->
    Lemma 
      (requires composable p x y) 
      (ensures composable q (f x) (f y) /\ f (op p x y) == op q (f x) (f y))
      [SMTPat (composable p x y)]
}

let pcm_morphism_id (#p: pcm 'a): pcm_morphism id p p = {
  f_refine = (fun _ -> ());
  f_one = (fun _ -> ());
  f_op = (fun _ _ -> ());
}

let pcm_morphism_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c) (#f: 'b -> 'c) (#g: 'a -> 'b)
  (mf: pcm_morphism f q r) (mg: pcm_morphism g p q)
: pcm_morphism (f `compose` g) p r = {
  f_refine = (fun x -> mg.f_refine x; mf.f_refine (g x));
  f_one = (fun () -> mg.f_one (); mf.f_one ());
  f_op = (fun x y -> mg.f_op x y; mf.f_op (g x) (g y));
}

open Aggregates
let pcm_morphism_both (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c) (#s: pcm 'd) (#f: 'a -> 'c) (#g: 'b -> 'd)
  (mf: pcm_morphism f p r) (mg: pcm_morphism g q s)
: pcm_morphism (both f g) (p `pcm_times` q) (r `pcm_times` s) = {
  f_refine = (fun (x, y) -> mf.f_refine x; mg.f_refine y);
  f_one = (fun () -> mg.f_one (); mf.f_one ());
  f_op = (fun (x, y) (z, w) -> mf.f_op x z; mg.f_op y w);
}

(** A refinement of a PCM (p: pcm a) consists of:
    (1) A set of elements f:(a -> prop) closed under (op p)
    (2) An element new_unit which satisfies the unit laws on the subset f
        and p.refine *)
let refine_t (f: 'a -> prop) = x:'a{f x}
noeq type pcm_refinement #a (p: pcm a) = {
  f: a -> prop;
  f_closed_comp: x: refine_t f -> y: a{composable p x y} -> Lemma (f (op p x y));
  new_one: (new_one:refine_t f{p.refine new_one});
  new_one_is_refined_unit: x: refine_t f -> Lemma (composable p x new_one /\ op p x new_one == x)
}

let pcm_refine_comp (#p: pcm 'a) (r: pcm_refinement p): symrel (refine_t r.f) = composable p

let pcm_refine_op (#p: pcm 'a) (r: pcm_refinement p)
  (x: refine_t r.f) (y: refine_t r.f{composable p x y}): refine_t r.f
= r.f_closed_comp x y; op p x y

(** Any refinement r for p can be used to construct a refined PCM with the same product
    and composability predicate, but restricted to elements in r.f *)
let refined_one_pcm a = p:pcm a{p.refine (one p)}
let refined_pcm (#p: pcm 'a) (r: pcm_refinement p): refined_one_pcm (refine_t r.f) = {
  p = {composable = pcm_refine_comp r; op = pcm_refine_op r; one = r.new_one};
  comm = (fun x y -> p.comm x y);
  assoc = (fun x y z -> p.assoc x y z);
  assoc_r = (fun x y z -> p.assoc_r x y z);
  is_unit = (fun x -> r.new_one_is_refined_unit x);
  refine = p.refine;
}

let pcm_refinement_comp_new_one (#p: pcm 'a)
  (re: pcm_refinement p) (x: refine_t re.f)
  (y: 'a{composable p x y})
: Lemma (composable p re.new_one y /\ re.f (op p re.new_one y) /\
         composable (refined_pcm re) x (op p re.new_one y))
= re.new_one_is_refined_unit x;
  p.assoc_r x re.new_one y;
  re.f_closed_comp re.new_one y

let pcm_refinement_compatible_closed (#p: pcm 'a)
  (re: pcm_refinement p) (x: refine_t re.f)
  (y: 'a{compatible p x y})
: Lemma (re.f y /\ compatible (refined_pcm re) x y)
= let p' = refined_pcm re in
  compatible_elim p x y (re.f y) (fun frame ->
   re.f_closed_comp x frame; p.comm frame x);
  compatible_elim p x y (compatible p' x y) (fun frame_x ->
    pcm_refinement_comp_new_one re x frame_x;
    let frame = op p re.new_one frame_x in
    re.new_one_is_refined_unit x;
    p.comm x frame_x;
    p.assoc x re.new_one frame_x;
    p.comm x (op p re.new_one frame_x);
    compatible_intro p' x y (op p re.new_one frame_x))

(** A PCM refinement is well-formed if frame-preserving updates on the
    refined PCM can be turned to frame-preserving updates on the
    unrefined PCM *)

(** Very well-behaved lenses *)
noeq type lens (a: Type u#a) (b: Type u#b) = {
  get: a -> b;
  put: b -> a -> a;
  get_put: s: a -> v: b -> Lemma (get (put v s) == v);
  put_get: s: a -> Lemma (put (get s) s == s);
  put_put: s: a -> v: b -> w: b -> Lemma (put v (put w s) == put v s);
}
let get_put' (l: lens 'a 'b) (s: 'a) (v: 'b)
  : Lemma (l.get (l.put v s) == v) [SMTPat (l.get (l.put v s))]
  = l.get_put s v
let put_get' (l: lens 'a 'b) (s: 'a)
  : Lemma (l.put (l.get s) s == s) [SMTPat (l.put (l.get s))]
  = l.put_get s
let put_put' (l: lens 'a 'b) (s: 'a) (v w: 'b)
  : Lemma (l.put v (l.put w s) == l.put v s) [SMTPat (l.put v (l.put w s))]
  = l.put_put s v w

(** Updating the target of a lens *)
let lens_upd (l: lens 'a 'b) (f: 'b -> 'b) (s: 'a): 'a = l.put (f (l.get s)) s

(** The identity lens *)
let const (x: 'a) (b: 'b): 'a = x
let lens_id #a : lens a a = {
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
let lens_comp (l: lens 'a 'b) (m: lens 'b 'c): lens 'a 'c = {
  get = get_comp l m;
  put = put_comp l m;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

(** Given PCMs (p: pcm a) and (q: pcm b), a (pcm_lens p q) is a (lens a b) where
    (1) get is a PCM morphism p -> q
    (2) put is a PCM morphism q×p -> p *)

noeq type pcm_lens #a #b (p: pcm a) (q: pcm b) = {
  l: lens a b;
  get_morphism: pcm_morphism l.get p q;
  put_morphism: pcm_morphism (uncurry l.put) (q `pcm_times` p) p;
}
let get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (s: 'a): 'b = l.l.get s
let put (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (v: 'b) (s: 'a): 'a = l.l.put v s
let upd (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (f: 'b -> 'b) (s: 'a): 'a = lens_upd l.l f s

(** The upd function of a pcm_lens lifts frame-preserving updates on the target to
    frame-preserving updates on the source *)

let compatible_pcm_morphism (#p: pcm 'a) (#q: pcm 'b)
  (f: 'a -> 'b) (m: pcm_morphism f p q) (x y: Ghost.erased 'a)
: Lemma (requires compatible p x y) (ensures compatible q (f x) (f y))
= compatible_elim p x y (compatible q (f x) (f y)) (fun frame_x ->
  let _ = m.f_op frame_x x in
  compatible_intro q (f x) (f y) (f frame_x))

let pcm_lens_compatible_get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (x y: 'a)
: Lemma (requires compatible p x y) (ensures compatible q (get l x) (get l y))
= compatible_pcm_morphism l.l.get l.get_morphism x y
    
let pcm_lens_frame_pres (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (s: 'a) (v: 'b) (f: 'b -> 'b)
: Lemma
    (requires frame_pres q f (get l s) v)
    (ensures frame_pres p (upd l f) s (put l v s))
    [SMTPat (frame_pres q f (get l s) v)]
= frame_pres_intro p (upd l f) s (put l v s) (fun full ->
    let _ = l.get_morphism.f_refine in
    pcm_lens_compatible_get l s full;
    l.put_morphism.f_refine (f (get l full), full);
    let goal = frame_pres_on p (upd l f) s (put l v s) full in
    compatible_elim p s full goal (fun frame_s ->
    compatible_elim q v (f (get l full)) goal (fun frame_v ->
    let frame_vs: 'a = put l frame_v frame_s in
    l.put_morphism.f_op (v, s) (frame_v, frame_s);
    p.comm frame_vs (put l v s);
    q.comm v frame_v;
    p.comm s frame_s;
    compatible_intro p (put l v s) (upd l f full) frame_vs;
    let aux (frame:'a{composable p s frame})
    : Lemma (composable p (put l v s) frame /\
             (op p s frame == full ==> op p (put l v s) frame == upd l f full))
    = l.get_morphism.f_op s frame;
      l.put_morphism.f_op (v, s) (get l frame, frame);
      let aux ()
      : Lemma (requires op p s frame == full) 
              (ensures op p (put l v s) frame == upd l f full)
      = () in ()
    in FStar.Classical.forall_intro aux)))

(** The identity lens is a pcm_lens *)
let pcm_lens_id (#p: pcm 'a): pcm_lens p p = {
  l = lens_id; 
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

(** pcm_lens composition is lens composition *)
let pcm_lens_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (l: pcm_lens p q) (m: pcm_lens q r): pcm_lens p r = 
{
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

let frame_pres_lift (p: pcm 'a) (x y: Ghost.erased 'a) (q: pcm 'b) (x' y': Ghost.erased 'b) =
  frame_preserving_upd p x y ->
  frame_preserving_upd q x' y'

let pcm_unrefinement (#p: pcm 'a) (r: pcm_refinement p) =
  x: Ghost.erased (refine_t r.f) ->
  y: Ghost.erased (refine_t r.f) ->
  frame_pres_lift (refined_pcm r) x y p (Ghost.reveal x) (Ghost.reveal y)

(** A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a.
    The base type of the lens, unlike the Steel.Memory.ref, is refined by a refinement re.
    This allows the reference to point to substructures of unions with known case. *)
noeq type ref (a:Type) (b:Type): Type = {
  p: refined_one_pcm a;
  re: pcm_refinement p;
  (** Needed to turn frame-preserving updates on (refined_pcm re) into
      frame-preserving updates on p. To do so, also requires that p and q
      be `refined_one_pcm`s *)
  u: pcm_unrefinement re;
  q: refined_one_pcm b;
  pl: pcm_lens (refined_pcm re) q;
  r: Steel.Memory.ref a p;
}

open Steel.Effect

let mpts_to (#p: pcm 'a) (r: Steel.Memory.ref 'a p) = Steel.PCMReference.pts_to r
let pts_to (r: ref 'a 'b) (v: Ghost.erased 'b): vprop = (* TODO unerase v, try [@@@smt_fallback] *)
  r.r `mpts_to` put r.pl v (one (refined_pcm r.re))

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

let inl_refinement (p: refined_one_pcm 'a) (q: pcm 'b): pcm_refinement (either_pcm p q) = {
  f = (fun (x: option (either 'a 'b)) -> Some? x /\ Inl? (Some?.v x));
  f_closed_comp = (fun _ _ -> ());
  new_one = Some (Inl #_ #'b (one p));
  new_one_is_refined_unit = (fun (Some (Inl x)) -> p.is_unit x);
}

(** A lens for the k-th field of an n-ary product *)

let fun_upd (#a:eqtype) #f_ty (k:a) (x':f_ty k)
  (f: restricted_t a f_ty)
: restricted_t a f_ty
= on_domain a (fun k' -> if k = k' then x' else f k')
let lens_field_get (#a:eqtype) f (k:a) (s:restricted_t a f): f k = s k
let lens_field (#a:eqtype) f (k:a): lens (restricted_t a f) (f k) = {
  get = lens_field_get f k;
  put = fun_upd k;
  get_put = (fun s v -> ());
  put_get = (fun s -> ext (fun_upd k (lens_field_get f k s) s) s (fun _ -> ()));
  put_put = (fun s v w -> ext (fun_upd k v (fun_upd k w s)) (fun_upd k v s) (fun _ -> ()));
}

(** lens_field is a pcm_lens *)

(* TODO move to Aggregates.fst *)
let prod_pcm_composable_intro (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b)
  (h:(k:'a -> Lemma (composable (p k) (x k) (y k))))
: Lemma (composable (prod_pcm p) x y) = FStar.Classical.forall_intro h

let field (#a:eqtype) #f (p:(k:a -> pcm (f k))) (k:a): pcm_lens (prod_pcm p) (p k) = {
  l = lens_field f k;
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {
    f_refine = (fun _ -> ());
    f_one = (fun _ ->
      ext
        (fun_upd k (one (p k)) (one (prod_pcm p)))
        (one (prod_pcm p))
        (fun k -> ()));
    f_op = (fun (v, s) (w, t) ->
      prod_pcm_composable_intro p (fun_upd k v s) (fun_upd k w t) (fun _ -> ());
      ext
        (fun_upd k (op (p k) v w) (op (prod_pcm p) s t))
        (op (prod_pcm p) (fun_upd k v s) (fun_upd k w t))
        (fun _ -> ()));
  }
}

(** The refinement of an n-ary union PCM to the k-th case *)

let case_refinement_f (p:(k:'a -> pcm ('b k))) (k:'a): union 'b -> prop =
  fun kx -> match kx with Some (|k', _|) -> k == k' | None -> False

let case_refinement_new_one (p:(k:'a -> pcm ('b k))) (k:'a)
: refine_t (case_refinement_f p k)
= Some (|k, one (p k)|)

let case_refinement (p:(k:'a -> refined_one_pcm ('b k))) (k:'a)
: pcm_refinement (union_pcm p) = {
  f = case_refinement_f p k;
  f_closed_comp = (fun x y -> ());
  new_one = case_refinement_new_one p k;
  new_one_is_refined_unit = (fun (Some (|k', x|)) -> (p k).is_unit x)
}

let case_unrefinement (#a:eqtype) #b (p:(k:a -> refined_one_pcm (b k))) (k:a)
: pcm_unrefinement (case_refinement p k)
= fun kx ky f kv ->
  let p' = refined_pcm (case_refinement p k) in
  let p = union_pcm p in
  match kv with
  | Some (|k', v|) ->
    if k = k' then begin
      let _ = Ghost.hide (
        let Some (|k, x|) = Ghost.reveal kx in
        let goal = compatible p' kx kv in
        compatible_elim p kx kv goal (fun kx_frame -> match kx_frame with
          | Some (|_, frame_x|) -> compatible_intro p' kx kv (Some (|k, frame_x|))
          | None -> compatible_refl p' kx))
      in
      let kw = f kv in
      let aux (frame:union b{composable p kx frame})
      : Lemma (composable p ky frame /\
               (op p kx frame == Some (|k, v|) ==>
                op p ky frame == f (Some (|k, v|))))
      = let Some (|_, w|) = f (Some (|k, v|)) in
        match frame with
        | Some (|frame_k, frame_v|) -> assert (composable p' kx frame)
        | None ->
          p'.is_unit kx;
          assert (composable p' kx (one p'));
          p'.is_unit ky
      in FStar.Classical.forall_intro aux;
      kw
    end else None
  | _ -> None

(** A lens for the k-th case of an n-ary union *)

let lens_case_get (p:(k:'a -> pcm ('b k))) (k:'a): refine_t (case_refinement_f p k) -> 'b k =
  fun (Some (|_, v|)) -> v
let lens_case_put (p:(k:'a -> pcm ('b k))) (k:'a) (v:'b k)
: refine_t (case_refinement_f p k) -> refine_t (case_refinement_f p k)
= fun _ -> Some (|k, v|)
  
let lens_case (p:(k:'a -> pcm ('b k))) (k:'a): lens (refine_t (case_refinement_f p k)) ('b k) = {
  get = lens_case_get p k;
  put = lens_case_put p k;
  get_put = (fun s v -> ());
  put_get = (fun s -> ());
  put_put = (fun s v w -> ());
}

(** lens_case is a pcm_lens *)
let case (p:(k:'a -> refined_one_pcm ('b k))) (k:'a)
: pcm_lens (refined_pcm (case_refinement p k)) (p k) = {
  l = lens_case p k;
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

(** Refining a pcm_lens *)

let extend_refinement_f (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement q) (x: 'a): prop
= re.f (get l x)

let lens_refine_get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement q) (s: refine_t (extend_refinement_f l re))
: refine_t re.f
= l.l.get s

let lens_refine_put (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement q)
  (v: refine_t re.f) (s: refine_t (extend_refinement_f l re))
: refine_t (extend_refinement_f l re)
= l.l.put v s

let lens_refine (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (re: pcm_refinement q)
: lens (refine_t (extend_refinement_f l re)) (refine_t re.f) = {
  get = lens_refine_get l re;
  put = lens_refine_put l re;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

let extend_refinement_f_closed (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement q) (x: refine_t (extend_refinement_f l re))
  (y: 'a{composable p x y})
: Lemma (extend_refinement_f l re (op p x y))
= l.get_morphism.f_op x y;
  re.f_closed_comp (get l x) (get l y)

let extend_refinement_new_one (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: new_one:refine_t (extend_refinement_f l re){p.refine new_one}
= l.put_morphism.f_refine (re.new_one, one p); put l re.new_one (one p)

let extend_refinement_new_one_is_refined_unit
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b) (l: pcm_lens p q)
  (re: pcm_refinement q) (x: refine_t (extend_refinement_f l re))
: Lemma (composable p x (extend_refinement_new_one l re) /\
         op p x (extend_refinement_new_one l re) == x)
= re.new_one_is_refined_unit (get l x);
  p.is_unit x;
  l.put_morphism.f_op (get l x, x) (re.new_one, one p)
  
let extend_refinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: pcm_refinement p = {
  f = extend_refinement_f l re;
  f_closed_comp = extend_refinement_f_closed l re;
  new_one = extend_refinement_new_one l re;
  new_one_is_refined_unit = extend_refinement_new_one_is_refined_unit l re;
}

let pcm_lens_refine_get_morphism_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: morphism_refine
    (refined_pcm (extend_refinement l re))
    (refined_pcm re)
    (lens_refine l re).get
= l.get_morphism.f_refine

let pcm_lens_refine_get_morphism_one
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: morphism_one
    (refined_pcm (extend_refinement l re))
    (refined_pcm re)
    (lens_refine l re).get
= l.get_morphism.f_one

let pcm_lens_refine_get_morphism_op
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: morphism_op
    (refined_pcm (extend_refinement l re))
    (refined_pcm re)
    (lens_refine l re).get
= l.get_morphism.f_op

let pcm_lens_refine_put_morphism_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: morphism_refine
    (refined_pcm re `pcm_times` refined_pcm (extend_refinement l re))
    (refined_pcm (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= fun (v, s) -> l.put_morphism.f_refine (v, s)

let pcm_lens_refine_put_morphism_one
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: morphism_one
    (refined_pcm re `pcm_times` refined_pcm (extend_refinement l re))
    (refined_pcm (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= l.put_morphism.f_one

let pcm_lens_refine_put_morphism_op
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: morphism_op
    (refined_pcm re `pcm_times` refined_pcm (extend_refinement l re))
    (refined_pcm (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= fun (v, s) (w, t) -> l.put_morphism.f_op (v, s) (w, t)

let pcm_lens_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
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

noeq type iso a b = {
  fwd: a -> b;
  bwd: b -> a;
  fwd_bwd: x:b -> Lemma (fwd (bwd x) == x);
  bwd_fwd: x:a -> Lemma (bwd (fwd x) == x);
}
let fwd_bwd' (i: iso 'a 'b) (x: 'b): Lemma (i.fwd (i.bwd x) == x) [SMTPat (i.fwd (i.bwd x))] = i.fwd_bwd x
let bwd_fwd' (i: iso 'a 'b) (x: 'a): Lemma (i.bwd (i.fwd x) == x) [SMTPat (i.bwd (i.fwd x))] = i.bwd_fwd x

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

noeq type pcm_iso #a #b (p: pcm a) (q: pcm b) = {
  i: iso a b;
  fwd_morphism: pcm_morphism i.fwd p q;
  bwd_morphism: pcm_morphism i.bwd q p;
}

let pcm_refinement_conj_iso_i (p: pcm 'a)
  (re1: pcm_refinement p)
  (re2: pcm_refinement (refined_pcm re1))
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
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
: 'a -> prop = conj #'a re1.f re2.f

let conj_refinement_f_closed (#p: pcm 'a)
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
  (x: refine_t (conj_refinement_f re1 re2))
  (y: 'a{composable p x y})
: Lemma (conj_refinement_f re1 re2 (op p x y))
= pcm_refinement_comp_new_one re1 x y;
  re1.f_closed_comp x (op p re1.new_one y);
  pcm_refinement_comp_new_one re2 x (op p re1.new_one y);
  re2.f_closed_comp x (op p re2.new_one (op p re1.new_one y));
  p.assoc x re2.new_one (op p re1.new_one y);
  re2.new_one_is_refined_unit x;
  p.assoc x re1.new_one y;
  re1.new_one_is_refined_unit x

(* re1.new_one and re2.new_one both work; we go with re2 *)
let conj_refinement_new_one (#p: pcm 'a)
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
: refine_t (conj_refinement_f re1 re2)
= re2.new_one

let conj_refinement_new_one_is_refined_unit (#p: pcm 'a)
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
  (x: refine_t (conj_refinement_f re1 re2))
: Lemma (composable p x (conj_refinement_new_one re1 re2) /\
         op p x (conj_refinement_new_one re1 re2) == x)
= re2.new_one_is_refined_unit x

let conj_refinement (#p: pcm 'a)
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
: pcm_refinement p = {
  f = conj_refinement_f re1 re2;
  f_closed_comp = conj_refinement_f_closed re1 re2;
  new_one = conj_refinement_new_one re1 re2;
  new_one_is_refined_unit = conj_refinement_new_one_is_refined_unit re1 re2;
}

(** A refinement re1 of a refinement re2 of a PCM is isomorphic to a
    refinement by the conjunction of re1 and re2 *)
let pcm_refinement_conj_iso (p: pcm 'a)
  (re1: pcm_refinement p)
  (re2: pcm_refinement (refined_pcm re1))
: pcm_iso (refined_pcm (conj_refinement re1 re2)) (refined_pcm re2) = {
  i = pcm_refinement_conj_iso_i p re1 re2;
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
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
  (h1: pcm_unrefinement re1) (h2: pcm_unrefinement re2)
: pcm_unrefinement (conj_refinement #'a re1 re2)
= fun x y ->
  h1 (Ghost.reveal x) (Ghost.reveal y) `compose`
  h2 (Ghost.reveal x) (Ghost.reveal y) `compose`
  upd_across_pcm_iso (pcm_refinement_conj_iso p re1 re2) x y

let extend_unrefinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q) (u: pcm_unrefinement re)
: pcm_unrefinement (extend_refinement l re)
= fun x y f v ->
  let re' = extend_refinement l re in
  let p' = refined_pcm re' in
  pcm_refinement_compatible_closed re' x v;
  pcm_lens_compatible_get l x v;
  let w = f v in
  let aux (frame:'a{composable p x frame})
  : Lemma (composable p y frame /\ (op p x frame == v ==> op p y frame == w))
  = pcm_refinement_comp_new_one re' x frame;
    let frame' = op p re'.new_one frame in
    p.assoc y re'.new_one frame;
    re'.new_one_is_refined_unit y;
    p.assoc x re'.new_one frame;
    re'.new_one_is_refined_unit x
  in FStar.Classical.forall_intro aux;
  w

(** The refinement of a ref *)

let ref_refine (r: ref 'a 'b)
  (new_re: pcm_refinement r.q) (new_u: pcm_unrefinement new_re)
: ref 'a (refine_t new_re.f) = {
  p = r.p;
  re = conj_refinement r.re (extend_refinement r.pl new_re);
  u =
    conj_unrefinement r.re (extend_refinement r.pl new_re) r.u
      (extend_unrefinement r.pl new_re new_u);
  q = refined_pcm new_re;
  pl =
    pcm_iso_lens_comp
      (pcm_refinement_conj_iso r.p r.re (extend_refinement r.pl new_re))
      (pcm_lens_refine r.pl new_re);
  r = r.r
}

(** Fundamental operations on references *)

module M = Steel.Memory
module A = Steel.Effect.Atomic

let ref_focus (r: ref 'a 'b) (q: refined_one_pcm 'c) (l: pcm_lens r.q q): ref 'a 'c =
  {p = r.p; re = r.re; u = r.u; q = q; pl = pcm_lens_comp r.pl l; r = r.r}

let focus (r: ref 'a 'b) (q: refined_one_pcm 'c)
  (l: pcm_lens r.q q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: Steel (ref 'a 'c)
    (r `pts_to` s)
    (fun r' -> r' `pts_to` x)
    (fun _ -> Ghost.reveal s == put l x (one r.q))
    (fun _ r' _ -> r' == ref_focus r q l)
= let r' = ref_focus r q l in
  A.change_slprop_rel  
    (r `pts_to` s)
    (r' `pts_to` x)
    (fun _ _ -> True)
    (fun m -> r.pl.get_morphism.f_one ());
  A.return r'

let unfocus #inames (r: ref 'a 'c) (r': ref 'a 'b) (#r'q: pcm 'b) (#q: refined_one_pcm 'c)
  (l: pcm_lens r'q q) (x: Ghost.erased 'c)
: A.SteelGhost unit inames
    (r `pts_to` x)
    (fun _ -> r' `pts_to` put l x (one r'.q))
    (requires fun _ -> r'.q == r'q /\ r == ref_focus r' q l)
    (ensures fun _ _ _ -> True)
= A.change_slprop_rel  
    (r `pts_to` x)
    (r' `pts_to` put l x (one r'.q))
    (fun _ _ -> True)
    (fun m -> r'.pl.get_morphism.f_one ())

let change_equal_vprop #inames (p q: M.slprop)
: A.SteelGhost unit inames (to_vprop p) (fun _ -> to_vprop q) (fun _ -> p == q) (fun _ _ _ -> True)
= A.change_equal_slprop (to_vprop p) (to_vprop q)
// TODO rename

let split (r: ref 'a 'c) (xy x y: Ghost.erased 'c)
: Steel unit
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> composable r.q x y /\ xy == Ghost.hide (op r.q x y))
    (fun _ _ _ -> True)
= A.change_equal_slprop
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

let mgather (#a:Type)
            (#p:FStar.PCM.pcm a)
            (r:Steel.Memory.ref a p)
            (v0:Ghost.erased a)
            (v1:Ghost.erased a)
: SteelT (_:unit{composable p v0 v1})
    (mpts_to r v0 `star` mpts_to r v1)
    (fun _ -> mpts_to r (op p v0 v1))
= Steel.PCMReference.gather r v0 v1

let gather (r: ref 'a 'c) (x y: Ghost.erased 'c)
: SteelT (_:unit{composable r.q x y})
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op r.q x y)
= A.change_equal_slprop
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
  A.change_equal_slprop _ (r `pts_to` op r.q x y)

let rewrite_context #inames (p q: vprop)
: Steel.Effect.Atomic.SteelAtomicF unit inames
    (p)
    (fun _ -> q)
    (requires fun _ -> p == q)
    (ensures fun _ _ _ -> True)
= A.change_equal_slprop p q

let peel (r: ref 'a 'b) (#rq: pcm 'b) (#q: refined_one_pcm 'c)
  (l: pcm_lens rq q) (x: Ghost.erased 'b)
: Steel unit
    (r `pts_to` x)
    (fun _ ->
      (r `pts_to` put l (one q) x) `star` 
      (r `pts_to` put l (get l x) (one r.q)))
    (requires fun _ -> rq == r.q)
    (ensures fun _ _ _ -> True)
= q.is_unit (get l x);
  r.q.is_unit x;
  q.comm (get l x) (one q);
  l.put_morphism.f_op (one q, Ghost.reveal x) (get l (Ghost.reveal x), one r.q);
  split r x (put l (one q) x) (put l (get l x) (one r.q));
  A.sladmit()
  //A.rewrite_context
  //A.change_equal_slprop ((r `pts_to` (Ghost.reveal (Ghost.hide (put l (one q) (Ghost.reveal x))))) `star` (r `pts_to` _)) ((r `pts_to` _) `star` (r `pts_to` _))

let addr_of_lens (r: ref 'a 'b) (#rq: pcm 'b) (#q: refined_one_pcm 'c)
  (l: pcm_lens rq q) (x: Ghost.erased 'b)
: Steel (ref 'a 'c)
    (r `pts_to` x)
    (fun s ->
      (r `pts_to` put l (one q) x) `star` 
      (s `pts_to` get l x))
    (requires fun _ -> rq == r.q)
    (ensures fun _ r' _ -> rq == r.q /\ r' == ref_focus r q l)
= peel r l x;
  focus r q l (put l (get l x) (one r.q)) (get l x)

let un_addr_of_lens
  (r': ref 'a 'c) (r: ref 'a 'b) (#rq: pcm 'b) (#q: refined_one_pcm 'c) (l: pcm_lens rq q)
  (x: Ghost.erased 'b) (y: Ghost.erased 'c)
: Steel unit
    ((r `pts_to` x) `star` (r' `pts_to` y))
    (fun s -> r `pts_to` put l y x)
    (requires fun _ -> rq == r.q /\ r' == ref_focus r q l /\ get l x == one q)
    (ensures fun _ _ _ -> True)
= unfocus r' r l y;
  gather r x (put l y (one r.q));
  q.is_unit (Ghost.reveal y);
  r.q.is_unit (Ghost.reveal x);
  q.comm (get l x) y;
  l.put_morphism.f_op (get l x, Ghost.reveal x) (Ghost.reveal y, one r.q);
  A.change_equal_slprop (r `pts_to` _) (r `pts_to` _);
  A.return ()

let refine (r: ref 'a 'b)
  (re: pcm_refinement r.q)
  (u: pcm_unrefinement re)
  (x: Ghost.erased 'b{re.f x})
: Steel (ref 'a (refine_t re.f))
    (r `pts_to` x)
    (fun r' -> r' `pts_to` Ghost.reveal x)
    (fun _ -> True)
    (fun _ r' _ -> r' == ref_refine r re u)
= let r' = ref_refine r re u in
  A.change_equal_slprop (r `pts_to` x) (r' `pts_to` Ghost.reveal x);
  A.return r'

let unrefine #inames (r': ref 'a 'b)
  (re: pcm_refinement r'.q) (u: pcm_unrefinement re)
  (r: ref 'a (refine_t re.f)) (x: Ghost.erased 'b{re.f x})
: A.SteelGhost unit inames
    (r `pts_to` Ghost.reveal x)
    (fun _ -> r' `pts_to` x)
    (fun _ -> r == ref_refine r' re u)
    (fun _ _ _ -> True)
= A.change_equal_slprop (r `pts_to` Ghost.reveal x) (r' `pts_to` x)


(*

describe this situation:

  thread 1: pointer to p.x
  
  thread 2: pointer to p but with permissions {None, y}
  
  *p a value compatible with {None, y}
  i.e., any {x, y} for any x
  x could be:
    Some z for a garbage z, or
    None

  but, impossible to work with p->x:
    *p = {x, y}
    ( *p).x == 0
    need {x, y}.x is Some v
    if (( *p).x == 0) { .. } else { .. }
    
  {None, y} compatible with {vx, vy} 
  let vx = ref_read &p->x in
  match vx with None -> .. | Some x -> ..

  {None, y} compatible with {vx, vy} 
  let vx = ref_read &p->x in
  let bad = (f : option int -> option int) vx in

  could prevent pattern matching if option int were an abstract type

*)

let ref_read (r: ref 'a 'b) (x: Ghost.erased 'b)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> ~ (Ghost.reveal x == one r.q))
    (ensures fun _ x' _ -> compatible r.q x x')
= let x' = Ghost.hide (put r.pl x (one (refined_pcm r.re))) in
  A.change_equal_slprop (r `pts_to` x) (r.r `mpts_to` x');
  let v = Steel.PCMReference.read r.r x' in
  pcm_refinement_compatible_closed r.re x' v;
  pcm_lens_compatible_get r.pl x' v;
  A.change_equal_slprop (r.r `mpts_to` x') (r `pts_to` x);
  A.return (get r.pl v)

let whole_value (p: pcm 'a) (x: 'a) =
  p.refine x /\
  (forall (y:'a{composable p x y}).{:pattern op p y x} op p y x == x)

let valid_write (p:pcm 'a) x y =
  whole_value p x /\ whole_value p y /\
  (forall (frame:'a). composable p x frame ==> composable p y frame)

let ref_frame_preserving_upd (r: ref 'a 'b) (x y: Ghost.erased 'b)
  (f: ('b -> 'b){frame_pres r.q f x y})
: frame_preserving_upd r.p
    (put r.pl x (one (refined_pcm r.re)))
    (put r.pl y (one (refined_pcm r.re)))
= let x' = Ghost.hide (put r.pl x (one (refined_pcm r.re))) in
  let y' = Ghost.hide (put r.pl y (one (refined_pcm r.re))) in
  pcm_lens_frame_pres r.pl x' y f;
  r.u x' y' (frame_pres_mk_upd (refined_pcm r.re) x' y' (upd r.pl f))

let ref_upd_act (r: ref 'a 'b) (x y: Ghost.erased 'b) (f: ('b -> 'b){frame_pres r.q f x y})
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

let ref_upd (r: ref 'a 'b) (x y: Ghost.erased 'b) (f: ('b -> 'b){frame_pres r.q f x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
= as_action (ref_upd_act r x y f)

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

let ref_write (r: ref 'a 'b) (x: Ghost.erased 'b) (y: 'b{valid_write r.q x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
= ref_upd r x y (frame_preserving_upd_valid_write r.q x y)

let ref_write_opt_pcm (r: ref 'a (option 'b){r.q == opt_pcm #'b}) (x: Ghost.erased 'b) (y: 'b)
: SteelT unit (r `pts_to` Some (Ghost.reveal x)) (fun _ -> r `pts_to` Some y)
= ref_write r (Some (Ghost.reveal x)) (Some y)


