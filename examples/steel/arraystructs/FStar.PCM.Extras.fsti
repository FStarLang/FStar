module FStar.PCM.Extras

open FStar.PCM
open Lens

/// We can define a PCM for structs with two fields {a; b} by defining
/// a PCM for tuples (a & b) in terms of (potentially user-defined)
/// PCMs for a and b.

let pcm_times_comp (p: pcm 'a) (q: pcm 'b) (x y: 'a & 'b) : prop =
  composable p (fst x) (fst y) /\ composable q (snd x) (snd y)

let pcm_times_op (p: pcm 'a) (q: pcm 'b) (x: 'a & 'b) (y: ('a & 'b){pcm_times_comp p q x y}) : 'a & 'b =
  (op p (fst x) (fst y), op q (snd x) (snd y))

let pcm_times (p: pcm 'a) (q: pcm 'b): pcm ('a & 'b) = {
  p = {composable = pcm_times_comp p q; op = pcm_times_op p q; one = (p.p.one, q.p.one)};
  comm = (fun (xa, xb) (ya, yb) -> p.comm xa ya; q.comm xb yb);
  assoc = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc xa ya za; q.assoc xb yb zb);
  assoc_r = (fun (xa, xb) (ya, yb) (za, zb) -> p.assoc_r xa ya za; q.assoc_r xb yb zb);
  is_unit = (fun (xa, xb) -> p.is_unit xa; q.is_unit xb);
  refine = (fun (xa, xb) -> p.refine xa /\ q.refine xb)
}

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

let opt_comp (x y: option 'a): prop = match x, y with
  | None, _ | _, None -> True
  | _, _ -> False

let opt_op (x: option 'a) (y: option 'a{opt_comp x y}): option 'a = match x, y with
  | None, z | z, None -> z

let opt_pcm #a : pcm (option a) = {
  p = {composable = opt_comp; op = opt_op; one = None};
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True);
}

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
  on_domain 'a (fun k -> (p k).p.one)

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
  forall k. (p k).refine (x k)

let prod_pcm (p:(k:'a -> pcm ('b k))): pcm (restricted_t 'a 'b) = {
  p = {composable = prod_comp p; op = prod_op p; one = prod_one p};
  comm = prod_comm p;
  assoc = prod_assoc p;
  assoc_r = prod_assoc_r p;
  is_unit = prod_is_unit p;
  refine = prod_refine p
}

let prod_pcm_composable_intro (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b)
  (h:(k:'a -> Lemma (composable (p k) (x k) (y k))))
: Lemma (composable (prod_pcm p) x y) = FStar.Classical.forall_intro h

/// Similarly, given a PCM for each k:a, we can model a-ary unions
/// with an PCM for option (k:a & f k), where
/// - None is the unit of the PCM
/// - Some (k, x) is a union with tag k and content x

open FStar.Real
let union (f:'a -> Type) = option (real & dtuple2 'a f)

let union_comp (p:(k:'a -> pcm ('b k))): symrel (union 'b) = fun x y -> match x, y with
  | None, z | z, None -> True
  | Some (|xa, xb|), Some (|ya, yb|) -> xa == ya /\ composable (p xa) xb yb

let union_op (p:(k:'a -> pcm ('b k))) (x: union 'b) (y: union 'b{union_comp p x y}) : union 'b = match x, y with
  | None, z | z, None -> z
  | Some (|xa, xb|), Some (|ya, yb|) -> Some (|xa, (p xa).p.op xb yb|)

let union_pcm (p:(k:'a -> pcm ('b k))): pcm (union 'b) = {
  p = {composable = union_comp p; op = union_op p; one = None};
  comm = (fun x y -> match x, y with
    | None, _ | _, None -> ()
    | Some (|xa, xb|), Some (|ya, yb|) -> (p xa).comm xb yb);
  assoc = (fun x y z -> match x, y, z with
    | None, _, _ | _, _, None | _, None, _ -> ()
    | Some (|xa, xb|), Some (|ya, yb|), Some (|za, zb|) -> (p xa).assoc xb yb zb);
  assoc_r = (fun x y z -> match x, y, z with
    | None, _, _ | _, _, None | _, None, _ -> ()
    | Some (|xa, xb|), Some (|ya, yb|), Some (|za, zb|) -> (p xa).assoc_r xb yb zb);
  is_unit = (fun _ -> ());
  refine = (fun x -> match x with None -> True | Some (|xa, xb|) -> (p xa).refine xb)
}

(** The non-computational part of frame_preserving_upd *)
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
: Lemma (frame_pres p f x y)
= let _ = g in ()

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

val pcm_morphism_id (#p: pcm 'a): pcm_morphism id p p

let compose (f: 'b -> 'c) (g: 'a -> 'b) (x: 'a): 'c = f (g x)
val pcm_morphism_comp
  (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (#f: 'b -> 'c) (#g: 'a -> 'b)
  (mf: pcm_morphism f q r) (mg: pcm_morphism g p q)
: pcm_morphism (f `compose` g) p r

val compatible_pcm_morphism
  (#p: pcm 'a) (#q: pcm 'b)
  (f: 'a -> 'b) (m: pcm_morphism f p q)
  (x y: Ghost.erased 'a)
: Lemma (requires compatible p x y) (ensures compatible q (f x) (f y))

(** A refinement of a PCM (p: pcm a) consists of:
    (1) A set of elements f:(a -> prop) closed under (op p)
    (2) An element new_unit which satisfies the unit laws on the subset f
        and p.refine *)
let refine_t (f: 'a -> prop) = x:'a{f x}
noeq type pcm_refinement' #a (p: pcm a) = {
  f: a -> prop;
  f_closed_comp: x: refine_t f -> y: a{composable p x y} -> Lemma (f (op p x y));
  new_one: (new_one:refine_t f{p.refine new_one});
  new_one_is_refined_unit: x: refine_t f -> Lemma (composable p x new_one /\ op p x new_one == x)
}

let pcm_refine_comp (#p: pcm 'a) (r: pcm_refinement' p): symrel (refine_t r.f) = composable p

let pcm_refine_op (#p: pcm 'a) (r: pcm_refinement' p)
  (x: refine_t r.f) (y: refine_t r.f{composable p x y}): refine_t r.f
= r.f_closed_comp x y; op p x y

(** Any refinement r for p can be used to construct a refined PCM with the same product
    and composability predicate, but restricted to elements in r.f *)
let refined_one_pcm a = p:pcm a{p.refine (one p)}
let refined_pcm' (#p: pcm 'a) (r: pcm_refinement' p): refined_one_pcm (refine_t r.f) = {
  p = {composable = pcm_refine_comp r; op = pcm_refine_op r; one = r.new_one};
  comm = (fun x y -> p.comm x y);
  assoc = (fun x y z -> p.assoc x y z);
  assoc_r = (fun x y z -> p.assoc_r x y z);
  is_unit = (fun x -> r.new_one_is_refined_unit x);
  refine = p.refine;
}

val pcm_refinement'_comp_new_one
  (#p: pcm 'a) (re: pcm_refinement' p)
  (x: refine_t re.f) (y: 'a{composable p x y})
: Lemma (composable p re.new_one y /\ re.f (op p re.new_one y) /\
         composable (refined_pcm' re) x (op p re.new_one y))

val pcm_refinement'_compatible_closed
  (#p: pcm 'a) (re: pcm_refinement' p)
  (x: refine_t re.f) (y: 'a{compatible p x y})
: Lemma (re.f y /\ compatible (refined_pcm' re) x y)

(** A PCM refinement is well-formed if frame-preserving updates on the
    refined PCM can be turned to frame-preserving updates on the
    unrefined PCM *)

let frame_pres_lift (p: pcm 'a) (x y: Ghost.erased 'a) (q: pcm 'b) (x' y': Ghost.erased 'b) =
  frame_preserving_upd p x y ->
  frame_preserving_upd q x' y'

let pcm_unrefinement (#p: pcm 'a) (r: pcm_refinement' p) =
  x: Ghost.erased (refine_t r.f) ->
  y: Ghost.erased (refine_t r.f) ->
  frame_pres_lift (refined_pcm' r) x y p (Ghost.reveal x) (Ghost.reveal y)

noeq type pcm_refinement #a (p: pcm a) = {
  refi: pcm_refinement' p;
  u: pcm_unrefinement refi;
}

let refinement_f (#p: pcm 'a) (r: pcm_refinement p) = r.refi.f

let refined_pcm (#p: pcm 'a) (r: pcm_refinement p)
: refined_one_pcm (refine_t (refinement_f r))
= refined_pcm' r.refi

(** Given PCMs (p: pcm a) and (q: pcm b), a (pcm_lens p q) is a (lens a b) where
    (1) get is a PCM morphism p -> q
    (2) put is a PCM morphism q×p -> p *)

let uncurry (f: 'a -> 'b -> 'c) ((x, y): 'a & 'b): 'c = f x y
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

val pcm_lens_compatible_get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (x y: 'a)
: Lemma (requires compatible p x y) (ensures compatible q (get l x) (get l y))

val pcm_lens_frame_pres
  (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q)
  (s: 'a) (v: 'b) (f: 'b -> 'b)
: Lemma
    (requires frame_pres q f (get l s) v)
    (ensures frame_pres p (upd l f) s (put l v s))
    [SMTPat (frame_pres q f (get l s) v)]

(** The identity lens is a pcm_lens *)
let pcm_lens_id (#p: pcm 'a): pcm_lens p p = {
  l = lens_id; 
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

(** pcm_lens composition is lens composition *)
let pcm_lens_comp
  (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (l: pcm_lens p q) (m: pcm_lens q r)
: pcm_lens p r = {
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

(** A lens for the k-th field of an n-ary product *)

open FStar.FunctionalExtensionality
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

let case_refinement' (p:(k:'a -> refined_one_pcm ('b k))) (k:'a)
: pcm_refinement' (union_pcm p) = {
  f = case_refinement_f p k;
  f_closed_comp = (fun x y -> ());
  new_one = case_refinement_new_one p k;
  new_one_is_refined_unit = (fun (Some (|k', x|)) -> (p k).is_unit x)
}

val case_unrefinement (#a:eqtype) (#b:a->Type) (p:(k:a -> refined_one_pcm (b k))) (k:a)
: pcm_unrefinement (case_refinement' p k)

let case_refinement (#a:eqtype) #b (p:(k:a -> refined_one_pcm (b k))) (k:a)
: pcm_refinement (union_pcm p) = {
  refi = case_refinement' p k;
  u = case_unrefinement p k;
}

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
: pcm_lens (refined_pcm' (case_refinement' p k)) (p k) = {
  l = lens_case p k;
  get_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  put_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

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
    (refined_pcm' (extend_refinement l re))
    (refined_pcm' re)
    (lens_refine l re).get
= l.get_morphism.f_refine

let pcm_lens_refine_get_morphism_one
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_one
    (refined_pcm' (extend_refinement l re))
    (refined_pcm' re)
    (lens_refine l re).get
= l.get_morphism.f_one

let pcm_lens_refine_get_morphism_op
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_op
    (refined_pcm' (extend_refinement l re))
    (refined_pcm' re)
    (lens_refine l re).get
= l.get_morphism.f_op

let pcm_lens_refine_put_morphism_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_refine
    (refined_pcm' re `pcm_times` refined_pcm' (extend_refinement l re))
    (refined_pcm' (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= fun (v, s) -> l.put_morphism.f_refine (v, s)

let pcm_lens_refine_put_morphism_one
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_one
    (refined_pcm' re `pcm_times` refined_pcm' (extend_refinement l re))
    (refined_pcm' (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= l.put_morphism.f_one

let pcm_lens_refine_put_morphism_op
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: morphism_op
    (refined_pcm' re `pcm_times` refined_pcm' (extend_refinement l re))
    (refined_pcm' (extend_refinement l re))
    (uncurry (lens_refine l re).put)
= fun (v, s) (w, t) -> l.put_morphism.f_op (v, s) (w, t)

let pcm_lens_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: pcm_lens (refined_pcm' (extend_refinement l re)) (refined_pcm' re) = {
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

let conj (f: 'a -> prop) (g:(x:'a{f x} -> prop)) (x: 'a): prop = f x /\ g x

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
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
: 'a -> prop = conj #'a re1.f re2.f

let conj_refinement_f_closed (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
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
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
: refine_t (conj_refinement_f re1 re2)
= re2.new_one

let conj_refinement_new_one_is_refined_unit (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
  (x: refine_t (conj_refinement_f re1 re2))
: Lemma (composable p x (conj_refinement_new_one re1 re2) /\
         op p x (conj_refinement_new_one re1 re2) == x)
= re2.new_one_is_refined_unit x

let conj_refinement (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
: pcm_refinement' p = {
  f = conj_refinement_f re1 re2;
  f_closed_comp = conj_refinement_f_closed re1 re2;
  new_one = conj_refinement_new_one re1 re2;
  new_one_is_refined_unit = conj_refinement_new_one_is_refined_unit re1 re2;
}

let pcm_refinement'_conj_iso_i (p: pcm 'a)
  (re1: pcm_refinement' p)
  (re2: pcm_refinement' (refined_pcm' re1))
: iso (refine_t #'a (conj #'a re1.f re2.f)) (refine_t #(x:'a{re1.f x}) re2.f) =
  refine_conj_iso re1.f re2.f
  
(** A refinement re1 of a refinement re2 of a PCM is isomorphic to a
    refinement by the conjunction of re1 and re2 *)
let pcm_refinement'_conj_iso (p: pcm 'a)
  (re1: pcm_refinement' p)
  (re2: pcm_refinement' (refined_pcm' re1))
: pcm_iso (refined_pcm' (conj_refinement re1 re2)) (refined_pcm' re2) = {
  i = pcm_refinement'_conj_iso_i p re1 re2;
  fwd_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
  bwd_morphism = {f_refine = (fun _ -> ()); f_one = (fun _ -> ()); f_op = (fun _ _ -> ())};
}

let upd_across_pcm_iso
  (#p: pcm 'a) (#q: pcm 'b) (i: pcm_iso p q) (x y: Ghost.erased 'a)
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

val conj_unrefinement (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
  (h1: pcm_unrefinement re1) (h2: pcm_unrefinement re2)
: pcm_unrefinement (conj_refinement #'a re1 re2)

val extend_unrefinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q) (u: pcm_unrefinement re)
: pcm_unrefinement (extend_refinement l re)

(** A PCM for possibly-uninitialized data *)

type init a =
| One : init a
| Uninitialized : init a
| Initialized : a -> init a

let init_comp (p: pcm 'a): symrel (init 'a) = fun x y -> match x, y with
  | One, _ | _, One -> True
  | Initialized x, Initialized y -> composable p x y
  | _, _ -> False

let init_op (p: pcm 'a) (x: init 'a) (y: init 'a{init_comp p x y}): init 'a = match x, y with
  | One, z | z, One -> z
  | Initialized x, Initialized y -> Initialized (op p x y)

let init_pcm (p: pcm 'a): pcm (init 'a) = {
  p = {composable = init_comp p; op = init_op p; one = One #'a};
  comm = (fun x y -> match x, y with
    | Initialized x, Initialized y -> p.comm x y
    | _, _ -> ());
  assoc = (fun x y z -> match x, y, z with
    | Initialized x, Initialized y, Initialized z -> p.assoc x y z
    | _, _, _ -> ());
  assoc_r = (fun x y z -> match x, y, z with
    | Initialized x, Initialized y, Initialized z -> p.assoc_r x y z
    | _, _, _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> match x with
    | Initialized x -> p.refine x
    | _ -> True)
}
