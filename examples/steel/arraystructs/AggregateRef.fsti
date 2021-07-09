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

val frame_pres_intro (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a)
  (g:(v:'a{p.refine v /\ compatible p x v} -> 
     Lemma (p.refine (f v) /\ compatible p y (f v) /\
            (forall (frame:'a{composable p x frame}).
              composable p y frame /\
              (op p x frame == v ==> op p y frame == f v)))
     [SMTPat (compatible p x v)]))
: Lemma (frame_pres p f x y)

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

val pcm_morphism_id (#p: pcm 'a): pcm_morphism id p p

val pcm_morphism_comp
  (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (#f: 'b -> 'c) (#g: 'a -> 'b)
  (mf: pcm_morphism f q r) (mg: pcm_morphism g p q)
: pcm_morphism (f `compose` g) p r

open Aggregates
val pcm_morphism_both
  (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c) (#s: pcm 'd)
  (#f: 'a -> 'c) (#g: 'b -> 'd)
  (mf: pcm_morphism f p r) (mg: pcm_morphism g q s)
: pcm_morphism (both f g) (p `pcm_times` q) (r `pcm_times` s)

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
let refined_pcm (#p: pcm 'a) (r: pcm_refinement' p): refined_one_pcm (refine_t r.f) = {
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
         composable (refined_pcm re) x (op p re.new_one y))

val pcm_refinement'_compatible_closed
  (#p: pcm 'a) (re: pcm_refinement' p)
  (x: refine_t re.f) (y: 'a{compatible p x y})
: Lemma (re.f y /\ compatible (refined_pcm re) x y)

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
val lens_upd (l: lens 'a 'b) (f: 'b -> 'b) (s: 'a): 'a

(** The identity lens *)
val lens_id: lens 'a 'a

(** Lens composition *)
val lens_comp (l: lens 'a 'b) (m: lens 'b 'c): lens 'a 'c

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

val compatible_pcm_morphism
  (#p: pcm 'a) (#q: pcm 'b)
  (f: 'a -> 'b) (m: pcm_morphism f p q)
  (x y: Ghost.erased 'a)
: Lemma (requires compatible p x y) (ensures compatible q (f x) (f y))

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
val pcm_lens_id (#p: pcm 'a): pcm_lens p p

(** pcm_lens composition is lens composition *)
val pcm_lens_comp
  (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (l: pcm_lens p q) (m: pcm_lens q r)
: pcm_lens p r

open FStar.FunctionalExtensionality

let frame_pres_lift (p: pcm 'a) (x y: Ghost.erased 'a) (q: pcm 'b) (x' y': Ghost.erased 'b) =
  frame_preserving_upd p x y ->
  frame_preserving_upd q x' y'

let pcm_unrefinement (#p: pcm 'a) (r: pcm_refinement' p) =
  x: Ghost.erased (refine_t r.f) ->
  y: Ghost.erased (refine_t r.f) ->
  frame_pres_lift (refined_pcm r) x y p (Ghost.reveal x) (Ghost.reveal y)

noeq type pcm_refinement #a (p: pcm a) = {
  refi: pcm_refinement' p;
  (** Needed to turn frame-preserving updates on (refined_pcm re) into
      frame-preserving updates on p. To do so, also requires that p and q
      be `refined_one_pcm`s *)
  u: pcm_unrefinement refi;
}

(** A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a.
    The base type of the lens, unlike the Steel.Memory.ref, is refined by a refinement re.
    This allows the reference to point to substructures of unions with known case. *)
noeq type ref a #b (q: refined_one_pcm b): Type = {
  p: refined_one_pcm a;
  re: pcm_refinement p;
  pl: pcm_lens (refined_pcm re.refi) q;
  r: Steel.Memory.ref a p;
}

open Steel.Effect

val pts_to
  (#a: Type u#1) (#b: Type u#b) (#p: refined_one_pcm b)
  (r: ref a p) ([@@@smt_fallback] v: Ghost.erased b)
: vprop

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
: pcm_refinement' (union_pcm p) = {
  f = case_refinement_f p k;
  f_closed_comp = (fun x y -> ());
  new_one = case_refinement_new_one p k;
  new_one_is_refined_unit = (fun (Some (|k', x|)) -> (p k).is_unit x)
}

(* TODO could be made abstract? *)
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

val extend_refinement
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: pcm_refinement' p

val pcm_lens_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q)
: pcm_lens (refined_pcm (extend_refinement l re)) (refined_pcm re)

(** Isomorphisms *)

noeq type iso a b = {
  fwd: a -> b;
  bwd: b -> a;
  fwd_bwd: x:b -> Lemma (fwd (bwd x) == x);
  bwd_fwd: x:a -> Lemma (bwd (fwd x) == x);
}
let fwd_bwd' (i: iso 'a 'b) (x: 'b): Lemma (i.fwd (i.bwd x) == x) [SMTPat (i.fwd (i.bwd x))] = i.fwd_bwd x
let bwd_fwd' (i: iso 'a 'b) (x: 'a): Lemma (i.bwd (i.fwd x) == x) [SMTPat (i.bwd (i.fwd x))] = i.bwd_fwd x

val iso_lens_comp (i: iso 'a 'b) (l: lens 'b 'c): lens 'a 'c

(** A refinement f of a refinement g of 'a is isomorphic to a refinement by conj f g *)

val refine_conj_iso (f: 'a -> prop) (g:(x:'a{f x} -> prop))
: iso (refine_t #'a (conj #'a f g)) (refine_t #(x:'a{f x}) g)

(** PCM isomorphisms *)

noeq type pcm_iso #a #b (p: pcm a) (q: pcm b) = {
  i: iso a b;
  fwd_morphism: pcm_morphism i.fwd p q;
  bwd_morphism: pcm_morphism i.bwd q p;
}

val pcm_iso_lens_comp
  (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (i: pcm_iso p q) (l: pcm_lens q r)
: pcm_lens p r

(** The conjunction of two refinements *)

val conj_refinement
  (#p: pcm 'a) (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
: pcm_refinement' p

(** A refinement re1 of a refinement re2 of a PCM is isomorphic to a
    refinement by the conjunction of re1 and re2 *)
val pcm_refinement'_conj_iso
  (p: pcm 'a) (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
: pcm_iso (refined_pcm (conj_refinement re1 re2)) (refined_pcm re2)

val upd_across_pcm_iso
  (#p: pcm 'a) (#q: pcm 'b) (i: pcm_iso p q) (x y: Ghost.erased 'a)
: frame_pres_lift p x y q (i.i.fwd x) (i.i.fwd y)

val conj_unrefinement (#p: pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm re1))
  (h1: pcm_unrefinement re1) (h2: pcm_unrefinement re2)
: pcm_unrefinement (conj_refinement #'a re1 re2)

val extend_unrefinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q) (u: pcm_unrefinement re)
: pcm_unrefinement (extend_refinement l re)

(** The refinement of a ref *)

val ref_refine (#a:Type) (#b:Type) (#p:refined_one_pcm b)
  (r: ref a p) (new_re: pcm_refinement p)
: ref a (refined_pcm new_re.refi)

(** Fundamental operations on references *)

module A = Steel.Effect.Atomic

let ref_focus (r: ref 'a 'p) (q: refined_one_pcm 'c) (l: pcm_lens 'p q): ref 'a q =
  {p = r.p; re = r.re; pl = pcm_lens_comp r.pl l; r = r.r}

val split (#a:Type) (#b:Type) (#p: refined_one_pcm b) (r: ref a p) (xy x y: Ghost.erased b)
: Steel unit
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> composable p x y /\ xy == Ghost.hide (op p x y))
    (fun _ _ _ -> True)

val gather (#a:Type) (#b:Type) (#p: refined_one_pcm b) (r: ref a p) (x y: Ghost.erased b)
: SteelT (_:unit{composable p x y})
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op p x y)

val addr_of_lens
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b) (#q: refined_one_pcm c)
  (r: ref a p) (l: pcm_lens p q)
  (x: Ghost.erased b)
: Steel (ref a q)
    (r `pts_to` x)
    (fun s ->
      (r `pts_to` put l (one q) x) `star` 
      (s `pts_to` get l x))
    (requires fun _ -> True)
    (ensures fun _ r' _ -> r' == ref_focus r q l)

val un_addr_of_lens
  (#a:Type) (#b:Type) (#c:Type) (#p: refined_one_pcm b) (#q: refined_one_pcm c)
  (r': ref a q) (r: ref a p) (l: pcm_lens p q)
  (x: Ghost.erased b) (y: Ghost.erased c)
: Steel unit
    ((r `pts_to` x) `star` (r' `pts_to` y))
    (fun s -> r `pts_to` put l y x)
    (requires fun _ -> r' == ref_focus r q l /\ get l x == one q)
    (ensures fun _ _ _ -> True)

val refine
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r: ref a p)
  (re: pcm_refinement p)
  (x: Ghost.erased b{re.refi.f x})
: Steel (ref a (refined_pcm re.refi))
    (r `pts_to` x)
    (fun r' -> r' `pts_to` Ghost.reveal x)
    (fun _ -> True)
    (fun _ r' _ -> r' == ref_refine r re)

val unrefine
  (#opened:Steel.Memory.inames)
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r': ref a p)
  (re: pcm_refinement p)
  (r: ref a (refined_pcm re.refi))
  (x: Ghost.erased b{re.refi.f x})
: A.SteelGhost unit opened
    (r `pts_to` Ghost.reveal x)
    (fun _ -> r' `pts_to` x)
    (fun _ -> r == ref_refine r' re)
    (fun _ _ _ -> True)

(** Generic read.

    Without the precondition ~ (x == one), it would be possible to read
    a completely uninformative value from a reference. This is safe
    from the model's standpoint (we can't learn anything from this value),
    but would extract to a potentially unsafe pointer dereference in C.

    For example, here's a use-after-free:
        {p `pts_to` x}
      split
        {(p `pts_to` x) `star` (p `pts_to` one)}
      free p
        {p `pts_to` one}
      read p

    Even with ~ (x == one), it's possible that x represents partial information
    about the value at r (for example, a tuple (one, z) representing a struct
    with permission to read/write from the second field only). But we should be
    safe as long as the carrier types of the PCMs involved are abstract.
    
    For example, suppose
      thread 1 has (p `pts_to` (y, one))
      thread 2 has (p `pts_to` (one, z))
    and thread 1 writes to p->fst while thread 2 performs the read (v, w) = *p.
    
    In this situation, we can't allow thread 2 to dereference (&q.fst),
    as then it'd be reading from a location while thread 1 is writing to it.

    Thread 2 can construct the pointer (&q.fst) just fine, but in
    order to dereference it, it needs to call ref_read, and ref_read
    requires that (&q.fst) point to a non-unit value (i.e., that ~ (v == one)).
    
    If v's type is suitably abstract, so that it's not possible to
    test v against the unit of its corresponding PCM, then there's no
    way to prove this precondition and we are safe from reading v
    as thread 1 is writing to it. *)
val ref_read
  (#a:Type) (#b:Type) (#p: refined_one_pcm b) (#x: Ghost.erased b) (r: ref a p)
: Steel b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> ~ (Ghost.reveal x == one p))
    (ensures fun _ x' _ -> compatible p x x')

val ref_upd
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r: ref a p) (x y: Ghost.erased b) (f: (b -> b){frame_pres p f x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)

(* TODO move to FStar.PCM.fst? *)
let whole_value (p: pcm 'a) (x: 'a) =
  p.refine x /\
  (forall (y:'a{composable p x y}).{:pattern op p y x} op p y x == x)

let valid_write (p:pcm 'a) x y =
  whole_value p x /\ whole_value p y /\
  (forall (frame:'a). composable p x frame ==> composable p y frame)

val ref_write
  (#a:Type) (#b:Type) (#p: refined_one_pcm b)
  (r: ref a p) (#x: Ghost.erased b) (y: b{valid_write p x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
