module AggregateRef

open FStar.PCM
module M = Steel.Memory
module P = FStar.PCM

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
    (2) put is a PCM morphism p×q -> p, where (×) = Aggregates.tuple_pcm
    The property get (s * t) = get s * get t is derivable from lens laws and the fact
    that put is a PCM morphism:
      get (s * t)
      = get (put (get s) s * put (get t) t)
      = get (put (get s * get t) (s * t))
      = get s * get t
    So one only needs to prove composable s t ==> composable (get s) (get t) when
    defining a pcm_lens. If we could find a way to also prove this from the fact that
    put is a PCM morphism, we could do away with get_op_composable entirely. *)
noeq type pcm_lens #a #b (p: pcm a) (q: pcm b) = {
  l: lens a b;
  get_refine: s:a ->
    Lemma (requires p.refine s) (ensures q.refine (l.get s)) [SMTPat (p.refine s)];
  get_op_composable: s:a -> t:a ->
    Lemma
      (requires composable p s t)
      (ensures composable q (l.get s) (l.get t));
  put_refine: s:a -> v:b ->
    Lemma (requires p.refine s /\ q.refine v) (ensures p.refine (l.put v s))
    [SMTPat (p.refine (l.put v s))];
  put_op: s:a -> t:a -> v:b -> w:b ->
    Lemma
      (requires composable p s t /\ composable q v w)
      (ensures composable p (l.put v s) (l.put w t) /\
               l.put (op q v w) (op p s t) == op p (l.put v s) (l.put w t))
    [SMTPat (l.put (op q v w) (op p s t)); SMTPat (composable p (l.put v s) (l.put w t))];
}
let get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (s: 'a): 'b = l.l.get s
let put (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (v: 'b) (s: 'a): 'a = l.l.put v s
let upd (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (f: 'b -> 'b) (s: 'a): 'a = lens_upd l.l f s

let get_op (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (s t: 'a)
: Lemma
    (requires composable p s t)
    (ensures composable q (get l s) (get l t) /\ get l (op p s t) == op q (get l s) (get l t))
    [SMTPat (composable p s t); SMTPat (get l (op p s t))]
= l.get_op_composable s t; l.put_op s t (get l s) (get l t)

(** The upd function of a pcm_lens lifts frame-preserving updates on the target to
    frame-preserving updates on the source *)

let pcm_lens_compatible_get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (x y: 'a)
: Lemma (requires compatible p x y) (ensures compatible q (get l x) (get l y))
= compatible_elim p x y (compatible q (get l x) (get l y)) (fun frame_x ->
  let _ = get_op l frame_x x in
  compatible_intro q (get l x) (get l y) (get l frame_x))
    
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
    
let pcm_lens_frame_pres (p: pcm 'a) (q: pcm 'b) (l: pcm_lens p q) (s: 'a) (v: 'b) (f: 'b -> 'b)
: Lemma
    (requires frame_pres q f (get l s) v)
    (ensures frame_pres p (upd l f) s (put l v s))
    [SMTPat (frame_pres q f (get l s) v)]
= frame_pres_intro p (upd l f) s (put l v s) (fun full ->
    let _ = l.get_refine in
    pcm_lens_compatible_get l s full;
    let _ = l.put_refine in
    let goal = frame_pres_on p (upd l f) s (put l v s) full in
    compatible_elim p s full goal (fun frame_s ->
    compatible_elim q v (f (get l full)) goal (fun frame_v ->
    let frame_vs: 'a = put l frame_v frame_s in
    l.put_op s frame_s v frame_v;
    p.comm frame_vs (put l v s);
    q.comm v frame_v;
    p.comm s frame_s;
    compatible_intro p (put l v s) (upd l f full) frame_vs;
    let aux (frame:'a{composable p s frame})
    : Lemma (composable p (put l v s) frame /\
             (op p s frame == full ==> op p (put l v s) frame == upd l f full))
    = get_op l s frame;
      l.put_op s frame v (get l frame)
    in FStar.Classical.forall_intro aux)))

(** The identity lens is a pcm_lens *)
let pcm_lens_id (#p: pcm 'a): pcm_lens p p = {
  l = lens_id; 
  get_refine = (fun _ -> ());
  get_op_composable = (fun _ _ -> ());
  put_refine = (fun _ _ -> ());
  put_op = (fun _ _ _ _ -> ());
}

(** pcm_lens composition is lens composition *)
let pcm_lens_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (l: pcm_lens p q) (m: pcm_lens q r): pcm_lens p r = 
{
  l = lens_comp l.l m.l;
  get_refine = (fun _ -> let _ = l.get_refine in let _ = m.get_refine in ());
  get_op_composable = (fun s t -> get_op l s t; get_op m (get l s) (get l t));
  put_refine = (fun s v -> let _ = l.put_refine in let _ = m.put_refine in let _ = l.get_refine in ());
  put_op = (fun s t v w ->
    get_op l s t;
    m.put_op (get l s) (get l t) v w;
    l.put_op s t (put m v (get l s)) (put m w (get l t)))
}

(** A refinement of a PCM p *)

let refine_t (f: 'a -> prop) = x:'a{f x}

noeq type pcm_refinement #a (p: pcm a) = {
  f: a -> prop;
  f_closed_under_op: x: refine_t f -> y: refine_t f{composable p x y} -> Lemma (f (op p x y));
  new_one: refine_t f;
  new_one_is_refined_unit: x: refine_t f -> Lemma (composable p x new_one /\ op p x new_one == x)
}

let pcm_refine_comp (p: pcm 'a) (r: pcm_refinement p): symrel (refine_t r.f) = composable p

let pcm_refine_op (p: pcm 'a) (r: pcm_refinement p)
  (x: refine_t r.f) (y: refine_t r.f{composable p x y}): refine_t r.f
= r.f_closed_under_op x y; op p x y

let pcm_refine (p: pcm 'a) (r: pcm_refinement p): pcm (refine_t r.f) = {
  p = {composable = pcm_refine_comp p r; op = pcm_refine_op p r; one = r.new_one};
  comm = (fun x y -> p.comm x y);
  assoc = (fun x y z -> p.assoc x y z);
  assoc_r = (fun x y z -> p.assoc_r x y z);
  is_unit = (fun x -> r.new_one_is_refined_unit x);
  refine = p.refine;
}

let trivial_refinement (p: pcm 'a): pcm_refinement p = {
  f = (fun x -> True);
  f_closed_under_op = (fun _ _ -> ());
  new_one = p.p.one;
  new_one_is_refined_unit = p.is_unit;
}

(** A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a.
    The base type of the lens, unlike the Steel.Memory.ref, is refined by a refinement re. *)
noeq type ref (a: Type u#a) (b: Type u#b) = {
  p: pcm a;
  re: pcm_refinement p;
  q: pcm b;
  pl: pcm_lens (pcm_refine p re) q;
  r: M.ref a p;
}

(** A ref r points to a value v if r `Steel.Memory.pts_to` put v one, where
    - put comes from r's pcm_lens
    - one is the unit of r's refined PCM for the source type *)
let pts_to (r: ref 'a 'b) (v: 'b): M.slprop =
  M.pts_to r.r (put r.pl v (pcm_refine r.p r.re).P.p.one)

(** Basic lenses *)

open Aggregates

let lens_fst_put (x:'a) (xy: 'a & 'b): 'a & 'b = (x, snd xy)
let lens_fst #a #b : lens (a & b) a = {
  get = fst;
  put = lens_fst_put;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

let pcm_lens_fst #a #b (p: pcm a) (q: pcm b): pcm_lens (tuple_pcm p q) p = {
  l = lens_fst;
  get_refine = (fun _ -> ());
  get_op_composable = (fun _ _ -> ());
  put_refine = (fun _ _ -> ());
  put_op = (fun _ _ _ _ -> ());
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

let inl_refinement (p: pcm 'a) (q: pcm 'b): pcm_refinement (either_pcm p q) = {
  f = (fun (x: option (either 'a 'b)) -> Some? x /\ Inl? (Some?.v x));
  f_closed_under_op = (fun _ _ -> ());
  new_one = Some (Inl #_ #'b p.P.p.one);
  new_one_is_refined_unit = (fun (Some (Inl x)) -> p.is_unit x);
}

(** A PCM for possibly uninitialized data *)

type init a =
| Uninitialized : init a
| One : init a
| Initialized : a -> init a

let init_comp (p: pcm 'a): symrel (init 'a) = fun x y -> match x, y with
  | One, _ | _, One -> True
  | Uninitialized, Uninitialized -> True
  | Initialized x, Initialized y -> composable p x y
  | _, _ -> False

let init_op (p: pcm 'a) (x: init 'a) (y: init 'a{init_comp p x y}): init 'a = match x, y with
  | One, z | z, One -> z
  | Uninitialized, Uninitialized -> Uninitialized
  | Initialized x, Initialized y -> Initialized (op p x y)

let init_pcm (p: pcm 'a): pcm (init 'a) = P.({
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
})

(** A lens for the k-th field of an n-ary product *)

open FStar.FunctionalExtensionality

let lens_field_get (#a:eqtype) f (k:a) (s:restricted_t a f): f k = s k
let lens_field (#a:eqtype) f (k:a): lens (restricted_t a f) (f k) = {
  get = lens_field_get f k;
  put = fun_upd k;
  get_put = (fun s v -> ());
  put_get = (fun s -> ext (fun_upd k (lens_field_get f k s) s) s (fun _ -> ()));
  put_put = (fun s v w -> ext (fun_upd k v (fun_upd k w s)) (fun_upd k v s) (fun _ -> ()));
}

(** lens_field is a pcm_lens for the n-ary product PCM *)

(* TODO move to Aggregates.fst *)
let prod_pcm_composable_intro (p:(k:'a -> pcm ('b k))) (x y: restricted_t 'a 'b)
  (h:(k:'a -> Lemma (composable (p k) (x k) (y k))))
: Lemma (composable (prod_pcm p) x y) = FStar.Classical.forall_intro h

let field (#a:eqtype) #f (p:(k:a -> pcm (f k))) (k:a): pcm_lens (prod_pcm p) (p k) = {
  l = lens_field f k;
  get_refine = (fun s -> ());
  get_op_composable = (fun s t -> ());
  put_refine = (fun s v -> ());
  put_op = (fun s t v w ->
    prod_pcm_composable_intro p (fun_upd k v s) (fun_upd k w t) (fun _ -> ());
    ext
      (fun_upd k (op (p k) v w) (op (prod_pcm p) s t))
      (op (prod_pcm p) (fun_upd k v s) (fun_upd k w t))
      (fun _ -> ()));
}

(** The refinement of an n-ary union PCM to the k-th case *)

let case_refinement_f (p:(k:'a -> pcm ('b k))) (k:'a): union 'b -> prop =
  fun kx -> match kx with Some (|k', _|) -> k == k' | None -> False

let case_refinement_new_one (p:(k:'a -> pcm ('b k))) (k:'a)
: refine_t (case_refinement_f p k)
= Some (|k, (p k).P.p.one|)

let case_refinement (p:(k:'a -> pcm ('b k))) (k:'a): pcm_refinement (union_pcm p) = {
  f = case_refinement_f p k;
  f_closed_under_op = (fun x y -> ());
  new_one = case_refinement_new_one p k;
  new_one_is_refined_unit = (fun (Some (|k', x|)) -> (p k).is_unit x)
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

(** lens_case is a pcm_lens for the k-th case of an n-ary union *)

let case (p:(k:'a -> pcm ('b k))) (k:'a): pcm_lens (pcm_refine (union_pcm p) (case_refinement p k)) (p k) = {
  l = lens_case p k;
  get_refine = (fun s -> ());
  get_op_composable = (fun s t -> ());
  put_refine = (fun s v -> ());
  put_op = (fun s t v w -> ());
}

(*

TODO:
- Types of basic Steel operations manipulating pts_to

*)
