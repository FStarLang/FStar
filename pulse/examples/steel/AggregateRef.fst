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

let const (x: 'a) (b: 'b): 'a = x
let lens_id #a : lens a a = {
  get = id;
  put = const;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

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

let refine_t (f: 'a -> prop) = x:'a{f x}

let ( << ) (f: 'b -> 'c) (g: 'a -> 'b) (x: 'a): 'c = f (g x)
let lens_refine_get (l: lens 'a 'b) f (s: refine_t (f << l.get)): refine_t f = l.get s
let lens_refine_put (l: lens 'a 'b) f (v: refine_t f) (s: refine_t (f << l.get)): refine_t (f << l.get) =
  l.put v s
let lens_refine (l: lens 'a 'b) (f: 'b -> prop) : lens (refine_t (f << l.get)) (refine_t f) = {
  get = lens_refine_get l f;
  put = lens_refine_put l f;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

let lens_fst_put (x:'a) (xy: 'a & 'b): 'a & 'b = (x, snd xy)
let lens_fst #a #b : lens (a & b) a = {
  get = fst;
  put = lens_fst_put;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
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

(** Given PCMs (p: pcm a) and (q: pcm b), a (pcm_lens p q) is a (lens a b)
    with the extra requirement that [get] and [put] be PCM morphisms. *)
noeq type pcm_lens #a #b (p: pcm a) (q: pcm b) = {
  l: lens a b;
  get_refine: s:a -> Lemma (requires p.refine s) (ensures q.refine (l.get s)) [SMTPat (p.refine s)];
  get_op: s:a -> t:a ->
    Lemma
      (requires composable p s t)
      (ensures composable q (l.get s) (l.get t) /\ 
               l.get (op p s t) == op q (l.get s) (l.get t))
               // Technically, this distributivity law is derivable from the one for put:
               //   get (s * t) = get (put (get s) s * put (get t) t)
               //   = get (put (get s * get t) (s * t)) = get s * get t
    [SMTPat (composable p s t); SMTPat (l.get (op p s t))];
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

let pcm_lens_compatible_get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (x y: 'a)
: Lemma (requires compatible p x y) (ensures compatible q (l.l.get x) (l.l.get y))
= compatible_elim p x y (compatible q (l.l.get x) (l.l.get y)) (fun frame_x ->
  let _ = l.get_op frame_x x in
  compatible_intro q (l.l.get x) (l.l.get y) (l.l.get frame_x))

let pcm_lens_frame_pres (p: pcm 'a) (q: pcm 'b) (l: pcm_lens p q) (s: 'a) (v: 'b) (f: 'b -> 'b)
: Lemma
    (requires frame_pres q f (l.l.get s) v)
    (ensures frame_pres p (lens_upd l.l f) s (l.l.put v s))
    [SMTPat (frame_pres q f (l.l.get s) v)]
= frame_pres_intro p (lens_upd l.l f) s (l.l.put v s) (fun full ->
    assert (p.refine full);
    assert (compatible p s full);
    assert (lens_upd l.l f full == l.l.put (f (l.l.get full)) full);
    let _ = l.get_refine in
    assert (q.refine (l.l.get full));
    pcm_lens_compatible_get l s full;
    assert (compatible q (l.l.get s) (l.l.get full));
    assert (q.refine (f (l.l.get full)));
    let _ = l.put_refine in
    assert (p.refine (lens_upd l.l f full));
    assert (compatible q v (f (l.l.get full)));
    let goal = frame_pres_on p (lens_upd l.l f) s (l.l.put v s) full in
    compatible_elim p s full goal (fun frame_s ->
    compatible_elim q v (f (l.l.get full)) goal (fun frame_v ->
    assert (composable q v frame_v /\ op q frame_v v == f (l.l.get full));
    let frame_vs: 'a = l.l.put frame_v frame_s in
    l.put_op s frame_s v frame_v;
    assert (composable p (l.l.put v s) frame_vs);
    p.comm frame_vs (l.l.put v s);
    q.comm v frame_v;
    p.comm s frame_s;
    assert (op p frame_vs (l.l.put v s) == op p (l.l.put v s) frame_vs);
    assert (op p frame_vs (l.l.put v s) == l.l.put (op q v frame_v) (op p s frame_s));
    assert (op p frame_vs (l.l.put v s) == l.l.put (op q v frame_v) (op p s frame_s));
    assert (op p frame_vs (l.l.put v s) == lens_upd l.l f full);
    compatible_intro p (l.l.put v s) (lens_upd l.l f full) frame_vs;
    let aux (frame:'a{composable p s frame})
    : Lemma (composable p (l.l.put v s) frame /\
             (op p s frame == full ==> op p (l.l.put v s) frame == lens_upd l.l f full))
    = l.get_op s frame;
      assert (composable q (l.l.get s) (l.l.get frame));
      assert (composable q v (l.l.get frame));
      assert (composable p s frame);
      l.put_op s frame v (l.l.get frame);
      let aux ()
      : Lemma (requires op p s frame == full) 
              (ensures op p (l.l.put v s) frame == lens_upd l.l f full)
      = assert (composable p (l.l.put v s) (l.l.put (l.l.get frame) frame));
        assert (op p (l.l.put v s) frame == op p (l.l.put v s) (l.l.put (l.l.get frame) frame));
        assert (op p (l.l.put v s) frame == l.l.put (op q v (l.l.get frame)) (op p s frame));
        assert (op p (l.l.put v s) frame == l.l.put (op q v (l.l.get frame)) full);
        ()
      in ()
    in FStar.Classical.forall_intro aux)))

// let pcm_lens_id (#p: pcm 'a): pcm_lens p p
//   = {raw = lens_id; upd_resp_pcm = (fun _ _ _ -> ())}
// let pcm_lens_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
//   (l: pcm_lens p q) (m: pcm_lens q r): pcm_lens p r
//   = {raw = lens_comp l.raw m.raw; upd_resp_pcm = (fun _ _ _ -> ())}
// 
// let get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (s: 'a): 'b = l.raw.get s
// let put (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (v: 'b) (s: 'a): 'a = l.raw.put v s
// let upd (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (f: 'b -> 'b) (s: 'a): 'a = lens_upd l.raw f s

open Aggregates

// let pcm_lens_fst #a #b (p: pcm a) (q: pcm b): pcm_lens (tuple_pcm p q) p = {
//   l = lens_fst;
//   upd_resp_pcm = (fun (x, y) x' f ->
//     assert (forall (v:a{p.refine v /\ compatible p x v}). p.refine (f v) /\ compatible p x' (f v));
//     frame_pres_intro (tuple_pcm p q) (lens_upd lens_fst f) (x, y) (x', y)
//       (fun (v, w) ->
//         let compat_ty = compatible (tuple_pcm p q) (x', y) (f v, w) in
//         compatible_elim p x' (f v) compat_ty (fun frame_v ->
//         compatible_elim q y w compat_ty (fun frame_w ->
//         compatible_intro (tuple_pcm p q) (x', y) (f v, w) (frame_v, frame_w)))));
// }

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
    
let either_pcm (p: pcm 'a) (q: pcm 'b): pcm (option (either 'a 'b)) = {
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

(** A refinement of a PCM p *)

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

let inl_refinement (p: pcm 'a) (q: pcm 'b): pcm_refinement (either_pcm p q) = {
  f = (fun (x: option (either 'a 'b)) -> Some? x /\ Inl? (Some?.v x));
  f_closed_under_op = (fun _ _ -> ());
  new_one = Some (Inl #_ #'b p.p.one);
  new_one_is_refined_unit = (fun (Some (Inl x)) -> p.is_unit x);
}

(** A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a.
    The base type of the lens, unlike the Steel.Memory.ref, is refined by a refinement re. *)
noeq type ref (a: Type u#a) (b: Type u#b) = {
  p: pcm a;
  re: pcm_refinement p;
  q: pcm b;
  l: pcm_lens (pcm_refine p re) q;
  r: M.ref a p;
}

// (** A ref r points to a value v if r `Steel.Memory.pts_to` put v one, where
//     - put comes from r's pcm_lens
//     - one is the unit of r's refined PCM for the source type *)
// let pts_to (r: ref 'a 'b) (v: 'b): M.slprop =
//   M.pts_to r.r (put r.l v (pcm_refine r.p r.re).P.p.one)
