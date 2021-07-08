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

val pcm_refinement_comp_new_one
  (#p: pcm 'a) (re: pcm_refinement p)
  (x: refine_t re.f) (y: 'a{composable p x y})
: Lemma (composable p re.new_one y /\ re.f (op p re.new_one y) /\
         composable (refined_pcm re) x (op p re.new_one y))

val pcm_refinement_compatible_closed
  (#p: pcm 'a) (re: pcm_refinement p)
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

(* TODO for some reason, run into universe issues if make this abstract *)
let pts_to (r: ref 'a 'b) (v: Ghost.erased 'b): vprop = (* TODO unerase v, try [@@@smt_fallback] *)
  r.r `mpts_to` put r.pl v (one (refined_pcm r.re))

(** A pcm_lens for the k-th field of an n-ary product *)
val field (#a:eqtype) (#b:a -> Type) (p:(k:a -> pcm (b k))) (k:a): pcm_lens (prod_pcm p) (p k)

(** The refinement of an n-ary union PCM to the k-th case *)

val case_refinement
  (#b:'a -> Type)
  (p:(k:'a -> refined_one_pcm (b k))) (k:'a)
: pcm_refinement (union_pcm p)

val case_unrefinement
  (#a:eqtype) (#b:a -> Type)
  (p:(k:a -> refined_one_pcm (b k))) (k:a)
: pcm_unrefinement (case_refinement p k)

(** A pcm_lens for the k-th case of an n-ary union *)
val case (#b:'a -> Type) (p:(k:'a -> refined_one_pcm (b k))) (k:'a)
: pcm_lens (refined_pcm (case_refinement p k)) (p k)

(** Refining a pcm_lens *)

val extend_refinement
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
: pcm_refinement p

val pcm_lens_refine
  (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q)
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
  (#p: pcm 'a) (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
: pcm_refinement p

(** A refinement re1 of a refinement re2 of a PCM is isomorphic to a
    refinement by the conjunction of re1 and re2 *)
val pcm_refinement_conj_iso
  (p: pcm 'a) (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
: pcm_iso (refined_pcm (conj_refinement re1 re2)) (refined_pcm re2)

val upd_across_pcm_iso
  (#p: pcm 'a) (#q: pcm 'b) (i: pcm_iso p q) (x y: Ghost.erased 'a)
: frame_pres_lift p x y q (i.i.fwd x) (i.i.fwd y)

val conj_unrefinement (#p: pcm 'a)
  (re1: pcm_refinement p) (re2: pcm_refinement (refined_pcm re1))
  (h1: pcm_unrefinement re1) (h2: pcm_unrefinement re2)
: pcm_unrefinement (conj_refinement #'a re1 re2)

val extend_unrefinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement q) (u: pcm_unrefinement re)
: pcm_unrefinement (extend_refinement l re)

(** The refinement of a ref *)

val ref_refine
  (r: ref 'a 'b) (new_re: pcm_refinement r.q) (new_u: pcm_unrefinement new_re)
: ref 'a (refine_t new_re.f)

(** Fundamental operations on references *)

module A = Steel.Effect.Atomic

val ref_focus (r: ref 'a 'b) (q: refined_one_pcm 'c) (l: pcm_lens r.q q): ref 'a 'c

val split (r: ref 'a 'c) (xy x y: Ghost.erased 'c)
: Steel unit
    (r `pts_to` xy)
    (fun _ -> (r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> composable r.q x y /\ xy == Ghost.hide (op r.q x y))
    (fun _ _ _ -> True)

val gather (r: ref 'a 'c) (x y: Ghost.erased 'c)
: SteelT (_:unit{composable r.q x y})
    ((r `pts_to` x) `star` (r `pts_to` y))
    (fun _ -> r `pts_to` op r.q x y)

val addr_of_lens
  (r: ref 'a 'b)
  (#rq: pcm 'b) (#q: refined_one_pcm 'c) (l: pcm_lens rq q)
  (x: Ghost.erased 'b)
: Steel (ref 'a 'c)
    (r `pts_to` x)
    (fun s ->
      (r `pts_to` put l (one q) x) `star` 
      (s `pts_to` get l x))
    (requires fun _ -> rq == r.q)
    (ensures fun _ r' _ -> rq == r.q /\ r' == ref_focus r q l)

val un_addr_of_lens
  (r': ref 'a 'c) (r: ref 'a 'b)
  (#rq: pcm 'b) (#q: refined_one_pcm 'c) (l: pcm_lens rq q)
  (x: Ghost.erased 'b) (y: Ghost.erased 'c)
: Steel unit
    ((r `pts_to` x) `star` (r' `pts_to` y))
    (fun s -> r `pts_to` put l y x)
    (requires fun _ -> rq == r.q /\ r' == ref_focus r q l /\ get l x == one q)
    (ensures fun _ _ _ -> True)

val refine
  (r: ref 'a 'b)
  (re: pcm_refinement r.q)
  (u: pcm_unrefinement re)
  (x: Ghost.erased 'b{re.f x})
: Steel (ref 'a (refine_t re.f))
    (r `pts_to` x)
    (fun r' -> r' `pts_to` Ghost.reveal x)
    (fun _ -> True)
    (fun _ r' _ -> r' == ref_refine r re u)

val unrefine
  (#opened:Steel.Memory.inames)
  (r': ref 'a 'b)
  (re: pcm_refinement r'.q) (u: pcm_unrefinement re)
  (r: ref 'a (refine_t re.f)) (x: Ghost.erased 'b{re.f x})
: A.SteelGhost unit opened
    (r `pts_to` Ghost.reveal x)
    (fun _ -> r' `pts_to` x)
    (fun _ -> r == ref_refine r' re u)
    (fun _ _ _ -> True)

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
val ref_read (r: ref 'a 'b) (x: Ghost.erased 'b)
: Steel 'b
    (r `pts_to` x)
    (fun _ -> r `pts_to` x)
    (requires fun _ -> ~ (Ghost.reveal x == one r.q))
    (ensures fun _ x' _ -> compatible r.q x x')

val ref_upd (r: ref 'a 'b) (x y: Ghost.erased 'b) (f: ('b -> 'b){frame_pres r.q f x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)

(* TODO move to FStar.PCM.fst? *)
let whole_value (p: pcm 'a) (x: 'a) =
  p.refine x /\
  (forall (y:'a{composable p x y}).{:pattern op p y x} op p y x == x)

let valid_write (p:pcm 'a) x y =
  whole_value p x /\ whole_value p y /\
  (forall (frame:'a). composable p x frame ==> composable p y frame)

val ref_write (r: ref 'a 'b) (x: Ghost.erased 'b) (y: 'b{valid_write r.q x y})
: SteelT unit (r `pts_to` x) (fun _ -> r `pts_to` y)
