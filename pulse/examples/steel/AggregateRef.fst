module AggregateRef

open FStar.PCM
module M = Steel.Memory

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

let refine (f: 'a -> prop) = x:'a{f x}
let ( << ) (f: 'b -> 'c) (g: 'a -> 'b) (x: 'a): 'c = f (g x)

let lens_refine_get (l: lens 'a 'b) f (s: refine (f << l.get)): refine f = l.get s
let lens_refine_put (l: lens 'a 'b) f (v: refine f) (s: refine (f << l.get)): refine (f << l.get) =
  l.put v s
let lens_refine (l: lens 'a 'b) (f: 'b -> prop) : lens (refine (f << l.get)) (refine f) = {
  get = lens_refine_get l f;
  put = lens_refine_put l f;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

(** The non-computational part of frame_preserving_upd
    TODO: move this and lemmas about this to FStar.PCM.fst *)
let frame_pres (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a) =
  forall (v:'a{p.refine v /\ compatible p x v}).{:pattern compatible p x v}
  p.refine (f v) /\
  compatible p y (f v) /\
  (forall (frame:'a{composable p x frame}).{:pattern composable p x frame}
     composable p y frame /\
     (op p x frame == v ==> op p y frame == f v))

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

(* TODO idea: problem is that PCM and lens need two different refinements.
   PCM needs f \/ is_unit
   lens just needs f
   instead of threading refinements through all the code,
   assume client wll instantiate with f \/ is_unit
   and make lens refinement be x:(refine f){x is not unit}

   problem:
   - unions require restrictions
   - restrictions mean changing the type of the pcm_lens
   - the pcm_lens has two parts: a lens and a pcm
   - need to change both, interact between the two gets very tricky
   - main sticking point: a PCM needs a unit. what is the unit of a PCM restricted to the Left case?
   - code gets "very dependently typed", can no longer take simply
     typed code and add some things on top *)
(** Given PCMs (p: pcm a) and (q: pcm b), a (pcm_lens p q) is a (lens a b)
    with the extra law that lens_upd lifts frame-preserving updates on
    b w.r.t. q to frame-preserving updates on a w.r.t. p. *)
noeq type pcm_lens #a #b (p: pcm a) (q: pcm b) = {
  raw: lens a b;
  upd_resp_pcm: s: a -> v: b -> upd:(b -> b) ->
    Lemma
      (requires frame_pres q upd (raw.get s) v)
      (ensures frame_pres p (lens_upd raw upd) s (raw.put v s));
}

let upd_resp_pcm' (p: pcm 'a) (q: pcm 'b) (l: pcm_lens p q) (s: 'a) (v: 'b) (f: 'b -> 'b)
  : Lemma
      (requires frame_pres q f (l.raw.get s) v)
      (ensures frame_pres p (lens_upd l.raw f) s (l.raw.put v s))
      [SMTPat (frame_pres q f (l.raw.get s) v)]
  = l.upd_resp_pcm s v f

let pcm_lens_id (#p: pcm 'a): pcm_lens p p
  = {raw = lens_id; upd_resp_pcm = (fun _ _ _ -> ())}
let pcm_lens_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (l: pcm_lens p q) (m: pcm_lens q r): pcm_lens p r
  = {raw = lens_comp l.raw m.raw; upd_resp_pcm = (fun _ _ _ -> ())}

let get (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (s: 'a): 'b = l.raw.get s
let put (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (v: 'b) (s: 'a): 'a = l.raw.put v s
let upd (#p: pcm 'a) (#q: pcm 'b) (l: pcm_lens p q) (f: 'b -> 'b) (s: 'a): 'a = lens_upd l.raw f s

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
  raw = lens_fst;
  upd_resp_pcm = (fun (x, y) x' f ->
    assert (forall (v:a{p.refine v /\ compatible p x v}). p.refine (f v) /\ compatible p x' (f v));
    frame_pres_intro (tuple_pcm p q) (lens_upd lens_fst f) (x, y) (x', y)
      (fun (v, w) ->
        let compat_ty = compatible (tuple_pcm p q) (x', y) (f v, w) in
        compatible_elim p x' (f v) compat_ty (fun frame_v ->
        compatible_elim q y w compat_ty (fun frame_w ->
        compatible_intro (tuple_pcm p q) (x', y) (f v, w) (frame_v, frame_w)))));
}

(* We can create lenses for unions if we know which case of the union we are in: *)

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

(* TODO
   This definition of restrictions is not quite right.
   It requires the restricted PCM to contain the unit of the unrestricted PCM, but it's possible that a new, more restricted element of the PCM is now a unit.
   Example: if you have PCM for a 2-case union (a + b), carrier is option (option a + option b) and unit is None.
   But, when when we know that we are in the left case, carrier should be x:option(option a + option b){Some?x /\ Inl? (Some?.v x)}
   and the unit should be Some (Inl None).
    *)
(* From a suitably well-behaved predicate f and PCM p with carrier a,
   we can construct a PCM with carrier x:a{f x \/ x == 1} *)

let satisfies (p: pcm 'a) (f: 'a -> prop) (x: 'a) = f x \/ x == p.p.one

let respects #a (p: pcm a) (f: a -> prop) =
  x:a{satisfies p f x} -> y:a{satisfies p f y /\ composable p x y} ->
  Lemma (satisfies p f (op p x y))

let satisfying (p: pcm 'a) f = x:'a{f x \/ x == p.p.one}

let comp_restrict (p: pcm 'a) #f (re: respects p f): symrel (satisfying p f) = composable p

let op_restrict (p: pcm 'a) #f (re: respects p f) (x: satisfying p f)
  (y:satisfying p f{composable p x y}): satisfying p f
= re x y; op p x y

let one_restrict (p: pcm 'a) #f (re: respects p f): satisfying p f = p.p.one
  
let restrict (p: pcm 'a) #f (re: respects p f): pcm (satisfying p f) = {
  p = {composable = comp_restrict p re; op = op_restrict p re; one = one_restrict p re};
  comm = (fun x y -> p.comm x y);
  assoc = (fun x y z -> p.assoc x y z);
  assoc_r = (fun x y z -> p.assoc_r x y z);
  is_unit = (fun x -> p.is_unit x);
  refine = p.refine;
}

(* A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a.
   The base type of the lens, unlike the Steel.Memory.ref, can be refined by a respects re. *)
noeq type ref (#a: Type u#a) (#b: Type u#b) (p: pcm a) #f (re: respects p f) (q: pcm b) = {
  l: pcm_lens (restrict p re) q;
  r: M.ref a p;
}

(* A ref r points to a value v if there exists a whole value s in the heap such that
   - v is inside s
   - s satisfies re.f *)
let pts_to (#p: pcm 'a) #f (#re: respects p f) (#q: pcm 'b) (r: ref p re q) (v: 'b): M.slprop =
  M.(h_exists (fun s -> pts_to r.r s `star` pure (f s /\ get r.l s == v)))

let weakest_respects (p: pcm 'a): respects p (fun _ -> True) =
  fun _ _ -> ()

let both (f g: 'a -> prop) (x: 'a): prop = f x /\ g x

let respects_both (p: pcm 'a) #f #g (r: respects p f) (s: respects p g): respects p (both f g) =
  fun x y -> r x y; s x y

let respects_iff (p: pcm 'a) (#f #g: 'a -> prop)
  (h:(x:'a -> Lemma (f x <==> g x))) (r: respects p f): respects p g
= fun x y -> h x; h y; r x y; h (op p x y)

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

let is_inl (x: option (either 'a 'b)): prop = Some? x /\ Inl? (Some?.v x)
let oeither_l a b = x:option (either a b){is_inl x}

let is_inl_resp (p: pcm 'a) (q: pcm 'b): respects (either_pcm p q) is_inl =
  fun x y -> ()

let pcm_inl_comp #b (p: pcm 'a): symrel (oeither_l 'a b) =
  fun (Some (Inl x)) (Some (Inl y)) -> composable p x y
  
let pcm_inl_op (p: pcm 'a) (x: oeither_l 'a 'b) (y: oeither_l 'a 'b{pcm_inl_comp p x y}): oeither_l 'a 'b
= match x, y with (Some (Inl x)), (Some (Inl y)) -> Some (Inl (op p x y))

let pcm_inl_one #b (p: pcm 'a): oeither_l 'a b = Some (Inl p.p.one)

let pcm_inl (p: pcm 'a) (q: pcm 'b): pcm (oeither_l 'a 'b) = {
  p = {composable = pcm_inl_comp p; op = pcm_inl_op p; one = pcm_inl_one p};
  comm = (fun (Some (Inl x)) (Some (Inl y)) -> p.comm x y);
  assoc = (fun (Some (Inl x)) (Some (Inl y)) (Some (Inl z)) -> p.assoc x y z);
  assoc_r = (fun (Some (Inl x)) (Some (Inl y)) (Some (Inl z)) -> p.assoc_r x y z);
  is_unit = (fun (Some (Inl x)) -> p.is_unit x);
  refine = (fun (Some (Inl x)) -> p.refine x)
}

// let lens_inl: lens (oeither_l a b) 'a
// let pcm_lens_inl (p: pcm 'a) (q: pcm 'b): pcm_lens (either_pcm p q) = {
// }

// {r `M.pts_to` op p (x, one) (one, y) }
// ..
// {r `M.pts_to` (x, one) `star` r `M.pts_to` (one, y)}
// ..
// {addr_of_fst r `pts_to` x `star` addr_of_snd r `pts_to` y `star` pure (lenses_compose r1.l r2.l /\ r2.r == r2.r)}
// exists s1 s2. r `pts_to` op p s1 s2
// get r1.l s1 = x ==> s1 is at least (x, one) (based on defn. of r1.l and fact that it's frame-preserving)
// get r2.l s2 = y ==> s2 is at least (one, y)
// ---------------
// op p s1 s2 = (x, y)
// 
// r1 `pts_to` x
//   M.(h_exists (fun (x, y) -> pts_to r.r (x, one) `star` pure (re.f (x, one) /\ x == x)))
//   `star`
// r2 `pts_to` y
//   M.(h_exists (fun (x, y) -> pts_to r.r (one, y) `star` pure (re.f (one, y) /\ y == y)))

(* TODO: construct instances of restricted PCMs for structs and their fields; unions and their cases *)
