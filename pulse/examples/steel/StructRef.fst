module StructRef

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

(** Given PCMs (p: pcm a) and (q: pcm b), a (pcm_lens p q) is a (lens a b)
    with the extra law that lens_upd lifts frame-preserving updates on
    b w.r.t. q to frame-preserving updates on a w.r.t. p. *)
noeq type pcm_lens (#a: Type u#a) (#b: Type u#b) (p: pcm a) (q: pcm b) = {
  raw: lens a b;
  upd_resp_pcm: s: a -> v: b -> f:(b -> b) ->
    Lemma
      (requires frame_pres q f (raw.get s) v)
      (ensures frame_pres p (lens_upd raw f) s (raw.put v s));
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

(* A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a *)
noeq type ref (#a: Type u#a) (#b: Type u#b) (p: pcm a) (q: pcm b) = {
  l: pcm_lens p q;
  r: M.ref a p;
}

