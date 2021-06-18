module StructRef

open FStar.PCM
module M = Steel.Memory

noeq type lens (a: Type u#a) (b: Type u#b) = {
  get: a -> b;
  put: b -> a -> a;
  get_put: s: a -> v: b -> Lemma (get (put v s) == v); // [SMTPat (get (put v s))];
  put_get: s: a -> Lemma (put (get s) s == s); // [SMTPat (put (get s) s)];
  put_put: s: a -> v: b -> w: b -> Lemma (put v (put w s) == put v s); // [SMTPat (put v (put w s))];
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

let upd (l: lens 'a 'b) (f: 'b -> 'b) (s: 'a): 'a = l.put (f (l.get s)) s

(* The non-computational part of frame_preserving_upd *)
let frame_pres (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a) =
  forall (v:'a{p.refine v /\ compatible p x v}).{:pattern compatible p x v}
  p.refine (f v) /\
  compatible p y (f v) /\
  (forall (frame:'a{composable p x frame}).{:pattern composable p x frame}
     composable p y frame /\
     (op p x frame == v ==> op p y frame == f v))

(* Every function satisfying frame_pres is a frame_preserving_upd *)
let frame_pres_mk_upd (p: pcm 'a) (x y: Ghost.erased 'a)
  (f:('a -> 'a){frame_pres p f x y})
  : frame_preserving_upd p x y
  = fun v -> f v

(* A pcm_lens is a lens for a 'b inside an 'a such that upd lifts
   frame-preserving updates on 'b to frame-preserving updates on 'a *)
noeq type pcm_lens (#a: Type u#a) (#b: Type u#b) (p: pcm a) (q: pcm b) = {
  raw: lens a b;
  upd_resp_pcm:
    s: a -> v: b -> f:(b -> b) ->
    Lemma
      (requires frame_pres q f (raw.get s) v)
      (ensures frame_pres p (upd raw f) s (raw.put v s));
}

(* A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a *)
noeq type ref (#a: Type u#a) (#b: Type u#b) (p: pcm a) (q: pcm b) = {
  l: pcm_lens p q;
  r: M.ref a p;
}

let get_comp (l: lens 'a 'b) (m: lens 'b 'c) (s: 'a): 'c = m.get (l.get s)
let put_comp (l: lens 'a 'b) (m: lens 'b 'c) (v: 'c) (s: 'a): 'a =
  upd l (m.put v) s

let lens_comp (l: lens 'a 'b) (m: lens 'b 'c): lens 'a 'c = {
  get = get_comp l m;
  put = put_comp l m;
  get_put = (fun _ _ -> ());
  put_get = (fun _ -> ());
  put_put = (fun _ _ _ -> ());
}

// The following two lemmas aren't strictly necessary, but nice to verify
open FStar.FunctionalExtensionality
let upd_comp (l: lens 'a 'b) (m: lens 'b 'c) (f: 'c -> 'c) (s: 'a)
  : Lemma (feq (upd (lens_comp l m) f) (upd l (upd m f)))
  = ()
let frame_pres_feq (p: pcm 'a) (f g: 'a -> 'a) (x y: 'a)
  : Lemma (requires feq f g) (ensures frame_pres p f x y <==> frame_pres p g x y)
  = ()

let pcm_lens_comp (#p: pcm 'a) (#q: pcm 'b) (#r: pcm 'c)
  (l: pcm_lens p q) (m: pcm_lens q r) : pcm_lens p r = {
  raw = lens_comp l.raw m.raw;
  upd_resp_pcm = (fun s v f ->
    (* Goal:
         s: a -> v: b -> f:(b -> b) ->
         Lemma
           (requires frame_pres q f ((comp l m).get s) v)
           (ensures frame_pres p (upd (comp l m) f) s ((comp l m).put v s));
       Since 
         (feq (upd (comp l m) f) (upd l (upd m f))
       and 
         feq f g ==> frame_pres p f x y <==> frame_pres p g x y,
       suff. to show
         (ensures frame_pres p (upd l (upd m f)) s (l.put (m.put v (l.get s)) s)).
       Because l respects pcms, suff. to show
         (ensures frame_pres p (upd m f) (l.get s) (m.put v (l.get s))).
       Because m respects pcms, suff. to show
         (ensures frame_pres p f (m.get (l.get s)) v,
       which we have by assumption
         (requires frame_pres q f ((comp l m).get s) v). *)
    m.upd_resp_pcm (l.raw.get s) v f;
    l.upd_resp_pcm s (m.raw.put v (l.raw.get s)) (upd m.raw f)
  );
}
