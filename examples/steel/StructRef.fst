module StructRef

open FStar.PCM
module M = Steel.Memory

noeq type lens (a: Type u#a) (b: Type u#b) = {
  get: a -> b;
  put: b -> a -> a;
  get_put: s: a -> v: b -> Lemma (get (put v s) == v);
  put_get: s: a -> Lemma (put (get s) s == s);
  put_put: s: a -> v: b -> w: b -> Lemma (put v (put w s) == put v s);
}

let upd (l: lens 'a 'b) (f: 'b -> 'b) (s: 'a): 'a = l.put (f (l.get s)) s

(* The non-computational part of frame_preserving_upd *)
let frame_preserv (p: pcm 'a) (f: 'a -> 'a) (x y: Ghost.erased 'a) =
  forall (v:'a{p.refine v /\ compatible p x v}).{:pattern compatible p x v}
  p.refine (f v) /\
  compatible p y (f v) /\
  (forall (frame:'a{composable p x frame}).{:pattern composable p x frame}
     composable p y frame /\
     (op p x frame == v ==> op p y frame == f v))

(* Every function satisfying frame_preserv is a frame_preserving_upd *)
let frame_preserv_mk_upd (p: pcm 'a) (x y: Ghost.erased 'a)
  (f:('a -> 'a){frame_preserv p f x y})
  : frame_preserving_upd p x y
  = fun v -> f v

(* A pcm_lens is a lens for a 'b inside an 'a such that upd lifts
   frame-preserving updates on 'b to frame-preserving updates on 'a *)
noeq type pcm_lens (#a: Type u#a) (#b: Type u#b) (p: pcm a) (q: pcm b) = {
  l: lens a b;
  upd_resp_pcm:
    s: a -> v: b -> f:(b -> b) ->
    Lemma
      (requires frame_preserv q f (l.get s) v)
      (ensures frame_preserv p (upd l f) s (l.put v s));
}

(* A ref is a pcm_lens combined with a Steel.Memory.ref for the base type 'a *)
noeq type ref (#a: Type u#a) (#b: Type u#b) (p: pcm a) (q: pcm b) = {
  l: pcm_lens p q;
  r: M.ref a p;
}
