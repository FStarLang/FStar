module Steel.C.Model.Ref.Base
module P = FStar.PCM
module U = Steel.C.Model.Universe
open FStar.FunctionalExtensionality

#push-options "--print_universes"

noeq type ref0 (a: Type u#0) (b: Type u#b) : Type u#b = {
  p: pcm a;
  q: pcm b;
  pl: connection p q;
  r: Steel.Memory.ref (U.raise_t u#0 u#1 a) (fstar_pcm_of_pcm (U.raise_pcm p));
}

noeq type ptr' (a: Type u#0) (b: Type u#b) : Type u#b =
  | NonNull: (v: ref0 a b) -> ptr' a b
  | Null: (v: pcm b) -> ptr' a b

let pcm_of_ptr'
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ptr' a b)
: Tot (pcm b)
= if Null? r then Null?.v r else (NonNull?.v r).q

let ptr a #b p = (r: ptr' a b { pcm_of_ptr' r == p })

let null a p = Null p

let ptr_is_null p = Null? p

let mpts_to (#a: Type u#1) (#p: P.pcm a) (r: Steel.Memory.ref a p) ([@@@smt_fallback] v: a) = Steel.PCMReference.pts_to r v

let raise_p
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ptr' a b { NonNull? r})
: Tot (pcm (U.raise_t u#0 u#1 a))
= U.raise_pcm (NonNull?.v r).p

let lower_conn
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ptr' a b { NonNull? r})
: Tot (connection (raise_p r) (NonNull?.v r).p)
= connection_of_isomorphism (isomorphism_inverse (U.raise_pcm_isomorphism u#0 u#1 (NonNull?.v r).p))

let raise_pl
  (#a: Type u#0)
  (#b: Type u#b)
  (r: ptr' a b {NonNull? r})
: Tot (connection (raise_p r) (NonNull?.v r).q)
= lower_conn r `connection_compose` (NonNull?.v r).pl

let t_ref_focus
  (#a:Type) (#b:Type) (#c:Type) (#p: pcm b)
  (r: ref a p) (#q: pcm c) (l: connection p q)
: Tot (ref a q)
= let NonNull r = r in
  NonNull ({p = r.p; pl = connection_compose r.pl l; r = r.r; q = q})

let ref_focus r l = t_ref_focus r l

let ref_focus_id r = connection_compose_id_right (NonNull?.v r).pl

let ref_focus_comp r l m
= connection_compose_assoc (NonNull?.v r).pl l m

(* freeable r if and only if r is a "base" reference, i.e. its connection path is empty *)

let freeable #a #b #p r =
  let NonNull r = r in
  a == b /\
  r.p == p /\
  r.pl == connection_id p

let pts_to r v =
  (NonNull?.v r).r `mpts_to` (raise_pl r).conn_small_to_large.morph v

let base_fpu p x y =
  fun _ ->
  compatible_refl p y;
  y
