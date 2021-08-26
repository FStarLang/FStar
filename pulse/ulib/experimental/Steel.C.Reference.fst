module Steel.C.Reference
open FStar.FunctionalExtensionality
open Steel.C.PCM
open Steel.C.Connection
open Steel.C.Ref
open Steel.Effect
open Steel.Effect.Atomic

open FStar.FSet

#push-options "--print_universes"

let ref (a: Type u#0) (view_t: Type u#0) (#b: Type u#b) (q: pcm b)
: Type u#b
= ref a q

[@@__steel_reduce__]
let pts_to_view
  (#a: Type u#0) 
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref a view_t p) (view: sel_view p view_t' false)
: vprop
= r `pts_to_view` view

(*
val ref_alloc
  (#a:Type0) (p: pcm a) (x: a)
: Steel (ref a p)
    emp
    (fun r -> r `pts_to` x)
    (requires fun _ -> p_refine p x)
    (ensures fun _ _ _ -> True)
*)

let ref_read
  (#a: Type u#0) (#b: Type u#b) (#p: pcm b)
  (#view_t: Type u#0)
  (#vw: sel_view p view_t false)
  (r: ref a view_t p)
: Steel view_t
  (r `pts_to_view` vw)
  (fun _ -> r `pts_to_view` vw)
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (r `pts_to_view` vw) /\
    res == h' (r `pts_to_view` vw)
  ))
= ref_read_sel r vw
