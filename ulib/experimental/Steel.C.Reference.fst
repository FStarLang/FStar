module Steel.C.Reference
open Steel.C.PCM
open Steel.C.Ref
open Steel.Effect
open Steel.Effect.Atomic

#push-options "--print_universes"

// [@@__reduce__]
let ptr (a: Type u#0) (view_t: Type u#0) (#b: Type u#b) (q: pcm b)
: Type u#b
= ptr a q

// [@@__reduce__]
inline_for_extraction
let ref (a: Type u#0) (view_t: Type u#0) (#b: Type u#b) (q: pcm b)
: Tot (Type u#b)
=
  (x: ptr a view_t q { not_null x })

unfold
let ref_of_ref
  (#a: Type u#0) (#view_t: Type u#0) (#b: Type u#b) (#q: pcm b)
  (r: ref a view_t q)
: Tot (Steel.C.Ref.ref a q)
= r

[@@__steel_reduce__] // ; __reduce__]
let pts_to_view
  (#a: Type u#0) 
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref a view_t p) (view: sel_view p view_t' false)
: vprop
= r `pts_to_view` view

let ref_read
  (#a: Type u#0) (#b: Type u#b)
  (#view_t: Type u#0)
  (#p: pcm b)
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

let null (a: Type u#0) (view_t: Type u#0) (#b: Type u#b) (p: pcm b) : Tot (ptr a view_t p) = null a p

[@@__steel_reduce__] // ; __reduce__]
let pts_to_view_or_null
  (#a: Type u#0) 
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr a view_t p) (view: sel_view p view_t' false)
: vprop
= r `pts_to_view_or_null` view

let is_null
  (#a: Type u#0) (#b: Type u#b) (#c: Type0) (#p: pcm b)
  (r: ptr a c p)
  (vw: sel_view p c false)
: Steel bool
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires (fun _ -> True))
    (ensures (fun h res h' ->
      let s = h (pts_to_view_or_null r vw) in
      h' (pts_to_view_or_null r vw) == s /\
      res == ptr_is_null r /\
      res == (None? s)
    ))
= is_null r vw

let intro_pts_to_view_or_null_null
  (#inames: _)
  (a: Type) (#b: Type) (#p: pcm b)
  (#c: Type0)
  (vw: sel_view p c false)
: SteelGhost unit inames
    emp
    (fun _ -> pts_to_view_or_null (null a c p) vw)
    (requires (fun _ -> True))
    (ensures (fun _ _ h' -> h' (pts_to_view_or_null (null a c p) vw) == None))
= intro_pts_to_view_or_null_null a vw

let elim_pts_to_view_or_null_null
  (#inames: _)
  (a: Type) (#b: Type) (#p: pcm b)
  (#c: Type0)
  (vw: sel_view p c false)
: SteelGhostT unit inames
    (pts_to_view_or_null (null a c p) vw)
    (fun _ -> emp)
= elim_pts_to_view_or_null_null a vw

let intro_pts_to_view_or_null_not_null
  (#inames: _)
  (#a: Type) (#b: Type) (#p: pcm b)
  (#c: Type0)
  (r: ref a c p)
  (vw: sel_view p c false)
: SteelGhost unit inames
    (pts_to_view r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires (fun _ -> True))
    (ensures (fun h _ h' -> h' (pts_to_view_or_null r vw) == Some (h (pts_to_view r vw))))
= intro_pts_to_view_or_null_not_null r vw

let elim_pts_to_view_or_null_not_null
  (#inames: _)
  (#a: Type) (#b: Type) (#p: pcm b)
  (#c: Type0)
  (r: ref a c p)
  (vw: sel_view p c false)
: SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view r vw)
    (requires (fun _ -> True))
    (ensures (fun h _ h' -> h (pts_to_view_or_null r vw) == Some (h' (pts_to_view r vw))))
= elim_pts_to_view_or_null_not_null r vw

let freeable
  (#a: Type u#0) (#view_t: Type u#0) (#b: Type u#0) (#q: pcm b)
  (r: ref a view_t q)
: Tot prop
= freeable (r <: Steel.C.Ref.ref a q)
