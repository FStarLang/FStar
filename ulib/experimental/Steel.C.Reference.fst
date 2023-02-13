module Steel.C.Reference
open Steel.C.Model.PCM
open Steel.C.Model.Ref
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
: Tot (Steel.C.Model.Ref.ref a q)
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
  (#a: Type u#0) (#b: Type u#b) (#c: Type0) (#opened: _) (#p: pcm b)
  (r: ptr a c p)
  (vw: sel_view p c false)
: SteelAtomicBase bool false opened Unobservable
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
  (r: ptr a c p)
  (vw: sel_view p c false)
: SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> emp)
    (requires (fun _ -> ptr_is_null r == true))
    (ensures (fun _ _ _ -> True))
= change_equal_slprop
    (pts_to_view_or_null r vw)
    (pts_to_view_or_null (null a c p) vw);
  elim_pts_to_view_or_null_null a vw

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
= freeable (r <: Steel.C.Model.Ref.ref a q)

(* Operations on views *)

let refine_view
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type u#b)
  (#can_view_unit:bool)
  (vw: sel_view p view can_view_unit)
  (pr: (view -> Tot prop))
: Tot (sel_view p (refine view pr) can_view_unit)
= {
  to_view_prop = (fun (c: carrier) -> vw.to_view_prop c /\ pr (vw.to_view c));
  to_view = (fun c -> vw.to_view c <: refine view pr);
  to_carrier = (fun (v: refine view pr) -> vw.to_carrier v <: carrier);
  to_carrier_not_one = vw.to_carrier_not_one;
  to_view_frame = (fun x frame -> vw.to_view_frame x frame);
}

let intro_refine_view'
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (#base: Type)
  (r: ref base view p)
: SteelGhost unit opened
    (pts_to_view r vw)
    (fun _ -> pts_to_view r (refine_view vw pr))
    (fun h -> pr (h (pts_to_view r vw)))
    (fun h _ h' ->
      let x = h (pts_to_view r vw) in
      pr x /\
      x == h' (pts_to_view r (refine_view vw pr))
    )
= let g = gget (pts_to_view r vw) in
  let v = pts_to_view_elim r vw in
  pts_to_view_intro r v (refine_view vw pr) (Ghost.hide (Ghost.reveal g))

inline_for_extraction
noextract
let intro_refine_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (#base: Type)
  (r: ref base view p)
: SteelAtomicBase (ref base (refine view pr) p) false opened Unobservable
    (pts_to_view r vw)
    (fun r' -> pts_to_view r' (refine_view vw pr))
    (fun h -> pr (h (pts_to_view r vw)))
    (fun h r' h' ->
      let x = h (pts_to_view r vw) in
      pr x /\
      r == r' /\
      x == h' (pts_to_view r' (refine_view vw pr))
    )
= intro_refine_view' vw pr r;
  let r' : ref base (refine view pr) p = r in
  change_equal_slprop
    (pts_to_view r (refine_view vw pr))
    (pts_to_view r' (refine_view vw pr));
  return r'

let elim_refine_view'
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (#base: Type)
  (r: ref base (refine view pr) p)
: SteelGhost unit opened
    (pts_to_view r (refine_view vw pr))
    (fun _ -> pts_to_view r vw)
    (fun h -> True)
    (fun h _ h' ->
      let x = h' (pts_to_view r vw) in
      pr x /\
      x == h (pts_to_view r (refine_view vw pr))
    )
= let g = gget (pts_to_view r (refine_view vw pr)) in
  let v = pts_to_view_elim r (refine_view vw pr) in
  pts_to_view_intro r v vw (Ghost.hide (Ghost.reveal g))

inline_for_extraction
noextract
let elim_refine_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (#base: Type)
  (r: ref base (refine view pr) p)
: SteelAtomicBase (ref base view p) false opened Unobservable
    (pts_to_view r (refine_view vw pr))
    (fun r' -> pts_to_view r' vw)
    (fun h -> True)
    (fun h r' h' ->
      let x = h' (pts_to_view r' vw) in
      pr x /\
      r' == r /\
      x == h (pts_to_view r (refine_view vw pr))
    )
= elim_refine_view' vw pr r;
  let r' : ref base view p = r in
  change_equal_slprop
    (pts_to_view r vw)
    (pts_to_view r' vw);
  return r'

let rewrite_view
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type u#b)
  (#can_view_unit:bool)
  (vw: sel_view p view can_view_unit)
  (#view' : Type u#c)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
: Tot (sel_view p view' can_view_unit)
= {
  to_view_prop = vw.to_view_prop;
  to_view = (fun c -> f (vw.to_view c));
  to_carrier = (fun v -> vw.to_carrier (g v));
  to_carrier_not_one = vw.to_carrier_not_one;
  to_view_frame = (fun x frame -> vw.to_view_frame (g x) frame);
}

let intro_rewrite_view'
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (#view' : Type)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
  (#base: _)
  (r: ref base view p)
  (x' : Ghost.erased view')
: SteelGhost unit opened
    (pts_to_view r vw)
    (fun _ -> pts_to_view r (rewrite_view vw f g prf))
    (fun h -> h (pts_to_view r vw) == g x')
    (fun h _ h' ->
      f (h (pts_to_view r vw)) == Ghost.reveal x' /\
      h' (pts_to_view r (rewrite_view vw f g prf)) == Ghost.reveal x'
    )
= let v = pts_to_view_elim r vw in
  pts_to_view_intro r v (rewrite_view vw f g prf) x'

inline_for_extraction
noextract
let intro_rewrite_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (#view' : Type)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
  (#base: _)
  (r: ref base view p)
  (x' : Ghost.erased view')
: SteelAtomicBase (ref base view' p) false opened Unobservable
    (pts_to_view r vw)
    (fun r' -> pts_to_view r' (rewrite_view vw f g prf))
    (fun h -> h (pts_to_view r vw) == g x')
    (fun h r' h' ->
      f (h (pts_to_view r vw)) == Ghost.reveal x' /\
      h' (pts_to_view r' (rewrite_view vw f g prf)) == Ghost.reveal x'
    )
= intro_rewrite_view' vw f g prf r x';
  let r' : ref base view' p = r in
  change_equal_slprop
    (pts_to_view r (rewrite_view vw f g prf))
    (pts_to_view r' (rewrite_view vw f g prf));
  return r'

let elim_rewrite_view'
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (#view' : Type)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
  (#base: _)
  (r: ref base view' p)
: SteelGhost unit opened
    (pts_to_view r (rewrite_view vw f g prf))
    (fun _ -> pts_to_view r vw)
    (fun _ -> True)
    (fun h _ h' ->
      let x = h (pts_to_view r (rewrite_view vw f g prf)) in
      let x' = h' (pts_to_view r vw) in
      Ghost.reveal x' == g (Ghost.reveal x) /\
      f (Ghost.reveal x') == Ghost.reveal x
    )
= let gv = gget (pts_to_view r (rewrite_view vw f g prf)) in
  let v = pts_to_view_elim r (rewrite_view vw f g prf) in
  pts_to_view_intro r v vw (g gv)

inline_for_extraction
noextract
let elim_rewrite_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (#view' : Type)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
  (#base: _)
  (r: ref base view' p)
: SteelAtomicBase (ref base view p) false opened Unobservable
    (pts_to_view r (rewrite_view vw f g prf))
    (fun r' -> pts_to_view r' vw)
    (fun _ -> True)
    (fun h r' h' ->
      let x = h (pts_to_view r (rewrite_view vw f g prf)) in
      let x' = h' (pts_to_view r' vw) in
      Ghost.reveal x' == g (Ghost.reveal x) /\
      f (Ghost.reveal x') == Ghost.reveal x
    )
= elim_rewrite_view' vw f g prf r;
  let r' : ref base view p = r in
  change_equal_slprop
    (pts_to_view r vw)
    (pts_to_view r' vw);
  return r'
