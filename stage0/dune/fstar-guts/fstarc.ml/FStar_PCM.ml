open Prims
type 'a symrel = unit
type 'a pcm' = {
  composable: unit ;
  op: 'a -> 'a -> 'a ;
  one: 'a }

let __proj__Mkpcm'__item__op (projectee : 'a pcm') : 'a -> 'a -> 'a=
  match projectee with | { composable; op; one;_} -> op
let __proj__Mkpcm'__item__one (projectee : 'a pcm') : 'a=
  match projectee with | { composable; op; one;_} -> one
type ('a, 'p) lem_commutative = unit
type ('a, 'p) lem_assoc_l = unit
type ('a, 'p) lem_assoc_r = unit
type ('a, 'p) lem_is_unit = unit
type 'a pcm =
  {
  p: 'a pcm' ;
  comm: unit ;
  assoc: unit ;
  assoc_r: unit ;
  is_unit: unit ;
  refine: unit }
let __proj__Mkpcm__item__p (projectee : 'a pcm) : 'a pcm'=
  match projectee with | { p; comm; assoc; assoc_r; is_unit; refine;_} -> p




let op (p : 'a pcm) (x : 'a) (y : 'a) : 'a= (p.p).op x y
type ('a, 'p, 'x, 'y) frame_preserving_upd = 'a -> 'a
let frame_preserving_val_to_fp_upd (p : 'a pcm) (x : unit) (v : 'a) :
  ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd= fun uu___ -> v
let no_op_is_frame_preserving (p : 'a pcm) (x : 'a) :
  ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd= fun v -> v
let compose_frame_preserving_updates (p : 'a pcm) (x : 'a) (y : 'a) (z : 'a)
  (f : ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd)
  (g : ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd) :
  ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd= fun v -> g (f v)
let frame_preserving_subframe (p : 'a pcm) (x : 'a) (y : 'a) (subframe : 'a)
  (f : ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd) :
  ('a, Obj.t, Obj.t, Obj.t) frame_preserving_upd= fun v -> let w = f v in w
