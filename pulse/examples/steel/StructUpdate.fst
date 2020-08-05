module StructUpdate
module P = FStar.PCM
module H = Steel.Heap
open FStar.PCM

type t (a:Type) (b:Type) =
  | Both : a -> b -> t a b
  | First : a -> t a b
  | Second : b -> t a b
  | Neither : t a b

let comp #a #b (x y:t a b) : prop =
  match x, y with
  | Neither, _
  | _, Neither
  | First _, Second _
  | Second _, First _ -> True
  | _ -> False

let combine #a #b (x: t a b) (y:t a b{comp x y}) : t a b =
  match x, y with
  | First a, Second b
  | Second b, First a -> Both a b
  | Neither, z
  | z, Neither -> z

let pcm_t #a #b : pcm (t a b) = FStar.PCM.({
  p = {
    composable=comp;
    op=combine;
    one=Neither
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> Both? x \/ Neither? x)
})
open Steel.Heap

let upd_first #a #b (r:ref (t a b) pcm_t) (x:Ghost.erased a) (y:a)
  : action (pts_to r (First #a #b x))
                       unit
           (fun _ -> pts_to r (First #a #b y))
  = let f
      : frame_preserving_cas_0
              pcm_t
              (Ghost.hide (First #a #b x))
              (First #a #b y)
      = fun old_v ->
          match old_v with
          | First _ -> Some (First y)
          | Both _ z -> Some (Both y z)
    in
    upd_gen_action r (Ghost.hide (First #a #b x)) (Ghost.hide (First #a #b y)) f

let upd_second #a #b (r:ref (t a b) pcm_t) (x:Ghost.erased b) (y:b)
  : action (pts_to r (Second #a #b x))
           unit
           (fun _ -> pts_to r (Second #a #b y))
  = let f
      : frame_preserving_cas_0
              pcm_t
              (Second #a #b x)
              (Second #a #b y)
      = fun old_v ->
          match old_v with
          | Second _ -> Some (Second y)
          | Both z _ -> Some (Both z y)
    in
    upd_gen_action r (Ghost.hide (Second #a #b x)) (Ghost.hide (Second #a #b y)) f
