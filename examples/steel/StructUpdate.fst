module StructUpdate
module P = FStar.PCM
module M = Steel.Memory
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
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.PCMReference

let upd_first (#a #b:Type u#1) (r:ref (t a b) pcm_t) (x:Ghost.erased a) (y:a)
  : SteelT unit 
           (pts_to r (First #a #b x))
           (fun _ -> pts_to r (First #a #b y))
  = let f
      : frame_preserving_upd
              pcm_t
              (Ghost.hide (First #a #b x))
              (First #a #b y)
      = fun old_v ->
          match old_v with
          | Both _ z -> Both y z
    in
    upd_gen r (First #a #b x) (First #a #b y) f

let upd_second (#a #b:Type u#1) (r:ref (t a b) pcm_t) (x:Ghost.erased b) (y:b)
  : SteelT unit
           (pts_to r (Second #a #b x))
           (fun _ -> pts_to r (Second #a #b y))
  = let f
      : frame_preserving_upd
              pcm_t
              (Second #a #b x)
              (Second #a #b y)
      = fun old_v ->
          match old_v with
          | Both z _ -> Both z y
    in
    upd_gen r (Second #a #b x) (Second #a #b y) f
