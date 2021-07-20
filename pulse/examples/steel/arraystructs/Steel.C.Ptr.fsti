module Steel.C.Ptr

module P = FStar.PCM
module R = Steel.C.Ref
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ref
open Steel.Effect

val ptr (a: Type u#0) (b: Type u#b) : Type u#b

val pts_to (p: ptr 'a 'b) (pb: pcm 'b) (v: Ghost.erased 'b): vprop

val pts_to_or_null (p: ptr 'a 'b) (pb: pcm 'b) (v: Ghost.erased 'b): vprop

val nullptr (#a:Type) (#b:Type) : ptr a b

val vptr (#a:Type) (#b:Type) (#pb: pcm b) (r: ref a pb) : ptr a b

val intro_pts_to
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (r: ref 'a pb)
: Steel (ptr 'a 'b)
    (r `R.pts_to` v)
    (fun p -> pts_to p pb v)
    (requires fun _ -> True)
    (ensures fun _ p _ -> p == vptr r)

val elim_pts_to
  (#opened:inames) (#pb: pcm 'b) (#v: Ghost.erased 'b)
  (r: ref 'a pb) (p: ptr 'a 'b)
: SteelGhost unit opened
    (pts_to p pb v)
    (fun _ -> r `R.pts_to` v)
    (requires fun _ -> p == vptr r)
    (ensures fun _ _ _ -> True)

val intro_pts_to_or_null_nullptr (#a:Type) (#b:Type) (#opened:inames)
  (pb: pcm b) (v: Ghost.erased b)
: SteelGhostT unit opened emp (fun _ -> pts_to_or_null (nullptr #a) pb v)

val intro_pts_to_or_null
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (p: ptr 'a 'b)
: SteelT (ptr 'a 'b)
    (pts_to p pb v)
    (fun p -> pts_to_or_null p pb v)

val elim_pts_to_or_null
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (p: ptr 'a 'b)
: Steel (ptr 'a 'b)
    (pts_to_or_null p pb v)
    (fun p -> pts_to p pb v)
    (requires fun _ -> p =!= nullptr)
    (ensures fun _ _ _ -> True)

val is_null
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (p: ptr 'a 'b)
: Steel bool
    (pts_to_or_null p pb v)
    (fun _ -> pts_to_or_null p pb v)
    (requires fun _ -> Ghost.reveal v =!= one pb)
    (ensures fun _ b _ -> b <==> p == nullptr)
