module Steel.C.Ptr

module P = FStar.PCM
module R = Steel.C.Ref
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ref
open Steel.C.Connection
open Steel.Effect

val ptr (a: Type u#0) (b: Type u#b) : Type u#b

val pts_to (p: ptr 'a 'b) (pb: pcm 'b) ([@@@smt_fallback] v: 'b): vprop

val pts_to_or_null (p: ptr 'a 'b) (pb: pcm 'b) ([@@@smt_fallback] v: option 'b): vprop

val nullptr (#a:Type) (#b:Type) : ptr a b

val vptr (#a:Type) (#b:Type) (#pb: pcm b) (r: ref a pb) : ptr a b

val nullptr_vptr_disjoint (#a:Type) (#b:Type) (#pb: pcm b) (r: ref a pb)
: Lemma (nullptr =!= vptr r) [SMTPat (vptr r)]

val vptr_injective (#a:Type) (#b:Type) (#pb: pcm b) (r r': ref a pb)
: Lemma (requires vptr r == vptr r') (ensures r == r') [SMTPat (vptr r); SMTPat (vptr r')]

val pts_to_nonnull (#opened:inames) (#a:Type) (#b:Type) (#pb: pcm b)
  (#v: Ghost.erased b)
  (p: ptr a b)
: SteelGhost unit opened
    (pts_to p pb v)
    (fun _ -> pts_to p pb v)
    (requires fun _ -> True)
    (ensures fun _ _ _ -> p =!= nullptr)

val intro_pts_to
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (r: ref 'a pb)
: Steel (ptr 'a 'b)
    (r `R.pts_to` v)
    (fun p -> pts_to p pb v)
    (requires fun _ -> True)
    (ensures fun _ p _ -> p == vptr r)

val elim_pts_to
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (p: ptr 'a 'b)
: Steel (ref 'a pb)
    (pts_to p pb v)
    (fun r -> r `R.pts_to` v)
    (requires fun _ -> True)
    (ensures fun _ r _ -> p == vptr r)

val intro_pts_to_or_null_nullptr (#a:Type) (#b:Type) (#opened:inames)
  (pb: pcm b)
: SteelGhostT unit opened emp (fun _ -> pts_to_or_null (nullptr #a) pb None)

val intro_pts_to_or_null (#opened:inames)
  (#pb: pcm 'b) (#v: Ghost.erased 'b) (p: ptr 'a 'b)
: SteelGhostT unit opened
    (pts_to p pb v)
    (fun _ -> pts_to_or_null p pb (Some #'b v))

val elim_pts_to_or_null_nullptr (#opened:inames)
  (#pb: pcm 'b) (#v: Ghost.erased (option 'b)) (p: ptr 'a 'b)
: SteelGhost unit opened
    (pts_to_or_null p pb v)
    (fun _ -> emp)
    (requires fun _ -> p == nullptr)
    (ensures fun _ _ _ -> Ghost.reveal v == None)

val elim_pts_to_or_null (#opened:inames)
  (#pb: pcm 'b) (#v: Ghost.erased (option 'b)) (p: ptr 'a 'b)
: SteelGhost (Ghost.erased 'b) opened
    (pts_to_or_null p pb v)
    (fun w -> pts_to p pb w)
    (requires fun _ -> p =!= nullptr)
    (ensures fun _ w _ -> Ghost.reveal v == Some #'b w)

val is_null
  (#pb: pcm 'b) (#v: Ghost.erased (option 'b)) (p: ptr 'a 'b)
: Steel bool
    (pts_to_or_null p pb v)
    (fun _ -> pts_to_or_null p pb v)
    (requires fun _ -> Some? v ==> Some?.v v =!= one pb)
    (ensures fun _ b _ -> b <==> p == nullptr)

val ptr_focused
  (#a:Type) (#b:Type) (#c:Type) (#p: pcm b)
  (r': ptr a c) (r: ptr a b) (#q: pcm c) (l: connection p q)
: prop

val focus (#p: pcm 'b) (r: ptr 'a 'b) (#q: pcm 'c)
  (l: connection p q) (s: Ghost.erased 'b) (x: Ghost.erased 'c)
: Steel (ptr 'a 'c)
    (pts_to r p s)
    (fun r' -> pts_to r' q x)
    (fun _ -> Ghost.reveal s == l.conn_small_to_large.morph x)
    (fun _ r' _ -> ptr_focused r' r l)

val unfocus (#a #b #c:Type) (#opened:Steel.Memory.inames)
  (#p: pcm b)
  (#q: pcm c)
  (r: ptr a c) (r': ptr a b)
  (l: connection p q) (x: Ghost.erased c)
: SteelGhost unit opened
    (pts_to r q x)
    (fun _ -> pts_to r' p (l.conn_small_to_large.morph x))
    (requires fun _ -> ptr_focused r r' l)
    (ensures fun _ _ _ -> True)
    
val ptr_opt_write
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (p: ptr a (option b)) (y: b)
: SteelT unit
    (pts_to p opt_pcm (Some #b x))
    (fun _ -> pts_to p opt_pcm (Some #b y))
