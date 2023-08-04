module Pulse.Lib.HigherReference
open Pulse.Lib.Core
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32

val ref (a:Type u#1) : Type u#0

val pts_to (#a:Type) (r:ref a) (p:perm) (n:a) : vprop

val alloc (#a:Type) (x:a)
  : stt (ref a) emp (fun r -> pts_to r full_perm x)

val ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt a
        (pts_to r p n)
        (fun x -> pts_to r p x ** pure (reveal n == x))

val ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  : stt unit
        (pts_to r full_perm n)
        (fun _ -> pts_to r full_perm (hide x))

val free (#a:Type) (r:ref a) (#n:erased a)
  : stt unit (pts_to r full_perm n) (fun _ -> emp)

val with_local
  (#a:Type u#1)
  (init:a)
  (#pre:vprop)
  (#ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r full_perm init)
                               (fun v -> post v ** exists_ (pts_to r full_perm)))
  : stt ret_t pre post
