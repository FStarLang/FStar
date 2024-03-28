module Pulse.Lib.Primitives
open PulseCore.Observability
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open Pulse.Main
open Pulse.Lib.Reference
open FStar.Ghost
module U32 = FStar.UInt32

/// This module provides primitive atomic operations that are not
/// meant to be extracted to C (since they are intended to be
/// implemented by handwritten C code.) Thus, please use Karamel
/// option `-library Pulse.Lib.Primitives`

val read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
  : stt_atomic U32.t #Observable emp_inames
    (pts_to r #p n)
    (fun x -> pts_to r #p n ** pure (reveal n == x))

val write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
  : stt_atomic unit #Observable emp_inames
        (pts_to r n) 
        (fun _ -> pts_to r (hide x))

val cas (r:ref U32.t) (u v:U32.t) (#i:erased U32.t)
  : stt_atomic bool #Observable emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))
