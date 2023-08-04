module Pulse.Lib.SpinLock
open Pulse.Lib.Core

val lock (p:vprop) : Type u#0

val new_lock
        (p:vprop)
  : stt (lock p)
        (requires p)
        (ensures (fun _ -> emp))

val acquire
        (#p:vprop)
        (l:lock p)
  : stt unit 
        (requires emp)
        (ensures (fun _ -> p))

val release
        (#p:vprop)
        (l:lock p)
  : stt unit
        (requires p)
        (ensures (fun _ -> emp))