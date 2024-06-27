module Pulse.Lib.ConditionVar
open Pulse.Lib.Pervasives
val cvar_t : Type0

val inv_name (c:cvar_t) : iref

val send (c:cvar_t) (p:vprop) : vprop

val recv (c:cvar_t) (p:vprop) : vprop

val create (p:storable)
: stt cvar_t emp (fun b -> send b p ** recv b p)

val signal (b:cvar_t) (#p:vprop)
: stt unit (send b p ** p) (fun _ -> emp)

val wait (b:cvar_t) (#p:vprop)
: stt unit (recv b p) (fun _ -> p)

val split (b:cvar_t) (#p #q:storable)
: stt_ghost unit (add_inv emp_inames (inv_name b))
  (recv b (p ** q)) (fun _ -> recv b p ** recv b q)