module Pulse.Lib.Forall
open Pulse.Lib.Core

val ( forall* )
    (#a:Type u#a)
    (p:a -> vprop)
: vprop

val elim_forall
    (#a:Type)
    (#p:a->vprop)
    (x:a)
: stt_ghost unit
    (forall* x. p x)
    (fun _ -> p x)

val intro_forall
    (#a:Type)
    (#p:a->vprop)
    (v:vprop)
    (f_elim : (x:a -> stt_ghost unit v (fun _ -> p x)))
: stt_ghost unit
    v
    (fun _ -> forall* x. p x)

val vprop_equiv_forall
    (#a:Type)
    (p q: a -> vprop)
    (_:squash (forall x. p x == q x))
: vprop_equiv (op_forall_Star p) (op_forall_Star q)
