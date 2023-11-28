module Pulse.Lib.FlippableInv

open Pulse.Lib.Pervasives

val finv (p:vprop) : Type0

val off #p (fi : finv p) : vprop
val on  #p (fi : finv p) : vprop

val mk_finv (p:vprop) : stt (finv p) emp off

val iname_of #p (f : finv p) : erased iname

val flip_on  (#p:vprop) (fi : finv p) : stt_ghost unit (add_iname emp_inames (iname_of fi)) (off fi ** p) (fun () -> on fi)
val flip_off (#p:vprop) (fi : finv p) : stt_ghost unit (add_iname emp_inames (iname_of fi)) (on fi) (fun () -> off fi ** p)
