module Pulse.Class.Duplicable

open Pulse.Lib.Core

class duplicable (p : slprop) = {
  dup_f : unit -> stt_ghost unit emp_inames p (fun _ -> p ** p);
}

let dup (p : slprop) {| d : duplicable p |} ()
  : stt_ghost unit emp_inames p (fun _ -> p ** p) = d.dup_f ()

instance val dup_inv (i : iref) (p : slprop) : duplicable (inv i p)
