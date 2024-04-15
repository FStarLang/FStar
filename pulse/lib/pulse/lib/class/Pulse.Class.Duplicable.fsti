module Pulse.Class.Duplicable

open Pulse.Lib.Core

class duplicable (p : vprop) = {
  dup_f : unit -> stt_ghost unit emp_inames p (fun _ -> p ** p);
}

let dup (p : vprop) {| d : duplicable p |} ()
  : stt_ghost unit emp_inames p (fun _ -> p ** p) = d.dup_f ()

instance val dup_inv (i : iref) (p : vprop) : duplicable (inv i p)
