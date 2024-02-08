module Pulse.Class.PtsTo

open Pulse.Lib.Pervasives
open FStar.Tactics.V2

(* NOTE: this class is not very useful unless we either inline these methods
early in the typechecking process, or we make the pulse checker normalize
(and unfold) the contexts. *)

let full_default () : Tac unit = exact (`full_perm)

class pointer (r v : Type) = {
  pts_to : r -> (#[full_default()] f : perm) -> v -> vprop;
}

instance pts_to_r (a:Type) : pointer (ref a) a = {
  pts_to = (fun r v -> Pulse.Lib.Reference.pts_to r v);
}

instance pts_to_gr (a:Type) : pointer (Pulse.Lib.GhostReference.ref a) a = {
  pts_to = (fun r v -> Pulse.Lib.GhostReference.pts_to r v);
}

instance pts_to_hr (a:Type) : pointer (Pulse.Lib.HigherReference.ref a) a = {
  pts_to = (fun r v -> Pulse.Lib.HigherReference.pts_to r v);
}

let ( |-> ) #r #v {| pointer r v |} = pts_to #r #v
