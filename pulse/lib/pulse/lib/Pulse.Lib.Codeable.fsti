module Pulse.Lib.Codeable

open Pulse.Lib.Pervasives

(* A code is a "small" type (in Type2) that can be interpreted
as big vprops (i.e. boxable). *)
noeq
type vcode : Type u#4 = {
    t : Type u#2;
    up : t -> boxable;
}

(* A class for codeable vprops. *)
class codeable (code:vcode) (v : vprop) = {
  code_of : code.t;
  pf : squash (code.up code_of == v);
}

let encode (#code:vcode) (v:vprop) {| d : codeable code v |} : code.t =
  d.code_of

let decode (#code:vcode) (c:code.t) : vprop =
  code.up c

(* Small vprops form a trivial code by lifting with up2. *)
let small_code : vcode = {
  t = Pulse.Lib.Core.small_vprop;
  up = (fun c -> up2_is_small c; Pulse.Lib.Core.up2 c);
}

(* A codeable instance for small vprops. Note: this only triggers if
there is an instance for Pulse.Class.Small.small for the given vprop (instead of
requiring (squash (is_small v)), since typeclass instantiation cannot backtrack if
a refinement proof fails. *)
instance codeable_small (v:vprop) (_ : Pulse.Class.Small.small v) : codeable small_code v = {
  code_of = down2 v;
  pf = ();
}
