module Pulse.Lib.Codeable

open Pulse.Lib.Pervasives

(* A code is a "small" type (in Type2) that can be interpreted
as "big" slprops (i.e. slprop2). *)
noeq
type vcode : Type u#4 = {
    t : Type u#2;
    up : t -> slprop2;
}

(* A class for codeable slprops. *)
class codeable (code:vcode) (v : slprop) = {
  code_of : code.t;
  pf : squash (code.up code_of == v);
}

let encode (#code:vcode) (v:slprop) {| d : codeable code v |} : code.t =
  d.code_of

let decode (#code:vcode) (c:code.t) : slprop =
  code.up c

(* Small slprops (slprop1) form a trivial code by lifting with up2. *)
let small_code : vcode = {
  t = slprop1_repr;
  up = (fun c -> up1_is_slprop1 c; Pulse.Lib.Core.up1 c);
}

(* A codeable instance for small slprops. Note: this only triggers if
there is an instance for Pulse.Class.Small.small for the given slprop (instead of
requiring (squash (is_slprop1 v)), since typeclass instantiation cannot backtrack if
a refinement proof fails. *)
instance codeable_small (v:slprop) (_ : Pulse.Class.Small.small v) : codeable small_code v = {
  code_of = down1 v;
  pf = ();
}
