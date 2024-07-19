module Pulse.Lib.Codeable

open Pulse.Lib.Pervasives

(* A code is a "small" type (in Type2) that can be interpreted
as "big" slprops (i.e. slprop3). *)
noeq
type vcode : Type u#4 = {
    t : Type u#2;
    up : t -> slprop3;
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

(* Small slprops (slprop2) form a trivial code by lifting with up3. *)
let small_code : vcode = {
  t = slprop2_base;
  up = (fun c -> up2_is_slprop2 c; Pulse.Lib.Core.up2 c);
}

(* A codeable instance for small slprops. Note: this only triggers if
there is an instance for Pulse.Class.Small.small for the given slprop (instead of
requiring (squash (is_slprop2 v)), since typeclass instantiation cannot backtrack if
a refinement proof fails. *)
instance codeable_small (v:slprop) (_ : Pulse.Class.Small.small v) : codeable small_code v = {
  code_of = down2 v;
  pf = ();
}
