module Pulse.Lib.Codeable

open Pulse.Lib.Pervasives

(* A code is a "small" type (in Type2) that can be interpreted
as "big" slprops (i.e. slprop3). *)
noeq
type vcode : Type u#4 = {
    t : Type u#2;
    up : t -> slprop;
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