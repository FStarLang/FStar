module FStar.DM4F.StMap

open FStar.DM4F.ST
open FStar.Map

irreducible type t (a:eqtype) : Type = int
type t0 = Map.t int int

let eq_int : eqtype = int

total  new_effect STMAP = STATE_h (Map.t int int)
