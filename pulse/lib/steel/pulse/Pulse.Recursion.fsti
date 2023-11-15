module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing

val add_knot (g : env)  (rng : R.range)
             (d : decl)
: Tac decl

val tie_knot (g : env)  (rng : R.range)
             (nm_orig : string)
             (d : decl) (r_typ : R.term)
: Tac (list (RT.sigelt_for (fstar_env g)))
