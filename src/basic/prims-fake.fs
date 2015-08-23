module Prims

(* Needed to make bootstraping working (boot target of the Makefile);
   but when we actually type-check this within F*, we have the right
   definition of totality *)
type Tot<'a> = 'a
