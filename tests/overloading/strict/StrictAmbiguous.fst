module StrictAmbiguous
open StrictInt
open StrictBool

(* Nothing discriminates between StrictInt.f and StrictBool.f here: no
   arguments, and no expected type. Under 'compat' this silently resolves
   to the innermost candidate, exactly as it does today. Under 'strict'
   it is an error that lists the candidates. *)
[@@expect_failure]
let amb = f

(* Given something to discriminate on, there is no ambiguity left and
   both resolutions succeed even under 'strict'. *)
let ok_int  : int  = f 0
let ok_bool : bool = f true
