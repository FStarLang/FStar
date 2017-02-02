module Prims

(* Needed to make bootstraping working (boot target of the Makefile);
   but when we actually type-check this within F*, we have the right
   definition of totality *)
type Tot<'a> = 'a
type nat = int
type int' = int
type int = int'
type unit' = unit
type unit = unit'
type bool' = bool
type bool = bool'
type 'a option' = 'a option
type 'a option = 'a option'
type 'a list' = 'a list
type 'a list = 'a list'
let op_Multiply x y = x * y