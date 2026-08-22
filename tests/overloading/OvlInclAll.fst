module OvlInclAll
(* Re-exports both [f]s. [OvlBool] is included last, so plain scope order
   inside this module resolves [f] to [OvlBool.f]. *)

include OvlInt
include OvlBool
