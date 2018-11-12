module OpenIface

open EnumEq
open Enum
open Eq

let test #a [|enum a|] (x y : a) : bool =
  eq x y
