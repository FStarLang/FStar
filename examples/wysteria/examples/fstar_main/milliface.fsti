module Smciface

open Prins
open FStar.OrdSet

val mill: ps:prins{ps = union (singleton Alice) (singleton Bob)} -> p:prin{mem p ps} -> x:int -> Tot bool
