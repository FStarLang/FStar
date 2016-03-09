module Smciface

open Prins
open FStar.OrdSet

val psi: ps:prins{ps = union (singleton Alice) (singleton Bob)} -> p:prin{mem p ps} -> x:list int -> Tot (list int)
val psi_reg: ps:prins{ps = union (singleton Alice) (singleton Bob)} -> p:prin{mem p ps} -> x:list int -> Tot (list int)
