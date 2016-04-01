module Smciface

open Prins
open FStar.OrdSet

val mono_median: ps:prins{ps = union (singleton Alice) (singleton Bob)} -> p:prin{mem p ps} -> x:(int * int) -> Tot int
val opt_median: ps:prins{ps = union (singleton Alice) (singleton Bob)} -> p:prin{mem p ps} -> x:(int * int) -> Tot int
