module Smciface

open Prins
open FStar.OrdSet

val gps: ps:prins{ps = union (singleton Alice) (union (singleton Bob) (singleton Charlie))} -> p:prin{mem p ps} -> x:int -> Tot prin
