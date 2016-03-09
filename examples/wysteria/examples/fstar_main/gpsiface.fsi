module Smciface

open Prins
open FStar.OrdSet

val gps: ps:prins -> p:prin{mem p ps} -> int -> Tot prin
