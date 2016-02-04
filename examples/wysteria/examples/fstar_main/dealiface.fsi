module Smciface

open Prins
open FStar.OrdSet

type sh

val deal: ps:prins{ps = union (union (singleton Alice) (singleton Bob)) (singleton Charlie)} -> p:prin{mem p ps} -> shares:list sh -> rands:int -> deal_to:prin -> Tot (list sh * int)
(* val deal: ps:prins{ps = union (union (singleton Alice) (singleton Bob)) (singleton Charlie)} -> p:prin{mem p ps} -> shares:list sh -> rands:int -> deal_to:prin -> Tot (list sh * int) *)
