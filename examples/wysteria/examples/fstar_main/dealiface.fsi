(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi FStar.OrdSet --admit_fsi FStar.IO --admit_fsi Smciface;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.Relational.fst ordset.fsi ../../prins.fst ../ffi.fst
 --*)

module Smciface

open Prins
open FStar.OrdSet

type sh

val deal: ps:prins{ps = union (union (singleton Alice) (singleton Bob)) (singleton Charlie)} -> p:prin{mem p ps} -> shares:list sh -> rands:int -> deal_to:prin -> Tot int
(* val deal: ps:prins{ps = union (union (singleton Alice) (singleton Bob)) (singleton Charlie)} -> p:prin{mem p ps} -> shares:list sh -> rands:int -> deal_to:prin -> Tot (list sh * int) *)
