(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi FStar.OrdSet --admit_fsi FStar.IO --admit_fsi Smciface;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.Relational.fst ordset.fsi ../../prins.fst ../ffi.fst ../wysteria.fsi psitest.fst
 --*)

module Smciface

open Prins
open FStar.OrdSet

val psi: ps:prins{ps = union (singleton Alice) (singleton Bob)} -> p:prin{mem p ps} -> x:list int -> Tot (list int)
