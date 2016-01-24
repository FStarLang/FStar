(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins --admit_fsi FStar.Set --admit_fsi FStar.Seq;
    variables:CONTRIB=../../contrib;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst ordset.fsi ordmap.fsi prins.fsi $CONTRIB/Platform/fst/Bytes.fst ast.fst
 --*)

module Prog

open AST

val program:exp
