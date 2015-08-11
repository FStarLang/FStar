(*--build-config
variables:LIB=../../lib;
variables:MATHS=../maths;
other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst located.fst
  --*)


module Lref
open Located

type lref (a:Type) : Type = located (ref a)
