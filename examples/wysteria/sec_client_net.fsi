(*--build-config
   options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap;
   variables:LIB=../../lib;
   other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/ordset.fsi $LIB/ordmap.fsi ast.fst
--*)


module SecClientNet

open AST

type pchan_in   // channel type to read input
type pchan_out  // channel type to send output

val open_connection: port:nat -> ML (pchan_in * pchan_out)

val write_input: pchan_out -> prin -> r:redex{is_R_assec r} -> ML unit
val read_output: pchan_in -> ML dvalue
