(*--build-config
   options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap;
   variables:LIB=../../lib;
   other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/ordset.fsi $LIB/ordmap.fsi ast.fst
--*)


module SecServerNet

open AST

type pchan_in   // channel type to read input
type pchan_out  // channel type to send output

val establish_server: callback:(pchan_in -> pchan_out -> ML unit) -> port:nat -> ML unit

val read_input: pchan_in -> ML (prin * (r:redex{is_R_assec r /\ is_clos (R_assec.v r)}))
val write_output: #meta:v_meta -> pchan_out -> value meta -> ML unit

val create_thread: f:(unit -> ML unit) -> ML unit
