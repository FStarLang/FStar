(*--build-config
   options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins;
   other-files:ghost.fst set.fsi heap.fst st.fst all.fst ordset.fsi ordmap.fsi prins.fsi ast.fst
--*)


module Runtime

open Prins
open AST

type chan_in   // channel type to read input
type chan_out  // channel type to send output

val establish_server: callback:(chan_in -> chan_out -> ML unit) -> port:nat -> ML unit
val server_read : chan_in  -> ML (prin * (r:redex{is_R_assec r /\ is_clos (R_assec.v r)}))
val server_write: chan_out -> dvalue -> ML unit

val open_connection : port:nat -> ML (chan_in * chan_out)
val client_write: chan_out -> prin -> r:redex{is_R_assec r} -> ML unit
val client_read : chan_in -> ML dvalue

val create_thread: f:(unit -> ML unit) -> ML unit  // server spawns a new thread for each sec block

val get_init_tenv : unit -> ML env

val is_server: unit -> ML bool
val me       : unit -> ML string
