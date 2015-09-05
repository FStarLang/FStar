(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi FFI --admit_fsi SecClientNet;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordmap.fsi $LIB/classical.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst ast.fst ffi.fsi sem.fst sinterpreter.fst sec_client_net.fsi
 --*)

module TargetInterpreter

open AST
open SecClientNet

val do_sec_comp: prin -> r:redex{is_R_assec r} -> ML dvalue
let do_sec_comp p r =
  let (c_in, c_out) = open_connection 8888 in
  let _ = write_input c_out p r in
  read_output c_in
  
val tstep: config -> ML (option config)
let tstep c =
  let Conf l m s en t = c in
  if is_T_red t && is_R_assec (T_red.r t) then
    let dv = do_sec_comp (Some.v (OrdSet.choose (Mode.ps m))) (T_red.r t) in
    Some (Conf l m s en (T_val #(D_v.meta dv) (D_v.v dv)))
  else SourceInterpreter.step c
