(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi FFI --admit_fsi Runtime;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordmap.fsi $LIB/classical.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst ast.fst ffi.fsi sem.fst sinterpreter.fst runtime.fsi
 --*)

module TargetInterpreter

open AST
open Runtime

open FStar.IO

val do_sec_comp: prin -> r:redex{is_R_assec r} -> ML dvalue
let do_sec_comp p r =
  print_string "Opening a connection\n";
  let (c_in, c_out) = open_connection 8888 in
  print_string "Connected to the server\n";
  let _ = client_write c_out p r in
  print_string "Done sending the input\n";
  client_read c_in
  
val tstep: config -> ML (option config)
let tstep c =
  print_string "Taking one step\n";
  let Conf l m s en t = c in
  if is_T_red t && is_R_assec (T_red.r t) then
    let dv = do_sec_comp (Some.v (OrdSet.choose (Mode.ps m))) (T_red.r t) in
    Some (Conf l m s en (T_val #(D_v.meta dv) (D_v.v dv)))
  else SourceInterpreter.step c

val tstep_star: config -> ML (option config)
let rec tstep_star c =
  if is_terminal c then Some c
  else
    match tstep c with
      | Some c' -> tstep_star c'
      | None    -> None
