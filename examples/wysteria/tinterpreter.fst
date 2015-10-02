(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Prins --admit_fsi FFI --admit_fsi Runtime;
    other-files:ghost.fst listTot.fst ordset.fsi ordmap.fsi classical.fst set.fsi heap.fst st.fst all.fst prins.fsi ast.fst ffi.fsi sem.fst sinterpreter.fst runtime.fsi
 --*)

module TargetInterpreter

open FStar.Ghost

open Prins
open AST
open Runtime

val do_sec_comp: prin -> r:redex{is_R_assec r} -> ML dvalue
let do_sec_comp p r =
  let (c_in, c_out) = open_connection 8888 in
  let _ = client_write c_out p r in
  client_read c_in
  
val tstep: config -> ML (option config)
let tstep c =
  let Conf l m s en t _ = c in
  if is_T_red t && is_R_assec (T_red.r t) then
    let dv = do_sec_comp (Some.v (OrdSet.choose (Mode.ps m))) (T_red.r t) in
    Some (Conf l m s en (T_val #(D_v.meta dv) (D_v.v dv)) (hide []))
  else SourceInterpreter.step c

val tstep_star: config -> ML (option config)
let rec tstep_star c =
  if is_terminal c then Some c
  else
    match tstep c with
      | Some c' -> tstep_star c'
      | None    -> None
