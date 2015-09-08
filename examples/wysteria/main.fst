(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi FFI --admit_fsi Runtime;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordmap.fsi $LIB/classical.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst ast.fst ffi.fsi sem.fst sinterpreter.fst runtime.fsi tinterpreter.fst sec_server.fst
 --*)

module Main

open Runtime

open AST
open SecServer
open TargetInterpreter

exception Invalid_arg

;;

let b = is_server () in
if b then establish_server handle_connection 8888
else
  let const_meta = Meta OrdSet.empty Can_b OrdSet.empty Can_w in
  let init_env =
    fun x ->
      if x = "alice" then Some (D_v const_meta (V_const (C_prin 0)))
      else if x = "bob" then Some (D_v const_meta (V_const (C_prin 1)))
      else if x = "charlie" then Some (D_v const_meta (V_const (C_prin 2)))
      else if x = "empty" then Some (D_v const_meta (V_const (C_eprins OrdSet.empty)))
      else None
  in
  let pname = me () in
  match init_env pname with
    | Some (D_v _ (V_const (C_prin p))) ->
      let c = Conf Target (Mode Par (OrdSet.singleton p)) [] init_env (T_exp (get_smc ())) in
      let _ = tstep_star c in
      ()
    | _                                 -> raise Invalid_arg
