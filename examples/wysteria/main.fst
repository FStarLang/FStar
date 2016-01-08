(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --__temp_no_proj PSemantics --__temp_no_proj SecServer --verify_module Main;
    variables:CONTRIB=../../contrib;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst FStar.IO.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst $CONTRIB/Platform/fst/Bytes.fst runtime.fsi print.fst ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst FStar.Crypto.fst interpreter.fst sec_server.fst prog.fsi
 --*)

module Main

open FStar.Ghost

open Runtime

open Prins
open AST
open Print
open SecServer
open Interpreter

exception Invalid_arg

;;

let b = is_server () in
if b then establish_server handle_connection 8888
else
  let const_meta = Meta OrdSet.empty Can_b OrdSet.empty Can_w in
  let init_env =
    fun x ->
      if name_of_var x = "alice" then Some (D_v const_meta (V_prin Alice))
      else if name_of_var x = "bob" then Some (D_v const_meta (V_prin Bob))
      else if name_of_var x = "charlie" then Some (D_v const_meta (V_prin Charlie))
      else None
  in
  let pname = me () in
  match init_env (Var pname T_prin) with
    | Some (D_v _ (V_prin p)) ->
      let c = Conf Target (Mode Par (OrdSet.singleton p)) [] init_env (T_exp Prog.program) (hide []) in
      let c' = tstep_star p c in
      if is_Some c' then
        let Some c' = c' in
	()
      else
        ()
    | _  -> failwith "Main failure: could not find me"
