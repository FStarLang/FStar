(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String;
    other-files:ghost.fst listTot.fst set.fsi ordset.fsi ordmap.fsi classical.fst heap.fst st.fst all.fst io.fsti string.fst prins.fst ast.fst ffibridge.fsi sem.fst runtime.fsi print.fst
 --*)

module Interpreter

open FStar.IO
open FStar.OrdMap
open FStar.OrdSet

open Prins
open AST
open Runtime

open Semantics

val step: c:config -> Tot (option config)
let step c =
  if pre_easpar c then Some (step_aspar_e1 c)
  else if is_value_ps c && is_sframe c is_F_aspar_ps then Some (step_aspar_e2 c)
  else if is_value c && is_sframe c is_F_aspar_e then Some (step_aspar_red c)
  else if not (pre_aspar c = NA) then Some (step_aspar c)
  else if pre_aspar_ret c = Do then Some (step_aspar_ret c)

  else if pre_ebox c then Some (step_box_e1 c)
  else if is_value_ps c && is_sframe c is_F_box_ps then Some (step_box_e2 c)
  else if is_value c && is_sframe c is_F_box_e then Some (step_box_red c)
  else if pre_box c = Do then Some (step_box c)

  else if pre_eunbox c then Some (step_unbox_e c)
  else if is_value c && is_sframe c is_F_unbox then Some (step_unbox_red c)
  else if pre_unbox c = Do then Some (step_unbox c)

  else if pre_emkwire c then Some (step_mkwire_e1 c)
  else if is_value c && is_sframe c is_F_mkwire_ps then Some (step_mkwire_e2 c)
  else if is_value c && is_sframe c is_F_mkwire_e then Some (step_mkwire_red c)
  else if pre_mkwire c = Do then Some (step_mkwire c)
  
  else if pre_eprojwire c then Some (step_projwire_e1 c)
  else if is_value_p c && is_sframe c is_F_projwire_p then Some (step_projwire_e2 c)
  else if is_value c && is_sframe c is_F_projwire_e then Some (step_projwire_red c)
  else if pre_projwire c = Do then Some (step_projwire c)

  else if pre_econcatwire c then Some (step_concatwire_e1 c)
  else if is_value c && is_sframe c is_F_concatwire_e1 then Some (step_concatwire_e2 c)
  else if is_value c && is_sframe c is_F_concatwire_e2 then Some (step_concatwire_red c)
  else if pre_concatwire c = Do then Some (step_concatwire c)

  else if pre_econst c then Some (step_const c)

  else if pre_evar c then Some (step_var c)

  else if pre_elet c then Some (step_let_e1 c)
  else if is_value c && is_sframe c is_F_let then Some (step_let_red c)
  else if pre_let c then Some (step_let c)

  else if pre_eabs c then Some (step_abs c)
  
  else if pre_efix c then Some (step_fix c)

  else if pre_eempabs c then Some (step_empabs c)

  else if pre_eapp c then Some (step_app_e1 c)
  else if is_value c && is_sframe c is_F_app_e1 then Some (step_app_e2 c)
  else if is_value c && is_sframe c is_F_app_e2 then Some (step_app_red c)
  else if pre_app c then Some (step_app c)

  else if pre_effi c then Some (step_ffi_e c)
  else if is_value c && is_sframe c is_F_ffi then Some (step_ffi_l c)
  else if pre_ffi c = Do then Some (step_ffi c)

  else if pre_econd c then Some (step_cond_e c)
  else if is_value c && is_sframe c is_F_cond then Some (step_cond_red c)
  else if pre_cond c then Some (step_cond c)

  else if pre_eassec c then Some (step_assec_e1 c)
  else if is_value_ps c && is_sframe c is_F_assec_ps then Some (step_assec_e2 c)
  else if is_value c && is_sframe c is_F_assec_e then Some (step_assec_red c)
  else if not (pre_assec c = NA) then Some (step_assec c)
  else if is_value c && is_sframe c is_F_assec_ret then Some (step_assec_ret c)

  else None

val step_correctness: c:config{is_Some (step c)} -> Tot (sstep c (Some.v (step c)))
let step_correctness c =
  let c' = v_of_some (step c) in

  if pre_easpar c then C_aspar_ps c c'
  else if is_value_ps c && is_sframe c is_F_aspar_ps then C_aspar_e c c'
  else if is_value c && is_sframe c is_F_aspar_e then C_aspar_red c c'
  else if not (pre_aspar c = NA) then C_aspar_beta c c'
  else if pre_aspar_ret c = Do then C_aspar_ret c c'

  else if pre_ebox c then C_box_ps c c'
  else if is_value_ps c && is_sframe c is_F_box_ps then C_box_e c c'
  else if is_value c && is_sframe c is_F_box_e then C_box_red c c'
  else if pre_box c = Do then C_box_beta c c'

  else if pre_eunbox c then C_unbox c c'
  else if is_value c && is_sframe c is_F_unbox then C_unbox_red c c'
  else if pre_unbox c = Do then C_unbox_beta c c'

  else if pre_emkwire c then C_mkwire_e1 c c'
  else if is_value c && is_sframe c is_F_mkwire_ps then C_mkwire_e2 c c'
  else if is_value c && is_sframe c is_F_mkwire_e then C_mkwire_red c c'
  else if pre_mkwire c = Do then C_mkwire_beta c c'

  else if pre_eprojwire c then C_projwire_p c c'
  else if is_value_p c && is_sframe c is_F_projwire_p then C_projwire_e c c'
  else if is_value c && is_sframe c is_F_projwire_e then C_projwire_red c c'
  else if pre_projwire c = Do then C_projwire_beta c c'

  else if pre_econcatwire c then C_concatwire_e1 c c'
  else if is_value c && is_sframe c is_F_concatwire_e1 then C_concatwire_e2 c c'
  else if is_value c && is_sframe c is_F_concatwire_e2 then C_concatwire_red c c'
  else if pre_concatwire c = Do then C_concatwire_beta c c'

  else if pre_econst c then C_const c c'

  else if pre_evar c then C_var c c'

  else if pre_elet c then C_let_e1 c c'
  else if is_value c && is_sframe c is_F_let then C_let_red c c'
  else if pre_let c then C_let_beta c c'

  else if pre_eabs c then C_abs c c'
  
  else if pre_efix c then C_fix c c'

  else if pre_eempabs c then C_empabs c c'

  else if pre_eapp c then C_app_e1 c c'
  else if is_value c && is_sframe c is_F_app_e1 then C_app_e2 c c'
  else if is_value c && is_sframe c is_F_app_e2 then C_app_red c c'
  else if pre_app c then C_app_beta c c'

  else if pre_effi c then C_ffi_e c c'
  else if is_value c && is_sframe c is_F_ffi then C_ffi_l c c'
  else if pre_ffi c = Do then C_ffi_beta c c'

  else if pre_econd c then C_cond_e c c'
  else if is_value c && is_sframe c is_F_cond then C_cond_red c c'
  else if pre_cond c then C_cond_beta c c'

  else if pre_eassec c then C_assec_ps c c'
  else if is_value_ps c && is_sframe c is_F_assec_ps then C_assec_e c c'
  else if is_value c && is_sframe c is_F_assec_e then C_assec_red c c'
  else if not (pre_assec c = NA) then C_assec_beta c c'
  else C_assec_ret c c'

open Print

val step_star: config -> ML (option config)
let rec step_star c =
  print_string "SStepping: "; print_string (config_to_string c); print_string "\n";
  let c' = step c in
  match c' with
    | Some c' -> step_star c'
    | None    ->
      print_string "Could not sstep\n";
      Some c

val do_sec_comp: prin -> r:redex{is_R_assec r} -> ML dvalue
let do_sec_comp p r =
  let (c_in, c_out) = open_connection 8888 in
  let _ = client_write c_out p r in
  client_read c_in

open FStar.Ghost

val tstep: config -> ML (option config)
let tstep c =
  let Conf l m s en t _ = c in
  if is_T_red t && is_R_assec (T_red.r t) then
    let dv = do_sec_comp (Some.v (OrdSet.choose (Mode.ps m))) (T_red.r t) in
    Some (Conf l m s en (T_val #(D_v.meta dv) (D_v.v dv)) (hide []))
  else step c

val tstep_star: config -> ML (option config)
let rec tstep_star c =
  print_string "Stepping: "; print_string (config_to_string c); print_string "\n";
  let c' = tstep c in
  match c' with
    | Some c' -> tstep_star c'
    | None    ->
      print_string "Could not step\n";
      Some c
