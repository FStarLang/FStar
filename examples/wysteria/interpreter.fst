(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi Hashtable --__temp_no_proj PSemantics --verify_module Interpreter;
    variables:CONTRIB=../../contrib;
    other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst seq.fsi seqproperties.fst ghost.fst listTot.fst ordset.fsi ordmap.fsi list.fst io.fsti string.fst prins.fst ast.fst ffibridge.fsi sem.fst psem.fst $CONTRIB/Platform/fst/Bytes.fst runtime.fsi print.fst hashtable.fsi ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst
 --*)

module Interpreter

open FStar.IO
open FStar.OrdMap
open FStar.OrdSet

open Prins
open AST
open Runtime

open Semantics
open PSemantics

open Crypto

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
  else if is_value_ps c && is_sframe c is_F_mkwire_ps then Some (step_mkwire_e2 c)
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
  else if is_value_ps c && is_sframe c is_F_mkwire_ps then C_mkwire_e2 c c'
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

val step_completeness: c:config -> c':config -> h:sstep c c' -> Lemma (requires (True)) (ensures (is_Some (step c)))
let step_completeness c c' h = ()

#set-options "--z3timeout 10"

val target_step_lemma:
  p:prin -> c:config{Conf.l c = Target /\ Conf.m c = Mode Par (singleton p) /\
                    is_Some (step c)}
  -> c':config{c' = Some.v (step c)}
  -> Lemma (requires (True))
          (ensures (Conf.l c' = Target /\ Conf.m c' = Mode Par (singleton p)))
let target_step_lemma p c c' = ()

#reset-options

open Print

open FStar.Ghost

val construct_sstep_star:
  c:config -> c':config{step c = Some c'} -> c'':config -> h:sstep_star c' c''
  -> Tot (sstep_star c c'')
let construct_sstep_star c c' c'' h = SS_tran #c #c' #c'' (step_correctness c) h

(* TODO: FIXME: make the sstep_star erased *)
val step_star: c:config -> Dv (c':config & (sstep_star c c'))
let rec step_star c =
  let c' = step c in
  match c' with
    | Some c' ->
      let MkDTuple2 'a 'b c'' h'' = step_star c' in
      let h' = construct_sstep_star c c' c'' h'' in
      (| c'', h' |)
    | None    ->
      let h1 = SS_refl c in
      MkDTuple2 #config #(fun c' -> sstep_star c c') c h1

type tstep_config (p:prin) = c:config{Conf.l c = Target /\
                                      Conf.m c = Mode Par (singleton p)}

opaque type witness_client_config (#a:Type) (x:a) = True

let client_key:client_key =
  let k = Platform.Bytes.createBytes SHA1.keysize 0uy in
  assume (client_key_prop k == client_prop_t);
  k

let server_key:server_key =
  let k = Platform.Bytes.createBytes SHA1.keysize 0uy in
  assume (server_key_prop k == server_prop_t);
  k

val do_sec_comp:
  p:prin -> c:tstep_config p{is_T_red (Conf.t c) /\ is_R_assec (T_red.r (Conf.t c))}
  -> ML dvalue
let do_sec_comp p c =
  let R_assec ps v = T_red.r (Conf.t c) in
  let _ = admitP (b2t (is_clos v)) in
  let (en, _, e) = get_en_b v in
  let dv = Circuit.rungmw p ps en (fun _ -> None) e in
  dv
  (* let r = T_red.r (Conf.t c) in *)
  (* let R_assec ps v = r in *)
  (* if is_clos v && mem p ps then *)
  (*   let (en, x, e) = get_en_b v in *)

  (*   let (c_in, c_out) = open_connection 8888 in *)

  (*   let _ = cut (witness_client_config c) in *)
  (*   let _ = assert (exists c.{:pattern (witness_client_config c)} Conf.t c = T_red r /\ Conf.l c = Target /\ Conf.m c = Mode Par (singleton p)) in *)
  (*   let _ = assert (client_prop p r) in *)

  (*   let (m, t) = mac_client_msg p r client_key in *)
  (*   send c_out m; *)
  (*   send c_out t; *)

  (*   let s_m = recv c_in in *)
  (*   let s_t = recv c_in in *)

  (*   let r_opt = verify_server_msg server_key s_m s_t in *)
  (*   if r_opt = None then failwith "Failed to verify secure server mac" *)
  (*   else *)
  (*     let Some (p', r', ps', x', e', dv) = r_opt in       *)
  (*     admitP (r = r' /\ e = e'); (\* TODO: add sec block ids *\) *)
  (*     if p = p' && ps = ps' && x = x' (\* TODO:sec block id && r = r' && e = e' *\) then *)
  (* 	let _ = assert (server_prop p r ps x e dv) in *)
  (* 	dv *)
  (*   else failwith "Secure server returned bad output" *)
  (* else failwith "Reached a non-participating secure block" *)

val tstep: p:prin -> tstep_config p -> ML (option (tstep_config p))
let tstep p c =
  let Conf l m s en t _ = c in
  if is_T_red t && is_R_assec (T_red.r t) then
    let dv = do_sec_comp p c in
    Some (Conf l m s en (T_val #(D_v.meta dv) (D_v.v dv)) (hide []))
  else
    let c'_opt = step c in
    match c'_opt with
      | None    -> None
      | Some c' -> target_step_lemma p c c'; Some c'

val tstep_star: p:prin -> tstep_config p -> ML (option (tstep_config p))
let rec tstep_star p c =
  let c' = tstep p c in
  match c' with
    | Some c' -> tstep_star p c'
    | None    -> Some c

val run: p:prin -> env -> exp -> ML (option dvalue)
let run p en e =
  let c = Conf Target (Mode Par (OrdSet.singleton p)) [] en (T_exp e) (hide []) in
  let c' = tstep_star p c in
  match c' with
    | None    -> None
    | Some c' ->
      if is_terminal c' then Some (c_value c') else None
