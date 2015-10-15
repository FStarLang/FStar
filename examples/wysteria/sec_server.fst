(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String;
    other-files:ghost.fst listTot.fst ordset.fsi ordmap.fsi classical.fst set.fsi heap.fst st.fst all.fst io.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst runtime.fsi print.fst interpreter.fst
 --*)

module SecServer

open FStar.Ghost

open FStar.OrdMap
open FStar.OrdSet

open Runtime

open Prins
open AST
open Semantics
open Interpreter

exception Comp_error

type en_map = ordmap prin env p_cmp
type out_map = ordmap prin chan_out p_cmp

type psmap_v = en_map * out_map * varname * exp

type psmap = ordmap prins psmap_v ps_cmp

type psmap_ref_t =  // TODO: FIXME: writing this type forces instantiation of dummy type variables for OrdMap.empty
  | Mk_ref: r:ref (ordmap prins psmap_v ps_cmp) -> psmap_ref_t

let psmap_ref = Mk_ref (alloc (OrdMap.empty #prins #psmap_v #ps_cmp))

val send_output: #meta:v_meta -> ps:prins -> out_m:out_map{contains_ps ps out_m}
                 -> v:value meta -> ML unit
let rec send_output #meta ps out_m v =
  let Some p = choose ps in
  let Some out = select p out_m in
  let ps_rest = remove p ps in
  server_write out (slice_v p v);
  if ps_rest = empty then ()
  else send_output #meta ps_rest out_m v

val is_sterminal: config -> Tot bool
let is_sterminal (Conf _ _ s _ t _) = s = [] && is_T_val t

val do_sec_comp: ps:prins -> env_m:en_map{contains_ps ps env_m}
                 -> out_m:out_map{contains_ps ps out_m}
                 -> varname -> exp -> unit -> ML unit
let do_sec_comp ps env_m out_m x e _ =
  let en = update_env (compose_envs_m ps env_m) x V_unit in
  let conf = Conf Target (Mode Sec ps) [] en (T_exp e) (hide []) in
  let c_opt = step_star conf in
  if is_Some c_opt && is_sterminal (Some.v c_opt) then
    let _ = send_output ps out_m (T_val.v (Conf.t (Some.v c_opt))) in
    ()
  else
    raise Comp_error

val handle_connection: chan_in -> chan_out -> ML unit
let handle_connection c_in c_out =
  let p, R_assec #meta ps v = server_read c_in in
  let (en, x, e) = get_en_b v in

  let psmap_ref = Mk_ref.r psmap_ref in
  let env_m', out_m', x', e' =
    if contains ps !psmap_ref then
      let Some (env_m', out_m', x', e') = select ps !psmap_ref in
      let env_m':en_map = update p en env_m' in
      let out_m' = update p c_out out_m' in
      env_m', out_m', x', e'
    else
      (update p en OrdMap.empty), (update p c_out OrdMap.empty), x, e
  in

  if OrdMap.size env_m' = size ps then
    let _ = admitP (contains_ps ps env_m') in
    let _ = admitP (contains_ps ps out_m') in
    create_thread (do_sec_comp ps env_m' out_m' x e);
    psmap_ref := OrdMap.remove ps (!psmap_ref)
  else
    psmap_ref := (update ps (env_m', out_m', x', e') (!psmap_ref))
