module Pulse.Soundness.Return

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module R = FStar.Reflection

module WT = Pulse.Steel.Wrapper.Typing
module LN = Pulse.Typing.LN

#push-options "--z3rlimit_factor 10 --fuel 4 --ifuel 2"
let return_soundess
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Return? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Return _ ctag use_eq u t e post x t_typing e_typing post_typing = d in
  let ru = elab_universe u in
  let rt = elab_term t in
  let re = elab_term e in
  let rpost = elab_term post in
  let rpost = mk_abs rt R.Q_Explicit rpost in
  let rt_typing : RT.typing _ rt (R.pack_ln (R.Tv_Type ru)) =
    tot_typing_soundness t_typing in
  let re_typing : RT.typing _ re rt =
    tot_typing_soundness e_typing in
  let rpost_typing
    : RT.typing _ rpost
                  (mk_arrow (rt, R.Q_Explicit) vprop_tm) =
    mk_t_abs_tot f g RT.pp_name_default t_typing post_typing in

  // re is ln
  LN.tot_typing_ln e_typing;
  elab_ln e (-1);

  // (elab_term post) is (ln 0)
  RT.well_typed_terms_are_ln _ rpost _ rpost_typing;
  assert (RT.ln' (elab_term post) 0);

  elab_open_commute' post e 0;
  // RT.beta_reduction rt R.Q_Explicit (elab_term post) re;
  admit ();
  
  match ctag, use_eq with
  | STT, true ->
    WT.return_stt_typing x rt_typing re_typing rpost_typing
  | STT, false -> 
    WT.return_stt_noeq_typing rt_typing re_typing rpost_typing
  | STT_Atomic, true ->
    WT.return_stt_atomic_typing x rt_typing re_typing rpost_typing
  | STT_Atomic, false -> 
    WT.return_stt_atomic_noeq_typing rt_typing re_typing rpost_typing
  | STT_Ghost, true ->
    WT.return_stt_ghost_typing x rt_typing re_typing rpost_typing
  | STT_Ghost, false -> 
    WT.return_stt_ghost_noeq_typing rt_typing re_typing rpost_typing
#pop-options
