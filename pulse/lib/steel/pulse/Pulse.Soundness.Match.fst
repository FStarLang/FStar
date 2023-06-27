module Pulse.Soundness.Match

open Pulse.Soundness.Common
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Elaborate.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module L = FStar.List.Tot

let complete_soundness
  (g:stt_env)
  (#sc_u:universe)
  (#sc_ty:term)
  (#sc:term)
  (brs:list branch)
  (c:comp_st)
  (d : brs_typing g sc_u sc_ty sc brs c)
  (comp : pats_complete g sc sc_ty (L.map (fun (p, _) -> elab_pat p) brs))
  (bs : list (list R.binding))
  : RT.match_is_complete (elab_env g) (elab_term sc) (elab_term sc_ty)
                                 (List.Tot.map fst (elab_branches d))
                                 bs
  = let PC_Elab _ _ _ _ bs' s = comp in
    assume (L.map fst (elab_branches d) == L.map (fun (p, _) -> elab_pat p) brs); // FIXME
    assume (bs == bs'); // FIXME
    s

let match_soundness
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c{T_Match? d})
  (soundness:soundness_t d)
  (ct_soundness: (g:stt_env -> c:comp -> uc:universe ->
                  d':comp_typing g c uc{d' << d} ->
              GTot (RT.tot_typing (elab_env g)
                              (elab_comp c)
                              (RT.tm_type uc))))
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))
  =
  let T_Match _g sc_u sc_ty sc (E sc_ty_d) (E sc_d) _c brs brs_ty brs_complete = d in

  let sc_e_ty : R.typ = elab_term sc_ty in
  let sc_e_ty_t : RT.typing (elab_env g) sc_e_ty (T.E_Total, RT.tm_type sc_u) = sc_ty_d in

  let sc_e = elab_term sc in
  let sc_e_t : RT.typing (elab_env g) sc_e (T.E_Total, sc_e_ty) = sc_d in

  let brs_e : list R.branch =
    elab_branches brs_ty
  in
  let rcty = (T.E_Total, elab_comp c) in
  let PC_Elab _ _ _ _ bnds _ = brs_complete in
  let brs_e_ty : RT.branches_typing (elab_env g) sc_u sc_e_ty sc_e rcty brs_e bnds =
    magic ()
  in
  let brs_complete
     : RT.match_is_complete (elab_env g) (elab_term sc) (elab_term sc_ty) (List.Tot.map fst brs_e) bnds
   = assume (L.map fst (elab_branches brs_ty) == L.map fst brs_e);
     complete_soundness g brs c brs_ty brs_complete bnds
  in
  assume (elab_st_typing d == R.pack_ln (R.Tv_Match sc_e None brs_e));
  RT.T_Match _ _ _ sc_e T.E_Total sc_e_ty_t T.E_Total sc_e_t brs_e rcty bnds brs_complete brs_e_ty
