module Pulse.Checker.Exists

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

module Metatheory = Pulse.Typing.Metatheory

let vprop_as_list_typing (#g:env) (#p:term)
  (t:tot_typing g p tm_vprop)
  (x:term { List.Tot.memP x (vprop_as_list p) })
  : tot_typing g x tm_vprop
  = assume false; t

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

let check_elim_exists
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_ElimExists? t.term})
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_elim_exists" t.range in

  let Tm_ElimExists { p = t } = t.term in
  let (| t, t_typing |) : (t:term & tot_typing g t tm_vprop ) = 
    match t.t with
    | Tm_Unknown -> (
      //There should be exactly one exists_ vprop in the context and we eliminate it      
      let ts = vprop_as_list pre in
      let exist_tms = List.Tot.Base.filter #term (function | {t = Tm_ExistsSL _ _ _ } -> true | _ -> false) ts in
      match exist_tms with
      | [one] -> 
        assume (one `List.Tot.memP` ts);
        (| one, vprop_as_list_typing pre_typing one |) //shouldn't need to check this again
      | _ -> 
        fail g (Some t.range)
          (Printf.sprintf "Could not decide which exists term to eliminate: choices are\n%s"
             (terms_to_string exist_tms))
      )
    | _ ->
      let t, _ = instantiate_term_implicits g t in
      check_vprop g t
  in

  if not (Tm_ExistsSL? t.t)
  then fail g (Some t.range)
         (Printf.sprintf "check_elim_exists: elim_exists argument %s not an existential"
            (P.term_to_string t));

  let Tm_ExistsSL u { binder_ty=ty } p = t.t in

  let (| u', ty_typing |) = check_universe g ty in
  if eq_univ u u'
  then let x = fresh g in
       let d = T_ElimExists g u ty p x ty_typing t_typing in
       prove_post_hint (try_frame_pre pre_typing d res_ppname) post_hint t.range
  else fail g (Some t.range)
         (Printf.sprintf "check_elim_exists: universe checking failed, computed %s, expected %s"
            (P.univ_to_string u') (P.univ_to_string u))

let is_intro_exists_erased (st:st_term) = 
  match st.term with
  | Tm_IntroExists { erased } -> erased
  | _ -> false

let check_intro_exists_erased
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { intro_exists_witness_singleton st /\
                is_intro_exists_erased st })
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) tm_vprop))
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_intro_exists_erased" st.range in

  let Tm_IntroExists { p=t; witnesses=[e] } = st.term in
  let (| t, t_typing |) = 
    match vprop_typing with
    | Some typing -> (| t, typing |)
    | _ -> check_vprop g t
  in

  if not (Tm_ExistsSL? (t <: term).t)  // why this ascription?
  then fail g (Some st.range)
         (Printf.sprintf "check_intro_exists_erased: vprop %s is not an existential"
            (P.term_to_string t));

  let Tm_ExistsSL u b p = (t <: term).t in

  Pulse.Typing.FV.tot_typing_freevars t_typing;
  let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #b.binder_ty #p t_typing (fresh g) in
  let (| e, e_typing |) = 
    check_tot_term_with_expected_type g e (mk_erased u b.binder_ty) in
  let d = T_IntroExistsErased g u b p e ty_typing t_typing e_typing in
  prove_post_hint (try_frame_pre pre_typing d res_ppname) post_hint (t <: term).range

let check_intro_exists_non_erased
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { intro_exists_witness_singleton st /\
                not (is_intro_exists_erased st) })
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) tm_vprop))
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_intro_exists_non_erased" st.range in

  let Tm_IntroExists { p=t; witnesses=[witness] } = st.term in
  let (| t, t_typing |) =
    match vprop_typing with
    | Some typing -> (| t, typing |)
    | _ -> check_vprop g t
  in

  if not (Tm_ExistsSL? (t <: term).t)
  then fail g (Some st.range)
         (Printf.sprintf "check_intro_exists_non_erased: vprop %s is not an existential"
            (P.term_to_string t));

  let Tm_ExistsSL u b p = (t <: term).t in

  Pulse.Typing.FV.tot_typing_freevars t_typing;
  let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #b.binder_ty #p t_typing (fresh g) in
  let (| witness, witness_typing |) = 
    check_tot_term_with_expected_type g witness b.binder_ty in
  let d = T_IntroExists g u b p witness ty_typing t_typing witness_typing in
  let (| c, d |) : (c:_ & st_typing g _ c) = (| _, d |) in
  prove_post_hint (try_frame_pre pre_typing d res_ppname) post_hint (t <: term).range

let check_intro_exists
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { intro_exists_witness_singleton st })
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) tm_vprop))

  : T.Tac (checker_result_t g pre post_hint) = 
  
  if is_intro_exists_erased st
  then check_intro_exists_erased g pre pre_typing post_hint res_ppname st vprop_typing
  else check_intro_exists_non_erased g pre pre_typing post_hint res_ppname st vprop_typing 
