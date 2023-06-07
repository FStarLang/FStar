module Pulse.Checker.Exists

module T = FStar.Tactics
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Checker.VPropEquiv

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV

module Metatheory = Pulse.Typing.Metatheory

let vprop_as_list_typing (#g:env) (#p:term)
  (t:tot_typing g p Tm_VProp)
  (x:term { List.Tot.memP x (vprop_as_list p) })
  : tot_typing g x Tm_VProp
  = assume false; t

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

let check_elim_exists
  (g:env)
  (t:st_term{Tm_ElimExists? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint) =
  let Tm_ElimExists { p = t } = t.term in
  let t_t_typing : (t:term & tot_typing g t Tm_VProp ) = 
      match t with
      | Tm_Unknown -> (
        //There should be exactly one exists_ vprop in the context and we eliminate it      
        let ts = vprop_as_list pre in
        let exist_tms = List.Tot.Base.filter (function | Tm_ExistsSL _ _ _ -> true | _ -> false) ts in
        match exist_tms with
        | [one] -> 
          assume (one `List.Tot.memP` ts);
          (| one, vprop_as_list_typing pre_typing one |) //shouldn't need to check this again
        | _ -> 
          T.fail 
            (Printf.sprintf "Could not decide which exists term to eliminate: choices are\n%s"
               (terms_to_string exist_tms))
        )
      | _ ->
        let t, _ = instantiate_term_implicits g t in
        assume false;
        (| t, pre_typing |)
//        check_vprop g t
  in
  let (| t, t_typing |) = t_t_typing in
//  let (| t, t_typing |) = check_vprop g t in
  match t with
  | Tm_ExistsSL u { binder_ty=ty } p ->
    // T.print (Printf.sprintf "LOG ELIM EXISTS: %s\n"
    //                         (P.term_to_string t));

    // Could this come from inversion of t_typing?
    let (| u', ty_typing |) = check_universe g ty in
    if eq_univ u u'
    then let x = fresh g in
         let d = T_ElimExists g u ty p x ty_typing t_typing in
         repack (try_frame_pre pre_typing d) post_hint
    else T.fail "Universe checking failed in elim_exists"
  | _ -> T.fail "elim_exists argument not a Tm_ExistsSL"

let is_intro_exists_erased (st:st_term) = 
  match st.term with
  | Tm_IntroExists { erased } -> erased
  | _ -> false

let check_intro_exists_erased
  (g:env)
  (st:st_term{intro_exists_witness_singleton st /\
              is_intro_exists_erased st})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint) =

  let Tm_IntroExists { p=t; witnesses=[e]; should_check } = st.term in
  let (| t, t_typing |) = 
    match vprop_typing with
    | Some typing -> (| t, typing |)
    | _ ->   
      if T.unseal should_check
      then check_vprop g t
      else let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t in
           (| t, magic () |)
  in
  match t with
  | Tm_ExistsSL u { binder_ty=ty } p ->
    Pulse.Typing.FV.tot_typing_freevars t_typing;
    let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #ty #p t_typing (fresh g) in
    let (| e, e_typing |) = 
        check_term_with_expected_type g e (mk_erased u ty) in
    let d = T_IntroExistsErased g u ty p e ty_typing t_typing (E e_typing) in
    repack (try_frame_pre pre_typing d) post_hint
  | _ -> T.fail "elim_exists argument not a Tm_ExistsSL"


let check_intro_exists
  (g:env)
  (st:st_term{intro_exists_witness_singleton st /\ not (is_intro_exists_erased st)})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint) =

  let Tm_IntroExists { p=t; witnesses=[witness]; should_check } = st.term in
  let (| t, t_typing |) =
    match vprop_typing with
    | Some typing -> (| t, typing |)
    | _ -> 
      if T.unseal should_check
      then check_vprop g t
      else let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t in
           (| t, magic () |)
  in
  match t with
  | Tm_ExistsSL u { binder_ty = ty } p ->
    Pulse.Typing.FV.tot_typing_freevars t_typing;
    let ty_typing, _ = Metatheory.tm_exists_inversion #g #u #ty #p t_typing (fresh g) in
    let (| witness, witness_typing |) = 
        check_term_with_expected_type g witness ty in
    let d = T_IntroExists g u ty p witness ty_typing t_typing (E witness_typing) in
    let (| c, d |) : (c:_ & st_typing g _ c) = (| _, d |) in
    T.print (Printf.sprintf "Intro exists with witness, got: %s\n"
                     (P.comp_to_string c));
    repack (try_frame_pre pre_typing d) post_hint
  | _ -> T.fail "elim_exists argument not a Tm_ExistsSL"

let check_intro_exists_either
  (g:env)
  (st:st_term{intro_exists_witness_singleton st})
  (vprop_typing: option (tot_typing g (intro_exists_vprop st) Tm_VProp))
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g pre post_hint) = 
  // T.print (Printf.sprintf "LOG INTRO EXISTS: %s"
  //                           (P.term_to_string (intro_exists_vprop st)));
    if is_intro_exists_erased st
    then check_intro_exists_erased g st vprop_typing pre pre_typing post_hint
    else check_intro_exists g st vprop_typing pre pre_typing post_hint
