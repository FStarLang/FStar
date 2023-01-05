module Pulse.Checker.Pure
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins


let tc_no_inst (f:R.env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.typing f e t))
  = let ropt = RTB.core_check_term f e in
    match ropt with
    | None -> None
    | Some (t) ->
      Some (| t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |)

let tc_meta_callback (f:R.env) (e:R.term) 
  : T.Tac (option (e:R.term & t:R.term & RT.typing f e t))
  = let ropt = RTB.tc_term f e in
    match ropt with
    | None -> None
    | Some (e, t) ->
      Some (| e, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |)

let tc_expected_meta_callback (f:R.env) (e:R.term) (t:R.term)
  : T.Tac (option (e:R.term & RT.typing f e t)) =

  let ropt = RTB.tc_term f e in
  match ropt with
  | None -> None
  | Some (e, te) ->
    //we have typing_token f e te
    match RTB.check_subtyping f te t with
    | None -> None
    | Some p -> //p:squash (subtyping_token f te t)
      Some (| e,
              RT.T_Sub _ _ _ _ (RT.T_Token _ _ _ (FStar.Squash.get_proof (RTB.typing_token f e te)))
                             (RT.ST_Token _ _ _ p) |)


let check_universe (f0:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe & universe_of f0 g t u) { is_pure_term t })
  = let f = extend_env_l f0 g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt ->
      let ru_opt = RTB.universe_of f rt in
      match ru_opt  with
      | None -> T.fail (Printf.sprintf "%s elaborated to %s; Not typable as a universe"
                         (P.term_to_string t)
                         (T.term_to_string rt))
      | Some ru ->
        let uopt = readback_universe ru in
        let proof : squash (RTB.typing_token f rt (R.pack_ln (R.Tv_Type ru))) =
          FStar.Squash.get_proof _ in
        let proof : RT.typing f rt (R.pack_ln (R.Tv_Type ru)) = RT.T_Token _ _ _ proof in
        match uopt with
        | None -> T.fail "check_universe: failed to readback the universe"
        | Some u ->
          let proof : tot_typing f0 g t (Tm_Type u) =
            E (T_Tot g _ _ proof) in
          (| u, proof |)
      
let check_tot_univ (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(t:term &
              u:universe &
              ty:pure_term &
              universe_of f g ty u &
              src_typing f g t (C_Tot ty)) { is_pure_term t } )
  = let fg = extend_env_l f g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> 
        T.fail
          (Printf.sprintf "check_tot_univ: %s elaborated to %s Not typeable"
                          (P.term_to_string t)
                          (T.term_to_string rt))
      | Some (| rt, ty', tok |) ->
        match readback_ty rt, readback_ty ty' with
        | None, _
        | _, None -> T.fail "Inexpressible type/term"
        | Some t, Some ty -> 
          let (| u, uty |) = check_universe f g ty in
          (| t, u, ty, uty, T_Tot g t ty tok |)

let check_tot (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(t:term &
              ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })
  = let fg = extend_env_l f g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> 
        T.fail 
          (Printf.sprintf "check_tot: %s elaborated to %s Not typeable"
            (P.term_to_string t)
            (T.term_to_string rt))
      | Some (| rt, ty', tok |) ->
        match readback_ty rt, readback_ty ty' with
        | None, _
        | _, None -> T.fail "Inexpressible type/term"
        | Some t, Some ty -> 
          (| t, ty, T_Tot g t ty tok |)

let check_tot_with_expected_typ (f:RT.fstar_top_env) (g:env) (e:term) (t:pure_term)
  : T.Tac (_:(e:term & src_typing f g e (C_Tot t)){is_pure_term e}) =

  let fg = extend_env_l f g in
  match elab_term e with
  | None -> 
    T.fail ("check_tot_with_expected_typ: not a pure term: " ^ P.term_to_string e)
  | Some re ->
    match elab_term t with
    | None ->
      T.fail ("check_tot_with_expected_typ: not a pure type: " ^ P.term_to_string t)
    | Some rt ->
      match tc_expected_meta_callback fg re rt with
      | None -> T.fail "check_tot_with_expected_typ: Not typeable"
      | Some (| re, tok |) ->
        match readback_ty re with
        | Some e -> (| e, T_Tot g e t tok |)
        | None -> T.fail "readback failed"

let check_tot_no_inst (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })
  = let fg = extend_env_l f g in
    match elab_term t with
    | None ->
      T.fail ("Not a syntactically pure term: " ^ P.term_to_string t)
    | Some rt -> 
      match tc_no_inst fg rt with
      | None -> 
        T.fail 
          (Printf.sprintf "check_tot: %s elaborated to %s Not typeable"
            (P.term_to_string t)
            (T.term_to_string rt))
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail (Printf.sprintf "Inexpressible type %s for term %s"
                                        (T.term_to_string ty')
                                        (P.term_to_string t))
        | Some ty -> 
          (| ty, T_Tot g t ty tok |)


let check_vprop_no_inst (f:RT.fstar_top_env)
                        (g:env)
                        (t:term)
  : T.Tac (_:tot_typing f g t Tm_VProp{is_pure_term t})
  = let (| ty, d |) = check_tot_no_inst f g t in
    match ty with
    | Tm_VProp -> E d
    | _ -> T.fail "Expected a vprop"

let check_vprop (f:RT.fstar_top_env)
                (g:env)
                (t:term)
  : T.Tac (t:term & _:tot_typing f g t Tm_VProp{is_pure_term t})
  = let (| t, ty, d |) = check_tot f g t in
    match ty with
    | Tm_VProp -> (| t, E d |)
    | _ -> T.fail "Expected a vprop"
