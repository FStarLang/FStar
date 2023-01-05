module Pulse.Checker
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

let rec vprop_as_list (vp:pure_term)
  : list pure_term
  = match vp with
    | Tm_Star vp0 vp1 -> vprop_as_list vp0 @ vprop_as_list vp1
    | _ -> [vp]

let rec list_as_vprop (vps:list pure_term)
  : pure_term
  = match vps with
    | [] -> Tm_Emp
    | hd::tl -> Tm_Star hd (list_as_vprop tl)

let canon_vprop (vp:pure_term)
  : pure_term
  = list_as_vprop (vprop_as_list vp)

let rec list_as_vprop_append f g (vp0 vp1:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                          (Tm_Star (list_as_vprop vp0) 
                                   (list_as_vprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : vprop_equiv f g (list_as_vprop vp1)
                              (Tm_Star Tm_Emp (list_as_vprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | hd::tl ->
      let tl_vp1 = list_as_vprop_append f g tl vp1 in
      let d : vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star hd (Tm_Star (list_as_vprop tl) (list_as_vprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ _) tl_vp1
      in
      let d : vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star (Tm_Star hd (list_as_vprop tl)) (list_as_vprop vp1))
            = VE_Trans _ _ _ _ d (VE_Assoc _ _ _ _) in
      d

let list_as_vprop_comm f g (vp0 vp1:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp1))
                          (list_as_vprop (vp1 @ vp0)))
  = let d1 : _ = list_as_vprop_append f g vp0 vp1 in
    let d2 : _ = VE_Sym _ _ _ (list_as_vprop_append f g vp1 vp0) in
    let d1 : _ = VE_Trans _ _ _ _ d1 (VE_Comm _ _ _) in
    VE_Trans _ _ _ _ d1 d2

let list_as_vprop_assoc f g (vp0 vp1 vp2:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ (vp1 @ vp2)))
                          (list_as_vprop ((vp0 @ vp1) @ vp2)))
  = List.Tot.append_assoc vp0 vp1 vp2;
    VE_Refl _ _

let list_as_vprop_ctx f g (vp0 vp1 vp2:list pure_term)
  (d:vprop_equiv f g (list_as_vprop vp0) (list_as_vprop vp1))
  : GTot (vprop_equiv f g (list_as_vprop (vp0 @ vp2)) (list_as_vprop (vp1 @ vp2)))

  = admit ()

let list_as_vprop_singleton f g
  (p q:pure_term)
  (d:vprop_equiv f g p q)
  : GTot (vprop_equiv f g (list_as_vprop [p]) (list_as_vprop [q]))
  = VE_Ctxt _ p Tm_Emp q Tm_Emp d (VE_Refl _ Tm_Emp)

let rec vprop_list_equiv (f:RT.fstar_top_env)
                         (g:env)
                         (vp:pure_term)
  : GTot (vprop_equiv f g vp (canon_vprop vp))
         (decreases vp)
  = match vp with
    | Tm_Star vp0 vp1 ->
      let eq0 = vprop_list_equiv f g vp0 in
      let eq1 = vprop_list_equiv f g vp1 in      
      let app_eq
        : vprop_equiv _ _ (canon_vprop vp) (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = list_as_vprop_append f g (vprop_as_list vp0) (vprop_as_list vp1)
      in
      let step
        : vprop_equiv _ _ vp (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> 
      VE_Sym _ _ _
        (VE_Trans _ _ _ _ (VE_Comm g vp Tm_Emp) (VE_Unit _ vp))

module L = FStar.List.Tot.Base

let check_one_vprop f g (p q:pure_term) : T.Tac (option (vprop_equiv f g p q)) =
  if p = q
  then Some (VE_Refl _ _)
  else
    let check_extensional_equality =
      match p, q with
      | Tm_PureApp hd_p _ _, Tm_PureApp hd_q _ _ ->
        hd_p = hd_q
      | _, _ -> false in
    if check_extensional_equality
    then
      let v0 = elab_pure p in
      let v1 = elab_pure q in
      let vprop_eq_tm = vprop_eq_tm v0 v1 in
      match T.check_prop_validity (extend_env_l f g) vprop_eq_tm with
      | Some token -> Some (VE_Ext g p q token)
      | None -> None
    else None

type split_one_vprop_res f g (p:pure_term) (qs:list pure_term) =
  r:option (l:list pure_term & q:pure_term & vprop_equiv f g p q & list pure_term){
    Some? r ==>
    (let Some (| l, q, _, r |) = r in
     qs == (l @ [q]) @ r)
  }

let rec maybe_split_one_vprop f g (p:pure_term) (qs:list pure_term)
  : T.Tac (split_one_vprop_res f g p qs)
  = match qs with
    | [] -> None
    | q::qs ->
      let d_opt = check_one_vprop f g p q in
      if Some? d_opt
      then Some (| [], q, Some?.v d_opt, qs |)
      else match maybe_split_one_vprop f g p qs with
           | None -> None
           | Some (| l, q', d, r |) -> Some (| q::l, q', d, r |)
    
// let can_split_one_vprop f g p qs = Some? (maybe_split_one_vprop f g p qs)

// let split_one_vprop_l f g
//   (p:pure_term) 
//   (qs:list pure_term { can_split_one_vprop f g p qs })
//   : list pure_term
//   = let Some (| l, _, _, _ |) = maybe_split_one_vprop f g p qs in
//     l

// let split_one_vprop_r f g
//   (p:pure_term) 
//   (qs:list pure_term { can_split_one_vprop f g p qs })
//   : list pure_term
//   = let Some (| _, _, _, r |) = maybe_split_one_vprop f g p qs in
//     r

// let split_one_vprop_q f g
//   (p:pure_term)
//   (qs:list pure_term { can_split_one_vprop f g p qs })
//   : q:pure_term & vprop_equiv f g p q
//   = let Some (| _, q, d, _ |) = maybe_split_one_vprop f g p qs in
//     (| q, d |)

let vprop_equiv_swap_equiv (f:_) (g:_) (l0 l2:list pure_term)
  (p q:pure_term) (d_p_q:vprop_equiv f g p q)
  : GTot (vprop_equiv f g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop ([p] @ (l0 @ l2)))) =
  let d : vprop_equiv f g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop (([q] @ l0) @ l2))
    = list_as_vprop_ctx f g (l0 @ [q]) ([q] @ l0) l2 (list_as_vprop_comm f g l0 [q]) in
  let d' : vprop_equiv f g (list_as_vprop (([q] @ l0) @ l2))
                           (list_as_vprop ([q] @ (l0 @ l2)))
    = List.Tot.append_assoc [q] l0 l2;
      VE_Refl _ _ in
  let d : vprop_equiv f g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop ([q] @ (l0 @ l2)))
    = VE_Trans _ _ _ _ d d' in
  let d_q_p = VE_Sym _ _ _ d_p_q in
  let d' : vprop_equiv f g (list_as_vprop [q]) (list_as_vprop [p]) =
    list_as_vprop_singleton _ _ _ _ d_q_p in
  let d' : vprop_equiv f g (list_as_vprop ([q] @ (l0 @ l2)))
                           (list_as_vprop ([p] @ (l0 @ l2)))
    = list_as_vprop_ctx f g [q] [p] (l0 @ l2) d' in
  VE_Trans _ _ _ _ d d'

// let vprop_equiv_swap (f:_) (g:_) (l0 l1 l2:list pure_term)
//   : GTot (vprop_equiv f g (list_as_vprop ((l0 @ l1) @ l2))
//                           (list_as_vprop (l1 @ (l0 @ l2))))
//   = let d1 : _ = list_as_vprop_append f g (l0 @ l1) l2 in
//     let d2 = VE_Trans _ _ _ _ d1 (VE_Ctxt _ _ _ _ _ (list_as_vprop_comm _ _ _ _) (VE_Refl _ _)) in
//     let d3 = VE_Sym _ _ _ (list_as_vprop_append f g (l1 @ l0) l2) in
//     let d4 = VE_Trans _ _ _ _ d2 d3 in
//     List.Tot.append_assoc l1 l0 l2;
//     d4

// let split_one_vprop f g
//   (p:pure_term) 
//   (qs:list pure_term { can_split_one_vprop f g p qs })
//   : list pure_term
//   = split_one_vprop_l f g p qs @ split_one_vprop_r f g p qs

// let split_one_vprop_equiv f g (p:pure_term) (qs:list pure_term { can_split_one_vprop f g p qs })
//   : vprop_equiv f g (list_as_vprop qs) (Tm_Star p (list_as_vprop (split_one_vprop f g p qs)))
//   = let rec aux (qs:list pure_term { can_split_one_vprop f g p qs })
//       : Lemma (let Some (| l, q, _, r |) = maybe_split_one_vprop f g p qs in
//                qs == ((l @ [q]) @ r))
//       = match qs with
//         | q :: qs ->
//           if Some? (check_one_vprop f g p q) then ()
//           else aux qs
//     in
//     aux qs;
//     let Some (| l, q, d, r |) = maybe_split_one_vprop f g p qs in
//     vprop_equiv_swap_equiv f g l r p q d

let rec try_split_vprop f g (req:list pure_term) (ctxt:list pure_term)
  : T.Tac (option (frame:list pure_term &
                   vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop ctxt)))
  = match req with
    | [] -> Some (| ctxt, VE_Refl g _ |)
    | hd::tl ->
      match maybe_split_one_vprop f g hd ctxt with
      | None -> None
      | Some (| l, q, d, r |) -> 
        let d1 : vprop_equiv f g (list_as_vprop ctxt) (list_as_vprop (hd :: (l@r))) =
          vprop_equiv_swap_equiv f g l r hd q d in
        match try_split_vprop f g tl (l @ r) with
        | None -> None
        | Some (| frame, d |) ->
          let d : vprop_equiv f g (list_as_vprop (tl @ frame)) (list_as_vprop (l @ r)) = d in
          let dd : vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop (hd :: (l @ r))) = 
              VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) d
          in
          let ddd = VE_Trans _ _ _ _ dd (VE_Sym _ _ _ d1) in
          Some (| frame, ddd |)
                       
let split_vprop (f:RT.fstar_top_env)
                (g:env)
                (ctxt:pure_term)
                (ctxt_typing: tot_typing f g ctxt Tm_VProp)
                (req:pure_term)
   : T.Tac (frame:pure_term &
            tot_typing f g frame Tm_VProp &
            vprop_equiv f g (Tm_Star req frame) ctxt)
   = let ctxt_l = vprop_as_list ctxt in
     let req_l = vprop_as_list req in
     match try_split_vprop f g req_l ctxt_l with
     | None -> T.fail (Printf.sprintf "Could not find frame: \n\tcontext = %s\n\trequires = %s\n"
                                            (String.concat " ** " (List.Tot.map P.term_to_string ctxt_l))
                                            (String.concat " ** " (List.Tot.map P.term_to_string req_l)))
     | Some (| frame, veq |) ->
       let d1 
         : vprop_equiv _ _ (Tm_Star (canon_vprop req) (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Sym _ _ _ (list_as_vprop_append f g req_l frame)
       in
       let d1 
         : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (vprop_list_equiv f g req) (VE_Refl _ _)) d1
       in
       let d : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                               (canon_vprop ctxt) =
           VE_Trans _ _ _ _ d1 veq
       in
       let d : vprop_equiv _ _ (Tm_Star req (list_as_vprop frame))
                               ctxt =
         VE_Trans _ _ _ _ d (VE_Sym _ _ _ (vprop_list_equiv f g ctxt))
       in
       let typing : tot_typing f g (list_as_vprop frame) Tm_VProp = 
         let fwd, bk = vprop_equiv_typing _ _ _ _ d in
         let star_typing = bk ctxt_typing in
         snd (star_typing_inversion _ _ _ _ star_typing)
       in
       (| list_as_vprop frame, typing, d |)

let rec check_equiv_emp (f:RT.fstar_top_env) (g:env) (vp:pure_term)
  : option (vprop_equiv f g vp Tm_Emp)
  = match vp with
    | Tm_Emp -> Some (VE_Refl _ _)
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp f g vp1, check_equiv_emp f g vp2 with
       | Some d1, Some d2 ->
         let d3 : vprop_equiv f g (Tm_Star vp1 vp2) (Tm_Star Tm_Emp Tm_Emp)
           = VE_Ctxt _ _ _ _ _ d1 d2 in
         let d4 : vprop_equiv f g (Tm_Star Tm_Emp Tm_Emp) Tm_Emp =
           VE_Unit _ _ in
         Some (VE_Trans _ _ _ _ d3 d4)
       | _, _ -> None)
     | _ -> None

#push-options "--z3rlimit_factor 2"
let check_vprop_equiv
  (f:RT.fstar_top_env)
  (g:env)
  (vp1 vp2:pure_term)
  (vp1_typing:tot_typing f g vp1 Tm_VProp)

  : T.Tac (vprop_equiv f g vp1 vp2) =

  let (| frame, _, d |) = split_vprop f g vp1 vp1_typing vp2 in
  match check_equiv_emp f g frame with
  | Some d_frame_equiv_emp ->
    let d : vprop_equiv f g (Tm_Star vp2 frame) vp1 = d in
    let d : vprop_equiv f g vp1 (Tm_Star vp2 frame) =
      VE_Sym _ _ _ d in
    let d' : vprop_equiv f g (Tm_Star vp2 frame) (Tm_Star vp2 Tm_Emp) =
      VE_Ctxt _ _ _ _ _ (VE_Refl _ vp2) d_frame_equiv_emp in
    let d : vprop_equiv f g vp1 (Tm_Star vp2 Tm_Emp) =
      VE_Trans _ _ _ _ d d' in
    let d' : vprop_equiv f g (Tm_Star vp2 Tm_Emp) (Tm_Star Tm_Emp vp2) = VE_Comm _ _ _ in
    let d  : vprop_equiv f g vp1 (Tm_Star Tm_Emp vp2) = VE_Trans _ _ _ _ d d' in
    let d' : vprop_equiv f g (Tm_Star Tm_Emp vp2) vp2 = VE_Unit _ _ in
    VE_Trans _ _ _ _ d d'
  | None ->
    T.fail (Printf.sprintf "check_vprop_equiv: %s and %s are not equivalent, frame: %s\n"
                 (P.term_to_string vp1)
                 (P.term_to_string vp2)
                 (P.term_to_string frame))
#pop-options

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

#push-options "--query_stats --fuel 1 --ifuel 2 --z3rlimit_factor 8"
let try_frame_pre (#f:RT.fstar_top_env)
                  (#g:env)
                  (#t:term)
                  (#pre:pure_term)
                  (pre_typing: tot_typing f g pre Tm_VProp)
                  (#c:pure_comp { C_ST? c })
                  (t_typing: src_typing f g t c)
  : T.Tac (c':pure_comp_st { comp_pre c' == pre } &
           src_typing f g t c')
  = let C_ST s = c in
    let (| frame, frame_typing, ve |) = split_vprop f g pre pre_typing s.pre in
    let t_typing
      : src_typing f g t (add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let x = fresh g in
    let c' = add_frame c frame in
    let C_ST s' = c' in
    let ve: vprop_equiv f g s'.pre pre = ve in
    let s'' = { s' with pre = pre } in
    let c'' = C_ST s'' in
    assert (is_pure_comp (C_ST s'));
    assert (is_pure_comp (C_ST s''));
    assert (comp_post c' == comp_post c'');
    opening_pure_term_with_pure_term
      (comp_post c')
      (null_var x)
      0;
    opening_pure_term_with_pure_term
      (comp_post c'')
      (null_var x)
      0;    
    assert (is_pure_term (open_term (comp_post c') x));
    let g' = ((x, Inl (comp_res c'))::g) in
    let ve: vprop_equiv f g (comp_pre c') (comp_pre c'') = ve in    
    let ve' 
      : vprop_equiv f g'
                      (open_term (comp_post c') x)
                      (open_term (comp_post c'') x)
      = VE_Refl _ _
    in
    let pre_typing = check_vprop_no_inst f g (comp_pre c') in
    let post_typing = check_vprop_no_inst f g' (open_term (comp_post c') x) in
    let (| u, res_typing |) = check_universe f g (comp_res c') in
    if u <> comp_u c' 
    then T.fail "Unexpected universe"
    else (
      let st_equiv = ST_VPropEquiv g c' c'' x pre_typing res_typing post_typing ve ve' in
      let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
      (| C_ST s'', t_typing |)
    )
#pop-options

#push-options "--z3rlimit_factor 2"
let frame_empty (f:RT.fstar_top_env)
                (g:env)
                (pre:pure_term)
                (pre_typing: tot_typing f g pre Tm_VProp)
                (u:universe)
                (ty:pure_term) 
                (ut:universe_of f g ty u)
                (t:term)
                (c0:pure_comp_st{ comp_pre c0 == Tm_Emp })
                (d:src_typing f g t c0)
  : T.Tac (c:pure_comp_st { comp_pre c == pre} &
           src_typing f g t c)
  = let d = T_Frame g t c0 pre pre_typing d in
    let c = add_frame c0 pre in
    let C_ST s = c in
    let d : src_typing f g t c = d in
    let s' = { s with pre = pre } in
    let c' = C_ST s' in
    let x = fresh g in
    let pre_typing = check_vprop_no_inst f g (comp_pre c) in
    let (| u, res_typing |) = check_universe f g (comp_res c) in
    if u <> comp_u c
    then T.fail "Unexpected universe"
    else (
      let post_typing = check_vprop_no_inst f ((x, Inl (comp_res c))::g) 
                                            (open_term (comp_post c) x) in
      let eq
        : st_equiv f g c c'
        = ST_VPropEquiv g c c' x
                        pre_typing
                        res_typing
                        post_typing
                        (VE_Unit g pre)
                        (VE_Refl _ _)
      in
      (| c', T_Equiv _ _ _ _ d eq |)
    )
#pop-options

let replace_equiv_post
  (f:RT.fstar_top_env)
  (g:env)
  (c:pure_comp{C_ST? c})
  (post_hint:option term)

  : T.Tac (c1:pure_comp & st_equiv f g c c1) =

  let C_ST {u=u_c;res=res_c;pre=pre_c;post=post_c} = c in
  let x = fresh g in
  let g_post = (x, Inl res_c)::g in

  let pre_c_typing : tot_typing f g pre_c Tm_VProp =
    check_vprop_no_inst f g pre_c in
  let res_c_typing : tot_typing f g res_c (Tm_Type u_c) =
    let (| u, ty |) = check_universe f g res_c in
    if u = u_c
    then ty
    else T.fail "T_Abs: re-typechecking the return type returned different universe" in
  let post_c_opened = open_term post_c x in
  let post_c_typing
    : tot_typing f g_post (open_term post_c x) Tm_VProp
    = check_vprop_no_inst f g_post post_c_opened in

  match post_hint with
  | None ->
    (| c,
       ST_VPropEquiv
         g c c x pre_c_typing res_c_typing post_c_typing
         (VE_Refl _ _)
         (VE_Refl _ _) |)
  | Some post ->
    let post_opened = open_term post x in
    let (| post_opened, post_typing |) = check_vprop f g_post post_opened in
    let post_c_post_eq : vprop_equiv f g_post post_c_opened post_opened =
      check_vprop_equiv f g_post post_c_opened post_opened post_c_typing in

    let c_with_post = 
      C_ST {
        u=u_c;
        res=res_c;
        pre=pre_c;
        post=close_term post_opened x
      }
    in
    assume (open_term (close_term post_opened x) x == post_opened);
    assume (is_pure_comp c_with_post);
    (| c_with_post,
       ST_VPropEquiv
         g c c_with_post x pre_c_typing res_c_typing post_c_typing
         (VE_Refl _ _)
         post_c_post_eq |)

let check_abs
  (f:RT.fstar_top_env)
  (g:env)
  (t:term{Tm_Abs? t})
  (pre:pure_term)
  (pre_typing:tot_typing f g pre Tm_VProp)
  (post_hint:option term)
  (check:check_t)
  : T.Tac (t:term &
           c:pure_comp { C_ST? c ==> comp_pre c == pre } &
           src_typing f g t c) =
  match t with  
  | Tm_Abs {binder_ty=t;binder_ppname=ppname} qual pre_hint body post_hint ->  (* {pre}  (fun (x:t) -> body) : ? { pre } *)
    let (| t, _, _ |) = check_tot f g t in //elaborate it first
    let (| u, t_typing |) = check_universe f g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let g' = (x, Inl t) :: g in
    let pre_opened = open_term pre_hint x in
    match check_tot f g' pre_opened with
    | (| pre_opened, Tm_VProp, pre_typing |) ->
      let pre = close_term pre_opened x in
      let post =
        match post_hint with
        | None -> None
        | Some post ->
          let post = open_term' post (Tm_Var {nm_ppname="_";nm_index=x}) 1 in
          Some post
      in
      assume (is_pure_term pre_opened);
      let (| body', c_body, body_typing |) = check f g' (open_term body x) pre_opened (E pre_typing) post in

      let body_closed = close_term body' x in
      assume (open_term body_closed x == body');

      let tt = T_Abs g ppname x qual t u body_closed c_body pre_hint post_hint t_typing body_typing in
      let tres = Tm_Arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| Tm_Abs {binder_ty=t;binder_ppname=ppname} qual pre_hint body_closed post_hint, 
         C_Tot tres,
         tt |)
    | _ -> T.fail "bad hint"

#push-options "--z3rlimit_factor 8 --fuel 2 --ifuel 1 --query_stats"

let force_st #f #g #t (#pre:pure_term)
             (pre_typing:tot_typing f g pre Tm_VProp)
             (x:(c:pure_comp { C_ST? c ==> comp_pre c == pre } & src_typing f g t c))
  : T.Tac (c:pure_comp_st { comp_pre c == pre } & src_typing f g t c)
  = let (| c, d_c |) = x in
    match c with
    | C_Tot ty ->
      let (| ures, ures_ty |) = check_universe f g ty in
      let c = return_comp_noeq ures ty in
      let d = T_ReturnNoEq _ _ _ _ d_c ures_ty in
      frame_empty f g pre pre_typing ures ty ures_ty _ c d        

    | C_ST _ -> (|c, d_c|)

let check_bind
  (f:RT.fstar_top_env)
  (g:env)
  (t:term{Tm_Bind? t})
  (pre:pure_term)
  (pre_typing:tot_typing f g pre Tm_VProp)
  (post_hint:option term)
  (check:check_t)
  : T.Tac (t:term &
           c:pure_comp { C_ST? c ==> comp_pre c == pre } &
           src_typing f g t c) =
  let frame_empty = frame_empty f g pre pre_typing in
  let Tm_Bind e1 e2 = t  in
  let (| e1, c1, d1 |) = check f g e1 pre pre_typing None in
  let (| c1, d1 |) = force_st pre_typing (| c1, d1 |) in
  let C_ST s1 = c1 in
  let t = s1.res in
  let (| u, t_typing |) = check_universe f g t in
  if u <> s1.u then T.fail "incorrect universe"
  else (
      let x = fresh g in
      let next_pre = open_term s1.post x in
      let g' = (x, Inl s1.res)::g in
      //would be nice to prove that this is typable as a lemma,
      //without having to re-check it
      let next_pre_typing : tot_typing f g' next_pre Tm_VProp
        = check_vprop_no_inst f g' next_pre
      in
      let (| e2', c2, d2 |) = check f g' (open_term e2 x) next_pre next_pre_typing post_hint in
      let (| c2, d2 |) = force_st #_ #_ #e2' next_pre_typing (| c2, d2 |) in
      let e2_closed = close_term e2' x in
      assume (open_term e2_closed x == e2');
      let d2 : src_typing f g' e2' c2 = d2 in
      let d2 : src_typing f g' (open_term e2_closed x) c2 = d2 in
      let C_ST s2 = c2 in
      let (| u, res_typing |) = check_universe f g s2.res in
      if u <> s2.u
      then T.fail "Unexpected universe for result type"
      else if x `Set.mem` freevars s2.post
      then T.fail (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
      else (
        let s2_post_opened = open_term s2.post x in
        let post_typing = check_vprop_no_inst f ((x, Inl s2.res)::g) s2_post_opened in
        let bc : bind_comp f g x c1 c2 _ = (Bind_comp g x c1 c2 res_typing x post_typing) in
        (| Tm_Bind e1 e2_closed, _, T_Bind _ e1 e2_closed _ _ _ _ d1 t_typing d2 bc |)
      )
  )
#pop-options

let rec infer_gen_uvars (t_head:term) : T.Tac (list term & term & comp) =
  match t_head with
  | Tm_Arrow {binder_ty=t} (Some Implicit) (C_Tot rest) ->
    let uv = gen_uvar t in
    let rest = open_term' rest uv 0 in
    let uv_rest, last_arg_t, comp_typ = infer_gen_uvars rest in
    uv::uv_rest, last_arg_t, comp_typ

  | Tm_Arrow {binder_ty=t} None st ->
    [], t, st

  | _ ->
   T.fail (FStar.Printf.sprintf "infer_gen_uvars: unexpected t_head: %s" (P.term_to_string t_head))

let rec infer_check_valid_solution (t1 t2:term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

  match uv_sols with
  | [] -> [t1, t2]
  | (t1', t2')::tl ->
    if t1 = t1'
    then if t2 = t2' then uv_sols
         else T.fail "infer_check_valid_solution failed"
    else (t1', t2')::(infer_check_valid_solution t1 t2 tl)

let rec infer_match_typ (t1 t2:term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

  match t1, t2 with
  | Tm_UVar _ n, _ ->
    infer_check_valid_solution t1 t2 uv_sols
  | _, Tm_UVar _ _ -> T.fail "infer_match_typ: t2 is a uvar"

  | Tm_PureApp head1 arg_qual1 arg1, Tm_PureApp head2 arg_qual2 arg2 ->
    if arg_qual1 = arg_qual2
    then let uv_sols = infer_match_typ head1 head2 uv_sols in
         infer_match_typ arg1 arg2 uv_sols
    else uv_sols

  | _, _ -> uv_sols

let rec infer_atomic_vprop_has_uvar (t:term) : bool =
  match t with
  | Tm_UVar _ _ -> true
  | Tm_PureApp head _ arg ->
    infer_atomic_vprop_has_uvar head || infer_atomic_vprop_has_uvar arg
  | Tm_Emp -> false
  | _ -> false

let rec infer_atomic_vprops_may_match (t1:term) (t2:pure_term) : bool =
  match t1, t2 with
  | Tm_UVar _ _, _ -> true
  | Tm_PureApp head1 q1 arg1, Tm_PureApp head2 q2 arg2 ->
    infer_atomic_vprops_may_match head1 head2 &&
    q1 = q2 &&
    infer_atomic_vprops_may_match arg1 arg2
  | _, _ -> t1 = t2

let infer_one_atomic_vprop (t:pure_term) (ctxt:list pure_term) (uv_sols:list (term & term))
  : T.Tac (list (term & term)) =

  if infer_atomic_vprop_has_uvar t
  then
    let matching_ctxt = List.Tot.filter (fun ctxt_vp -> infer_atomic_vprops_may_match t ctxt_vp) ctxt in
    T.print (FStar.Printf.sprintf "infer_one_atomic_vprop %s, found %d matching candidates\n"
               (P.term_to_string t)
               (List.Tot.length matching_ctxt));
    if List.Tot.length matching_ctxt = 1
    then
      let _ = T.print (FStar.Printf.sprintf "infer_one_atomic_vprop: matching %s and %s with %d exisiting solutions\n"
                         (P.term_to_string t)
                         (P.term_to_string (List.Tot.hd matching_ctxt))
                         (List.Tot.length uv_sols)) in 
      let uv_sols = infer_match_typ t (List.Tot.hd matching_ctxt) uv_sols in
      T.print (FStar.Printf.sprintf "post matching, uv_sols has %d solutions\n"
                 (List.Tot.length uv_sols));
      uv_sols
    else uv_sols
  else uv_sols

let rec infer_build_head (head:term) (uvs:list term) (uv_sols:list (term & term))
  : T.Tac term
  = match uvs with
    | [] -> head
    | hd::tl ->
      let ropt = List.Tot.find (fun (t1, _) -> t1 = hd) uv_sols in
      match ropt with
      | None -> T.fail "inference failed in building head"
      | Some (_, t2) ->
        let app_node = Tm_PureApp head (Some Implicit) t2 in
        infer_build_head app_node tl uv_sols

let infer
  (head:term)
  (t_head:term)
  (arg:term)
  (t_arg:term)
  qual
  (ctxt_pre:term)
  
  : T.Tac term =

  let uvs, t_arg_expected, pre =
    let uvs, t_arg_expected, comp = infer_gen_uvars t_head in
    let comp = open_comp' comp arg 0 in
    match comp with
    | C_ST st_comp -> uvs, t_arg_expected, st_comp.pre
    | _ -> T.fail "infer:unexpected comp type" in

  if List.Tot.length uvs = 0
  then head
  else begin
    T.print (FStar.Printf.sprintf "infer: generated %d uvars, ctx: %s, st_comp.pre: %s\n"
               (List.Tot.length uvs)
               (P.term_to_string ctxt_pre)
               (P.term_to_string pre));

    let uv_sols = infer_match_typ t_arg_expected t_arg [] in

    assume (is_pure_term pre);
    let pre_list = vprop_as_list pre in

    assume (is_pure_term ctxt_pre);
    let ctxt_pre_list = vprop_as_list ctxt_pre in

    let uv_sols = T.fold_left (fun uv_sols st_pre_vprop ->
      infer_one_atomic_vprop st_pre_vprop ctxt_pre_list uv_sols) uv_sols pre_list in

    let head = infer_build_head head uvs uv_sols in
    Tm_STApp head qual arg
  end

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 4"
#push-options "--print_implicits --print_universes --print_full_names"
let rec check =
  fun (f:RT.fstar_top_env)
    (g:env)
    (t:term)
    (pre:pure_term)
    (pre_typing: tot_typing f g pre Tm_VProp)
    (post_hint:option term) ->
  let repack #g #pre #t (x:(c:pure_comp_st { comp_pre c == pre } & src_typing f g t c)) (apply_post_hint:bool)
    : T.Tac (t:term & c:pure_comp { C_ST? c ==> comp_pre c == pre } & src_typing f g t c) =
    let (| c, d_c |) = x in
    if apply_post_hint && C_ST? c
    then
      let (| c1, c_c1_eq |) = replace_equiv_post f g c post_hint in
      assume (comp_pre c1 == comp_pre c);
      (| t, c1, T_Equiv _ _ _ _ d_c c_c1_eq |)
    else (| t, c, d_c |)
  in

  let frame_empty = frame_empty f g pre pre_typing in
  match t with
  | Tm_BVar _ -> T.fail "not locally nameless"
  | Tm_Var _
  | Tm_FVar _ 
  | Tm_UInst _ _
  | Tm_Constant _
  | Tm_PureApp _ _ _
  | Tm_Let _ _ _ ->
    let (| t, u, ty, uty, d |) = check_tot_univ f g t in
    assume (is_pure_term t);
    let c = return_comp u ty t in
    let d = T_Return _ _ _ _ (E d) uty in
    repack (frame_empty u ty uty t c d) false

  | Tm_Emp
  | Tm_Pure _
  | Tm_Star _ _ 
  | Tm_ExistsSL _ _
  | Tm_ForallSL _ _
  | Tm_Arrow _ _ _
  | Tm_Type _
  | Tm_VProp
  | Tm_Refine _ _ ->
    let (| t, ty, d_ty |) = check_tot f g t in
    (| t, C_Tot ty, d_ty |)

  | Tm_Abs _ _ _ _ _ -> check_abs f g t pre pre_typing post_hint check
  | Tm_STApp head qual arg ->
    let (| head, ty_head, dhead |) = check_tot f g head in
    begin
    match ty_head with
    | Tm_Arrow {binder_ty=formal;binder_ppname=ppname} bqual comp_typ ->
      if bqual = Some Implicit && qual = None
      then let (| arg, ty_arg, _ |) = check_tot f g arg in
           let t = infer head ty_head arg ty_arg qual pre in
           check f g t pre pre_typing post_hint
      else if bqual = None && qual = Some Implicit
      then T.fail "Unexpected qualifier"
      else (
        let res =
          match comp_typ with
          | C_ST res -> res
          | _ ->
            T.fail (Printf.sprintf "Unexpected comp type in impure application: %s" (P.term_to_string ty_head)) in
        let (| arg, darg |) = check_tot_with_expected_typ f g arg formal in
        assume (is_pure_term arg);
        let d = T_STApp g head ppname formal qual (C_ST res) arg dhead (E darg) in
        opening_pure_comp_with_pure_term (C_ST res) arg 0;
        repack (try_frame_pre pre_typing d) true
      )
    | _ -> T.fail (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head))
    end

  | Tm_Bind _ _ ->
    check_bind f g t pre pre_typing post_hint check
  | Tm_If _ _ _ ->
    T.fail "Not handling if yet"

  | Tm_UVar _ _ ->
    T.fail "Unexpected Tm_Uvar in check"
#pop-options
