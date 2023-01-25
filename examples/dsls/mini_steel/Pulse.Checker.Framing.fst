module Pulse.Checker.Framing
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Pure
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins

let rec vprop_as_list (vp:pure_term)
  : list pure_term
  = match vp with
    | Tm_Emp -> []
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
    | Tm_Emp -> VE_Refl _ _
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

#push-options "--query_stats --fuel 1 --ifuel 2 --z3rlimit_factor 10"
let try_frame_pre (#f:RT.fstar_top_env)
                  (#g:env)
                  (#t:term)
                  (#pre:pure_term)
                  (pre_typing: tot_typing f g pre Tm_VProp)
                  (#c:pure_comp { stateful_comp c })
                  (t_typing: src_typing f g t c)
  : T.Tac (c':pure_comp_st { comp_pre c' == pre } &
           src_typing f g t c')
  = let s = st_comp_of_comp c in
    let (| frame, frame_typing, ve |) = split_vprop f g pre pre_typing s.pre in
    let t_typing
      : src_typing f g t (add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let x = fresh g in
    let c' = add_frame c frame in
    let s' = st_comp_of_comp c' in
    let ve: vprop_equiv f g s'.pre pre = ve in
    let s'' = { s' with pre = pre } in
    let c'' = c' `with_st_comp` s'' in
    assert (is_pure_comp (c `with_st_comp` s'));
    assert (is_pure_comp c'');
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
      (| c'', t_typing |)
    )
#pop-options

#push-options "--z3rlimit_factor 2"
let frame_empty (#f:RT.fstar_top_env)
                (#g:env)
                (#pre:pure_term)
                (pre_typing: tot_typing f g pre Tm_VProp)
                (#u:universe)
                (#ty:pure_term) 
                (ut:universe_of f g ty u)
                (t:term)
                (c0:pure_comp_st{ comp_pre c0 == Tm_Emp })
                (d:src_typing f g t c0)
  : T.Tac (c:pure_comp_st { comp_pre c == pre} &
           src_typing f g t c)
  = let d = T_Frame g t c0 pre pre_typing d in
    let c = add_frame c0 pre in
    let s = st_comp_of_comp c in
    let d : src_typing f g t c = d in
    let s' = { s with pre = pre } in
    let c' = c `with_st_comp` s' in
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
