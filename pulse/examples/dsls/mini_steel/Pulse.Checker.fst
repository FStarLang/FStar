module Pulse.Checker
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

module RTB = Refl.Typing.Builtins

let tc_meta_callback (f:R.env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.typing f e t))
  = let topt = RTB.tc_term f e in
    match topt with
    | None -> None
    | Some t ->
      Some (| t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |)

assume
val readback_ty (t:R.term)
  : T.Tac (option (ty:pure_term { elab_term ty == Some t }))

let check_universe (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe & universe_of f g t u) { is_pure_term t })
  = let f = extend_env_l f g in
    match elab_term t with
    | None -> T.fail "Not a syntactically pure term"
    | Some rt ->
      match tc_meta_callback f rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | Some (Tm_Type u) -> (| u, E (T_Tot _ _ _ tok) |)
        | _ -> T.fail "Not typeable as a universe"
      
let check_tot_univ (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(u:universe &
              ty:pure_term &
              universe_of f g ty u &
              src_typing f g t (C_Tot ty)) { is_pure_term t } )
  = let fg = extend_env_l f g in
    match elab_term t with
    | None -> T.fail "Not a syntactically pure term"
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail "Inexpressible type"
        | Some ty -> 
          let (| u, uty |) = check_universe f g ty in
          (| u, ty, uty, T_Tot g t ty tok |)

let check_tot (f:fstar_top_env) (g:env) (t:term)
  : T.Tac (_:(ty:pure_term &
              src_typing f g t (C_Tot ty)) { is_pure_term t })
  = let fg = extend_env_l f g in
    match elab_term t with
    | None -> T.fail "Not a syntactically pure term"
    | Some rt -> 
      match tc_meta_callback fg rt with
      | None -> T.fail "Not typeable"
      | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None -> T.fail "Inexpressible type"
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
  
let rec vprop_list_equiv (f:fstar_top_env)
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
let rec maybe_split_one_vprop (p:term) (qs:list pure_term)
  : option (list pure_term & list pure_term)
  = match qs with
    | [] -> None
    | q::qs -> 
      if p = q
      then Some ([], qs)
      else match maybe_split_one_vprop p qs with
           | None -> None
           | Some (l, r) -> Some (q::l, r)
    
let can_split_one_vprop p qs = Some? (maybe_split_one_vprop p qs)

let split_one_vprop_l (p:pure_term) 
                      (qs:list pure_term { can_split_one_vprop p qs })
  : list pure_term
  = let Some (l, r) = maybe_split_one_vprop p qs in
    l

let split_one_vprop_r (p:pure_term) 
                      (qs:list pure_term { can_split_one_vprop p qs })
  : list pure_term
  = let Some (l, r) = maybe_split_one_vprop p qs in
    r

let vprop_equiv_swap (f:_) (g:_) (l0 l1 l2:list pure_term)
  : GTot (vprop_equiv f g (list_as_vprop ((l0 @ l1) @ l2))
                          (list_as_vprop (l1 @ (l0 @ l2))))
  = let d1 : _ = list_as_vprop_append f g (l0 @ l1) l2 in
    let d2 = VE_Trans _ _ _ _ d1 (VE_Ctxt _ _ _ _ _ (list_as_vprop_comm _ _ _ _) (VE_Refl _ _)) in
    let d3 = VE_Sym _ _ _ (list_as_vprop_append f g (l1 @ l0) l2) in
    let d4 = VE_Trans _ _ _ _ d2 d3 in
    List.Tot.append_assoc l1 l0 l2;
    d4

let split_one_vprop (p:pure_term) 
                    (qs:list pure_term { can_split_one_vprop p qs })
  : list pure_term
  = split_one_vprop_l p qs @ split_one_vprop_r p qs 

let split_one_vprop_equiv f g (p:pure_term) (qs:list pure_term { can_split_one_vprop p qs })
  : vprop_equiv f g (list_as_vprop qs) (Tm_Star p (list_as_vprop (split_one_vprop p qs)))
  = let rec aux (qs:list pure_term { can_split_one_vprop p qs })
      : Lemma (qs == ((split_one_vprop_l p qs @ [p]) @ split_one_vprop_r p qs))
      = match qs with
        | q :: qs ->
          if p = q then ()
          else aux qs
    in
    aux qs;
    vprop_equiv_swap f g (split_one_vprop_l p qs) [p] (split_one_vprop_r p qs)

let rec try_split_vprop f g (req:list pure_term) (ctxt:list pure_term)
  : option (frame:list pure_term &
            vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop ctxt))
  = match req with
    | [] -> Some (| ctxt, VE_Refl g _ |)
    | hd::tl ->
      match maybe_split_one_vprop hd ctxt with
      | None -> None
      | Some (l, r) -> 
        let d1 : vprop_equiv f g (list_as_vprop ctxt) (list_as_vprop (hd :: (l@r))) = split_one_vprop_equiv _ _ hd ctxt in
        match try_split_vprop f g tl (l @ r) with
        | None -> None
        | Some (| frame, d |) ->
          let d : vprop_equiv f g (list_as_vprop (tl @ frame)) (list_as_vprop (l @ r)) = d in
          let dd : vprop_equiv f g (list_as_vprop (req @ frame)) (list_as_vprop (hd :: (l @ r))) = 
              VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) d
          in
          let ddd = VE_Trans _ _ _ _ dd (VE_Sym _ _ _ d1) in
          Some (| frame, ddd |)
                       
let split_vprop (f:fstar_top_env)
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
     | None -> T.fail "Could not find frame"
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

#push-options "--query_stats --fuel 1 --ifuel 2 --z3rlimit_factor 4"
let try_frame_pre (#f:fstar_top_env)
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
    opening_pure_term_with_pure_term (comp_post c') (Tm_Var x) 0;
    opening_pure_term_with_pure_term (comp_post c'') (Tm_Var x) 0;    
    assert (is_pure_term (open_term (comp_post c') x));
    let g' = ((x, Inl (comp_res c'))::g) in
    let ve: vprop_equiv f g (comp_pre c') (comp_pre c'') = ve in    
    let ve' 
      : vprop_equiv f g'
                      (open_term (comp_post c') x)
                      (open_term (comp_post c'') x) = VE_Refl _ _ in
    let st_equiv = ST_VPropEquiv g c' c'' x ve ve' in
    let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
    (| C_ST s'', t_typing |)
#pop-options

let frame_empty (f:fstar_top_env)
                (g:env)
                (pre:pure_term)
                (pre_typing: tot_typing f g pre Tm_VProp)
                (u:universe)
                (ty:pure_term) 
                (ut:universe_of f g ty u)
                (t:term)
                (c:pure_comp_st{ comp_pre c == Tm_Emp })
                (d:src_typing f g t c)
  : (c:pure_comp_st { comp_pre c == pre} &
     src_typing f g t c)
  = let d = T_Frame g t c pre pre_typing d in
    let c = add_frame c pre in
    let C_ST s = c in
    let d : src_typing f g t c = d in
    let s' = { s with pre = pre } in
    let c' = C_ST s' in
    let x = fresh g in
    let eq : st_equiv f g c c' = ST_VPropEquiv g c c' x (VE_Unit g pre) (VE_Refl _ _) in
    (| c', T_Equiv _ _ _ _ d eq |)
      
#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 10"
let rec check (f:fstar_top_env)
              (g:env)
              (t:term)
              (pre:pure_term)
              (pre_typing: tot_typing f g pre Tm_VProp)
  : T.Tac (c:pure_comp_st { comp_pre c == pre } &
           src_typing f g t c)
  = let frame_empty = frame_empty f g pre pre_typing in
    match t with
    | Tm_BVar _ -> T.fail "not locally nameless"
    | Tm_Var _
    | Tm_FVar _ 
    | Tm_Constant _
    | Tm_PureApp _ _
    | Tm_Let _ _ _ 
    | Tm_Emp
    | Tm_Pure _
    | Tm_Star _ _ 
    | Tm_ExistsSL _ _
    | Tm_ForallSL _ _
    | Tm_Arrow _ _
    | Tm_Type _
    | Tm_VProp ->
      let (| u, ty, uty, d |) = check_tot_univ f g t in
      let c = return_comp u ty t in
      let d = T_Return _ _ _ _ (E d) uty in
      frame_empty u ty uty t c d

    | Tm_Abs t pre_hint body ->
      let (| u, t_typing |) = check_universe f g t in
      let x = fresh g in
      let g' = (x, Inl t) :: g in
      let pre = open_term pre_hint x in
      (
        match check_tot f g' pre with
        | (| Tm_VProp, pre_typing |) ->
          let (| c_body, body_typing |) = check f g' (open_term body x) pre (E pre_typing) in
          let tt = T_Abs g x t u body c_body pre_hint t_typing body_typing in
          let tres = Tm_Arrow t (close_comp c_body x) in
          (* could avoid this re-checking call if we had a lemma about arrow typing *)
          let (| ures, ures_ty |) = check_universe f g tres in
          let c = return_comp_noeq ures tres in
          let d = T_ReturnNoEq _ _ _ _ tt ures_ty in
          frame_empty ures tres ures_ty _ c d
          
        | _ -> T.fail "bad hint"
      )

    | Tm_STApp head arg ->
      let (| ty_head, dhead |) = check_tot f g head in
      let (| ty_arg, darg |) = check_tot f g arg in      
      begin
      match ty_head with
      | Tm_Arrow formal (C_ST res) ->
        if ty_arg <> formal
        then T.fail "Type of formal parameter does not match type of argument"
        else let d = T_STApp g head formal (C_ST res) arg dhead (E darg) in
             opening_pure_comp_with_pure_term (C_ST res) arg 0;
             try_frame_pre pre_typing d
      | _ -> T.fail "Unexpected head type in impure application"
      end

    | Tm_Bind t e1 e2 ->
      let (| c1, d1 |) = check f g e1 pre pre_typing in
      let C_ST s1 = c1 in
      if t <> s1.res 
      then T.fail "Annotated type of let-binding is incorrect"
      else (
        match check_tot f g t with
        | (| Tm_Type u, t_typing |) ->
          if u <> s1.u then T.fail "incorrect universe"
          else (
            let x = fresh g in
            let next_pre = open_term s1.post x in
            let g' = (x, Inl s1.res)::g in
            let next_pre_typing : tot_typing f g' next_pre Tm_VProp =
              //would be nice to prove that this is typable as a lemma,
              //without having to re-check it
              match check_tot f g' next_pre with
              | (| Tm_VProp, nt |) -> E nt
              | _ -> T.fail "next pre is not typable"
            in
            let (| c2, d2 |) = check f g' (open_term e2 x) next_pre next_pre_typing in
            let C_ST s2 = c2 in
            let (| u, res_typing |) = check_universe f g s2.res in
            if u <> s2.u || x `Set.mem` freevars s2.post
            then T.fail "Unexpected universe for result type or variable escapes scope in bind"
            else (
              match check_tot f ((x, Inl s2.res)::g) (open_term s2.post x) with
              | (| Tm_VProp, post_typing |) ->
                let bc : bind_comp f g x c1 c2 _ = (Bind_comp g x c1 c2 res_typing x (E post_typing)) in
                (| _, T_Bind _ _ _ _ _ _ _ d1 (E t_typing) d2 bc |)
              | _ -> T.fail "Ill-typed postcondition in bind"
            )
          )
        | _ -> T.fail "Ill-typed annotated type on `bind`"
     )
    | Tm_If _ _ _ ->
      T.fail "Not handling if yet"
#pop-options
