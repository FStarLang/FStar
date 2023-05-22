module Pulse.Checker.Framing
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Pure
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins
module FV = Pulse.Typing.FV

let rec vprop_as_list (vp:term)
  : list term
  = match vp with
    | Tm_Emp -> []
    | Tm_Star vp0 vp1 -> vprop_as_list vp0 @ vprop_as_list vp1
    | _ -> [vp]

let rec list_as_vprop (vps:list term)
  : term
  = match vps with
    | [] -> Tm_Emp
    | hd::tl -> Tm_Star hd (list_as_vprop tl)

let canon_vprop (vp:term)
  : term
  = list_as_vprop (vprop_as_list vp)

let rec list_as_vprop_append g (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (Tm_Star (list_as_vprop vp0) 
                                 (list_as_vprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : vprop_equiv g (list_as_vprop vp1)
                            (Tm_Star Tm_Emp (list_as_vprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | hd::tl ->
      let tl_vp1 = list_as_vprop_append g tl vp1 in
      let d : vprop_equiv g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star hd (Tm_Star (list_as_vprop tl) (list_as_vprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) tl_vp1
      in
      let d : vprop_equiv g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star (Tm_Star hd (list_as_vprop tl)) (list_as_vprop vp1))
            = VE_Trans _ _ _ _ d (VE_Assoc _ _ _ _) in
      d

let list_as_vprop_comm g (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (list_as_vprop (vp1 @ vp0)))
  = let d1 : _ = list_as_vprop_append g vp0 vp1 in
    let d2 : _ = VE_Sym _ _ _ (list_as_vprop_append g vp1 vp0) in
    let d1 : _ = VE_Trans _ _ _ _ d1 (VE_Comm _ _ _) in
    VE_Trans _ _ _ _ d1 d2

let list_as_vprop_assoc g (vp0 vp1 vp2:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ (vp1 @ vp2)))
                        (list_as_vprop ((vp0 @ vp1) @ vp2)))
  = List.Tot.append_assoc vp0 vp1 vp2;
    VE_Refl _ _
    
let list_as_vprop_ctx g (vp0 vp1 vp2:list term)
  (d:vprop_equiv g (list_as_vprop vp0) (list_as_vprop vp1))
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp2)) (list_as_vprop (vp1 @ vp2)))

  = let split_app = list_as_vprop_append _ vp0 vp2 in
    let ctxt = VE_Ctxt _ _ _ _ _ d (VE_Refl _ (list_as_vprop vp2)) in
    let split_app2 = VE_Sym _ _ _ (list_as_vprop_append _ vp1 vp2) in
    VE_Trans _ _ _ _ split_app (VE_Trans _ _ _ _ ctxt split_app2)
  

let list_as_vprop_singleton g
  (p q:term)
  (d:vprop_equiv g p q)
  : GTot (vprop_equiv g (list_as_vprop [p]) (list_as_vprop [q]))
  = VE_Ctxt _ p Tm_Emp q Tm_Emp d (VE_Refl _ Tm_Emp)

let rec vprop_list_equiv (g:env)
                         (vp:term)
  : GTot (vprop_equiv g vp (canon_vprop vp))
         (decreases vp)
  = match vp with
    | Tm_Emp -> VE_Refl _ _
    | Tm_Star vp0 vp1 ->
      let eq0 = vprop_list_equiv g vp0 in
      let eq1 = vprop_list_equiv g vp1 in      
      let app_eq
        : vprop_equiv _ (canon_vprop vp) (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = list_as_vprop_append g (vprop_as_list vp0) (vprop_as_list vp1)
      in
      let step
        : vprop_equiv _ vp (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> 
      VE_Sym _ _ _
        (VE_Trans _ _ _ _ (VE_Comm g vp Tm_Emp) (VE_Unit _ vp))

module L = FStar.List.Tot.Base

#push-options "--z3rlimit_factor 4"
let check_one_vprop g (p q:term) : T.Tac (option (vprop_equiv g p q)) =
  if eq_tm p q
  then Some (VE_Refl _ _)
  else
    let check_extensional_equality =
      match p, q with
      | Tm_PureApp hd_p _ _, Tm_PureApp hd_q _ _ ->
        eq_tm hd_p hd_q
      | Tm_FStar _, _
      | _, Tm_FStar _ -> true
      | _, _ -> false in
    if check_extensional_equality
    then
      let v0 = elab_term p in
      let v1 = elab_term q in
      match T.check_equiv (elab_env g) v0 v1 with
      | Some token, _ -> Some (VE_Ext g p q token)
      | None, _ -> None
    else None
#pop-options

type split_one_vprop_res g (p:term) (qs:list term) =
  r:option (l:list term & q:term & vprop_equiv g p q & list term){
    Some? r ==>
    (let Some (| l, q, _, r |) = r in
     qs == (l @ [q]) @ r)
  }

let rec maybe_split_one_vprop g (p:term) (qs:list term)
  : T.Tac (split_one_vprop_res g p qs)
  = match qs with
    | [] -> None
    | q::qs ->
      let d_opt = check_one_vprop g p q in
      if Some? d_opt
      then Some (| [], q, Some?.v d_opt, qs |)
      else match maybe_split_one_vprop g p qs with
           | None -> None
           | Some (| l, q', d, r |) -> Some (| q::l, q', d, r |)
    
// let can_split_one_vprop g p qs = Some? (maybe_split_one_vprop g p qs)

// let split_one_vprop_l g
//   (p:pure_term) 
//   (qs:list pure_term { can_split_one_vprop g p qs })
//   : list pure_term
//   = let Some (| l, _, _, _ |) = maybe_split_one_vprop g p qs in
//     l

// let split_one_vprop_r g
//   (p:pure_term) 
//   (qs:list pure_term { can_split_one_vprop g p qs })
//   : list pure_term
//   = let Some (| _, _, _, r |) = maybe_split_one_vprop g p qs in
//     r

// let split_one_vprop_q g
//   (p:pure_term)
//   (qs:list pure_term { can_split_one_vprop g p qs })
//   : q:pure_term & vprop_equiv g p q
//   = let Some (| _, q, d, _ |) = maybe_split_one_vprop g p qs in
//     (| q, d |)

let vprop_equiv_swap_equiv (g:_) (l0 l2:list term)
  (p q:term) (d_p_q:vprop_equiv g p q)
  : GTot (vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop ([p] @ (l0 @ l2)))) =
  let d : vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop (([q] @ l0) @ l2))
    = list_as_vprop_ctx g (l0 @ [q]) ([q] @ l0) l2 (list_as_vprop_comm g l0 [q]) in
  let d' : vprop_equiv g (list_as_vprop (([q] @ l0) @ l2))
                           (list_as_vprop ([q] @ (l0 @ l2)))
    = List.Tot.append_assoc [q] l0 l2;
      VE_Refl _ _ in
  let d : vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop ([q] @ (l0 @ l2)))
    = VE_Trans _ _ _ _ d d' in
  let d_q_p = VE_Sym _ _ _ d_p_q in
  let d' : vprop_equiv g (list_as_vprop [q]) (list_as_vprop [p]) =
    list_as_vprop_singleton _ _ _ d_q_p in
  let d' : vprop_equiv g (list_as_vprop ([q] @ (l0 @ l2)))
                           (list_as_vprop ([p] @ (l0 @ l2)))
    = list_as_vprop_ctx g [q] [p] (l0 @ l2) d' in
  VE_Trans _ _ _ _ d d'

// let vprop_equiv_swap (f:_) (g:_) (l0 l1 l2:list pure_term)
//   : GTot (vprop_equiv g (list_as_vprop ((l0 @ l1) @ l2))
//                           (list_as_vprop (l1 @ (l0 @ l2))))
//   = let d1 : _ = list_as_vprop_append g (l0 @ l1) l2 in
//     let d2 = VE_Trans _ _ _ _ d1 (VE_Ctxt _ _ _ _ _ (list_as_vprop_comm _ _ _ _) (VE_Refl _ _)) in
//     let d3 = VE_Sym _ _ _ (list_as_vprop_append g (l1 @ l0) l2) in
//     let d4 = VE_Trans _ _ _ _ d2 d3 in
//     List.Tot.append_assoc l1 l0 l2;
//     d4

// let split_one_vprop g
//   (p:pure_term) 
//   (qs:list pure_term { can_split_one_vprop g p qs })
//   : list pure_term
//   = split_one_vprop_l g p qs @ split_one_vprop_r g p qs

// let split_one_vprop_equiv g (p:pure_term) (qs:list pure_term { can_split_one_vprop g p qs })
//   : vprop_equiv g (list_as_vprop qs) (Tm_Star p (list_as_vprop (split_one_vprop g p qs)))
//   = let rec aux (qs:list pure_term { can_split_one_vprop g p qs })
//       : Lemma (let Some (| l, q, _, r |) = maybe_split_one_vprop g p qs in
//                qs == ((l @ [q]) @ r))
//       = match qs with
//         | q :: qs ->
//           if Some? (check_one_vprop g p q) then ()
//           else aux qs
//     in
//     aux qs;
//     let Some (| l, q, d, r |) = maybe_split_one_vprop g p qs in
//     vprop_equiv_swap_equiv g l r p q d

let framing_success g req ctxt =
  (frame:list term &
   vprop_equiv g (list_as_vprop (req @ frame)) (list_as_vprop ctxt))
   
let try_frame_result g req ctxt = either (framing_success g req ctxt) framing_failure


let mk_framing_failure #g #req #req' #ctxt #ctxt'
                       (unmatched_pre:term)
                       (res:try_frame_result g req ctxt)
  : try_frame_result g req' ctxt'
  = match res with
    | Inr failure -> 
      Inr { failure with
            unmatched_preconditions=
              unmatched_pre::failure.unmatched_preconditions
          }
    | Inl (| frame, _ |) ->  
      Inr { unmatched_preconditions = [unmatched_pre];
            remaining_context = frame }
            
let rec try_split_vprop g (req:list term) (ctxt:list term)
  : T.Tac 
    (either (frame:list term &
             vprop_equiv g (list_as_vprop (req @ frame)) (list_as_vprop ctxt))
            framing_failure)
  = match req with
    | [] -> Inl (| ctxt, VE_Refl g _ |)
    | hd::tl ->
      match maybe_split_one_vprop g hd ctxt with
      | None -> mk_framing_failure hd (try_split_vprop g tl ctxt)

      | Some (| l, q, d, r |) -> 
        let d1
          : vprop_equiv g (list_as_vprop ctxt)
                            (list_as_vprop (hd :: (l@r)))
          = vprop_equiv_swap_equiv g l r hd q d
        in
        match try_split_vprop g tl (l @ r) with
        | Inr failure -> Inr failure
        | Inl (| frame, d |) ->
          let d
            : vprop_equiv g (list_as_vprop (tl @ frame))
                              (list_as_vprop (l @ r))
            = d
          in
          let dd
            : vprop_equiv g (list_as_vprop (req @ frame))
                              (list_as_vprop (hd :: (l @ r)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) d
          in
          let ddd = VE_Trans _ _ _ _ dd (VE_Sym _ _ _ d1) in
          Inl (| frame, ddd |)
                       
let split_vprop (g:env)
                (ctxt:term)
                (ctxt_typing: tot_typing g ctxt Tm_VProp)
                (req:term)
   : T.Tac (either (frame:term &
                    tot_typing g frame Tm_VProp &
                    vprop_equiv g (Tm_Star req frame) ctxt)
                   framing_failure)
   = let ctxt_l = vprop_as_list ctxt in
     let req_l = vprop_as_list req in
     match try_split_vprop g req_l ctxt_l with
     | Inr failure -> Inr failure 
     | Inl (| frame, veq |) ->
       let d1 
         : vprop_equiv _ (Tm_Star (canon_vprop req) (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Sym _ _ _ (list_as_vprop_append g req_l frame)
       in
       let d1 
         : vprop_equiv _ (Tm_Star req (list_as_vprop frame))
                           (list_as_vprop (req_l @ frame))
         = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (vprop_list_equiv g req) (VE_Refl _ _)) d1
       in
       let d : vprop_equiv  _ (Tm_Star req (list_as_vprop frame))
                             (canon_vprop ctxt) =
           VE_Trans _ _ _ _ d1 veq
       in
       let d : vprop_equiv _ (Tm_Star req (list_as_vprop frame))
                               ctxt =
         VE_Trans _ _ _ _ d (VE_Sym _ _ _ (vprop_list_equiv g ctxt))
       in
       let typing : tot_typing g (list_as_vprop frame) Tm_VProp = 
         let fwd, bk = vprop_equiv_typing d in
         let star_typing = bk ctxt_typing in
         snd (star_typing_inversion star_typing)
       in
       Inl (| list_as_vprop frame, typing, d |)

let rec check_equiv_emp (g:env) (vp:term)
  : option (vprop_equiv g vp Tm_Emp)
  = match vp with
    | Tm_Emp -> Some (VE_Refl _ _)
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp g vp1, check_equiv_emp g vp2 with
       | Some d1, Some d2 ->
         let d3 : vprop_equiv g (Tm_Star vp1 vp2) (Tm_Star Tm_Emp Tm_Emp)
           = VE_Ctxt _ _ _ _ _ d1 d2 in
         let d4 : vprop_equiv g (Tm_Star Tm_Emp Tm_Emp) Tm_Emp =
           VE_Unit _ _ in
         Some (VE_Trans _ _ _ _ d3 d4)
       | _, _ -> None)
     | _ -> None

#push-options "--z3rlimit_factor 2"
let check_vprop_equiv
  (g:env)
  (vp1 vp2:term)
  (vp1_typing:tot_typing g vp1 Tm_VProp)

  : T.Tac (vprop_equiv g vp1 vp2) =

  match split_vprop g vp1 vp1_typing vp2 with
  | Inr failure ->
    T.fail (Printf.sprintf
              "check_vprop_equiv: %s and %s are not equivalent; missing preconditions:\n%s\n"
                (P.term_to_string vp1)
                (P.term_to_string vp2)
                (String.concat "\n" (T.map P.term_to_string failure.unmatched_preconditions)))
                
  | Inl (| frame, _, d |) ->
    match check_equiv_emp g frame with
    | Some d_frame_equiv_emp ->
      let d : vprop_equiv g (Tm_Star vp2 frame) vp1 = d in
      let d : vprop_equiv g vp1 (Tm_Star vp2 frame) =
        VE_Sym _ _ _ d in
      let d' : vprop_equiv g (Tm_Star vp2 frame) (Tm_Star vp2 Tm_Emp) =
        VE_Ctxt _ _ _ _ _ (VE_Refl _ vp2) d_frame_equiv_emp in
      let d : vprop_equiv g vp1 (Tm_Star vp2 Tm_Emp) =
        VE_Trans _ _ _ _ d d' in
      let d' : vprop_equiv g (Tm_Star vp2 Tm_Emp) (Tm_Star Tm_Emp vp2) = VE_Comm _ _ _ in
      let d  : vprop_equiv g vp1 (Tm_Star Tm_Emp vp2) = VE_Trans _ _ _ _ d d' in
      let d' : vprop_equiv g (Tm_Star Tm_Emp vp2) vp2 = VE_Unit _ _ in
      VE_Trans _ _ _ _ d d'
    | None ->
      T.fail (Printf.sprintf "check_vprop_equiv: %s and %s are not equivalent, frame: %s\n"
                             (P.term_to_string vp1)
                             (P.term_to_string vp2)
                             (P.term_to_string frame))
#pop-options

let freevars_comp_post (c:comp { stateful_comp c })
  : Lemma (freevars (comp_post c) `Set.subset` freevars_comp c)
  = ()

#push-options "--z3rlimit_factor 20 --query_stats --fuel 4 --ifuel 2 --query_stats"

let try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre Tm_VProp)
                  (#c:comp { stateful_comp c })
                  (t_typing: st_typing g t c)
  : T.Tac (either (c':comp_st { comp_pre c' == pre } &
                   st_typing g t c')
                  framing_failure)
  = let s = st_comp_of_comp c in
    match split_vprop g pre pre_typing s.pre with
    | Inr failure -> Inr failure
    | Inl (| frame, frame_typing, ve |) ->
      let t_typing
        : st_typing g t (add_frame c frame)
        = T_Frame g t c frame frame_typing t_typing in
      let x = fresh g in
      let px = v_as_nv x in
      let c' = add_frame c frame in
      assert (None? (lookup g x));
      FV.st_typing_freevars_inv t_typing x;
      assert (~ (x `Set.mem` freevars_comp c'));
      freevars_comp_post c';
      assert (~ (x `Set.mem` freevars (comp_post c')));
      let s' = st_comp_of_comp c' in
      let ve: vprop_equiv g s'.pre pre = ve in
      let s'' = { s' with pre = pre } in
      let c'' = c' `with_st_comp` s'' in
      assert (comp_post c' == comp_post c'');
      let g' = extend x (Inl (comp_res c')) g in
      let ve: vprop_equiv g (comp_pre c') (comp_pre c'') = ve in    
      let ve' 
        : vprop_equiv g'
                        (open_term (comp_post c') x)
                        (open_term (comp_post c'') x)
        = VE_Refl _ _
      in
      let pre_typing = check_vprop_with_core g (comp_pre c') in
      let post_typing = check_vprop_with_core g' (open_term_nv (comp_post c') px) in
      let (| u, res_typing |) = check_universe g (comp_res c') in
      if u <> comp_u c' 
      then T.fail "Unexpected universe"
      else (
        let st_equiv = ST_VPropEquiv g c' c'' x pre_typing res_typing post_typing ve ve' in
        let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
        Inl (| c'', t_typing |)
      )

let frame_empty (#g:env)
                (#pre:term)
                (pre_typing: tot_typing g pre Tm_VProp)
                (#u:universe)
                (#ty:term) 
                (ut:universe_of g ty u)
                (t:st_term)
                (c0:comp_st{ comp_pre c0 == Tm_Emp })
                (d:st_typing g t c0)
  : T.Tac (c:comp_st { comp_pre c == pre} &
           st_typing g t c)
  = let d = T_Frame g t c0 pre pre_typing d in
    let c = add_frame c0 pre in
    let s = st_comp_of_comp c in
    let d : st_typing g t c = d in
    let s' = { s with pre = pre } in
    let c' = c `with_st_comp` s' in
    assert (stateful_comp c');
    let x = fresh g in
    let px = v_as_nv x in
    let pre_typing 
      : tot_typing g (comp_pre c) Tm_VProp
      = check_vprop_with_core g (comp_pre c)
    in
    let (| u, res_typing |) = check_universe g (comp_res c) in
    if u <> comp_u c
    then T.fail "Unexpected universe"
    else (
      let res_typing 
        : tot_typing g (comp_res c) (Tm_Type (comp_u c))
        = res_typing 
      in
      let post_typing
        : tot_typing (extend x (Inl (comp_res c)) g)
                     (open_term_nv (comp_post c) px)
                     Tm_VProp
        = check_vprop_with_core (extend x (Inl (comp_res c)) g) 
                                (open_term_nv (comp_post c) px)
      in
      FV.st_typing_freevars_inv d x;
      freevars_comp_post c;
      let eq
        : st_equiv g c c'
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
