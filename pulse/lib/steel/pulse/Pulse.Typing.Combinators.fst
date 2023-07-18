module Pulse.Typing.Combinators

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure

let rec vprop_equiv_typing (#g:_) (#t0 #t1:term) (v:vprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 tm_vprop -> tot_typing g t1 tm_vprop) &
          (tot_typing g t1 tm_vprop -> tot_typing g t0 tm_vprop))
        (decreases v)
  = match v with
    | VE_Refl _ _ -> (fun x -> x), (fun x -> x)

    | VE_Sym _ _ _ v' -> 
      let f, g = vprop_equiv_typing v' in
      g, f

    | VE_Trans g t0 t2 t1 v02 v21 ->
      let f02, f20 = vprop_equiv_typing v02 in
      let f21, f12 = vprop_equiv_typing v21 in
      (fun x -> f21 (f02 x)), 
      (fun x -> f20 (f12 x))

    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      let f0, f0' = vprop_equiv_typing v0 in
      let f1, f1' = vprop_equiv_typing v1 in      
      let ff (x:tot_typing g (tm_star s0 s1) tm_vprop)
        : tot_typing g (tm_star s0' s1') tm_vprop
        = let s0_typing = star_typing_inversion_l x in
          let s1_typing = star_typing_inversion_r x in
          let s0'_typing, s1'_typing = f0 s0_typing, f1 s1_typing in
          star_typing s0'_typing s1'_typing
      in
      let gg (x:tot_typing g (tm_star s0' s1') tm_vprop)
        : tot_typing g (tm_star s0 s1) tm_vprop
        = let s0'_typing = star_typing_inversion_l x in
          let s1'_typing = star_typing_inversion_r x in
          star_typing (f0' s0'_typing) (f1' s1'_typing)        
      in
      ff, gg

    | VE_Unit g t ->
      let fwd (x:tot_typing g (tm_star tm_emp t) tm_vprop)
        : tot_typing g t tm_vprop
        = let r = star_typing_inversion_r x in
          r
      in
      let bk (x:tot_typing g t tm_vprop)
        : tot_typing g (tm_star tm_emp t) tm_vprop
        = star_typing emp_typing x
      in
      fwd, bk

    | VE_Comm g t0 t1 ->
      let f t0 t1 (x:tot_typing g (tm_star t0 t1) tm_vprop)
        : tot_typing g (tm_star t1 t0) tm_vprop
        = let tt0 = star_typing_inversion_l x in
          let tt1 = star_typing_inversion_r x in
          star_typing tt1 tt0
      in
      f t0 t1, f t1 t0

    | VE_Assoc g t0 t1 t2 ->
      let fwd (x:tot_typing g (tm_star t0 (tm_star t1 t2)) tm_vprop)
        : tot_typing g (tm_star (tm_star t0 t1) t2) tm_vprop
        = let tt0 = star_typing_inversion_l x in
          let tt12 = star_typing_inversion_r x in
          let tt1 = star_typing_inversion_l tt12 in
          let tt2 = star_typing_inversion_r tt12 in
          star_typing (star_typing tt0 tt1) tt2
      in
      let bk (x : tot_typing g (tm_star (tm_star t0 t1) t2) tm_vprop)
        : tot_typing g (tm_star t0 (tm_star t1 t2)) tm_vprop
        = let tt01 = star_typing_inversion_l x in
          let tt2 = star_typing_inversion_r x in
          let tt0 = star_typing_inversion_l tt01 in
          let tt1 = star_typing_inversion_r tt01 in
          star_typing tt0 (star_typing tt1 tt2)
      in
      fwd, bk
   
    | VE_Ext g t0 t1 token ->
      let d1, d2 = vprop_eq_typing_inversion g t0 t1 token in
      (fun _ -> d2),
      (fun _ -> d1)


#push-options "--z3rlimit_factor 8 --ifuel 1 --fuel 2 --query_stats"
let rec mk_bind (g:env)
                (pre:term)
                (e1:st_term)
                (e2:st_term)
                (c1:comp_st)
                (c2:comp_st)
                (px:nvar { ~ (Set.mem (snd px) (dom g)) })
                (d_e1:st_typing g e1 c1)
                (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
                (d_e2:st_typing (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2)
                (res_typing:universe_of g (comp_res c2) (comp_u c2))
                (post_typing:tot_typing (push_binding g (snd px) (fst px) (comp_res c2))
                                        (open_term_nv (comp_post c2) px)
                                        tm_vprop)
  : T.TacH (t:st_term &
            c:comp_st { st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre } &
            st_typing g t c)
           (requires fun _ ->
              let _, x = px in
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True) =
  let _, x = px in
  let b = nvar_as_binder px (comp_res c1) in
  match c1, c2 with
  | C_ST _, C_ST _ ->
    let bc = Bind_comp g x c1 c2 res_typing x post_typing in
    (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
  | C_STGhost inames1 _, C_STGhost inames2 _ ->
    if eq_tm inames1 inames2
    then begin
      let bc = Bind_comp g x c1 c2 res_typing x post_typing in
      (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
    end
    else fail g None "Cannot compose two stghost computations with different opened invariants"
  | C_STAtomic inames _, C_ST _ ->
    if eq_tm inames tm_emp_inames
    then begin
      let c1lifted = C_ST (st_comp_of_comp c1) in
      let d_e1 : st_typing g e1 c1lifted =
        T_Lift _ _ _ c1lifted d_e1 (Lift_STAtomic_ST _ c1) in
      let bc = Bind_comp g x c1lifted c2 res_typing x post_typing in
      (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
    end
    else fail g None "Cannot compose atomic with non-emp opened invariants with stt"
  | C_STGhost inames1 _, C_STAtomic inames2 _ ->
    if eq_tm inames1 inames2
    then begin
      let w = get_non_informative_witness g (comp_u c1) (comp_res c1) in
      let bc = Bind_comp_ghost_l g x c1 c2 w res_typing x post_typing in
      (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
    end
    else fail g None "Cannot compose ghost and atomic with different opened invariants"
  | C_STAtomic inames1 _, C_STGhost inames2 _ ->
    if eq_tm inames1 inames2
    then begin
      let w = get_non_informative_witness g (comp_u c2) (comp_res c2) in
      let bc = Bind_comp_ghost_r g x c1 c2 w res_typing x post_typing in
      (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
    end
    else fail g None "Cannot compose atomic and ghost with different opened invariants"
  | C_ST _, C_STAtomic inames _ ->
    if eq_tm inames tm_emp_inames
    then begin
      let c2lifted = C_ST (st_comp_of_comp c2) in
      let g' = push_binding g x (fst px) (comp_res c1) in
      let d_e2 : st_typing g' (open_st_term_nv e2 px) c2lifted =
        T_Lift _ _ _ c2lifted d_e2 (Lift_STAtomic_ST _ c2) in
      let bc = Bind_comp g x c1 c2lifted res_typing x post_typing in
      (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
    end
    else fail g None "Cannot compose stt with atomic with non-emp opened invariants"
  | C_STGhost inames _, C_ST _ ->
    if eq_tm inames tm_emp_inames
    then begin
      let w = get_non_informative_witness g (comp_u c1) (comp_res c1) in
      let c1lifted = C_STAtomic inames (st_comp_of_comp c1) in
      let d_e1 : st_typing g e1 c1lifted =
        T_Lift _ _ _ c1lifted d_e1 (Lift_STGhost_STAtomic g c1 w) in
      mk_bind g pre e1 e2 c1lifted c2 px d_e1 d_c1res d_e2 res_typing post_typing
    end
    else fail g None "Cannot compose ghost with stt with non-emp opened invariants"
  | C_ST _, C_STGhost inames _ ->
    if eq_tm inames tm_emp_inames
    then begin
      let g' = push_binding g x (fst px) (comp_res c1) in
      let w = get_non_informative_witness g' (comp_u c2) (comp_res c2) in
      let c2lifted = C_STAtomic inames (st_comp_of_comp c2) in
      let d_e2 : st_typing g' (open_st_term_nv e2 px) c2lifted =
        T_Lift _ _ _ c2lifted d_e2 (Lift_STGhost_STAtomic g' c2 w) in
      let (| t, c, d |) = mk_bind g pre e1 e2 c1 c2lifted px d_e1 d_c1res d_e2 res_typing post_typing in
      (| t, c, d |)
    end
    else fail g None "Cannot compose stt with ghost with non-emp opened invariants"
  | C_STAtomic inames _, C_STAtomic _ _ ->
    if eq_tm inames tm_emp_inames
    then begin
      let c1lifted = C_ST (st_comp_of_comp c1) in
      let d_e1 : st_typing g e1 c1lifted =
        T_Lift _ _ _ c1lifted d_e1 (Lift_STAtomic_ST _ c1) in
      mk_bind g pre e1 e2 c1lifted c2 px d_e1 d_c1res d_e2 res_typing post_typing
    end
    else fail g None "Cannot compose statomics with non-emp opened invariants"
  | _, _ -> fail g None "bind either not implemented (e.g. ghost) or not possible"
#pop-options


let bind_res_and_post_typing (g:env) (s2:st_comp) (x:var { fresh_wrt x g (freevars s2.post) })
                             (post_hint:post_hint_opt g { comp_post_matches_hint (C_ST s2) post_hint })
  : T.Tac (universe_of g s2.res s2.u &
           tot_typing (push_binding g x ppname_default s2.res) (open_term_nv s2.post (v_as_nv x)) tm_vprop)
  = match post_hint with
    | None -> 
      (* We're inferring a post, so these checks are unavoidable *)
      (* since we need to type the result in a smaller env g *)          
      let (| u, res_typing |) = check_universe g s2.res in 
      if not (eq_univ u s2.u)
      then fail g None "Unexpected universe for result type"
      else if x `Set.mem` freevars s2.post
      then fail g None (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
      else (
        let y = x in //fresh g in
        let s2_post_opened = open_term_nv s2.post (v_as_nv y) in
        let post_typing =
          check_vprop_with_core (push_binding g y ppname_default s2.res) s2_post_opened in
        res_typing, post_typing
      )
    | Some post -> 
      if x `Set.mem` freevars s2.post
      then fail g None "Unexpected mismatched postcondition in bind" //exclude with a stronger type on check'
      else (
         let pr = post_hint_typing g post x in
         pr.ty_typing, pr.post_typing
      )

let add_frame (#g:env) (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
  (#frame:vprop)
  (frame_typing:tot_typing g frame tm_vprop)
  : t':st_term &
    c':comp_st { c' == add_frame c frame } &
    st_typing g t' c' =

  (| t, add_frame c frame, T_Frame _ _ _ _ frame_typing t_typing |)

let apply_frame (#g:env)
                (#t:st_term)
                (#ctxt:term)
                (ctxt_typing: tot_typing g ctxt tm_vprop)
                (#c:comp { stateful_comp c })
                (t_typing: st_typing g t c)
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Tot (c':comp_st { comp_pre c' == ctxt /\
                      comp_res c' == comp_res c /\
                      comp_u c' == comp_u c /\
                      comp_post c' == tm_star (comp_post c) (frame_of frame_t) } &
           st_typing g t c')
  = let s = st_comp_of_comp c in
    let (| frame, frame_typing, ve |) = frame_t in
    let t_typing
      : st_typing g t (add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let c' = add_frame c frame in
    let c'_typing = Metatheory.st_typing_correctness t_typing in
    let s' = st_comp_of_comp c' in
    let ve: vprop_equiv g s'.pre ctxt = ve in
    let s'' = { s' with pre = ctxt } in
    let c'' = c' `with_st_comp` s'' in
    assert (comp_post c' == comp_post c'');
    let ve: vprop_equiv g (comp_pre c') (comp_pre c'') = ve in    
    let st_typing = Metatheory.comp_typing_inversion c'_typing in
    let (| res_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_typing in
    let st_equiv = ST_VPropEquiv g c' c'' x pre_typing res_typing post_typing ve (VE_Refl _ _) in
    let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
    (| c'', t_typing |)
