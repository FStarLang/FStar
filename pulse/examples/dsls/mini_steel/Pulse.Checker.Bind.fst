module Pulse.Checker.Bind
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
module P = Pulse.Syntax.Printer
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.Pure

let force_st #f #g #t (#pre:pure_term)
             (pre_typing:tot_typing f g pre Tm_VProp)
             (x:(c:pure_comp { stateful_comp c ==> comp_pre c == pre } & src_typing f g t c))
  : T.Tac (c:pure_comp_st { comp_pre c == pre } & src_typing f g t c)
  = let (| c, d_c |) = x in
    match c with
    | C_Tot ty ->
      let (| ures, ures_ty |) = check_universe f g ty in
      let c = return_comp_noeq ures ty in
      let d = T_ReturnNoEq _ _ _ _ d_c ures_ty in
      Framing.frame_empty pre_typing ures_ty _ c d        

    | C_ST _
    | C_STAtomic _ _
    | C_STGhost _ _ -> (|c, d_c|)

#push-options "--z3rlimit_factor 8 --ifuel 1 --fuel 1"
let rec mk_bind (f:RT.fstar_top_env) (g:env)
  (pre:pure_term)
  (e1:term)
  (e2:term)
  (c1:pure_comp_st)
  (c2:pure_comp_st)
  (x:var)
  (d_e1:src_typing f g e1 c1)
  (d_c1res:tot_typing f g (comp_res c1) (Tm_Type (comp_u c1)))
  (d_e2:src_typing f ((x, Inl (comp_res c1))::g) (open_term e2 x) c2)
  (res_typing:universe_of f g (comp_res c2) (comp_u c2))
  (post_typing:tot_typing f ((x, Inl (comp_res c2))::g) (open_term (comp_post c2) x) Tm_VProp)
  : T.TacH (t:term &
            c:pure_comp { stateful_comp c ==> comp_pre c == pre } &
            src_typing f g t c)
           (requires fun _ ->
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True) =

  match c1, c2 with
  | C_ST _, C_ST _ ->
    let bc = Bind_comp g x c1 c2 res_typing x post_typing in
    (| Tm_Bind e1 e2, _, T_Bind _ e1 e2 _ _ _ _ d_e1 d_c1res d_e2 bc |)
  | C_STGhost inames1 _, C_STGhost inames2 _ ->
    if eq_tm inames1 inames2
    then begin
      assume (inames1 == inames2);   
      let bc = Bind_comp g x c1 c2 res_typing x post_typing in
      (| Tm_Bind e1 e2, _, T_Bind _ e1 e2 _ _ _ _ d_e1 d_c1res d_e2 bc |)
    end
    else T.fail "Cannot compose two stghost computations with different opened invariants"
  | C_STAtomic inames _, C_ST _ ->
    if eq_tm inames Tm_EmpInames
    then begin
      assume (inames == Tm_EmpInames);
      let c1lifted = C_ST (st_comp_of_comp c1) in
      let d_e1 : src_typing f g e1 c1lifted =
        T_Lift _ _ _ c1lifted d_e1 (Lift_STAtomic_ST _ c1) in
      let bc = Bind_comp g x c1lifted c2 res_typing x post_typing in
      (| Tm_Bind e1 e2, _, T_Bind _ e1 e2 _ _ _ _ d_e1 d_c1res d_e2 bc |)
    end
    else T.fail "Cannot compose atomic with non-emp opened invariants with stt"
  | C_STGhost inames1 _, C_STAtomic inames2 _ ->
    if eq_tm inames1 inames2
    then begin
      assume (inames1 == inames2);
      let w = get_non_informative_witness f g (comp_u c1) (comp_res c1) in
      let bc = Bind_comp_ghost_l g x c1 c2 w res_typing x post_typing in
      (| Tm_Bind e1 e2, _, T_Bind _ e1 e2 _ _ _ _ d_e1 d_c1res d_e2 bc |)
    end
    else T.fail "Cannot compose ghost and atomic with different opened invariants"
  | C_STAtomic inames1 _, C_STGhost inames2 _ ->
    if eq_tm inames1 inames2
    then begin
      assume (inames1 == inames2);
      let w = get_non_informative_witness f g (comp_u c2) (comp_res c2) in
      let bc = Bind_comp_ghost_r g x c1 c2 w res_typing x post_typing in
      (| Tm_Bind e1 e2, _, T_Bind _ e1 e2 _ _ _ _ d_e1 d_c1res d_e2 bc |)
    end
    else T.fail "Cannot compose atomic and ghost with different opened invariants"
  | C_ST _, C_STAtomic inames _ ->
    if eq_tm inames Tm_EmpInames
    then begin
      assume (inames == Tm_EmpInames);
      let c2lifted = C_ST (st_comp_of_comp c2) in
      let g' = (x, Inl (comp_res c1))::g in
      let d_e2 : src_typing f g' (open_term e2 x) c2lifted =
        T_Lift _ _ _ c2lifted d_e2 (Lift_STAtomic_ST _ c2) in
      let bc = Bind_comp g x c1 c2lifted res_typing x post_typing in
      (| Tm_Bind e1 e2, _, T_Bind _ e1 e2 _ _ _ _ d_e1 d_c1res d_e2 bc |)
    end
    else T.fail "Cannot compose stt with atomic with non-emp opened invariants"
  | C_STGhost inames _, C_ST _ ->
    if eq_tm inames Tm_EmpInames
    then begin
      assume (inames == Tm_EmpInames);
      let w = get_non_informative_witness f g (comp_u c1) (comp_res c1) in
      let c1lifted = C_STAtomic inames (st_comp_of_comp c1) in
      let d_e1 : src_typing f g e1 c1lifted =
        T_Lift _ _ _ c1lifted d_e1 (Lift_STGhost_STAtomic g c1 w) in
      mk_bind f g pre e1 e2 c1lifted c2 x d_e1 d_c1res d_e2 res_typing post_typing
    end
    else T.fail "Cannot compose ghost with stt with non-emp opened invariants"
  | C_ST _, C_STGhost inames _ ->
    if eq_tm inames Tm_EmpInames
    then begin
      assume (inames == Tm_EmpInames);
      let g' = (x, Inl (comp_res c1))::g in
      let w = get_non_informative_witness f g' (comp_u c2) (comp_res c2) in
      let c2lifted = C_STAtomic inames (st_comp_of_comp c2) in
      let d_e2 : src_typing f g' (open_term e2 x) c2lifted =
        T_Lift _ _ _ c2lifted d_e2 (Lift_STGhost_STAtomic g' c2 w) in
      mk_bind f g pre e1 e2 c1 c2lifted x d_e1 d_c1res d_e2 res_typing post_typing
    end
    else T.fail "Cannot compose stt with ghost with non-emp opened invariants"
  | _, _ -> T.fail "bind either not implemented (e.g. ghost) or not possible"
#pop-options

#push-options "--z3rlimit_factor 8 --fuel 2 --ifuel 1 --query_stats"
let check_bind
  (f:RT.fstar_top_env)
  (g:env)
  (t:term{Tm_Bind? t})
  (pre:pure_term)
  (pre_typing:tot_typing f g pre Tm_VProp)
  (post_hint:option term)
  (check:check_t)
  : T.Tac (t:term &
           c:pure_comp { stateful_comp c ==> comp_pre c == pre } &
           src_typing f g t c) =
  let Tm_Bind e1 e2 = t  in
  let (| e1, c1, d1 |) = check f g e1 pre pre_typing None in
  let (| c1, d1 |) = force_st pre_typing (| c1, d1 |) in
  let s1 = st_comp_of_comp c1 in
  let t = s1.res in
  let (| u, t_typing |) = check_universe f g t in
  if u <> s1.u then T.fail "incorrect universe"
  else (
      let x = fresh g in
      let next_pre = open_term s1.post x in
      // T.print (Printf.sprintf "Bind::e1 %s \n\nx %s\n\ne2 %s\n\nnext_pre %s\n\n"
      //            (P.term_to_string e1)
      //            (string_of_int x)
      //            (P.term_to_string (open_term e2 x))
      //            (P.term_to_string next_pre));
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
      let s2 = st_comp_of_comp c2 in
      let (| u, res_typing |) = check_universe f g s2.res in
      if u <> s2.u
      then T.fail "Unexpected universe for result type"
      else if x `Set.mem` freevars s2.post
      then T.fail (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
      else (
        let s2_post_opened = open_term s2.post x in
        let post_typing = check_vprop_no_inst f ((x, Inl s2.res)::g) s2_post_opened in
        mk_bind f g pre e1 e2_closed c1 c2 x d1 t_typing d2 res_typing post_typing
      )
  )
#pop-options
