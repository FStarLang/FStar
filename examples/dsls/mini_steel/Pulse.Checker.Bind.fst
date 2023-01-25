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

let get_bind_comp (f:RT.fstar_top_env) (g:env)
  (c1:pure_comp_st)
  (c2:pure_comp_st)
  (x:var)
  (res_typing:universe_of f g (comp_res c2) (comp_u c2))
  (post_typing:tot_typing f ((x, Inl (comp_res c2))::g) (open_term (comp_post c2) x) Tm_VProp)
  : T.TacH (c:pure_comp_st{comp_pre c == comp_pre c1} & bind_comp f g x c1 c2 c)
           (requires fun _ ->
              None? (lookup g x) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True) =

  if C_ST? c1 && C_ST? c2
  then (| bind_comp_out c1 c2, Bind_comp g x c1 c2 res_typing x post_typing |)
  else T.fail ""

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
        let (| _, bc |) = get_bind_comp f g c1 c2 x res_typing post_typing in
        //let bc : bind_comp f g x c1 c2 _ = (Bind_comp g x c1 c2 res_typing x post_typing) in
        (| Tm_Bind e1 e2_closed, _, T_Bind _ e1 e2_closed _ _ _ _ d1 t_typing d2 bc |)
      )
  )
#pop-options
