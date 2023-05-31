module Pulse.Checker.Auto.Prover
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.VPropEquiv
module T = FStar.Tactics
module VP = Pulse.Checker.VPropEquiv
module F = Pulse.Checker.Framing

let vprop_typing g v = tot_typing g v Tm_VProp

let ghost_comp pre post = 
  C_STGhost Tm_EmpInames { u=u_zero; res=tm_unit; pre; post }

let unit_const = magic()
let proof_steps_idem
  : st_term
  = { term = Tm_Return { ctag=STT_Ghost; insert_eq=false; term=unit_const};
      range = Range.range_0 }
let proof_steps_idem_typing (g:env) (ctxt:vprop)
  : st_typing g proof_steps_idem (ghost_comp ctxt ctxt)
  = magic()

let comp_st_with_post (c:comp_st) (post:term) : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i st -> C_STAtomic i {st with post}

let comp_st_with_pre (c:comp_st) (pre:term) : comp_st =
  match c with
  | C_ST st -> C_ST { st with pre }
  | C_STGhost i st -> C_STGhost i { st with pre }
  | C_STAtomic i st -> C_STAtomic i {st with pre }

assume
val post_with_emp (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (comp_st_with_post c (Tm_Star (canon_vprop (comp_post c)) Tm_Emp) )

module Metatheory = Pulse.Typing.Metatheory

let vprop_equiv_x g t p1 p2 =
  x:var { Metatheory.fresh_wrt x g (freevars p1) } ->
  vprop_equiv (extend x (Inl t) g) 
              (open_term p1 x)
              (open_term p2 x)

assume
val st_typing_equiv_post (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                         (#post:term )//{ freevars post `Set.subset` freevars (comp_post c)}
                         (veq: vprop_equiv_x g (comp_res c) (comp_post c) post)
  : st_typing g t (comp_st_with_post c post)

assume
val st_typing_equiv_pre (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
                        (#pre:term )//{ freevars post `Set.subset` freevars (comp_post c)}
                        (veq: vprop_equiv g (comp_pre c) pre)
  : st_typing g t (comp_st_with_pre c pre)


noeq
type prover_state (g:env) (ctxt:vprop) = {
  (* the original context is well-typed *)
  ctxt_typing: vprop_typing g ctxt;
  (* the program whose precondition we're trying to derive *)
  t:st_term;
  c:comp_st;
  t_typing:st_typing g t c;
  (* the in-progress proof state *)
  matched_pre:term; (* conjuncts that we have already derived *)
  unmatched_pre:list term; (* conjuncts remaining to be derived *)
  remaining_ctxt:list term; (* unused conjuncts in the context *)
  (* Ghost proof steps witnessing the derivation of matched_pre from ctxt *)
  proof_steps: st_term;
  proof_steps_typing: st_typing g proof_steps (ghost_comp ctxt (Tm_Star (list_as_vprop remaining_ctxt) matched_pre));
  pre_equiv:vprop_equiv g (comp_pre c) (Tm_Star (list_as_vprop unmatched_pre) matched_pre);
}

let proof_steps_post #g #o (p:prover_state g o) : vprop = Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre

let bind_proof_steps_with #g #o (p:prover_state g o) 
                                (t:st_term)
                                (c:comp_st {comp_pre c == proof_steps_post p})
                                (t_typing:st_typing g t c)
   : (t':st_term & st_typing g t' (comp_st_with_pre c o))
   = admit()

let init_prover_state (#g:env) (#ctxt:vprop) (ctxt_typing: vprop_typing g ctxt)
                      (#t:st_term) (#c:comp_st) (t_typing: st_typing g t c)
  : prover_state g ctxt
  = { 
        ctxt_typing;
        t; 
        c; 
        t_typing;

        matched_pre = Tm_Emp;
        unmatched_pre = vprop_as_list (comp_pre c);
        remaining_ctxt = vprop_as_list ctxt;

        pre_equiv = VE_Trans _ _ _ _ (vprop_list_equiv _ (comp_pre c))
                                     (VE_Sym _ _ _ (VP.ve_unit_r _ (canon_vprop (comp_pre c))));
        proof_steps=proof_steps_idem;
        proof_steps_typing=post_with_emp (proof_steps_idem_typing _ ctxt);
    }

open FStar.List.Tot 

let step_t = #g:_ -> #o:_ -> p:prover_state g o -> T.Tac (option (prover_state g o))

let step_match : step_t = 
  fun #g #o (p:prover_state g o) ->
    let res = F.all_matches g p.unmatched_pre p.remaining_ctxt in
    match res.matched with
    | [] -> None
    | _ ->
      let matched_pre = Tm_Star (list_as_vprop res.matched) p.matched_pre in
        // remaining_ctxt ~ res.ctxt' * res.matched
      let veq 
        : vprop_equiv_x g tm_unit 
                          (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre)
                          (Tm_Star (list_as_vprop res.unmatched_q) matched_pre)
        = magic ()
      in
        // p.unmatched_pre ~ res.unmatched @ res.matched
      let pre_equiv
          : vprop_equiv g (comp_pre p.c) (Tm_Star (list_as_vprop res.unmatched_p) matched_pre)
          = magic ()
      in
      let proof_steps_typing = st_typing_equiv_post p.proof_steps_typing veq in
      Some 
        { p with unmatched_pre = res.unmatched_p;
                 matched_pre;
                 remaining_ctxt = res.unmatched_q;
                 proof_steps_typing;
                 pre_equiv }

let step_intro_exists #g #o (p:prover_state g o) : T.Tac (option (prover_state g o)) = None

let step_intro_pure #g #o (p:prover_state g o) : T.Tac (option (prover_state g o)) = None
let step_intro_rewrite #g #o (p:prover_state g o) : T.Tac (option (prover_state g o)) = None

let rec first_success (l:list step_t) : step_t = 
  fun #g #o p ->
    match l with
    | [] -> None
    | s :: l -> 
      match s p with
      | None -> first_success l p
      | Some p -> Some p

(* Take one step of proving, matching at least one unmatched pre, or rewriting the context.
   If neither, then returns None; and the outer loop should fail reporting unmatched preconditions *)
let step : step_t
  = first_success [ step_match <: step_t;
                    step_intro_exists <: step_t;
                    step_intro_pure <: step_t;
                    step_intro_rewrite <: step_t ]

                                //  
let finish #g #o (p:prover_state g o { p.unmatched_pre == []})
  : (t:st_term & c:comp_st { comp_pre c == o } & st_typing g t c)
  = assume (list_as_vprop [] == Tm_Emp);
    let veq1 : vprop_equiv _ (comp_pre p.c) p.matched_pre = VE_Trans _ _ _ _ p.pre_equiv (VE_Unit _ _) in
    let t_typing : st_typing g p.t (comp_st_with_pre p.c p.matched_pre) = st_typing_equiv_pre p.t_typing veq1 in
    let remaining_context_typing : vprop_typing g (list_as_vprop p.remaining_ctxt) = magic () in
    let framing_token : F.frame_for_req_in_ctxt g (proof_steps_post p) p.matched_pre =
      (| list_as_vprop p.remaining_ctxt,
         remaining_context_typing,
         VE_Comm _ _ _ |)
    in
    let ctxt_typing : vprop_typing g (proof_steps_post p) = magic () in
    let (| _, t_typing |) = F.apply_frame ctxt_typing t_typing framing_token in
    let (| t, t_typing |) = bind_proof_steps_with p _ _ t_typing in
    (| _, _, t_typing |)

let as_failure #g #o (p:prover_state g o) = {
  unmatched_preconditions = p.unmatched_pre;
  remaining_context = p.remaining_ctxt
}

let rec solve #g #o (p:prover_state g o)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == o } &
         st_typing g t c)
        framing_failure)
  = match step p with
    | None -> Inr (as_failure p)
    | Some p ->
      match p.unmatched_pre with
      | [] -> Inl (finish p)
      | _ -> solve p

let prove_precondition (#g:env)
                       (#ctxt:term)
                       (ctxt_typing: tot_typing g ctxt Tm_VProp)
                       (#t:st_term)
                       (#c:comp_st)
                       (t_typing: st_typing g t c)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == ctxt } &
         st_typing g t c)
        framing_failure)
   = solve (init_prover_state ctxt_typing t_typing)