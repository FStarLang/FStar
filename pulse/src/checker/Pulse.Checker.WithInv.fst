(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Checker.WithInv

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Checker.Comp
open Pulse.Show

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RT = FStar.Reflection.Typing
module MT = Pulse.Typing.Metatheory

let rt_recheck (gg:env) (#g:T.env) (#e:T.term) (#ty: T.typ) () : T.Tac (RT.tot_typing g e ty) =
  let open Pulse.PP in
  // info_doc gg (Some (T.range_of_term e)) [
  //   doc_of_string "Re-checking" ^/^
  //     pp e ^/^
  //   doc_of_string "at type" ^/^
  //     pp ty
  //  ];
  match T.core_check_term g e ty T.E_Total with
  | Some tok, _ -> RT.T_Token _ _ _ ()
  | None, _ -> T.fail "Checker.WithInv: rt_recheck failed" // fixme add a range

let recheck (#g:env) (#e:term) (#ty: typ) () : T.Tac (tot_typing g e ty) =
  core_check_tot_term g e ty

let term_remove_inv (inv:vprop) (tm:term) : T.Tac (tm':term { tm_star tm' inv == tm}) =
  match inspect_term tm with
  | Some (Tm_Star tm inv') ->
    if eq_tm inv inv' then tm
    else T.fail "term_remove_inv"
  | _ ->
    T.fail "term_remove_inv: not a star?"

let st_comp_remove_inv (inv:vprop) (c:st_comp) : T.Tac (s:st_comp { add_frame (C_ST s) inv == (C_ST c) }) =
  { c with pre = term_remove_inv inv c.pre
         ; post = term_remove_inv inv c.post }

#push-options "--z3rlimit 50 --query_stats --split_queries no --max_fuel 2 --max_ifuel 1"  
let check_iname_disjoint (g:env) (r:range) (inv_p inames inv:term)
: T.Tac (Pulse.Typing.prop_validity g (inv_disjointness inv_p inames inv))
= let goal = inv_disjointness inv_p inames inv in
  let (| tag, goal_typing |) =
    Pulse.Checker.Pure.core_check_term_at_type g goal tm_prop
  in
  if tag <> T.E_Total
  then T.fail "Impossible: prop typing is always total"
  else (
    let tok = Pulse.Checker.Pure.try_check_prop_validity g goal goal_typing in
    match tok with
    | None ->
      fail_doc g (Some r) [
        Pulse.PP.text "Failed to prove that an invariant is not recursively opened:";
        Pulse.PP.prefix 4 1 (Pulse.PP.text "The set of invariant names: ") (Pulse.PP.pp inames);
        Pulse.PP.prefix 4 1 (Pulse.PP.text "may contain the invariant: ") (Pulse.PP.pp inv);
      ]
    | Some tok -> tok
  )
 
#push-options "--ifuel 2 --fuel 8"
let remove_iname (inv_p inames inv:term)
: term
= tm_fstar 
    (Pulse.Reflection.Util.remove_inv_tm
      (elab_term inv_p)
      (elab_term inames)
      (elab_term inv))
  (Pulse.RuntimeUtils.range_of_term inames)
let add_iname (inv_p inames inv:term)
: term
= tm_fstar 
    (Pulse.Reflection.Util.add_inv_tm
      (elab_term inv_p)
      (elab_term inames)
      (elab_term inv))
  (Pulse.RuntimeUtils.range_of_term inames)
#pop-options

module RU = Pulse.RuntimeUtils
let all_inames =
  tm_fstar Pulse.Reflection.Util.all_inames_tm FStar.Range.range_0
let all_inames_typing (g:env)
: tot_typing g all_inames tm_inames
= RU.magic()

let remove_iname_typing
    (g:env) (#inv_p #inames #inv:term)
    (_:tot_typing g inv_p tm_vprop)
    (_:tot_typing g inames tm_inames)
    (_:tot_typing g inv (tm_inv inv_p))
: tot_typing g (remove_iname inv_p inames inv) tm_inames
= RU.magic()

let add_iname_typing
    (g:env) (#inv_p #inames #inv:term)
    (_:tot_typing g inv_p tm_vprop)
    (_:tot_typing g inames tm_inames)
    (_:tot_typing g inv (tm_inv inv_p))
: tot_typing g (add_iname inv_p inames inv) tm_inames
= RU.magic()

let tm_inames_subset_typing
    (g:env) (#i #j:term)
    (_:tot_typing g i tm_inames)
    (_:tot_typing g j tm_inames)
: tot_typing g (tm_inames_subset i j) tm_prop
= RU.magic()

let disjointness_remove_i_i (g:env) (inv_p inames inv:term)
: T.Tac (Pulse.Typing.prop_validity g 
            (inv_disjointness inv_p (remove_iname inv_p inames inv) inv))
= RU.magic()

let add_remove_inverse (g:env)
     (inv_p inames inv:term)
     (inv_p_typing:tot_typing g inv_p tm_vprop)
     (inames_typing:tot_typing g inames tm_inames)
     (inv_typing:tot_typing g inv (tm_inv inv_p))
: T.Tac 
    (prop_validity g 
        (tm_inames_subset 
            (add_iname inv_p
              (remove_iname inv_p inames inv)
              inv)
            inames))
= let typing
  : tot_typing g 
          (tm_inames_subset 
              (add_iname inv_p
                (remove_iname inv_p inames inv)
                inv)
              inames)
          tm_prop
  = let remove_typing = remove_iname_typing g inv_p_typing inames_typing inv_typing in
    let add_typing = add_iname_typing g inv_p_typing remove_typing inv_typing in
    tm_inames_subset_typing g 
      add_typing
      inames_typing
  in
  match Pulse.Checker.Pure.try_check_prop_validity g _ typing with
  | None -> 
    let open Pulse.PP in
    fail_doc g None [
      Pulse.PP.text "Failed to prove that only the following invariants are opened";
      prefix 4 1 (text "Inferred the following invariants were opened: ") 
        (pp (add_iname inv_p
              (remove_iname inv_p inames inv)
            inv)) ^/^
      prefix 4 1 (text "But expected to only open: ") (pp inames)
    ]
      
  | Some tok -> tok

module R = FStar.Reflection.V2

#push-options "--warn_error -271"
let tm_star_inj (p1 p2 q:term)
  : Lemma (requires tm_star p1 q == tm_star p2 q)
          (ensures p1 == p2) =
  let aux tv
    : Lemma (ensures R.inspect_ln (R.pack_ln tv) == tv)
            [SMTPat ()] = R.inspect_pack_inv tv in
  ()
#pop-options

#push-options "--z3rlimit_factor 8 --split_queries no"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_WithInv? t.term})
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= let Tm_WithInv {name=inv_tm; returns_inv; body} = t.term in
  let post : post_hint_t =
    match returns_inv, post_hint with
    | None, Some p -> p
    | Some (b, p), None ->
      Pulse.Checker.Base.intro_post_hint g EffectAnnotSTT (Some b.binder_ty) p
    | Some (_, p), Some q ->
      let open Pulse.PP in
      fail_doc g (Some t.range) 
        [ doc_of_string "Fatal: multiple annotated postconditions on with_invariant";
          prefix 4 1 (text "First postcondition:") (pp p);
          prefix 4 1 (text "Second postcondition:") (pp q) ]
    | _, _ ->
      fail g (Some t.range) "Fatal: no post hint on with_invariant"
  in
  match post.effect_annot with
  | EffectAnnotGhost -> 
    let open Pulse.PP in
    fail_doc g (Some t.range) 
    [ doc_of_string "Cannot open invariants in a 'ghost' context" ]

  | _ ->
    (* Checking the body seems to change its range, so store the original one
    for better errors. *)
    let body_range = body.range in
    let inv_tm_range = Pulse.RuntimeUtils.range_of_term inv_tm in

    // info_doc g (Some t.range) [
    //   let open Pulse.PP in
    //   prefix 4 1 (doc_of_string "Checker.WithInv: using post_hint =") (pp post_hint)
    // ];

    (* FIXME: should check `inv_tm` at expected type `inv ?u`, and then
    we obtain vprop from u. If so the whole block below should not be
    needed. *)
    let (| inv_tm, eff, inv_tm_ty, inv_tm_typing |) = compute_term_type g inv_tm in

    if eff <> T.E_Total then
      fail g (Some inv_tm_range) "Ghost effect on inv?";

    (* Check the term without an expected type, and check that it's Tm_Inv p *)
    let inv_p =
      match inspect_term inv_tm_ty with
      | Some (Tm_Inv p) -> p
      | Some _ -> begin
        (* FIXME: should unrefine... meh *)
        let ropt = Pulse.Syntax.Pure.is_fvar_app inv_tm_ty in
        match ropt with
        | Some (lid, _, _, Some tm) -> 
          if lid = ["Pulse"; "Lib"; "Core"; "inv" ]
          then tm
          else fail g (Some inv_tm_range)
                    (Printf.sprintf "Does not have invariant type (%s)" (P.term_to_string inv_tm_ty))
        | _ -> fail g (Some inv_tm_range)
                    (Printf.sprintf "Does not have invariant type (%s)" (P.term_to_string inv_tm_ty))
      end
      | _ -> fail g (Some inv_tm_range)
                  (Printf.sprintf "Does not have invariant type (%s)" (P.term_to_string inv_tm_ty))
    in
    
    (* FIXME: This is bogus for the Tm_FStar case!!! *)
    assume (tm_inv inv_p == inv_tm_ty);

    (* Can this come from some inversion instead? *)
    let inv_p_typing : tot_typing g inv_p tm_vprop = recheck () in

    (* pre'/post' are extended with inv_p *)
    let pre' : vprop = tm_star pre inv_p in
    let pre'_typing : tot_typing g pre' tm_vprop = recheck () in

    let post_p' : vprop = tm_star post.post inv_p in
    let elab_ret_ty = elab_term post.ret_ty in
    let x = fresh g in
    assume (fresh_wrt x g (freevars post_p'));
    // Pulse.Typing.FV.freevars_close_term post_p' x 0;
    // let post_p' = close_term post_p' x in
    let g' = (push_binding g x ppname_default post.ret_ty) in
    let r_g' = elab_env g' in
    let post_p'_typing_src
      : RT.tot_typing r_g'
                      (elab_term (open_term_nv post_p' (v_as_nv x)))
                      (elab_term tm_vprop)
      = rt_recheck g' #r_g' ()
    in
    let post_p'_typing = Pulse.Checker.Base.post_typing_as_abstraction #g #_ #post.ret_ty #post_p' (E post_p'_typing_src) in
    (* the post hint for the body, extended with inv_p, removing the name of invariant *)
  begin
    let (| opens, opens_typing |) 
      : t:term & tot_typing g t tm_inames 
      = match post.effect_annot with
        | EffectAnnotSTT ->
          (| all_inames, all_inames_typing g |)
        | EffectAnnotAtomic { opens } ->
          (| opens, (post_hint_typing g post x).effect_annot_typing |)
    in
    let opens_remove_i = remove_iname inv_p opens inv_tm in
    let effect_annot = EffectAnnotAtomic { opens=opens_remove_i } in
    let effect_annot_typing
      : effect_annot_typing g effect_annot
      = remove_iname_typing g #inv_p #opens #inv_tm inv_p_typing opens_typing inv_tm_typing
    in
    let post' : post_hint_for_env g =  { post with
      effect_annot;
      effect_annot_typing;
      g;
      ty_typing = recheck (); // Pulse.Typing.Metatheory.tot_typing_weakening _ _ _ _ post.ty_typing _;
      post = post_p';
      x;
      post_typing_src=E post_p'_typing_src;
      post_typing = post_p'_typing;
    } in
    let (| body, c_body, body_typing |) =
      let ppname = mk_ppname_no_range "with_inv_body" in
      let r = check g pre' pre'_typing (Some post') ppname body in
      apply_checker_result_k r ppname
    in
    let C_STAtomic inames obs st = c_body in
    assert (inames == opens_remove_i);
    let c_out = C_STAtomic inames obs (st_comp_remove_inv inv_p st) in
    assert (tm_star (comp_pre c_out) inv_p == pre');
    tm_star_inj (comp_pre c_out) pre inv_p;
    assert (comp_pre c_out == pre);
    assert (add_inv c_out inv_p == c_body);
    let tok = disjointness_remove_i_i g inv_p opens inv_tm in
    let tm : st_term =
      { term = Tm_WithInv {name=inv_tm; body; returns_inv = None};
        range = t.range;
        effect_tag = Sealed.seal (Some <| ctag_of_effect_annot post.effect_annot) }
    in
      
    let d = T_WithInv g inv_tm inv_p inv_p_typing inv_tm_typing body c_out body_typing tok in
    let c_out = add_iname_at_least_unobservable c_out inv_p inv_tm in
    let d : st_typing _ _ c_out = d in
    match post.effect_annot with
    | EffectAnnotAtomic _ -> 
      let C_STAtomic add_inv obs' st = c_out in
      let tok : prop_validity g (tm_inames_subset add_inv opens) =
        add_remove_inverse g inv_p opens inv_tm
            inv_p_typing
            opens_typing
            inv_tm_typing
      in
      let c_out = C_STAtomic opens obs' st in
      let d : st_typing _ _ c_out =
        T_Sub _ _ _ _ d (STS_AtomicInvs _ st add_inv opens obs' obs' tok) in
      checker_result_for_st_typing (| tm, _, d |) res_ppname
    | EffectAnnotSTT ->
      let d = T_Lift _ _ _ _ d (Lift_STAtomic_ST _ c_out) in
      checker_result_for_st_typing (| tm, _, d |) res_ppname
    end
#pop-options
