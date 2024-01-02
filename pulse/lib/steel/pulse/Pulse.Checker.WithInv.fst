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
  info_doc gg (Some (T.range_of_term e)) [
    doc_of_string "Re-checking" ^/^
      pp e ^/^
    doc_of_string "at type" ^/^
      pp ty
   ];
  match T.core_check_term g e ty T.E_Total with
  | Some tok, _ -> RT.T_Token _ _ _ ()
  | None, _ -> T.fail "Checker.WithInv: rt_recheck failed" // fixme add a range

let recheck (#g:env) (#e:term) (#ty: typ) () : T.Tac (tot_typing g e ty) =
  core_check_tot_term g e ty

let term_remove_inv (inv:vprop) (tm:term) : T.Tac term =
  match tm.t with
  | Tm_Star tm inv' ->
    if eq_tm inv inv' then tm
    else T.fail "term_remove_inv"

  | _ ->
    T.fail "term_remove_inv: not a star?"

let st_comp_remove_inv (inv:vprop) (c:st_comp) : T.Tac st_comp =
  { c with pre = term_remove_inv inv c.pre
         ; post = term_remove_inv inv c.post }

#push-options "--z3rlimit 50 --query_stats --split_queries no --max_fuel 2 --max_ifuel 1"

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_WithInv? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  let Tm_WithInv {name=inv_tm; returns_inv; body} = t.term in

  (* Checking the body seems to change its range, so store the original one
  for better errors. *)
  let body_range = body.range in

  let post : post_hint_t =
    match returns_inv, post_hint with
    | None, Some p -> p
    | Some p, None ->
      Pulse.Checker.Base.intro_post_hint g None None p
    | Some p, Some q ->
      fail g (Some t.range) "Fatal: multiple posts hint on with_invariant"
    | _, _ ->
      fail g (Some t.range) "Fatal: no post hint on with_invariant"
  in
  let post_hint = Some post in

  info_doc g (Some t.range) [
    let open Pulse.PP in
    prefix 4 1 (doc_of_string "Checker.WithInv: using post_hint =") (pp post_hint)
  ];

  (* FIXME: should check `inv_tm` at expected type `inv ?u`, and then
  we obtain vprop from u. If so the whole block below should not be
  needed. *)
  let (| inv_tm, eff, inv_tm_ty, inv_tm_typing |) = compute_term_type g inv_tm in

  if eff <> T.E_Total then
    fail g (Some inv_tm.range) "Ghost effect on inv?";

  (* Check the term without an expected type, and check that it's Tm_Inv p *)
  let inv_p =
    match inv_tm_ty.t with
    | Tm_Inv p -> p
    | Tm_FStar _ -> begin
      (* FIXME: should unrefine... meh *)
      let ropt = Pulse.Syntax.Pure.is_fvar_app inv_tm in
      match ropt with
      | Some (lid, _, _, Some tm) -> 
        if lid = ["Pulse"; "Lib"; "Core"; "inv" ]
        then tm
        else fail g (Some inv_tm.range)
                  (Printf.sprintf "Does not have invariant type (%s)" (P.term_to_string inv_tm_ty))
      | _ -> fail g (Some inv_tm.range)
                  (Printf.sprintf "Does not have invariant type (%s)" (P.term_to_string inv_tm_ty))
    end
    | _ -> fail g (Some inv_tm.range)
                (Printf.sprintf "Does not have invariant type (%s)" (P.term_to_string inv_tm_ty))
  in
  
  (* FIXME: This is bogus for the Tm_FStar case!!! *)
  assume (tm_inv inv_p == inv_tm);

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
  let post_p'_typing = Pulse.Checker.Base.post_typing_as_abstraction (E post_p'_typing_src) in
  let ctag_hint' =
    if None? post.ctag_hint || post.ctag_hint = Some STT then
      Some STT_Atomic
    else
      post.ctag_hint
  in


  (* the post hint for the body, extended with inv_p *)
  let post' : post_hint_for_env g = { post with
    g = g;
    ty_typing = recheck (); // Pulse.Typing.Metatheory.tot_typing_weakening _ _ _ _ post.ty_typing _;
    post = post_p';
    x;
    post_typing_src=E post_p'_typing_src;
    post_typing = post_p'_typing;
    ctag_hint = ctag_hint';
  }
  in

  let (| body, c_body, body_typing |) =
    let ppname = mk_ppname_no_range "with_inv_body" in
    let r = check g pre' pre'_typing (Some post') ppname body in
    apply_checker_result_k r ppname
  in
  
  (let open Pulse.PP in
   info_doc g (Some body_range) [
     text "Checked body at comp type:" ^/^ arbitrary_string (P.comp_to_string c_body)
   ]);

  let add_iname (inames:term) (i:term) : T.Tac term =
    let a = elab_term inames in
    let b = elab_term i in
    let inv_p = elab_term inv_p in
    let inv_tm = (Pulse.Reflection.Util.add_inv_tm inv_p a b) in
    assume (not_tv_unknown inv_tm);
    with_range (Tm_FStar inv_tm) (T.range_of_term a)
  in

  let c_out : comp_st =
    match c_body with
    | C_ST _
    | C_STGhost _ _  -> 
      let open Pulse.PP in
      fail_doc g (Some body_range)
        [text "This computation is not atomic nor ghost. \
               `with_invariants` blocks can only contain atomic computations."]
    | C_STAtomic inames obs st -> C_STAtomic (add_iname inames inv_tm) Observable (st_comp_remove_inv inv_p st)
  //  | C_STGhost inames st -> C_STAtomic (add_iname inames inv_tm) Observable (st_comp_remove_inv inv_p st)
  in
  assume (add_inv c_out inv_p == c_body);

  let tm : st_term =
    { term = Tm_WithInv {name=inv_tm; body; returns_inv = None};
      range = t.range;
      effect_tag = Sealed.seal (Some STT_Atomic) } // fix
  in

  let d : st_typing g tm c_out =
    T_WithInv g inv_tm inv_p inv_p_typing inv_tm_typing body c_out body_typing
  in

  info g (Some body_range)
    (Printf.sprintf "Returning comp type %s"
        (P.comp_to_string c_out));

  checker_result_for_st_typing (| tm, c_out, d |)  res_ppname
