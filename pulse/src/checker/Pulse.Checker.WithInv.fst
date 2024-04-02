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

// let term_remove_inv (inv:vprop) (tm:term) : T.Tac (tm':term { tm_star tm' inv == tm}) =
//   match inspect_term tm with
//   | Tm_Star tm inv' ->
//     if eq_tm inv inv' then tm
//     else T.fail "term_remove_inv"
//   | _ ->
//     T.fail "term_remove_inv: not a star?"

// let st_comp_remove_inv (inv:vprop) (c:st_comp) : T.Tac (s:st_comp { add_frame (C_ST s) inv == (C_ST c) }) =
//   { c with pre = term_remove_inv inv c.pre
//          ; post = term_remove_inv inv c.post }

// #push-options "--z3rlimit 50 --query_stats --split_queries no --max_fuel 2 --max_ifuel 1"  
// let check_iname_disjoint (g:env) (r:range) (inv_p inames inv:term)
// : T.Tac (Pulse.Typing.prop_validity g (inv_disjointness inv_p inames inv))
// = let goal = inv_disjointness inv_p inames inv in
//   let (| tag, goal_typing |) =
//     Pulse.Checker.Pure.core_check_term_at_type g goal tm_prop
//   in
//   if tag <> T.E_Total
//   then T.fail "Impossible: prop typing is always total"
//   else (
//     let tok = Pulse.Checker.Pure.try_check_prop_validity g goal goal_typing in
//     match tok with
//     | None ->
//       fail_doc g (Some r) [
//         Pulse.PP.text "Failed to prove that an invariant is not recursively opened:";
//         Pulse.PP.prefix 4 1 (Pulse.PP.text "The set of invariant names: ") (Pulse.PP.pp inames);
//         Pulse.PP.prefix 4 1 (Pulse.PP.text "may contain the invariant: ") (Pulse.PP.pp inv);
//       ]
//     | Some tok -> tok
//   )

let remove_iname (inames i:term)
: term
= wr 
    (Pulse.Reflection.Util.remove_inv_tm
      (elab_term inames)
      (elab_term i))
  (Pulse.RuntimeUtils.range_of_term inames)

let add_iname (inames i:term)
: term
= wr 
    (Pulse.Reflection.Util.add_inv_tm
      (elab_term inames)
      (elab_term i))
  (Pulse.RuntimeUtils.range_of_term inames)

module RU = Pulse.RuntimeUtils
let all_inames =
  wr Pulse.Syntax.Pure.tm_all_inames FStar.Range.range_0
let all_inames_typing (g:env)
: tot_typing g all_inames tm_inames
= RU.magic()

let remove_iname_typing
    (g:env) (#inames #i:term)
    (_:tot_typing g inames tm_inames)
    (_:tot_typing g i tm_iname_ref)
: tot_typing g (remove_iname inames i) tm_inames
= RU.magic()

let add_iname_typing
    (g:env) (#inames #i:term)
    (_:tot_typing g inames tm_inames)
    (_:tot_typing g i tm_iname_ref)
: tot_typing g (add_iname inames i) tm_inames
= RU.magic()

let tm_inames_subset_typing
    (g:env) (#i #j:term)
    (_:tot_typing g i tm_inames)
    (_:tot_typing g j tm_inames)
: tot_typing g (tm_inames_subset i j) tm_prop
= RU.magic()

let disjointness_remove_i_i (g:env) (inames i:term)
: T.Tac (Pulse.Typing.prop_validity g (inv_disjointness (remove_iname inames i) i))
= RU.magic()

let add_remove_inverse (g:env)
     (inames i:term)
     (inames_typing:tot_typing g inames tm_inames)
     (i_typing:tot_typing g i tm_iname_ref)
: T.Tac 
    (prop_validity g (tm_inames_subset (add_iname (remove_iname inames i) i) inames))
= let typing
  : tot_typing g 
          (tm_inames_subset 
              (add_iname
                (remove_iname inames i)
                i)
              inames)
          tm_prop
  = let remove_typing = remove_iname_typing g inames_typing i_typing in
    let add_typing = add_iname_typing g remove_typing i_typing in
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
        (pp (add_iname
              (remove_iname inames i)
            i)) ^/^
      prefix 4 1 (text "But expected to only open: ") (pp inames)
    ]
      
  | Some tok -> tok

// module R = FStar.Reflection.V2

// #push-options "--warn_error -271"
// let tm_star_inj (p1 p2 q:term)
//   : Lemma (requires tm_star p1 q == tm_star p2 q)
//           (ensures p1 == p2) =
//   let aux tv
//     : Lemma (ensures R.inspect_ln (R.pack_ln tv) == tv)
//             [SMTPat ()] = R.inspect_pack_inv tv in
//   ()
// #pop-options

//
// Find i -~- p in pre, where pre is well-typed
//
let rec find_inv (#g:env) (#pre:term) (pre_typing:tot_typing g pre tm_vprop) (i:term)
  : T.Tac (option (p:term &
                   frame:term &
                   tot_typing g (tm_inv i p) tm_vprop &
                   tot_typing g frame tm_vprop &
                   vprop_equiv g (tm_star (tm_inv i p) frame) pre)) =

  match inspect_term pre with
  | Tm_Inv i' p ->
    if eq_tm i i'
    then let frame = tm_emp in
         let tm_inv_typing = magic () in
         let frame_typing = magic () in
         let d_eq = magic () in
         Some (| p, frame, tm_inv_typing, frame_typing, d_eq |)
    else None
  
  | Tm_Star l r -> begin
    match find_inv #g #l (magic ()) i with
    | Some res ->
      let (| p, frame, _, _, _ |) = res in
     Some (| p, tm_star frame r, magic (), magic (), magic () |)
    | None ->
      match find_inv #g #r (magic ()) i with
      | Some res ->
        let (| p, frame, _, _, _ |) = res in
        Some (| p, tm_star l frame, magic (), magic (), magic () |)
      | _ -> None
    end
    
  | _ -> None

let find_inv_post (#g:env) (x:var { lookup g x == None})
  (u:universe)
  (ret_ty:term)
  (post:term)
  (ret_ty_typing:universe_of g ret_ty u)
  (post_typing:tot_typing (push_binding g x ppname_default ret_ty) (open_term post x) tm_vprop)
  (i:term)

  : T.Tac (option (p:term &
                   frame:term &
                   tot_typing g (tm_inv i p) tm_vprop &
                   tot_typing (push_binding g x ppname_default ret_ty) (open_term frame x) tm_vprop &
                   vprop_equiv (push_binding g x ppname_default ret_ty)
                               (tm_star (tm_inv i p) (open_term frame x))
                               (open_term post x))) =
  
  let post_opened = open_term_nv post (ppname_default, x) in
  let res = find_inv #_ #post_opened post_typing i in
  match res with
  | None -> None
  | Some (| p, frame, inv_typing, frame_typing, d_eq |) ->
    let frame_typing : tot_typing _ frame tm_vprop = frame_typing in
    assume (open_term (close_term frame x) x == frame);
    let tm_inv_typing : tot_typing g (tm_inv i p) tm_vprop = recheck () in
    Some (| p, close_term frame x, tm_inv_typing, frame_typing, d_eq |)

// (#pre:term) (pre_typing:tot_typing g pre tm_vprop) (i:term)
//   : option (p:term &
//             frame:term &
//             tot_typing g (tm_inv i p) tm_vprop &
//             tot_typing g frame tm_vprop &
//             vprop_equiv g pre (tm_star (tm_inv i p) frame)) =

//   match inspect_term pre with
//   | Tm_Inv i' p ->
//     if eq_tm i i'
//     then let frame = tm_emp in
//          let tm_inv_typing = magic () in
//          let frame_typing = magic () in
//          let d_eq = magic () in
//          Some (| p, frame, tm_inv_typing, frame_typing, d_eq |)
//     else None
  
//   | Tm_Star l r -> begin
//     match find_inv_pre #g #l (magic ()) i with
//     | Some res ->
//       let (| p, frame, _, _, _ |) = res in
//      Some (| p, tm_star frame r, magic (), magic (), magic () |)
//     | None ->
//       match find_inv_pre #g #l (magic ()) i with
//       | Some res ->
//         let (| p, frame, _, _, _ |) = res in
//         Some (| p, tm_star l frame, magic (), magic (), magic () |)
//       | _ -> None
//     end
    
//   | _ -> None

let atomic_or_ghost_with_inames_and_pre_post
  (c:comp { C_STAtomic? c \/ C_STGhost? c})
  (inames pre post:term) =
  match c with
  | C_STAtomic _ obs s ->
    C_STAtomic inames obs { s with pre; post }
  | C_STGhost _ s ->
    C_STGhost inames { s with pre; post }

#restart-solver
#push-options "--z3rlimit_factor 15 --split_queries no"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term{Tm_WithInv? t.term})
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= let Tm_WithInv {name=i; returns_inv; body} = t.term in
  let (| i, _ |) = check_tot_term g i tm_iname_ref in
  
  let post_hint : post_hint_t =
    match returns_inv, post_hint with
    | None, Some p -> p
    | Some (b, p), None ->
      Pulse.Checker.Base.intro_post_hint g (EffectAnnotAtomic { opens = Pulse.Reflection.Util.add_inv_tm tm_emp_inames i }) (Some b.binder_ty) p
    | Some (_, p), Some q ->
      let open Pulse.PP in
      fail_doc g (Some t.range) 
        [ doc_of_string "Fatal: multiple annotated postconditions on with_invariant";
          prefix 4 1 (text "First postcondition:") (pp p);
          prefix 4 1 (text "Second postcondition:") (pp q) ]
    | _, _ ->
      fail g (Some t.range) "Fatal: no post hint on with_invariant"
  in
  match post_hint.effect_annot with
  // | EffectAnnotGhost _ -> 
  //   let open Pulse.PP in
  //   fail_doc g (Some t.range) 
  //   [ doc_of_string "Cannot open invariants in a 'ghost' context" ]

  | _ ->
    (* Checking the body seems to change its range, so store the original one
    for better errors. *)
    let body_range = body.range in
    let i_range = Pulse.RuntimeUtils.range_of_term i in

    let (| i, _ |) = check_tot_term g i tm_iname_ref in

    let res = find_inv pre_typing i in
    if None? res then fail g (Some i_range) "Cannot find inv in the context";
    
    let Some (| p, pre_frame, inv_typing, pre_frame_typing, d_pre_frame_eq |) = res in

    let pre_body : vprop = tm_star p pre_frame in
    //
    // we know tm_inv i p is well-typed,
    // so p is well-typed
    // and frame is well-typed
    // therefore tm_star is well-typed
    //
    let pre_body_typing : tot_typing g pre_body tm_vprop = magic () in

    let x = fresh g in
    assume (fresh_wrt x g (freevars post_hint.post));
    let g' = (push_binding g x ppname_default post_hint.ret_ty) in
    let post_hint_ret_ty_typing
      : universe_of g post_hint.ret_ty post_hint.u = recheck () in
    let post_hint_post_typing
      : tot_typing g'
                   (open_term_nv post_hint.post (ppname_default, x))
                   tm_vprop
      = recheck ()
    in
    
    let res = find_inv_post #g
      x
      post_hint.u
      post_hint.ret_ty
      post_hint.post
      post_hint_ret_ty_typing
      post_hint_post_typing
      i in

    if None? res then fail g (Some i_range) "Cannot find inv in the postcondition";

    let Some (| p', post_frame, _, post_frame_typing, d_post_frame_equiv |) = res in
    assume (p' == p);

    let post_body = tm_star p post_frame in
    
    let (| opens, opens_typing |) 
      : t:term & tot_typing g t tm_inames 
      = match post_hint.effect_annot with
        | EffectAnnotSTT ->
          (| all_inames, all_inames_typing g |)
        | EffectAnnotGhost { opens }
        | EffectAnnotAtomic { opens } ->
          (| opens, (post_hint_typing g post_hint x).effect_annot_typing |)
    in
    let opens_remove_i = remove_iname opens i in
    let effect_annot =
      match post_hint.effect_annot with
      | EffectAnnotSTT
      | EffectAnnotAtomic _ ->
        EffectAnnotAtomic { opens=opens_remove_i }
      | EffectAnnotGhost _ ->
        EffectAnnotGhost { opens=opens_remove_i } in
    let effect_annot_typing
      : effect_annot_typing g effect_annot
      = remove_iname_typing g #opens #i opens_typing (magic ())  // from inversion of tm_inv_typing
    in

    assume (fresh_wrt x g (freevars post_body));
    let post_hint_body : post_hint_for_env g =  { post_hint with
      effect_annot;
      effect_annot_typing;
      g;
      ty_typing = post_hint_ret_ty_typing;
      post = post_body;
      x;
      post_typing_src=magic ();
      post_typing=magic ();
    } in

    let (| body, c_body, body_typing |) =
      let ppname = mk_ppname_no_range "with_inv_body" in
      let r = check g pre_body pre_body_typing (Some post_hint_body) ppname body in
      apply_checker_result_k r ppname
    in

    assert (comp_inames c_body == opens_remove_i);
    assert (comp_pre c_body == tm_star p pre_frame);
    assert (comp_post c_body == tm_star p post_frame);

    let c_out = atomic_or_ghost_with_inames_and_pre_post c_body
      (Pulse.Reflection.Util.add_inv_tm (comp_inames c_body) i)
      pre
      post_hint.post in 

    let tok = disjointness_remove_i_i g opens i in

    let tm = wtag (Some (ctag_of_comp_st c_out)) (Tm_WithInv {name=i;body;returns_inv=None}) in
    let d : st_typing _ tm c_out =
      let c = atomic_or_ghost_with_inames_and_pre_post
        c_body
        (comp_inames c_body)
        pre_frame
        post_frame in
      let c_out_eq = atomic_or_ghost_with_inames_and_pre_post
        c_body
        (Pulse.Reflection.Util.add_inv_tm (comp_inames c_body) i)
        (tm_star (tm_inv i p) pre_frame)
        (tm_star (tm_inv i p) post_frame) in
      
      assert (add_frame_l c p == c_body);
      assert (comp_with_inv c i p == c_out_eq);
      let d : st_typing _ _ c_out_eq =
        T_WithInv _ i p _ c (magic ()) (magic ()) body_typing tok in
      let d_pre_eq : vprop_equiv g (comp_pre c_out_eq) (comp_pre c_out) = d_pre_frame_eq in
      let d_post_eq : vprop_equiv (push_binding g x ppname_default post_hint.ret_ty)
                                  (tm_star (tm_inv i p) (open_term post_frame x))
                                  (open_term post_hint.post x) = d_post_frame_equiv in
      assume (open_term (tm_inv i p) x == tm_inv i p);
      assert (comp_post c_out_eq == tm_star (tm_inv i p) post_frame);
      assume (open_term (comp_post c_out_eq) x ==
              tm_star (tm_inv i p) (open_term post_frame x));
      let d_post_eq : vprop_equiv (push_binding g x ppname_default post_hint.ret_ty)
                                  (open_term (comp_post c_out_eq) x)
                                  (open_term (comp_post c_out) x) = d_post_eq in
      assert (comp_res c_out_eq == comp_res c_out);
      assume (~ (x `Set.mem` freevars (comp_post c_out_eq)));
      assume (~ (x `Set.mem` freevars (comp_post c_out)));
      let d_st_equiv : st_equiv _ c_out_eq c_out =
        ST_VPropEquiv _ c_out_eq c_out x (magic ())
                                         (magic ())
                                         (magic ())
                                         (RT.Rel_refl _ _ RT.R_Eq)
                                         d_pre_eq
                                         d_post_eq in
      let d : st_typing _ _ c_out =
        T_Equiv _ _ _ _ d d_st_equiv in
      d
    in
    match post_hint.effect_annot with
    | EffectAnnotGhost _
    | EffectAnnotAtomic _ ->
      let tok : prop_validity g (tm_inames_subset (comp_inames c_out) opens) =
        add_remove_inverse g opens i opens_typing (magic ())
      in
      let (| c_out_opens, d_sub_c |) : (c_out_opens:comp & st_sub _ c_out c_out_opens) =
        match c_out with
        | C_STAtomic add_inv obs st ->
          (| C_STAtomic opens obs st,
             STS_AtomicInvs _ st add_inv opens obs obs tok |)
        | C_STGhost add_inv st ->
          (| C_STGhost opens st,
            STS_GhostInvs _ st add_inv opens tok |) in
      let d : st_typing _ _ c_out_opens =
        T_Sub _ _ _ _ d d_sub_c in
      checker_result_for_st_typing (| _, _, d |) res_ppname

    | EffectAnnotSTT ->
      let d = T_Lift _ _ _ _ d (Lift_STAtomic_ST _ c_out) in
      checker_result_for_st_typing (| _, _, d |) res_ppname
#pop-options
