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

module Pulse.Checker.If

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module J = Pulse.JoinComp
module RU = Pulse.RuntimeUtils
module R = FStar.Reflection.V2
#set-options "--z3rlimit 40"


let retype_checker_result_post_hint #g #pre (ph:post_hint_for_env g)
    (ph':post_hint_opt g {PostHint? ph' ==> PostHint?.v ph' == ph})
    (r:checker_result_t g pre (PostHint ph))
: T.Tac (checker_result_t g pre ph')
= let (| x, g1, t, ctxt', k |) = r in
  (| x, g1, t, ctxt', k |)

let retype_checker_result (#g:env) (#ctxt:slprop) (#ph:post_hint_opt g) (ph':post_hint_opt g { not (PostHint? ph')})
  (r:checker_result_t g ctxt ph)
: checker_result_t g ctxt ph'
= let (| x, g1, t, ctxt, k |) = r in
  (| x, g1, t, ctxt, k |)

let set_effect_annot (#g:env) (ph:post_hint_for_env g) (ea:effect_annot)
: (ph':post_hint_for_env g { ph'.ret_ty == ph.ret_ty /\ ph'.post == ph.post /\
                             ph'.u == ph.u /\ ph'.effect_annot == ea })
= { ph with effect_annot = ea }

(* The effect of a conditional whose postcondition is inferred, from the
   natural effects of its branches, and each branch lifted to it. This follows
   the lifts that Pulse.Typing.Combinators.mk_bind applies when composing two
   computations without a hint: divergence wins over stt, which wins over
   atomic and ghost; ghost and atomic branches keep their effect, over the
   join of their invariant names. A ghost branch is only lifted to a
   non-ghost effect if its result type is non-informative
   ([lift_ghost_atomic]). *)
let same_st (c c':comp_st) : prop =
  comp_pre c' == comp_pre c /\ comp_res c' == comp_res c /\
  comp_u c' == comp_u c /\ comp_post c' == comp_post c

let lift_ghost (g:env) (e:st_term) (c:comp_st) : T.Tac unit =
  if C_STGhost? c then lift_ghost_atomic g e c

let with_opens (g:env) (c:comp_st { C_STGhost? c \/ C_STAtomic? c }) (opens:term)
: T.Tac (c':comp_st { same_st c c' /\
                      (C_STGhost? c ==> C_STGhost? c') /\
                      (C_STAtomic? c ==> C_STAtomic? c') /\
                      comp_inames c' == opens })
= if not (eq_tm (comp_inames c) opens) then
    ignore (check_prop_validity g (tm_inames_subset (comp_inames c) opens));
  match c with
  | C_STGhost _ sc -> C_STGhost opens sc
  | C_STAtomic _ obs sc -> C_STAtomic opens obs sc

let join_branch_effects (g:env) (e1 e2:st_term) (c1 c2:comp_st)
: T.Tac (ea:effect_annot &
         c1':comp_st { same_st c1 c1' /\ effect_annot_matches c1' ea } &
         c2':comp_st { same_st c2 c2' /\ effect_annot_matches c2' ea })
= match c1, c2 with
  | C_STDiv _, _ | _, C_STDiv _ ->
    lift_ghost g e1 c1; lift_ghost g e2 c2;
    (| EffectAnnotSTTDiv, C_STDiv (st_comp_of_comp c1), C_STDiv (st_comp_of_comp c2) |)
  | C_ST _, _ | _, C_ST _ ->
    lift_ghost g e1 c1; lift_ghost g e2 c2;
    (| EffectAnnotSTT, C_ST (st_comp_of_comp c1), C_ST (st_comp_of_comp c2) |)
  | _ ->
    let opens = tm_join_inames (comp_inames c1) (comp_inames c2) in
    let c1 = with_opens g c1 opens in
    let c2 = with_opens g c2 opens in
    match c1, c2 with
    | C_STGhost _ _, C_STGhost _ _ ->
      (| EffectAnnotGhost { opens }, c1, c2 |)
    | C_STAtomic _ _ _, C_STAtomic _ _ _ ->
      (| EffectAnnotAtomic { opens }, c1, c2 |)
    | _ ->
      (* One ghost and one atomic branch. Both have the same result type. A
         ghost branch with an informative result can only be joined with a
         neutral atomic one, as ghost. *)
      let neutral (c:comp_st) : bool =
        match c with
        | C_STAtomic _ obs _ -> Neutral? obs
        | _ -> true
      in
      if None? (try_get_non_informative_witness g (comp_u c1) (comp_res c1))
         && neutral c1 && neutral c2
      then
        let c1 : comp_st = C_STGhost opens (st_comp_of_comp c1) in
        let c2 : comp_st = C_STGhost opens (st_comp_of_comp c2) in
        (| EffectAnnotGhost { opens }, c1, c2 |)
      else (
        lift_ghost g e1 c1; lift_ghost g e2 c2;
        let as_atomic (c:comp_st { C_STGhost? c \/ C_STAtomic? c })
        : c':comp_st { same_st c c' /\ C_STAtomic? c' /\ comp_inames c' == comp_inames c } =
          match c with
          | C_STGhost i sc -> C_STAtomic i Neutral sc
          | C_STAtomic _ _ _ -> c
        in
        (| EffectAnnotAtomic { opens }, as_atomic c1, as_atomic c2 |)
      )

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 2"
#restart-solver
(* The trust boundary for an inferred postcondition.

   Pulse.JoinComp only proposes candidates, as plain terms; nothing it computes
   is trusted. A candidate becomes the postcondition of the conditional only
   after
   (1) [post_hint_of_candidate] core-checks it as an slprop over the result in
       [g], the context outside the conditional, so that it cannot mention the
       branch hypothesis or any variable a branch bound; and
   (2) both branches are proved against it ([prove_post_hint], which also
       checks the result type) and elaborated ([extract_nat]), since the
       prover leaves some of its checks to elaboration.
   A user-written `ensures` on the `if` goes through the same checks. So a
   wrong candidate is rejected, or skipped for the next one: an inference bug
   can at worst make a program be rejected, or get a weaker postcondition than
   it could have.
   A candidate only fixes the result type and the postcondition. Its effect
   annotation is a placeholder that nothing reads: [prove_post_hint] ignores
   it, and [extract_nat] elaborates each branch at its own effect. The effect
   of the conditional is computed from the elaborated branches by
   [join_branch_effects]. *)
let post_hint_of_candidate (g:env) (ret_ty:term) (post:term)
: T.Tac (ph:post_hint_for_env g { ph.ret_ty == ret_ty /\ ph.effect_annot == EffectAnnotSTT })
= let u = check_universe g ret_ty in
  let x = fresh g in
  let g' = push_binding g x ppname_default ret_ty in
  check_slprop_with_core g' (open_term_nv post (ppname_default, x));
  { g; effect_annot = EffectAnnotSTT; ret_ty; u; post }

(* Does a joined postcondition still keep something under the branch
   condition? `Pulse.JoinComp.join_post_candidate` with no pick leaves what the
   branches do not agree on as `match b with true -> .. | false -> ..`, which
   nothing later can take apart unless `b` is a variable that a later test
   rewrites. *)
let rec post_keeps_conditional (p:slprop) : T.Tac bool =
  match inspect_term p with
  | Tm_Star l r -> if post_keeps_conditional l then true else post_keeps_conditional r
  | Tm_ExistsSL _ _ body -> post_keeps_conditional body
  | Tm_WithPure _ _ body -> post_keeps_conditional body
  | Tm_FStar t -> R.Tv_Match? (R.inspect_ln t)
  | _ -> false

let check
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g)
  (annot_post:option (post_hint_for_env g))
  (res_ppname:ppname)
  (b:st_term)
  (e1 e2:st_term)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  
  let g = Pulse.Typing.Env.push_context g "check_if" e1.range in

  let b : term =
    match b.term with
    | Tm_Return { term=bt } -> check_tot_term g bt tm_bool
    | _ -> fail g (Some b.range) "check_if: expected a pure condition (Tm_Return); stateful conditions should have been elaborated away"
  in

  let hyp = fresh g in

  //
  // The hint the branches are checked against. When the surrounding context
  // fixes the postcondition (and effect), use it directly. Otherwise, if the
  // conditional carries an `ensures` annotation, check the branches against that
  // postcondition slprop but leave the effect to be inferred from the branches
  // (issue #4368); with no annotation, infer the postcondition too (issue #4366).
  // Note that `annot_post` carries the effect admitted by the enclosing
  // computation (see Pulse.Checker.Base.ambient_effect_annot), which is what a
  // branch that needs the hint itself is checked against (issue #4418); the
  // effect of the conditional is still read back from the branches below.
  //
  let branch_hint : post_hint_opt g =
    match post_hint with
    | PostHint _ -> post_hint
    | _ -> (match annot_post with | Some ap -> PostHint ap | None -> NoHint)
  in

  let g_with_eq = g_with_eq g hyp b in  
  let use_rewrites_to = Some? (term_as_subst_var b) in
  let check_branch (eq_v:term) (br:st_term) (is_then:bool)
  : T.Tac (checker_result_t (g_with_eq eq_v) pre branch_hint)
  =
    let branch_range = br.range in
    let branch_g = g_with_eq eq_v in
    let br =
      if use_rewrites_to
      then br
      else
        let t =
          mk_term (Tm_ProofHintWithBinders {
            binders = [];
            hint_type = RENAME {
              pairs = [(b, eq_v)];
              goal = None;
              tac_opt = Some Pulse.Reflection.Util.match_rename_tac_tm;
              elaborated = true
            };
            t = br;
          }) br.range in
        { t with effect_tag = br.effect_tag } in
    let ppname = mk_ppname_no_range "_if_br" in
    RU.with_error_bound branch_range (fun () ->
      check branch_g pre branch_hint ppname br)
  in

  let infer_post_branch (#eq_v:term) (r: checker_result_t (g_with_eq eq_v) pre NoHint) :
    T.Tac (p:post_hint_for_env g {p.g == g /\ p.effect_annot==EffectAnnotSTT}) =
    let (| x, g', (u, t), post, k |) = r in
    J.infer_post' g g' u t x post
  in

  (* Elaborate a branch and read back its natural effect. The trailing return
     is elaborated against a neutral effect (atomic over no invariants), so
     that it does not lift the branch: the postcondition proved of the branch
     fixes its state, not its effect. *)
  let extract_nat #g #pre (#ph:post_hint_for_env g) (r:checker_result_t g pre (PostHint ph))
  : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
           c:comp_st { comp_pre c == pre /\ comp_res c == ph.ret_ty /\
                       comp_u c == ph.u /\ comp_post c == ph.post })
  = let neutral = { ph with effect_annot = EffectAnnotAtomicOrGhost { opens = tm_emp_inames } } in
    let r = retype_checker_result_effect ph neutral r in
    let (| br, c |) =
      let ppname = mk_ppname_no_range "_if_br" in
      apply_checker_result_k_nohint r ppname
    in
    assume not (hyp `Set.mem` freevars_st br);
    (| br, c |)
  in

  let then_ = check_branch tm_true e1 true in
  let else_ = check_branch tm_false e2 false in
  let joinable : (
    ph:post_hint_for_env g &
    checker_result_t (g_with_eq tm_true) pre (PostHint ph) &
    checker_result_t (g_with_eq tm_false) pre (PostHint ph) &
    option (e1:st_term { ~(hyp `Set.mem` freevars_st e1) } &
            c1:comp_st { comp_pre c1 == pre /\ comp_res c1 == ph.ret_ty /\
                         comp_u c1 == ph.u /\ comp_post c1 == ph.post } &
            e2:st_term { ~(hyp `Set.mem` freevars_st e2) } &
            c2:comp_st { comp_pre c2 == pre /\ comp_res c2 == ph.ret_ty /\
                         comp_u c2 == ph.u /\ comp_post c2 == ph.post })
  ) = match branch_hint with
      | PostHint ph ->
        (| ph, then_, else_, None |)
      | _ ->
        let then_ : checker_result_t _ _ NoHint = retype_checker_result _ then_ in
        let else_ : checker_result_t _ _ NoHint = retype_checker_result _ else_ in
        let post_then = infer_post_branch then_ in
        let post_else = infer_post_branch else_ in
        let ret_ty = post_then.ret_ty in
        if not (T.term_eq (RU.deep_compress_safe ret_ty) (RU.deep_compress_safe post_else.ret_ty))
        then
          Pulse.Typing.Env.fail_doc g (Some (T.range_of_term ret_ty))
            Pulse.PP.(
              [text "The branches of a conditional must return the same type";
               text (Printf.sprintf "The types %s and %s are not equal"
                       (T.term_to_string ret_ty) (T.term_to_string post_else.ret_ty))]);
        (* Untrusted: see [post_hint_of_candidate]. *)
        let candidate (pick:option bool) (linked:bool) : T.Tac term =
          J.join_post_candidate pick linked #g #hyp #b post_then post_else in
        let post = post_hint_of_candidate g ret_ty (candidate None false) in
        let prove_both (post:post_hint_for_env g) ()
          : T.Tac (ph:post_hint_for_env g &
                   checker_result_t (g_with_eq tm_true) pre (PostHint ph) &
                   checker_result_t (g_with_eq tm_false) pre (PostHint ph)) =
          let then_ = Pulse.Checker.Prover.prove_post_hint then_ (PostHint post) e1.range in
          let else_ = Pulse.Checker.Prover.prove_post_hint else_ (PostHint post) e2.range in
          (| post, then_, else_ |)
        in
        (* A candidate is only accepted once both branches have been
           elaborated against it: the prover leaves some of its checks (e.g.
           that two cells it matched hold the same value) to elaboration. *)
        let prove_and_extract (post:post_hint_for_env g) ()
          : T.Tac (ph:post_hint_for_env g &
                   checker_result_t (g_with_eq tm_true) pre (PostHint ph) &
                   checker_result_t (g_with_eq tm_false) pre (PostHint ph) &
                   option (e1:st_term { ~(hyp `Set.mem` freevars_st e1) } &
                           c1:comp_st { comp_pre c1 == pre /\ comp_res c1 == ph.ret_ty /\
                                        comp_u c1 == ph.u /\ comp_post c1 == ph.post } &
                           e2:st_term { ~(hyp `Set.mem` freevars_st e2) } &
                           c2:comp_st { comp_pre c2 == pre /\ comp_res c2 == ph.ret_ty /\
                                        comp_u c2 == ph.u /\ comp_post c2 == ph.post })) =
          let (| post, then_, else_ |) = prove_both post () in
          let (| e1, c1 |) = extract_nat then_ in
          let (| e2, c2 |) = extract_nat else_ in
          (| post, then_, else_, Some (| e1, c1, e2, c2 |) |)
        in
        (* When the join keeps part of the state under the condition, try
           taking that part from one branch. The prover may reach it from the
           other branch by the folds and unfolds it applies on its own
           (`pulse_intro`), e.g. one branch leaves a struct unfolded and the
           other calls a function that returns it folded.
           Only the leftover part is taken from the branch. What the branches
           agree on is joined as usual. Taking the picked branch's whole
           postcondition would also fix the values of cells the other
           branch did not write: e.g. a cell written to a constant in one
           branch and untouched in the other, which the prover can only
           match by an SMT equality that does not hold.
           First try without generalizing a cell whose value names a
           witness the branch's other conjuncts also name: generalizing it
           cuts the two apart (a pointer to an iterator against the
           iterator's predicate over the same value). That join can still be
           proved of both branches, even when it keeps no conditional, but
           leaves a postcondition the code after the join cannot use. Such a
           cell is left to the picked branch as well. Only if that fails,
           generalize it.
           Each candidate is proved of, and elaborated in, both branches
           before it is used, so this only ever picks among sound options.
           If none works, keep the join. *)
        (* Only inspected, to decide which candidates to try. *)
        let linked_post = candidate None true in
        let with_leftover_of (linked then_:bool) () =
          prove_and_extract (post_hint_of_candidate g ret_ty (candidate (Some then_) linked)) ()
        in
        let rec first (cs:list (bool & bool))
          : T.Tac (ph:post_hint_for_env g &
                   checker_result_t (g_with_eq tm_true) pre (PostHint ph) &
                   checker_result_t (g_with_eq tm_false) pre (PostHint ph) &
                   option (e1:st_term { ~(hyp `Set.mem` freevars_st e1) } &
                           c1:comp_st { comp_pre c1 == pre /\ comp_res c1 == ph.ret_ty /\
                                        comp_u c1 == ph.u /\ comp_post c1 == ph.post } &
                           e2:st_term { ~(hyp `Set.mem` freevars_st e2) } &
                           c2:comp_st { comp_pre c2 == pre /\ comp_res c2 == ph.ret_ty /\
                                        comp_u c2 == ph.u /\ comp_post c2 == ph.post })) =
          match cs with
          | (linked, then_)::cs ->
            (match RU.try_quietly (with_leftover_of linked then_) with
             | Some r -> r
             | None -> first cs)
          | _ ->
            let (| post, then_, else_ |) = prove_both post () in
            (| post, then_, else_, None |)
        in
        let linked_cs =
          if post_keeps_conditional linked_post then [(true, false); (true, true)] else [] in
        let unlinked_cs =
          if post_keeps_conditional post.post then [(false, false); (false, true)] else [] in
        first (linked_cs @ unlinked_cs)
  in
  let (| post_hint', then_, else_, extracted |) = joinable in

  let assemble (post_final:post_hint_for_env g {
                  PostHint? post_hint ==> PostHint?.v post_hint == post_final })
               (e1:st_term { ~(hyp `Set.mem` freevars_st e1) })
               (c1:comp_st { comp_pre c1 == pre /\ comp_post_matches_hint c1 (PostHint post_final) })
               (e2:st_term { ~(hyp `Set.mem` freevars_st e2) })
               (c2:comp_st { comp_pre c2 == pre /\ comp_post_matches_hint c2 (PostHint post_final) })
  : T.Tac (checker_result_t g pre post_hint)
  = let c =
      J.join_comps (g_with_eq tm_true) e1 c1 (g_with_eq tm_false) e2 c2 post_final in
    let c_typing = comp_typing_from_post_hint c post_final in
    let b_st = mk_term (Tm_Return { expected_type = tm_bool; insert_eq = false; term = b }) e1.range in
    let if_st = wrst c (Tm_If { b=b_st; then_=e1; else_=e2; pre=None; post=None }) in
    let d : st_typing_in_ctxt g pre (PostHint post_final) =
      (| if_st, c |) in
    let res : checker_result_t g pre (PostHint post_final) = checker_result_for_st_typing d res_ppname in
    retype_checker_result_post_hint post_final post_hint res
  in

  match post_hint with
  | PostHint _ ->
    //
    // The postcondition (hence the effect) was supplied by the user: check each
    // branch against it directly and compose.
    //
    let extract #g #pre (#ph:post_hint_for_env g) (r:checker_result_t g pre (PostHint ph)) (is_then:bool)
    : T.Tac (br:st_term { ~(hyp `Set.mem` freevars_st br) } &
             c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (PostHint ph)})
    = let (| br, c |) =
        let ppname = mk_ppname_no_range "_if_br" in
        apply_checker_result_k r ppname
      in
      assume not (hyp `Set.mem` freevars_st br);
      (| br, c |)
    in
    let (| e1, c1 |) = extract then_ true in
    let (| e2, c2 |) = extract else_ false in
    assemble post_hint' e1 c1 e2 c2

  | _ ->
    //
    // The postcondition was inferred, or annotated without fixing the effect.
    // Read back the natural effect of each branch, so that e.g. a divergent
    // branch makes the whole conditional divergent (issue #4366), and a
    // conditional whose branches are ghost stays ghost.
    //
    let (| e1, c1, e2, c2 |) =
      match extracted with
      | Some r -> r
      | None ->
        let (| e1, c1 |) = extract_nat then_ in
        let (| e2, c2 |) = extract_nat else_ in
        (| e1, c1, e2, c2 |)
    in
    //
    // Join the natural effects of the branches (see [join_branch_effects]).
    //
    let (| joined_eff, c1, c2 |) = join_branch_effects g e1 e2 c1 c2 in
    let post_final = set_effect_annot post_hint' joined_eff in
    assemble post_final e1 c1 e2 c2
  #pop-options
