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

module Pulse.Checker.Abs
#set-options "--z3refresh" //stabilize some flaky proofs
module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base
open FStar.List.Tot

module RT = FStar.Reflection.Typing
module P = Pulse.Syntax.Printer
module PSB = Pulse.Syntax.Builder
module FV = Pulse.Typing.FV
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
module Env = Pulse.Typing.Env
module U = Pulse.Syntax.Pure
module PCP = Pulse.Checker.Pure
open Pulse.Checker.ImpureSpec
open Pulse.Show

let rec mk_abs (g:env) (qbs:list (option qualifier & binder & bv) { Cons? qbs }) (body:st_term) (comp:comp)
: T.Tac (t:st_term {Tm_Abs? t.term})
=
  let with_range (s:st_term') (r:range) : st_term =
    { term = s;
      range = r;
      effect_tag = default_effect_hint;
      source=Sealed.seal false;
      seq_lhs=Sealed.seal false;
    }
  in
  match qbs with
  | [(q, last, last_bv)] -> 
    let body = close_st_term body last_bv.bv_index in
    let comp = close_comp comp last_bv.bv_index in
    let ascription = { annotated = Some comp; elaborated = None } in
    with_range (Tm_Abs { b = last; q; ascription; body }) body.range
  | (q, b, bv)::qbs ->
    let body = mk_abs g qbs body comp in
    let body = close_st_term body bv.bv_index in
    with_range (Tm_Abs { b; q; ascription=empty_ascription; body }) body.range

let debug_abs g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.abs"
  then T.print (s ())

(* Infers the the type of the binders from the specification alone, not the body *)

let rec exists_as_binders (g: env) (t: slprop) : T.Tac (env & list (var & binder & option qualifier) & slprop) =
  match inspect_term t with
  | Tm_Star t s ->
    let g, bs1, t = exists_as_binders g t in
    let g, bs2, s = exists_as_binders g s in
    g, bs1 @ bs2, tm_star t s
  | Tm_ExistsSL u b t ->
    let x = fresh g in
    let px = b.binder_ppname, x in
    let x_ty = mk_erased u b.binder_ty in
    let g = push_binding g x (fst px) x_ty in
    let t = open_term' t (mk_reveal u b.binder_ty (term_of_nvar px)) 0 in
    let g, bs, t = exists_as_binders g t in
    g, (x, { b with binder_ty = x_ty }, Some Implicit) :: bs, t
  | Tm_WithPure p n t ->
    let x = fresh g in
    let px = n, x in
    let x_ty = mk_squash u0 p in
    let g = push_binding g x (fst px) x_ty in
    let t = open_term_nv t px in
    let g, bs, t = exists_as_binders g t in
    g, (x, { binder_ty = x_ty; binder_ppname = n; binder_attrs = T.seal [] }, Some Implicit) :: bs, t
  | _ ->
    g, [], t

let tc_term_phase1_with_type_twice g t ty =
  // If we call phase1 TC only once, then the universe instantiation in
  // coercion-inserted reveal calls remains a uvar.
  let ty, eff = tc_term_phase1_with_type g t ty in
  let ty, eff = tc_term_phase1_with_type g t ty in
  ty, eff

let preproc_ascription (g: env) (c: comp) : T.Tac (env & list (var & binder & option qualifier) & comp) =
  let preproc_inames is : T.Tac R.term =
    let is, _ = tc_term_phase1_with_type g is tm_inames in
    let is = T.norm_well_typed_term (elab_env g)
      [primops; iota; zeta; delta_attr ["Pulse.Lib.Core.unfold_check_opens"]]
      is in
    is in
  let preproc_stcomp (c: st_comp) : T.Tac (env & list (var & binder & option qualifier) & st_comp) = 
    let {u;res;pre;post} = c in
    let res, u = tc_type_phase1 g res in
    let g, bs, pre =
      let pre = purify_spec g { ctxt_now = tm_emp; ctxt_old = None } pre in
      exists_as_binders g pre in
    let x = fresh g in
    let post =
      let g' = push_binding g x ppname_default res in
      let post = open_term_nv post (v_as_nv x) in
        purify_spec g'
          { ctxt_old = Some pre; ctxt_now = tm_emp }
          post in
    let post = close_term post x in
    let res, u = tc_type_phase1 g res in // FIXME: unification fails to fill in u....
    g, bs, ({u;res;pre;post} <: st_comp) in
  match c with
  | C_Tot t -> g, [], C_Tot (fst (tc_type_phase1 g t))
  | C_ST c ->
    let g, bs, c = preproc_stcomp c in
    g, bs, C_ST c
  | C_STGhost is c ->
    let g, bs, c = preproc_stcomp c in
    g, bs, C_STGhost (preproc_inames is) c
  | C_STAtomic is obs c ->
    let g, bs, c = preproc_stcomp c in
    g, bs, C_STAtomic (preproc_inames is) obs c

let rec tm_abs_binders (bs: list (var & binder & option qualifier)) (t: st_term) : t':st_term { Cons? bs ==> Tm_Abs? t'.term } =
  match bs with
  | [] -> t
  | (x, b, q) :: bs ->
    let t = tm_abs_binders bs t in
    let t = close_st_term t x in
    PSB.with_range (Tm_Abs { b; q; ascription = empty_ascription; body = t }) t.range

let rec tm_arrow_binders (bs: list (var & binder & option qualifier)) (t: term) : term =
  match bs with
  | [] -> t
  | (x, b, q) :: bs ->
    let t = tm_arrow_binders bs t in
    let t = close_term t x in
    Pulse.Reflection.Util.mk_arrow_with_name b.binder_ppname.name (b.binder_ty, elab_qual q) t

let rec arrow_of_abs (env:_) (prog:st_term { Tm_Abs? prog.term })
  : T.Tac (term & t:st_term { Tm_Abs? t.term })
  = let Tm_Abs { b; q; ascription; body } = prog.term in
    let x = fresh env in
    let px = b.binder_ppname, x in
    let x_ty, _ = tc_type_phase1 env b.binder_ty in
    let b = { b with binder_ty = x_ty } in
    let env = push_binding env x (fst px) x_ty in
    let body = open_st_term_nv body px in
    let annot = ascription.annotated in
    if Some? ascription.elaborated
    then Env.fail env (Some prog.range) "Unexpected elaborated annotation on function";
    if Tm_Abs? body.term
    then (
      match annot with
      | None ->
        //no meaningful user annotation to process
        let arr, body = arrow_of_abs env body in
        let arr = close_term arr x in
        let body = close_st_term body x in
        let ty : term = tm_arrow b q (C_Tot arr) in
        let prog : st_term = { prog with term = Tm_Abs { b; q; ascription; body}} in
        ty, prog

      | Some c -> ( //we have an annotation
        let c = open_comp_with c (U.term_of_nvar px) in
        match c with
        | C_Tot tannot -> (
          let tannot, _ = tc_type_phase1 env tannot in
          let t = RU.hnf_lax (elab_env env) tannot in
          //retain the original annotation, so that we check it wrt the inferred type in maybe_rewrite_body_typing
          let t = close_term t x in
          let annot = close_comp c x in
          let ty : term = tm_arrow b q (C_Tot t) in
          let ascription = { annotated = Some annot; elaborated = None } in
          let body = close_st_term body x in
          let prog : st_term = { prog with term = Tm_Abs { b; q; ascription; body} } in
          ty, prog
        )

        | _ ->
          Env.fail 
            env 
            (Some prog.range) 
            (Printf.sprintf "Unexpected type of abstraction: %s"
                (P.comp_to_string c))
      )
    )
    else (
      match annot with
      | None -> 
        Env.fail env (Some prog.range) "Unannotated function body"
      
      | Some c -> ( //we're taking the annotation as is; remove it from the abstraction to avoid rechecking it
        let c = open_comp_nv c px in
        let g, bs, c = preproc_ascription env c in
        let bs = (x, b, q) :: bs in
        let ty = tm_arrow_binders bs (elab_comp c) in
        let prog' = tm_abs_binders bs body in
        ty, { prog with term = prog'.term }
      )
    )

let qualifier_compat g r (q:option qualifier) (q':T.aqualv) : T.Tac unit =
  match q, q' with
  | None, T.Q_Explicit -> ()
  | Some Implicit, T.Q_Implicit 
  | Some Implicit, T.Q_Meta _ -> ()
  | Some TcArg, T.Q_Meta _ -> ()
  | Some (Meta _), T.Q_Meta _ -> ()
  | _ -> Env.fail g (Some r) "Unexpected binder qualifier"

// let check_qual g (q:T.aqualv) : T.Tac T.aqualv =
//   match q with
//   | T.Q_Meta t ->
//     let t = T.tc (elab_env g) t in
//     (* FIXME *)
//     T.Q_Meta t
//   | q -> q
let check_qual g (q:qualifier) : T.Tac qualifier =
  match q with
  | Meta t ->
    let ty = (`(unit -> T.Tac u#0 unit)) in
    // let t = T.pack (T.Tv_AscribedT t ty None false) in
    let t =
      (* This makes sure to elaborate the meta qualifier so it
      matches exactly with what F* would generate. If not, we get
      weird errors using an `fn` in the implementation and a `val .. : stt`
      in the interface, or vice-versa, since they don't fully match. *)
      match T.instantiate_implicits (elab_env g) t (Some ty) false with
      | Some (_, t, _), _ -> t
      | None, iss ->
        T.log_issues iss;
        T.fail ("check_qual: failed to elaborate term " ^ show t)
    in
    Meta t
  | q -> q

let rec rebuild_abs (g:env) (t:st_term) (annot:T.term)
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = 
    debug_abs g (fun _ -> Printf.sprintf "rebuild_abs\n\t%s\n\t%s\n"
                (P.st_term_to_string t)
                (T.term_to_string annot));
    match t.term, R.inspect_ln annot with
    | Tm_Abs { b; q; ascription=asc; body }, R.Tv_Arrow b' c' -> (
      let b' = T.inspect_binder b' in
      qualifier_compat g b.binder_ppname.range q b'.qual;
      let ty = b'.sort in
      let comp = R.inspect_comp c' in
      match comp with
      | T.C_Total res_ty -> (
        if Tm_Abs? body.term
        then (
          let b = mk_binder_with_attrs ty b.binder_ppname b.binder_attrs in
          let body = rebuild_abs g body res_ty in
          let asc = { asc with elaborated = None } in
          { t with term = Tm_Abs { b; q; ascription=asc; body }}
        )
        else (
          match readback_comp res_ty with
          | None ->
            Env.fail g (Some (T.range_of_term res_ty))
              (Printf.sprintf "Expected a computation type; got %s"
                  (T.term_to_string res_ty))
          | Some (C_Tot ty) -> (
            match T.inspect res_ty with
            | T.Tv_Arrow b _ ->
              Env.fail g (Some body.range)
                         (Printf.sprintf "Expected a binder for %s" (T.binder_to_string b))

            | _ -> 
                Env.fail g (Some body.range)
                    (Printf.sprintf 
                      "Incorrect annotation on function body, expected a stateful computation type; got: %s"
                      (P.comp_to_string (C_Tot ty)))
          )

          | Some c ->
            let b = mk_binder_with_attrs ty b.binder_ppname b.binder_attrs in
            let asc = { asc with elaborated = Some c } in
            { t with term = Tm_Abs { b; q; ascription=asc; body }}              
        )
      )
      | _ ->
        Env.fail g (Some t.range) 
            (Printf.sprintf "Unexpected type of abstraction: %s"
                (T.term_to_string annot))
    )

    | _ -> 
      Env.fail g (Some t.range) 
                (Printf.sprintf "Unexpected arity of abstraction: expected a term of type %s"
                      (T.term_to_string annot))

let preprocess_abs
      (g:env)
      (t:st_term{Tm_Abs? t.term})
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = let annot, t = arrow_of_abs g t in
    debug_abs g (fun _ -> Printf.sprintf "arrow_of_abs = %s\n" (P.term_to_string annot));
    let annot, _ = Pulse.Checker.Pure.instantiate_term_implicits g annot None false in
    let annot = RU.hnf_lax (elab_env g) annot in
    let abs = rebuild_abs g t annot in
    debug_abs g (fun _ -> Printf.sprintf "rebuild_abs = %s\n" (P.st_term_to_string abs));
    abs

let sub_effect_comp g r (asc:comp_ascription) (c_computed:comp) : T.Tac (option (c2:comp & lift_comp g c_computed c2)) =
  let nop = None in
  match asc.elaborated with
  | None -> nop
  | Some c ->
    match c_computed, c with
    | C_Tot t1, C_Tot t2 -> nop
    | C_ST _, C_ST _ -> nop
    | C_STGhost _ _, C_STGhost _ _ -> nop
    | C_STAtomic i Neutral c1, C_STGhost _ _ ->
      let lift = Lift_Neutral_Ghost g c_computed in
      Some (| C_STGhost i c1, lift |)
    | C_STAtomic i o1 c1, C_STAtomic j o2 c2 ->
      if sub_observability o1 o2
      then let lift = Lift_Observability g c_computed o2 in
           Some (| C_STAtomic i o2 c1, lift |)
      else nop

    (* FIXME: more lifts here *) 
    | _ -> nop

let check_effect_annotation g r (asc:comp_ascription) (c_computed:comp) : T.Tac (c2:comp & st_sub g c_computed c2) =
  let nop = (| c_computed, STS_Refl _ _ |) in
  match asc.elaborated with
  | None -> nop
  | Some c ->
    match c, c_computed with
    | C_Tot _, C_Tot _
    | C_ST _, C_ST _  -> nop
    | C_STGhost i c1, C_STGhost j c2
    | C_STAtomic i Neutral c1, C_STAtomic j Neutral c2
    | C_STAtomic i Observable c1, C_STAtomic j Observable c2 ->
      // This should be true since we used the annotated computation type
      // to check the body of the function, but this fact is not exposed
      // by the checker and post hints yet.
      assume (c1 == c2);

      if eq_tm i j then (
        assert (c == c_computed);
        nop
      ) else
      
      let b = mk_binder "res" Range.range_0 c2.res in
      let phi = tm_inames_subset j i in
      let typing = tm_inames_subset_typing g j i in
      // Or:
      // let typing = core_check_tot_term g phi tm_prop in
      let tok = T.with_policy T.ForceSMT (fun () -> try_check_prop_validity g phi typing) in
      if None? tok then (
        let open Pulse.PP in
        fail_doc g (Some (RU.range_of_term i)) [
          prefix 4 1 (text "Annotated effect expects only invariants in") (pp i) ^/^
          prefix 4 1 (text "to be opened; but computed effect claims that invariants") (pp j) ^/^
          text "are opened"
        ]
      );

      let Some tok = tok in

      let d_sub : st_sub g c_computed c =
        match c_computed with
        | C_STAtomic _ obs _ -> STS_AtomicInvs g c2 j i obs obs tok
        | C_STGhost _ _ -> STS_GhostInvs g c2 j i tok
      in
      (| c, d_sub |)

    | _, _ ->
      let open Pulse.PP in
      fail_doc g (Some r) [
        prefix 4 1 (text "Expected effect")
                      (arbitrary_string (P.tag_of_comp c)) ^/^
        prefix 4 1 (text "but this function body has effect")
                      (arbitrary_string (P.tag_of_comp c_computed))
      ]


#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
(* Rewrite the comp c into the annotated one, if any,
preserving the st_typing derivation d *)
let maybe_rewrite_body_typing
      (#g:_) (#e:st_term) (#c:comp)
      (d:st_typing g e c)
      (asc:comp_ascription)
  : T.Tac (c':comp & st_typing g e c')
  = let open Pulse.PP in
    match asc.annotated, c with
    | None, _ -> (| c, d |)
    | Some (C_Tot t), C_Tot t' -> (
        let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t None false in
        let (| u, t_typing |) = Pulse.Checker.Pure.check_universe g t in
        match T.t_check_equiv true true (elab_env g) t t' with
        | None, _ ->
          Env.fail_doc g (Some e.range) [
            text "Inferred type is incompatible with annotation.";
            text "Inferred:" ^/^ pp t';
            text "Annotated:" ^/^ pp t;
          ]
        | Some tok, _ ->
          debug_abs g
            (fun _ -> Printf.sprintf "maybe_rewrite_body_typing:{\nfrom %s\nto %s}\n"
              (show c)
              (show (C_Tot t)));
          let sq : squash (RT.equiv_token (elab_env g) t t') = () in
          let t'_typing : universe_of g t' u =
            (* t is equiv to t', and t has universe t. *)
            magic ()
          in
          let tok' : st_equiv g (C_Tot t') (C_Tot t) =
            ST_TotEquiv _ t' t u t'_typing
              (RT.Rel_sym _ _ _ (RT.Rel_eq_token _ _ _ sq))
          in
          (| C_Tot t, T_Equiv _ _ _ _ d tok' |)
    )

    (* c is not a C_Tot *)
    | Some (C_Tot _), _ ->
      Env.fail_doc g (Some e.range) [
        text "Inferred type is incompatible with annotation.";
      ]

    (* The annotation is not a C_Tot *)
    | Some c, _ ->
      Env.fail_doc g (Some (range_of_comp c)) [
        Pulse.PP.text "Unexpected annotation on a function body."
      ]
#pop-options

let open_ascription (c:comp_ascription) (nv:nvar) : comp_ascription =
  let t = term_of_nvar nv in
  subst_ascription c [RT.DT 0 t]
let close_ascription (c:comp_ascription) (nv:nvar) : comp_ascription =
  subst_ascription c [RT.ND (snd nv) 0]

module R = FStar.Reflection.V2
#push-options "--z3rlimit_factor 20 --fuel 0 --ifuel 1 --split_queries no"
#restart-solver
let rec check_abs_core
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  //warn g (Some t.range) (Printf.sprintf "check_abs_core, t = %s" (P.st_term_to_string t));
  let range = t.range in
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname;binder_attrs}; q=qual; ascription=asc; body } -> //pre=pre_hint; body; ret_ty; post=post_hint_body } ->
    let qual = T.map_opt (check_qual g) qual in
    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = compute_tot_term_type g t in //elaborate it first
    let (| u, t_typing |) = universe_of_well_typed_term g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let px = ppname, x in
    let var = tm_var {nm_ppname=ppname;nm_index=x} in
    let g' = push_binding g x ppname t in
    let body_opened = open_st_term_nv body px in
    let asc = open_ascription asc px in 
    match body_opened.term with
    | Tm_Abs _ ->
      (* Check the opened body *)
      let (| body, c_body, body_typing |) = check_abs_core g' body_opened check in

      (* First lift into annotated effect *)
      let (| c_body, body_typing |) : ( c_body:comp & st_typing g' body c_body ) =
        match sub_effect_comp g' body.range asc c_body with
        | None -> (| c_body, body_typing |)
        | Some (| c_body, lift |) ->
          let body_typing = T_Lift _ _ _ _ body_typing lift in
          (| c_body, body_typing |)
      in

      (* Check if it matches annotation (if any, likely not), and adjust derivation
      if needed. Currently this only subtypes the invariants. *)
      let (| c_body, d_sub |) = check_effect_annotation g' body.range asc c_body in
      let body_typing = T_Sub _ _ _ _ body_typing d_sub in
      (* Similar to above, fixes the type of the computation if we need to match
      its annotation. TODO: merge these two by adding a tot subtyping (or equiv)
      case to the st_sub judg. *)
      let (| c_body, body_typing |) = maybe_rewrite_body_typing body_typing asc in

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);

      // instantiate implicits in the attributes
      let binder_attrs =
        binder_attrs
        |> T.unseal
        |> T.map (fun attr -> attr |> (fun t -> instantiate_term_implicits g t None false) |> fst)
        |> FStar.Sealed.seal in

      let b = {binder_ty=t;binder_ppname=ppname;binder_attrs} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname;binder_attrs} qual (close_comp c_body x) in
      (| _, C_Tot tres, tt |)
    | _ ->
      let elab_c, pre_opened, inames_opened, ret_ty, post_hint_body =
        match asc.elaborated with
        | None ->
          Env.fail g (Some body.range)
              "Missing annotation on a function body"

        | Some (C_Tot r) -> (
          Env.fail g (Some body.range)
                     (Printf.sprintf 
                       "Incorrect annotation on a function, expected a computation type, got: %s"
                        (P.comp_to_string (C_Tot r)))
        )

        | Some c -> 
          let inames_opened =
            if C_STGhost? c || C_STAtomic? c then
             let inames = open_term_nv (comp_inames c) px in
             let inames = PCP.norm_well_typed_term (elab_env g)
               [primops; iota; zeta; delta_attr ["Pulse.Lib.Core.unfold_check_opens"]]
               inames
             in
             inames
           else
             tm_emp_inames
          in
          let set_inames inames (c:comp) : comp =
            match c with
            | C_STAtomic _ obs st -> C_STAtomic inames obs st
            | C_STGhost  _ st     -> C_STGhost inames st
            | _ -> c
          in
          set_inames inames_opened c,
          open_term_nv (comp_pre c) px,
          inames_opened,
          Some (open_term_nv (comp_res c) px),
          Some (open_term' (comp_post c) var 1)
      in
      let (| pre_opened, pre_typing |) =
        (* In some cases F* can mess up the range in error reporting and make it
         point outside of this term. Bound it here. See e.g. Bug59, if we remove
         this bound then the range points to the span between the 'x' and 'y' binders. *)
        RU.with_error_bound (T.range_of_term pre_opened) (fun () -> check_slprop g' pre_opened)
      in
      let pre = close_term pre_opened x in
      let post : post_hint_opt g' =
        match post_hint_body with
        | None ->
          NoHint
        | Some post ->
          let post_hint_typing
            : post_hint_t
            = Pulse.Checker.Base.intro_post_hint
                  (push_context "post_hint_typing" range g')
                  (effect_annot_of_comp elab_c)
                  ret_ty
                  post
          in
          PostHint post_hint_typing
      in

      let ppname_ret = mk_ppname_no_range "_fret" in
      let r  = check g' pre_opened pre_typing post ppname_ret body_opened  in
      let (| post, r |) : (ph:post_hint_opt g' & checker_result_t g' pre_opened ph) =
        match post with
        | PostHint _ -> (| post, r |)
        | _ ->
          (* we support inference of postconditions for functions,
             but this functionality is still unusable from the front end,
             which expects functions to be annotated *)
          let ph = Pulse.Checker.Base.infer_post r in
          let r = Pulse.Checker.Prover.prove_post_hint r (PostHint ph) (T.range_of_term t) in
          (| PostHint ph, r |)
      in
      let (| body, c_body, body_typing |) : st_typing_in_ctxt g' pre_opened post =
        RU.record_stats "apply_checker_result_k" fun _ ->
        apply_checker_result_k #_ #_ #(PostHint?.v post) r ppname_ret in

      let c_opened : comp_ascription = { annotated = None; elaborated = Some (open_comp_nv elab_c px) } in

      (* First lift into annotated effect *)
      let (| c_body, body_typing |) : ( c_body:comp & st_typing g' body c_body ) =
        match sub_effect_comp g' body.range c_opened c_body with
        | None -> (| c_body, body_typing |)
        | Some (| c_body, lift |) ->
          let body_typing = T_Lift _ _ _ _ body_typing lift in
          (| c_body, body_typing |)
      in

      let (| c_body, d_sub |) = check_effect_annotation g' body.range c_opened c_body in
      let body_typing = T_Sub _ _ _ _ body_typing d_sub in

      let (| c_body, body_typing |) = maybe_rewrite_body_typing body_typing asc in

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname;binder_attrs} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname;binder_attrs} qual (close_comp c_body x) in

      (| _, C_Tot tres, tt |)
#pop-options

let check_abs (g:env) (t:st_term{Tm_Abs? t.term}) (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let t = preprocess_abs g t in
  check_abs_core g t check
