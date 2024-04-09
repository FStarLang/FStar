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

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base

module P = Pulse.Syntax.Printer
module FV = Pulse.Typing.FV
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils
module Env = Pulse.Typing.Env
module U = Pulse.Syntax.Pure

open Pulse.Show

let debug_abs g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.abs"
  then T.print (s ())

(* Infers the the type of the binders from the specification alone, not the body *)

let range_of_st_comp (st:st_comp) =
  RU.union_ranges (RU.range_of_term st.pre) (RU.range_of_term st.post)

let range_of_comp (c:comp) =
  match c with
  | C_Tot t -> RU.range_of_term t
  | C_ST st -> range_of_st_comp st
  | C_STAtomic _ _ st -> range_of_st_comp st
  | C_STGhost _ st -> range_of_st_comp st

let rec arrow_of_abs (env:_) (prog:st_term { Tm_Abs? prog.term })
  : T.Tac (term & t:st_term { Tm_Abs? t.term })
  = let Tm_Abs { b; q; ascription; body } = prog.term in
    let x = fresh env in
    let px = b.binder_ppname, x in
    let env = push_binding env x (fst px) b.binder_ty in
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
        let ty : term = wr (tm_arrow b q (C_Tot arr))
                           (RU.union_ranges (RU.range_of_term b.binder_ty) (RU.range_of_term arr)) in
        let prog : st_term = { prog with term = Tm_Abs { b; q; ascription; body}} in
        ty, prog

      | Some c -> ( //we have an annotation
        let c = open_comp_with c (U.term_of_nvar px) in
        match c with
        | C_Tot tannot -> (
          let t = RU.hnf_lax (elab_env env) (elab_term tannot) in
          //retain the original annotation, so that we check it wrt the inferred type in maybe_rewrite_body_typing
          let t = close_term t x in
          let annot = close_comp c x in
          let ty : term = wr (tm_arrow b q (C_Tot t))
                             (RU.union_ranges (RU.range_of_term b.binder_ty) (RU.range_of_term t)) in
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
        let ty : term = wr (tm_arrow b q c)
                                 (RU.union_ranges (RU.range_of_term b.binder_ty) (range_of_comp c)) in
        let ascription = empty_ascription in
        let body = close_st_term body x in
        let prog : st_term = { prog with term = Tm_Abs { b; q; ascription; body} } in
        ty, prog
      )
    )

let qualifier_compat g r (q:option qualifier) (q':T.aqualv) : T.Tac unit =
  match q, q' with
  | None, T.Q_Explicit -> ()
  | Some Implicit, T.Q_Implicit 
  | Some Implicit, T.Q_Meta _ -> ()
  | _ -> Env.fail g (Some r) "Unexpected binder qualifier"

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
    let annot, _ = Pulse.Checker.Pure.instantiate_term_implicits g annot in
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
      let tok = T.with_policy T.SMTSync (fun () -> try_check_prop_validity g phi typing) in
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
let maybe_rewrite_body_typing
      (#g:_) (#e:st_term) (#c:comp)
      (d:st_typing g e c)
      (asc:comp_ascription)
  : T.Tac (c':comp & st_typing g e c')
  = match asc.annotated with
    | None ->  (| c, d |)
    | Some (C_Tot t) -> (
      match c with
      | C_Tot t' -> (
        let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t in
        let (| u, t_typing |) = Pulse.Checker.Pure.check_universe g t in
        match Pulse.Checker.Base.norm_st_typing_inverse
                 #_ #_ #t' d t t_typing [hnf;delta]
        with
        | None -> 
          Env.fail g (Some e.range) "Inferred type is incompatible with annotation"
        | Some d -> 
          debug_abs g 
            (fun _ -> Printf.sprintf "maybe_rewrite_body_typing:{\nfrom %s\nto %s}\n" 
              (P.comp_to_string c)
              (P.comp_to_string (C_Tot t)));
          (| C_Tot t, d |)
      )
      | _ -> 
      Env.fail g (Some e.range) "Inferred type is incompatible with annotation"
    )
    | Some c -> 
      let st = st_comp_of_comp c in
      Env.fail g (Some (RU.range_of_term st.pre)) "Unexpected annotation on a function body"

let open_ascription (c:comp_ascription) (nv:nvar) : comp_ascription =
  let t = term_of_nvar nv in
  subst_ascription c [DT 0 t]
let close_ascription (c:comp_ascription) (nv:nvar) : comp_ascription =
  subst_ascription c [ND (snd nv) 0]

#push-options "--z3rlimit_factor 4"
let rec check_abs_core
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  //warn g (Some t.range) (Printf.sprintf "check_abs_core, t = %s" (P.st_term_to_string t));
  let range = t.range in
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname;binder_attrs}; q=qual; ascription=asc; body } -> //pre=pre_hint; body; ret_ty; post=post_hint_body } ->
    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = compute_tot_term_type g t in //elaborate it first
    let (| u, t_typing |) = check_universe g t in //then check that its universe ... We could collapse the two calls
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
        |> T.map (fun attr -> attr |> instantiate_term_implicits g |> fst)
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
          c,
          open_term_nv (comp_pre c) px,
          (if C_STAtomic? c then open_term_nv (comp_inames c) px else tm_emp_inames),
          Some (open_term_nv (comp_res c) px),
          Some (open_term' (comp_post c) var 1)
      in
      let (| pre_opened, pre_typing |) = check_vprop g' pre_opened in
      let pre = close_term pre_opened x in
      let post : post_hint_opt g' =
        match post_hint_body with
        | None ->
          let open Pulse.PP in
          fail_doc g (Some body.range) [text "Top-level functions must be annotated with pre and post conditions"]
        | Some post ->
          let post_hint_typing
            : post_hint_t
            = Pulse.Checker.Base.intro_post_hint
                  (push_context "post_hint_typing" range g')
                  (effect_annot_of_comp elab_c)
                  ret_ty
                  post
          in
          Some post_hint_typing
      in

      let ppname_ret = mk_ppname_no_range "_fret" in
      let r  = check g' pre_opened pre_typing post ppname_ret body_opened  in
      let (| body, c_body, body_typing |) : st_typing_in_ctxt g' pre_opened post =
        apply_checker_result_k #_ #_ #(Some?.v post) r ppname_ret in

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

let check_abs (g:env) (t:st_term{Tm_Abs? t.term}) (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let t = preprocess_abs g t in
  check_abs_core g t check
