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


let debug_abs g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.abs"
  then T.print (s ())

(* Infers the the type of the binders from the specification alone, not the body *)

let range_of_st_comp (st:st_comp) =
  RU.union_ranges (st.pre.range) (st.post.range)

let range_of_comp (c:comp) =
  match c with
  | C_Tot t -> t.range
  | C_ST st -> range_of_st_comp st
  | C_STAtomic _ st -> range_of_st_comp st
  | C_STGhost _ st -> range_of_st_comp st

let rec arrow_of_abs (env:_) (t:st_term { Tm_Abs? t.term })
  : T.Tac term
  = let Tm_Abs { b; q; ascription; body } = t.term in
    let x = fresh env in
    let px = b.binder_ppname, x in
    let env = push_binding env x (fst px) b.binder_ty in
    let body = open_st_term_nv body px in
    let annot = ascription.annotated in
    if Tm_Abs? body.term
    then (
      match annot with
      | None ->
        //no meaningful user annotation to process
        let arr = arrow_of_abs env body in
        let arr = close_term arr x in
        { tm_arrow b q (C_Tot arr) with range = RU.union_ranges b.binder_ty.range arr.range }

      | Some c -> (
        let c = open_comp_with c (U.term_of_nvar px) in
        match c with
        | C_Tot tannot -> (
          let tannot' = RU.whnf_lax (elab_env env) (elab_term tannot) in
          // T.print (Printf.sprintf "tannot=%s; tannot': %s" 
          //   (P.term_to_string tannot)
          //   (T.term_to_string tannot'));
          match Pulse.Readback.readback_ty tannot' with
          | None -> 
            Env.fail 
              env 
              (Some t.range) 
              (Printf.sprintf "Unexpected type of abstraction, expected an arrow, got: %s"
                  (T.term_to_string tannot'))
          | Some t ->
            let t = close_term t x in
            { tm_arrow b q (C_Tot t) with range = RU.union_ranges b.binder_ty.range t.range }
        )

        | _ ->
          Env.fail 
            env 
            (Some t.range) 
            (Printf.sprintf "Unexpected type of abstraction: %s"
                (P.comp_to_string c))
      )
    )
    else (
      match annot with
      | None -> 
        Env.fail env (Some t.range) "Unannotated function body"
      
      | Some c -> (
        { tm_arrow b q c with range = RU.union_ranges b.binder_ty.range (range_of_comp c) }
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
      let ty = readback_ty b'.sort in
      let comp = R.inspect_comp c' in
      match ty, comp with
      | Some ty, T.C_Total res_ty -> (
        if Tm_Abs? body.term
        then (
          let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
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
          | Some c ->
            let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
            let asc = { asc with elaborated = Some c } in
            { t with term = Tm_Abs { b; q; ascription=asc; body }}              
        )
      )
      | _ ->
        Env.fail g (Some t.range) 
            (Printf.sprintf "Unexpected type of abstraction: %s"
                (T.term_to_string annot))
    )
    // | Tm_Abs { b; q; ascription=Some asc; body }, R.Tv_Arrow b' c' -> (
    //   let ty = readback_ty (T.inspect_binder b').sort in
    //   let comp = R.inspect_comp c' in
    //   match ty, comp with
    //   | Some ty, R.C_Total res -> (
    //     let c = readback_comp res in
    //     match c with
    //     | None -> 
    //       Env.fail g (Some t.range) 
    //                   (Printf.sprintf "Unexpected computation type in abstraction: %s"
    //                       (T.term_to_string res))
    //     | Some c ->
    //       let b = { binder_ty = ty ; binder_ppname = b.binder_ppname } in
    //       let asc = { asc with elaborated = c } in
    //       { t with term = Tm_Abs { b; q; ascription=Some asc; body }}
    //   )
    //   | _ ->
    //     Env.fail g (Some t.range) 
    //                 (Printf.sprintf "Unexpected type of abstraction: %s"
    //                       (T.term_to_string annot))
    // )
    | _ -> 
      Env.fail g (Some t.range) 
                (Printf.sprintf "Unexpected arity of abstraction: expected a term of type %s"
                      (T.term_to_string annot))

let preprocess_abs
      (g:env)
      (t:st_term{Tm_Abs? t.term})
  : T.Tac (t:st_term { Tm_Abs? t.term })
  = let annot = arrow_of_abs g t in
    debug_abs g (fun _ -> Printf.sprintf "arrow_of_abs = %s\n" (P.term_to_string annot));
    let annot, _ = Pulse.Checker.Pure.instantiate_term_implicits g annot in
    match annot.t with
    | Tm_FStar annot ->
      let abs = rebuild_abs g t annot in
      debug_abs g (fun _ -> Printf.sprintf "rebuild_abs = %s\n" (P.st_term_to_string abs));
      abs
    | _ ->
      Env.fail g (Some t.range) 
                 (Printf.sprintf "Expected an arrow type as an annotation, got %s"
                          (P.term_to_string annot))

let check_effect_annotation g r (asc:comp_ascription) (c_computed:comp) =
  match asc.elaborated with
  | None -> ()
  | Some c ->
    match c, c_computed with
    | C_Tot _, C_Tot _ -> ()
    | C_ST _, C_ST _ -> ()
    | C_STAtomic i _, C_STAtomic j _
    | C_STGhost i _, C_STGhost j _ ->
      if eq_tm i j
      then ()
      else fail g (Some i.range)
                  (Printf.sprintf "Annotated effect expects only invariants in %s to be opened; but computed effect claims that invariants %s are opened"
                    (P.term_to_string i)
                    (P.term_to_string j))
    | _, _ ->
      fail g (Some r)
            (Printf.sprintf "Expected effect %s but this function body has effect %s"
                    (P.tag_of_comp c)
                    (P.tag_of_comp c_computed))


#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
let rec check_abs_core
  (g:env)
  (t:st_term{Tm_Abs? t.term})
  (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let range = t.range in
  match t.term with  
  | Tm_Abs { b = {binder_ty=t;binder_ppname=ppname}; q=qual; ascription=c; body } -> //pre=pre_hint; body; ret_ty; post=post_hint_body } ->

    (*  (fun (x:t) -> {pre_hint} body : t { post_hint } *)
    let (| t, _, _ |) = check_tot_term g t in //elaborate it first
    let (| u, t_typing |) = check_universe g t in //then check that its universe ... We could collapse the two calls
    let x = fresh g in
    let px = ppname, x in
    let var = tm_var {nm_ppname=ppname;nm_index=x} in
    let g' = push_binding g x ppname t in
    let body_opened = open_st_term_nv body px in
    match body_opened.term with
    | Tm_Abs _ ->
      let (| body, c_body, body_typing |) = check_abs_core g' body_opened check in
      check_effect_annotation g' body.range c c_body;
      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| _, C_Tot tres, tt |)
    | _ ->
      let elab_c, pre_opened, ret_ty, post_hint_body =
        match c.elaborated with
        | None ->
          Env.fail g (Some body.range)
              "Missing annotation on a function body"

        | Some (C_Tot r) ->
          Env.fail g (Some body.range)
            (Printf.sprintf 
              "Incorrect annotation on a function body: %s"
              (P.comp_to_string (C_Tot r)))

        | Some c -> 
          c,
          open_term_nv (comp_pre c) px,
          Some (open_term_nv (comp_res c) px),
          Some (open_term' (comp_post c) var 1)
      in
      let (| pre_opened, pre_typing |) = check_vprop g' pre_opened in
      let pre = close_term pre_opened x in
      let post : post_hint_opt g' =
        match post_hint_body with
        | None -> fail g (Some body.range) "Top-level functions must be annotated with pre and post conditions"
        | Some post ->
          let post_hint_typing
            : post_hint_t
            = Pulse.Checker.Base.intro_post_hint
                  (push_context "post_hint_typing" range g')
                  (Some (ctag_of_comp_st elab_c))
                  ret_ty
                  post
          in
          Some post_hint_typing
      in

      let ppname = mk_ppname_no_range "_fret" in
      let r  = check g' pre_opened pre_typing post ppname body_opened  in
      let (| body, c_body, body_typing |) : st_typing_in_ctxt g' pre_opened post =
        apply_checker_result_k #_ #_ #(Some?.v post) r ppname in

      check_effect_annotation g' body.range c c_body;

      FV.st_typing_freevars body_typing;
      let body_closed = close_st_term body x in
      assume (open_st_term body_closed x == body);
      let b = {binder_ty=t;binder_ppname=ppname} in
      let tt = T_Abs g x qual b u body_closed c_body t_typing body_typing in
      let tres = tm_arrow {binder_ty=t;binder_ppname=ppname} qual (close_comp c_body x) in
      (| _, C_Tot tres, tt |)

let check_abs (g:env) (t:st_term{Tm_Abs? t.term}) (check:check_t)
  : T.Tac (t:st_term & c:comp & st_typing g t c) =
  let t = preprocess_abs g t in
  check_abs_core g t check