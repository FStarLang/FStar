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

module Pulse.Checker.Base

module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module CP = Pulse.Checker.Pure
module RU = Pulse.RuntimeUtils
open Pulse.Checker.Util
open Pulse.Show

open Pulse.Typing.Combinators
let debug (g:env) (f: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.checker" then
    T.print (f())

let format_failed_goal (g:env) (ctxt:list term) (goal:list term) =
  let terms_to_strings (ts:list term)= T.map Pulse.Syntax.Printer.term_to_string ts in
  let numbered_list ss = 
       let _, s = T.fold_left (fun (i, acc) s -> (i+1, Printf.sprintf "%d. %s" i s :: acc)) (1, []) ss in
       String.concat "\n  " (List.rev s)
  in
  let format_terms (ts:list term) = numbered_list (terms_to_strings ts) in
  Printf.sprintf 
    "Failed to prove the following goals:\n  \
     %s\n\
     The remaining conjuncts in the separation logic context available for use are:\n  \
     %s\n\
     The typing context is:\n  \
     %s\n"
    (format_terms goal)
    (format_terms ctxt)
    (env_to_string g)


let mk_arrow ty t = RT.mk_arrow ty T.Q_Explicit t
let mk_abs ty t = RT.(mk_abs ty T.Q_Explicit t)

let intro_comp_typing (g:env) 
                      (c:comp_st)
                      (x:var { fresh_wrt x g (freevars (comp_post c)) })
  : T.Tac unit
  = ()

irreducible
let post_typing_as_abstraction
  (g:env) (x:var) (ty:term) (t:term { fresh_wrt x g (freevars t) })
  : FStar.Ghost.erased (RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty tm_slprop))                                 
  = admit()

(* This should be in reflection typing *)
let fstar_equiv_preserves_typing
    (g:R.env) (t1 : R.term) (typ : R.term) (t2 : R.term)
    (eq : squash (T.equiv_token g t1 t2))
    (t1_typing : RT.tot_typing g t1 typ)
  : RT.tot_typing g t2 typ
  = admit()

let equiv_preserves_typing
    (g:env) (t1 : term) (typ : term) (t2 : term)
    (eq : squash (T.equiv_token (elab_env g) t1 t2))
  : unit
  = ()

let check_effect_annot (g:env) (e:effect_annot)
  : T.Tac (e':effect_annot { effect_annot_labels_match e e' }) =
  let check_opens opens : T.Tac term =
    let opens = CP.check_term g opens T.E_Total tm_inames in
    let opens' =
      CP.norm_well_typed_term
        (elab_env g)
        [primops; iota; zeta; delta_attr ["Pulse.Lib.Core.unfold_check_opens"]]
        opens
    in
    opens'
  in
  match e with
  | EffectAnnotSTT -> e
  | EffectAnnotGhost { opens } ->
    let opens = check_opens opens in
    EffectAnnotGhost { opens }
  | EffectAnnotAtomic { opens } ->
    let opens = check_opens opens in
    EffectAnnotAtomic { opens }
  | EffectAnnotAtomicOrGhost { opens } ->
    let opens = check_opens opens in
    EffectAnnotAtomicOrGhost { opens }

let intro_post_hint g effect_annot ret_ty_opt post =
  let x = fresh g in
  let ret_ty = 
      match ret_ty_opt with
      | None -> wr RT.unit_ty FStar.Range.range_0
      | Some t -> t
  in
  let ret_ty, _ = CP.instantiate_term_implicits g ret_ty None false in
  let u = CP.check_universe g ret_ty in
  let post = CP.check_slprop (push_binding g x ppname_default ret_ty) (open_term_nv post (v_as_nv x)) in 
  let post' = close_term post x in
  let effect_annot = check_effect_annot g effect_annot in
  assume (open_term post' x == post);
  { g;
    effect_annot;
    ret_ty; u;
    post=post';
    }

let post_hint_from_comp_typing g c = 
  let p : post_hint_t = 
    { g;
      effect_annot = effect_annot_of_comp c;
      ret_ty = comp_res c; u=comp_u c; 
      post=comp_post c }
  in
  p

#push-options "--z3rlimit_factor 4"
let comp_typing_from_post_hint
    (#g: env)
    (c: comp_st)
    (p:post_hint_for_env g { comp_post_matches_hint c (PostHint p) })
: T.Tac unit
= let x = fresh g in
  if x `Set.mem` freevars p.post //exclude this
  then fail g None "Impossible: unexpected freevar in post, please file a bug-report"
  else intro_comp_typing g c
        x


let extend_post_hint g p x tx conjunct =
  let g' = push_binding g x ppname_default tx in
  let y = fresh g' in
  let g'' = push_binding g' y ppname_default p.ret_ty in
  let new_post = tm_star p.post conjunct in
  assume (fresh_wrt y g'' (freevars new_post));
  { p with
    g=g';
    post=new_post }

let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans
  (#g0:env) (#g1:env { g1 `env_extends` g0 }) (#g2:env { g2 `env_extends` g1 }) (#ctxt0 #ctxt1 #ctxt2:term)
  (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
  (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let comp_st_with_post (c:comp_st) (post:term)
  : c':comp_st { st_comp_of_comp c' == ({ st_comp_of_comp c with post} <: st_comp) } =
  match c with
  | C_ST st -> C_ST { st with post }
  | C_STGhost i st -> C_STGhost i { st with post }
  | C_STAtomic i obs st -> C_STAtomic i obs {st with post}

let comp_with_pre (c:comp_st) (pre:term) =
  match c with
  | C_ST st -> C_ST { st with pre }
  | C_STGhost i st -> C_STGhost i { st with pre }
  | C_STAtomic i obs st -> C_STAtomic i obs {st with pre}

let k_elab_equiv_continuation (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt #ctxt1:term) (ctxt2:term)
  (k:continuation_elaborator g1 ctxt g2 ctxt1)
  : continuation_elaborator g1 ctxt g2 ctxt2 =
  fun post_hint res ->
    let (| st, c |) = res in
    assert (comp_pre c == ctxt2);
    k post_hint (| st, comp_with_pre c ctxt1 |)

let k_elab_equiv_prefix
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt:term) (ctxt2:term)
  (k:continuation_elaborator g1 ctxt1 g2 ctxt)
  : continuation_elaborator g1 ctxt2 g2 ctxt =
  fun post_hint res ->
  let framing_token : frame_for_req_in_ctxt g1 ctxt2 ctxt1 = 
    tm_emp
  in
  let res = k post_hint res in
  let (| st, c |) = res in
  assert (comp_pre c == ctxt1);
  (| st, comp_with_pre c ctxt2 |)

let k_elab_equiv
  (#g1:env) (#g2:env { g2 `env_extends` g1 }) (#ctxt1 #ctxt2:term) (ctxt1' ctxt2':term)                 
  (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
  : continuation_elaborator g1 ctxt1' g2 ctxt2' =
  
  let k : continuation_elaborator g1 ctxt1 g2 ctxt2' =
    k_elab_equiv_continuation ctxt2' k in
  let k : continuation_elaborator g1 ctxt1' g2 ctxt2' =
    k_elab_equiv_prefix ctxt1' k in
  k

#push-options "--fuel 3 --ifuel 1 --split_queries no --z3rlimit_factor 20"
open Pulse.PP
let continuation_elaborator_with_bind' (#g:env) (ctxt:term)
  (c1:comp{stateful_comp c1})
  (e1:st_term)
  (x:nvar {freshv g (snd x)})
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             (push_binding g (snd x) (fst x) (comp_res c1))
             (tm_star (open_term (comp_post c1) (snd x)) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing = () in
  let v_eq = () in
  let framing_token : frame_for_req_in_ctxt g (tm_star ctxt pre1) pre1 = 
    ctxt
  in
  Pulse.Checker.Prover.Util.debug_prover g (fun _ ->
    Printf.sprintf "Applying frame %s to computation %s\n"
      (show ctxt)
      (show c1));
  let c1 =
    apply_frame g e1 (tm_star ctxt pre1) c1 framing_token in
  let u_of_1 = () in
  let b = res1 in
  let ppname, x = x in
  let g' = push_binding g x ppname b in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (tm_star ctxt pre1) g' (tm_star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2 |) = res in
    assert (comp_post_matches_hint c2 post_hint);
    let e2_closed = close_st_term e2 x in
    assume (open_st_term e2_closed x == e2);
    assert (comp_pre c1 == (tm_star ctxt pre1));
    assert (comp_post c1 == tm_star post1 ctxt);
    assert (comp_pre c2 == tm_star post1_opened ctxt);
    assert (open_term (comp_post c1) x == tm_star post1_opened (open_term ctxt x));
    // ctxt is well-typed, hence ln
    assume (open_term ctxt x == ctxt);
    assert (open_term (comp_post c1) x == comp_pre c2);
    // we closed e2 with x
    assume (~ (x `Set.mem` freevars_st e2_closed));
    if x `Set.mem` freevars (RU.deep_compress_safe (comp_post c2))
    then fail g' None ("Impossible: freevar clash when constructing continuation elaborator for bind, please file a bug-report" ^ show (comp_post c2))
    else (
      let _ =
        RU.record_stats "bind_res_and_post_typing" fun _ ->
        Pulse.Typing.Combinators.bind_res_and_post_typing g c2 x post_hint in
      let g = push_context g "mk_bind" e1.range in
      // info_doc g None
      //   [prefix 4 1 (doc_of_string "mk_bind e1 = ") (doc_of_string (Pulse.Syntax.Printer.st_term_to_string e1));
      //    prefix 4 1 (doc_of_string "mk_bind c1 = ") (pp #comp c1);
      //    prefix 4 1 (doc_of_string "mk_bind e2 = ") (doc_of_string (Pulse.Syntax.Printer.st_term_to_string e2));
      //    prefix 4 1 (doc_of_string "mk_bind c2 = ") (pp #comp c2)]
      // ;
      let (| e, c |) =
        Pulse.Typing.Combinators.mk_bind
          g (tm_star ctxt pre1) 
          e1 e2_closed c1 c2 (ppname, x)
          post_hint
      in
      (| e, c |)
    )
  in
  k
#pop-options

let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (c1:comp{stateful_comp c1})
  (e1:st_term)
  (x:nvar { freshv g (snd x) })
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             (push_binding g (snd x) (fst x) (comp_res c1))
             (tm_star (open_term (comp_post c1) (snd x)) ctxt)) =
  RU.record_stats "continuation_elaborator_with_bind" fun _ -> 
    continuation_elaborator_with_bind' ctxt c1 e1 x


let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let st_comp_typing_with_post_hint 
      (#g:env) (#ctxt:_)
      (post_hint:post_hint_opt g { PostHint? post_hint })
      (c:comp_st { comp_pre c == ctxt /\ comp_post_matches_hint c post_hint })
: unit
= let st = st_comp_of_comp c in
  let PostHint ph = post_hint in
  let x = RU.magic () in //fresh g in
  assume (fresh_wrt x g (freevars ph.post));


  assert (st.res == ph.ret_ty);
  assert (st.post == ph.post);
  ()
#pop-options

let continuation_elaborator_with_bind_fn (#g:env) (ctxt:term)
  (e1:st_term)
  (c1:comp { C_Tot? c1 })
  (b:binder{b.binder_ty == comp_res c1})
  (x:nvar { freshv g (snd x) })
: T.Tac (continuation_elaborator
          g ctxt
          (push_binding g (snd x) ppname_default (comp_res c1)) ctxt)
= let t1 = comp_res c1 in
  assert ((push_binding g (snd x) (fst x) t1) `env_extends` g);
  fun post_hint (| e2, c2 |) ->
    if not (PostHint? post_hint) then T.fail "bind_fn: expects the post_hint to be set";
    let ppname, x = x in
    let e2_closed = close_st_term e2 x in
    assume (open_st_term (close_st_term e2 x) x == e2);
    let e = wrst c2 (Tm_Bind {binder=b; head=e1; body=e2_closed}) in
    let u : Ghost.erased universe = RU.magic () in

    (| e, c2 |)

let rec check_equiv_emp (g:env) (vp:term)
  : option unit
  = match inspect_term vp with
    | Tm_Emp -> Some ()
    | Tm_Star vp1 vp2 ->
      (match check_equiv_emp g vp1, check_equiv_emp g vp2 with
       | Some d1, Some d2 ->
         Some ()
       | _, _ -> None)
     | _ -> None

let emp_inames_included (g:env) (i:term)
: prop_validity g (tm_inames_subset tm_emp_inames i)
= RU.magic()

#push-options "--ifuel 1"
let return_in_ctxt (g:env) (y:var) (y_ppname:ppname) (u:universe) (ty:term) (ctxt:slprop)
  (ty_typing:unit)
  (post_hint0:post_hint_opt g { PostHint? post_hint0 /\ checker_res_matches_post_hint g post_hint0 y ty ctxt})
: Div  (st_typing_in_ctxt g ctxt post_hint0)
       (requires lookup g y == Some ty)
       (ensures fun _ -> True)
= let PostHint post_hint = post_hint0 in
  let x = fresh g in
  assume (~ (x `Set.mem` freevars post_hint.post));
  let ctag =
    match post_hint.effect_annot with
    | EffectAnnotAtomic _ -> STT_Atomic
    | EffectAnnotGhost _ -> STT_Ghost
    | EffectAnnotAtomicOrGhost _ -> STT_Atomic
    | EffectAnnotSTT -> STT
  in
  let y_tm = tm_var {nm_index=y;nm_ppname=y_ppname} in
  let t = wtag (Some ctag) (Tm_Return {expected_type=tm_unknown;insert_eq=false;term=y_tm}) in
  let c = comp_return ctag false u ty y_tm post_hint.post x in

  assume (comp_u c == post_hint.u); // this u should follow from equality of t
  match c, post_hint.effect_annot with
  | C_STAtomic _ obs st, EffectAnnotAtomic { opens }
  | C_STAtomic _ obs st, EffectAnnotAtomicOrGhost { opens } ->
    assert (comp_inames c == tm_emp_inames);
    let validity = emp_inames_included g opens in
    let c' = C_STAtomic opens obs st in
    (| t, c' |)
  | C_STGhost _ st, EffectAnnotGhost { opens }
  | C_STGhost _ st, EffectAnnotAtomicOrGhost { opens } ->
    assert (comp_inames c == tm_emp_inames);
    let validity = emp_inames_included g opens in
    let c' = C_STGhost opens st in
    (| t, c' |)
  | _ -> 
    (| t, c |)

#push-options "--z3rlimit_factor 4 --ifuel 1 --split_queries always"
#restart-solver
let match_comp_res_with_post_hint (#g:env) (t:st_term) (c:comp_st)
  (post_hint:post_hint_opt g)
  : T.Tac (c':comp_st { comp_pre c' == comp_pre c }) =

  match post_hint with
  | NoHint -> c
  | TypeHint ret_ty
  | PostHint { ret_ty } ->
    let cres = comp_res c in
    if eq_tm cres ret_ty
    then c
    else match Pulse.Typing.Util.check_equiv_now (elab_env g) cres ret_ty with
         | None, issues ->
           let open Pulse.PP in
           fail_doc_with_subissues g (Some t.range) issues [
            prefix 2 1 (text "Could not prove equality between computed type") (pp cres) ^/^
            prefix 2 1 (text "and expected type") (pp ret_ty);
           ]
         | Some tok, _ ->
           let d_equiv
             : RT.equiv _ cres ret_ty =
             RT.Rel_eq_token _ _ _ (FStar.Squash.return_squash tok) in
           
           let c' = with_st_comp c {(st_comp_of_comp c) with res = ret_ty } in


           c'
#pop-options
#pop-options

let apply_checker_result_k (#g:env) (#ctxt:slprop) (#post_hint:post_hint_for_env g)
  (r:checker_result_t g ctxt (PostHint post_hint))
  (res_ppname:ppname)
  : T.Tac (st_typing_in_ctxt g ctxt (PostHint post_hint)) =

  // TODO: FIXME add to checker result type?
  let (| y, g1, (u_ty, ty_y), pre', k |) = r in

  let u_ty_y = Pulse.Checker.Pure.universe_of_well_typed_term g1 ty_y in

  let d : st_typing_in_ctxt g1 pre' (PostHint post_hint) =
    return_in_ctxt g1 y res_ppname u_ty_y ty_y pre' () (PostHint post_hint) in

  k (PostHint post_hint) d

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 0"
//TODO: refactor and merge with continuation_elaborator_with_bind
let checker_result_for_st_typing (#g:env) (#ctxt:slprop) (#post_hint:post_hint_opt g)
  (d:st_typing_in_ctxt g ctxt post_hint)
  (ppname:ppname)
: T.Tac (checker_result_t g ctxt post_hint)
= let (| e1, c1 |) = d in
  let x = fresh g in
  assume (~ (x `Set.mem` freevars (comp_post c1)));
  let u_of_1, pre_typing, post_typing = (), (), () in
  let g' = push_binding g x ppname (comp_res c1) in
  let ctxt' = open_term_nv (comp_post c1) (ppname, x) in
  let k
    : continuation_elaborator g (comp_pre c1) g' ctxt'
    = fun post_hint st_k ->
        let (| e2, c2 |) = st_k in
        let e2_closed = close_st_term e2 x in
        assume (open_st_term e2_closed x == e2);
        if x `Set.mem` freevars (comp_post c2)
        then fail g None "Impossible: freevar clash when constructing continuation elaborator for bind, please file a bug-report"
        else (
          let _ =
            Pulse.Typing.Combinators.bind_res_and_post_typing g c2 x post_hint in
          let (| ee, cc |) =
            Pulse.Typing.Combinators.mk_bind
              g (comp_pre c1)
              e1 e2_closed c1 c2 (ppname, x)
              post_hint
          in
          (| ee, cc |)
        )
  in
  let _ : squash (checker_res_matches_post_hint g post_hint x (comp_res c1) ctxt') =
    match post_hint with
    | PostHint post_hint -> ()
    | _ -> () in
    
  assert (g' `env_extends` g);
  let u_of_1_g' : unit = () in
  assert (~ (x `Set.mem` freevars (comp_post c1)));
  (| x, g', (comp_u c1, comp_res c1), ctxt', k |)
#pop-options

let readback_comp_res_as_comp (c:T.comp) : option comp =
  match c with
  | T.C_Total t -> (
    match readback_comp t with
    | None -> None
    | Some c -> Some c
  )
  | _ -> None

#push-options "--ifuel 1"
let rec is_stateful_arrow (g:env) (c:option comp) (args:list T.argv) (out:list T.argv)
  : T.Tac (option (list T.argv & T.argv))
  = let open R in
    match c with
    | None -> None
    | Some (C_ST _)
    | Some (C_STGhost _ _)
    | Some (C_STAtomic _ _ _) -> (
      match args, out with
      | [], hd::tl -> Some (List.rev tl, hd)
      | _ -> None //leftover or not enough args
    )

    | Some (C_Tot c_res) -> (
      let ht = T.inspect c_res in
      match ht with
      | T.Tv_Arrow b c -> (
        match args with
        | [] -> ( //no more args; check that only implicits remain, ending in an stateful comp  
          let bs, c = T.collect_arr_ln_bs c_res in
          if List.Tot.for_all (fun b -> R.Q_Implicit? (R.inspect_binder b).qual) bs
          then is_stateful_arrow g (readback_comp_res_as_comp (R.inspect_comp c)) [] out
          else None //too few args    
        )

        | (arg, qual)::args' -> ( //check that this arg qual matches the binder and recurse accordingly
          let bqual =
            (* Ignore equality qualifiers in the binder *)
            match b.qual with
            | Q_Equality -> Q_Explicit
            | q -> q
          in
          match bqual, qual with
          | T.Q_Meta _, T.Q_Implicit
          | T.Q_Implicit, T.Q_Implicit 
          | T.Q_Explicit, T.Q_Explicit ->  //consume this argument
            is_stateful_arrow g (readback_comp_res_as_comp c) args' ((arg, qual)::out)

          | T.Q_Meta _, T.Q_Explicit
          | T.Q_Implicit, T.Q_Explicit -> 
            //don't consume this argument
            is_stateful_arrow g (readback_comp_res_as_comp c) args out

          | _ -> None //incompatible qualifiers; bail
        )
      )
      | _ ->
        let c_res' = RU.whnf_lax (elab_env g) c_res in
        let ht = T.inspect c_res' in
        if T.Tv_Arrow? ht
        then (
          let c_res' = wr c_res' (T.range_of_term c_res') in
          is_stateful_arrow g (Some (C_Tot c_res')) args out
        )
        else None
    )
#pop-options

let checker_result_t_equiv_ctxt (g:env) (ctxt ctxt' : slprop)
  (post_hint:post_hint_opt g)
  (r : checker_result_t g ctxt post_hint)
: checker_result_t g ctxt' post_hint
= let (| x, g1, t, ctxt_r, k |) = r in
  (| x, g1, t, ctxt_r, k_elab_equiv ctxt' ctxt_r k |)

module RU = Pulse.RuntimeUtils  
let as_stateful_application (e:term) (head:term) (args:list T.argv { Cons? args })
: st_term = mk_term (Tm_ST { t = e; args = [] }) (RU.range_of_term e)

let is_stateful_application (g:env) (e:term) 
: T.Tac (option st_term) = 
  RU.record_stats "Pulse.is_stateful_application" fun _ -> 
  let head, args = T.collect_app_ln e in
  match args with
  | _ :: _ -> (
    match RU.tc_term_phase1 (elab_env g) head false with
    | None, _ -> None
    | Some (_, ht, _), _ -> 
      let head_t = wr ht (T.range_of_term ht) in
      match is_stateful_arrow g (Some (C_Tot head_t)) args [] with 
      | None -> None
      | Some _ -> Some (as_stateful_application e head args)
  )
  | _ -> None

let apply_conversion
      (#g:env) (#e:term) (#eff:FStar.Tactics.V2.tot_or_ghost) (#t0:term)
      (#t1:term)
      (eq:Ghost.erased (RT.related (elab_env g) t0 RT.R_Eq t1))
  : unit
  = ()

open FStar.List.Tot    
module RT = FStar.Reflection.Typing
#push-options "--ifuel 1"
let decompose_app (g:env) (tt:either term st_term)
: T.Tac (option (term & list T.argv & (args:list T.argv{ Cons? args } -> T.Tac (res:either term st_term { Inr? tt ==> Inr? res }))))
= let decompose_st_app (t:st_term)
  : T.Tac (option (term & list T.argv & (args:list T.argv{ Cons? args } -> T.Tac (res:either term st_term { Inr? tt ==> Inr? res }))))
  = match t.term with
    | Tm_ST { t=e; args=st_args } -> (
      let head, args = T.collect_app_ln e in
      match args with 
      | [] -> None
      | _ -> 
        let rebuild (args:list T.argv{Cons? args}) : T.Tac (res:either term st_term { Inr? res }) = 
          let head = RU.mk_app_flat head args t.range in
          Inr <| mk_term (Tm_ST { t=head; args=st_args }) t.range
        in
        Some (head, args, rebuild)
    )
    | _ -> None
  in
  match tt with
  | Inl tt -> (
    match is_stateful_application g tt with
    | Some st_app -> decompose_st_app st_app
    | None -> 
      let head, args = T.collect_app_ln tt in
      let rebuild (args:list T.argv{Cons? args}) : T.Tac (either term st_term) =
        let head = RU.mk_app_flat head args (T.range_of_term tt) in
        Inl head
      in
      Some (head, args, rebuild)
  )
  | Inr st -> decompose_st_app st
#pop-options

let anf_binder name = T.pack (T.Tv_FVar (T.pack_fv (Pulse.Reflection.Util.mk_pulse_lib_core_lid (Printf.sprintf "__%s_binder__" name))))

let fresh_anf_name (g:env) : T.Tac (env & string) =
  let g, id = Pulse.Typing.Env.fresh_anf g in
  let nm = Printf.sprintf "__anf%d" id in
  g, nm

let bind_st_term (g:env) (s:st_term) 
: T.Tac (env & binder & var & term)
= let open Pulse.Syntax in
  let g, anf_name = fresh_anf_name g in
  let b = {
    binder_ty = tm_unknown;
    binder_ppname = mk_ppname (FStar.Reflection.Typing.seal_pp_name anf_name) s.range;
    binder_attrs = FStar.Sealed.seal [anf_binder anf_name]; // What is this for?
  } in
  let x = Pulse.Typing.Env.fresh g in
  let g = Pulse.Typing.Env.push_binding g x b.binder_ppname b.binder_ty in
  g, b, x, RT.var_as_term x

let rec maybe_hoist (g:env) (arg:T.argv)
: T.Tac (env & list (binder & var & st_term) & T.argv)
= let t, q = arg in
  let head, args = T.collect_app_ln t in
  match args with
  | [] -> g, [], arg //no args to hoist
  | _ ->
  match is_stateful_application g t with
  | None -> (
    let g, binders, args = maybe_hoist_args g args in
    match binders with
    | [] -> g, [], arg // no elab
    | _ -> 
      let t = RU.mk_app_flat head args (T.range_of_term t) in
      g, binders, (t, q)
  )
  | Some _ -> (
    let g, binders, args = maybe_hoist_args g args in
    if Cons? args 
    then (
      let st_app = as_stateful_application t head args  in
      let g, b, x, t = bind_st_term g st_app in
      let arg = t, q in
      g, binders@[b, x, st_app], arg
    )
    else T.fail "Impossible: is_stateful_application returned true but no args to hoist"
  )

and maybe_hoist_args (g:env) (args:list T.argv)
: T.Tac (env & list (binder & var & st_term) & list T.argv)
= T.fold_right
    (fun arg (g, binders, args) ->
      let g, binders', arg = maybe_hoist g arg in
      let binders = binders' @ binders in
      g, binders, arg::args)
    args
    (g, [], [])

#push-options "--ifuel 1"
let maybe_hoist_top 
  (hoist_top_level:bool)
  (g:env)
  (tt:either term st_term)
: T.Tac (env & list (binder & var & st_term) & res:either term st_term { 
    (if hoist_top_level then Inl? res else tt==res)
    })
= if not hoist_top_level then g, [], tt
  else (
    match tt with
    | Inl _ -> g, [], tt
    | Inr st -> 
      let g, b, x, t = bind_st_term g st in 
      g, [(b, x, st)], Inl t
  )

let hoist_stateful_apps
  (g:env)
  (tt:either term st_term)
  (hoist_top_level:bool)
  (context: (
    x:either term st_term { 
      (Inr? tt ==> Inr? x) /\
      (hoist_top_level /\ Inl? tt ==> Inl? x)
    } -> T.Tac st_term))
: T.Tac (option st_term)
= match decompose_app g tt with
  | None -> None
  | Some (head, args, rebuild) ->
    let _, binders, args = maybe_hoist_args g args in
    match args with
    | [] -> None
    | _ ->
      let tt' = rebuild args in
      let _, binders', tt' = maybe_hoist_top (hoist_top_level && Inl? tt) g tt' in 
      let binders = binders @ binders' in
      match binders with
      | [] -> (
        match tt, tt' with
        | Inl _, Inr _ -> (
          Some (context tt') //we at least elaborated a pure term to an inpure term
        )
        | _ -> None //No elaboration
      )
      | _ ->
        let bind_term = context tt' in
        let res = List.Tot.fold_right
          (fun (b, v, arg) body -> 
            let body = Pulse.Syntax.Naming.close_st_term body v in
            mk_term (Tm_Bind { binder = b; head = arg; body = body }) bind_term.range)
          binders
          bind_term
        in
        Some res

let hoist_st_lambda
  (g:env)
  (tt:either term st_term)
  (hoist_top_level:bool)
  (context: (
    x:either term st_term { 
      (Inr? tt ==> Inr? x) /\
      (hoist_top_level /\ Inl? tt ==> Inl? x)
    } -> T.Tac st_term))
: T.Tac (option st_term)
= match tt with
  | Inr { term = Tm_ST { t = e; args = arg::args }; range } -> (
    let _, e_ty, _ = CP.tc_term_phase1 g e in
    match R.inspect_ln e_ty with
    | R.Tv_Arrow bv _ ->
      let bv = R.inspect_binder bv in
      // TODO: check that bv.sort has no uvars
      let n = T.unseal bv.ppname in
      // NOTE: currently the only way to annotate the type of a lambda is to add
      // an extra binder with the ascription
      let g, b, x, t = bind_st_term g
        (mk_term (Tm_Abs {
          b = null_binder tm_unit;
          q = None;
          ascription = {
            annotated = Some (C_Tot bv.sort);
            elaborated = None;
          };
          body = arg;
        }) arg.range) in
      Some <|
        mk_term (Tm_Bind {
          binder = mk_binder n arg.range tm_unknown;
          head = mk_term (Tm_Abs {
            b = null_binder tm_unit;
            q = None;
            ascription = {
              annotated = Some (C_Tot bv.sort);
              elaborated = None;
            };
            body = arg;
          }) arg.range;
          body = Pulse.Syntax.Naming.close_st_term
            (context <| Inr <|
              { Inr?.v tt with
                term = Tm_ST {
                  t = R.mk_app e [R.mk_app t [unit_const, R.Q_Explicit], R.Q_Explicit];
                  args;
                }
              }) x;
        }) range
    | _ ->
      fail_doc g (Some (RU.range_of_term e)) [
        text "Expected function";
        text "Actual type:" ^^ hardline ^^
          pp e_ty
      ]
    )
  | _ -> None

let hoist
  (g:env)
  (tt:either term st_term)
  (hoist_top_level:bool)
  (context: (
    x:either term st_term { 
      (Inr? tt ==> Inr? x) /\
      (hoist_top_level /\ Inl? tt ==> Inl? x)
    } -> T.Tac st_term))
: T.Tac (option st_term)
= match hoist_stateful_apps g tt hoist_top_level context with
  | Some hoisted -> Some hoisted
  | None -> hoist_st_lambda g tt hoist_top_level context
 
let compose_checker_result_t 
  (#g:env) (#g':env { g' `env_extends` g }) (#ctxt #ctxt':slprop) (#post_hint:post_hint_opt g)
  (r1:checker_result_t g ctxt NoHint)
  (r2:checker_result_t g' ctxt' post_hint { composable r1 r2 })
: T.Tac (checker_result_t g ctxt post_hint)
= let (| x1, g1, t1, ctxt1, k1 |) = r1 in
  let (| x2, g2, t2, ctxt2, k2 |) = r2 in
  let k = k_elab_trans k1 k2 in
  (| x2, g2, t2, ctxt2, k |)
