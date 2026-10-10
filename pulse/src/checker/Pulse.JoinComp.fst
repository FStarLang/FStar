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

module Pulse.JoinComp

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open Pulse.Checker.Prover.Normalize
open Pulse.Reflection.Util
open Pulse.Typing.Env
open FStar.List.Tot
open Pulse.Show
module T = FStar.Tactics.V2
module MKeys = Pulse.Checker.Prover.Match.MKeys
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils

let mk_l_exists (u:R.universe) (ty:R.term) (p:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv R.exists_qn) [u]) in
  let hd = R.pack_ln (R.Tv_App hd (ty, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App hd (p, R.Q_Explicit))

let mk_and (l r:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_FVar (R.pack_fv R.and_qn)) in
  R.mk_app hd [(l, R.Q_Explicit); (r, R.Q_Explicit)]

(* Split [post] into the list of pure propositions mentioning [y] and the
   remainder of [post] (with those propositions removed).

   Returns [None] if [y] occurs anywhere else than in a pure proposition, i.e.,
   if [y] is constrained by an actual slprop of [post]. *)
let rec split_pure_deps (y:var) (post:slprop)
: T.Tac (option (list term & slprop))
= if not (y `Set.mem` freevars post) then Some ([], post)
  else
    match inspect_term post with
    | Tm_Star l r -> (
      match split_pure_deps y l with
      | None -> None
      | Some (pl, l') ->
        match split_pure_deps y r with
        | None -> None
        | Some (pr, r') -> Some (pl@pr, tm_star l' r')
    )
    | Tm_Pure p -> Some ([p], tm_emp)
    | Tm_WithPure p n body -> (
      (* The body lives under a (proof-irrelevant) [squash p] binder; open it,
         as the prover itself does, so that we can look inside. *)
      let body = open_term' body unit_const 0 in
      match split_pure_deps y body with
      | None -> None
      | Some (ps, body') ->
        if y `Set.mem` freevars p
        then Some (p::ps, body')
        else Some (ps, tm_with_pure p n body')
    )
    | _ -> None

(* Hoist the [exists*] of [post] to prenex position, opening their binders with
   fresh variables. Returns the hoisted binders, outermost first, together with
   the quantifier-free body. *)
let rec hoist_exists (g:env) (post:slprop)
: T.Tac (env & list (universe & binder & var) & slprop)
= match inspect_term post with
  | Tm_Star l r ->
    let g, bsl, l = hoist_exists g l in
    let g, bsr, r = hoist_exists g r in
    g, bsl@bsr, tm_star l r
  | Tm_ExistsSL u b body ->
    let x = fresh g in
    let g = push_binding g x b.binder_ppname b.binder_ty in
    let body = open_term_nv body (b.binder_ppname, x) in
    let g, bs, body = hoist_exists g body in
    g, (u, b, x)::bs, body
  | Tm_WithPure p n body ->
    let g, bs, body = hoist_exists g (open_term' body unit_const 0) in
    g, bs, tm_with_pure p n body
  | _ -> g, [], post

(* Inverse of [hoist_exists]; binders that became unused are dropped, since an
   [exists*] with an unused binder would need a witness for no reason. *)
let rec close_hoisted_exists (bs:list (universe & binder & var)) (post:slprop)
: T.Tac slprop
= match bs with
  | [] -> post
  | (u, b, x)::bs ->
    let post = close_hoisted_exists bs post in
    if not (x `Set.mem` freevars post)
    then post
    else tm_exists_sl u b (close_term post x)

let rec close_post x_ret dom_g g1 (bs1:env_bindings) (post:slprop)
: T.Tac slprop
= let quantify_pure_deps (n:ppname) (y:var) (ty:typ) (u:universe)
                         (preds:list term) (rest:slprop)
  : T.Tac slprop
  = match preds with
    | [] -> rest
    | p::ps ->
      let pred = List.Tot.fold_left mk_and p ps in
      let abs =
        mk_abs_with_name_and_range n.name n.range ty R.Q_Explicit (close_term pred y) in
      tm_star (tm_pure (mk_l_exists u ty abs)) rest
  in
  let maybe_close ((n, y, ty) : ppname & var & typ) (post:slprop) = 
    if not (y `Set.mem` freevars post) then post
    else (
      let u = Pulse.Checker.Pure.universe_of_well_typed_term g1 ty in
      let fallback () =
        let b = {binder_ty=ty; binder_ppname=n; binder_attrs=[]} in
        tm_exists_sl u b (close_term post y)
      in
      (* If [y] is not constrained by any slprop, an [exists*] over it leaves
         the prover with no way of finding a witness. Push the quantifier into
         the pure propositions instead, where the SMT solver can discharge it.
         If the pure propositions mentioning [y] are spread across nested
         [exists*], first hoist those to prenex position. *)
      match split_pure_deps y post with
      | Some (p::ps, rest) -> quantify_pure_deps n y ty u (p::ps) rest
      | _ ->
        let _, bs, body = hoist_exists g1 post in
        begin match bs, split_pure_deps y body with
        | _::_, Some (p::ps, rest) ->
          close_hoisted_exists bs (quantify_pure_deps n y ty u (p::ps) rest)
        | _ -> fallback ()
        end
    )
  in
  let maybe_elim_rewrites_to pr (post:term) : T.Tac term =
    let n, property = pr in
    let open R in
    let hd, args = T.collect_app_ln property in
    match T.inspect_ln hd, args with
    | Tv_UInst hd [u], [(typ, Q_Implicit); (lhs, Q_Explicit); (rhs, Q_Explicit)] ->
      if T.inspect_fv hd = rewrites_to_p_lid
      then (
        match T.inspect_ln lhs with
        | Tv_Var n1 ->
          let n1 = inspect_namedv n1 in
          if n1.uniq = x_ret then
            tm_with_pure (RT.eq2 u typ lhs rhs) n post
          else
            Pulse.Syntax.Naming.subst_term post [RT.NT n1.uniq rhs]
        | _ -> 
          let eq = RT.eq2 u typ lhs rhs in
          tm_with_pure eq n post
      )
      else tm_with_pure property n post
    | _ -> tm_with_pure property n post
  in
  let close_post = close_post x_ret dom_g g1 in
  match bs1 with
  | [] -> post
  | BindingVar {n;x=y;ty}::tl -> (
    if y = x_ret
    then close_post tl post
    else if y `Set.mem` dom_g
    then close_term post x_ret
    else (
      let open R in
      match T.inspect_ln ty with
      | Tv_App hd (p, Q_Explicit) -> (
        match T.inspect_ln hd with
        | Tv_FVar fv ->
          if inspect_fv fv = R.squash_qn
          then
            (* [y] is a hypothesis, but the post may still mention [y] itself;
               quantify it in that case so that it does not escape. *)
            close_post tl (maybe_close (n,y,ty) (maybe_elim_rewrites_to (n, p) post))
          else close_post tl (maybe_close (n,y,ty) post)
        | _ -> close_post tl (maybe_close (n,y,ty) post)
      )
      | _ -> close_post tl (maybe_close (n,y,ty) post)
    )
  )
  | _::tl -> close_post tl post

let rec bindings_var_dom : env_bindings -> Set.set var = function
  | [] -> Set.empty
  | BindingVar {x} :: bs -> Set.add x (bindings_var_dom bs)
  | _ :: bs -> bindings_var_dom bs

let var_dom (g: env) : Set.set var = bindings_var_dom (bindings g)

let infer_post' (g:env) (g':env { g' `env_extends` g })
  (u:universe) (t:typ) (x: var { lookup g' x == Some t })
  (post:term)
=
  // simplify post by applying elimination rules (particularly `frame ** is_unreachable ~~> is_unreachable`)
  let (| g1, post, _ |) = Pulse.Checker.Prover.elim_exists_and_pure #g' #post in
  let bs0 = bindings g in
  let dom_g = var_dom g in
  let fvs_t = freevars t in
  let fail_fv_typ (x:string) 
  : T.Tac unit =
    fail_doc g (Some (T.range_of_term t))
        [Pulse.PP.text "Could not infer a type for this block; the return type `";
          Pulse.PP.text (T.term_to_string t); 
          Pulse.PP.text "` contains free variable ";
          Pulse.PP.text x;
          Pulse.PP.text " that escape its environment"]
  in
  let mk_post_hint (post:term) : T.Tac (p:post_hint_for_env g {p.g==g /\ p.effect_annot == EffectAnnotSTT }) = 
    let u = Pulse.Checker.Pure.check_universe g t in
    let x = fresh g in
    let post' = open_term_nv post (ppname_default, x) in 
    let g' = push_binding g x ppname_default t in
    assume (fresh_wrt x g (freevars post));
    {
      g; effect_annot=EffectAnnotSTT;
      ret_ty=t; u;
      post
    }
  in
  let post = RU.beta_lax (elab_env g) post in // clean up spurious dependencies on variables
  let post = RU.deep_compress post in
  let close_post =
    if post `eq_tm` tm_is_unreachable then post else
    close_post x dom_g g1 (bindings g1) post in
  Pulse.Checker.Util.debug g "pulse.infer_post" (fun _ ->
    Printf.sprintf "Original postcondition: %s |= %s\nInferred postcondition: %s |= %s\n" 
    (env_to_string g1) (T.term_to_string post) (env_to_string g) (T.term_to_string close_post));
  let ph = mk_post_hint close_post in
  admit ();
  ph

let mk_imp lhs rhs =
  let open R in
  let hd = R.pack_ln (Tv_FVar (R.pack_fv R.imp_qn)) in
  R.mk_app hd [(lhs, Q_Explicit); (rhs, Q_Explicit)]

let rec guard_pures then_ b (ps:list slprop) 
: list slprop & list slprop
= let guard_pure pp =
    let def () = 
      let payload =
        if then_ then mk_imp (RT.eq2 u0 tm_bool b tm_true) pp
        else mk_imp (RT.eq2 u0 tm_bool b tm_false) pp
      in
      pack_term_view (Tm_Pure payload) (T.range_of_term pp)
    in    
    let hd, args = T.collect_app_ln pp in
    match R.inspect_ln hd, args with
    | R.Tv_UInst _ _, [(ty, _); _; _] -> //no need to retain unit equalities
      if FStar.Reflection.TermEq.term_eq hd (`(Prims.eq2 u#0))
      && FStar.Reflection.TermEq.term_eq ty (`Prims.unit)
      then tm_emp
      else def()
    | _ -> def ()
  in
  let guard_pures = guard_pures then_ in
  match ps with
  | [] -> [], []
  | p::ps -> (
    match inspect_term p with
    | Tm_Pure pp -> (
      let pure = guard_pure pp in
      let pures, ps = guard_pures b ps in
      pure::pures, ps
    )
  
    | _ ->
      let pures, ps = guard_pures b ps in
      pures, p::ps
  )

let may_match g (p:slprop) (q:slprop) = MKeys.eligible_for_smt_equality g p q

(* Pair [p] with a conjunct of [qs]. An identical conjunct is preferred:
   [may_match] holds for any two applications of a predicate without
   matching keys, and pairing such a [p] with the first one in [qs] would
   join, say, [cell r] with [cell s] (whose types may differ) when the other
   branch lists the same cells in another order. *)
let find_match g (p:slprop) (qs:list slprop)
: T.Tac (list (slprop & slprop) & list slprop & list slprop)
= let rec exact qs rest
  : T.Tac (option (slprop & list slprop))
  = match qs with
    | [] -> None
    | q::qs ->
      if T.term_eq p q
      then Some (q, rev_acc rest qs)
      else exact qs (q::rest)
  in
  match exact qs [] with
  | Some (q, rest) -> [p,q], [], rest
  | None ->
  let rec aux qs rest 
  : T.Tac (list (slprop & slprop) & list slprop & list slprop)
  = match qs with
    | [] -> [], [p], rest

    | q::qs ->
      if may_match g p q 
      then [p,q], [], qs@rest
      else (
        match inspect_term p, inspect_term q with
        | Tm_Pure _, Tm_Pure _ -> [p,q], [], qs@rest
        | _ -> aux qs (q::rest)
      )
  in
  aux qs []

let partition_matches g (ps qs:list slprop)
: T.Tac (list (slprop & slprop) & list slprop & list slprop)
= T.fold_right 
    (fun p (matches, remaining_ps, remaining_qs) ->
      let matches', remaining_ps', remaining_qs = find_match g p remaining_qs in
      matches'@matches, remaining_ps'@remaining_ps, remaining_qs)
    ps ([], [], qs)

let rec combine_terms top g b pq : T.Tac term =
  let p, q = pq in
  Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf "Combine terms %s and %s\n" (show p) (show q)
  );
  let pack t = pack_term_view t (T.range_of_term p) in
  let combine_terms p q = combine_terms true g b (p, q) in
  let def () = if T.term_eq p q then p else RT.mk_if b p q in
  match inspect_term p, inspect_term q with
  | Tm_IsUnreachable, _ -> q
  | _, Tm_IsUnreachable -> p
  | Tm_Emp, Tm_Emp
  | Tm_SLProp, Tm_SLProp
  | Tm_EmpInames, Tm_EmpInames
  | Tm_Inames, Tm_Inames -> p
  | Tm_Pure f1, Tm_Pure f2 ->
    let f = RT.mk_if b f1 f2 in
    pack <| Tm_Pure f
  | Tm_Inv i1 p1, Tm_Inv i2 p2 ->
    pack <| Tm_Inv (combine_terms i1 i2) (combine_terms p1 p2)
  | Tm_FStar f1, Tm_FStar f2 -> (
    if not top then def () else
    let hd1, args1 = T.collect_app_ln f1 in
    let hd2, args2 = T.collect_app_ln f2 in //not proving termination because collect_app_ln's type is not strong enough
    Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
      Printf.sprintf "Destructed\nlhs as %s [%s]\nrhs as %s [%s]"
        (show hd1) (show args1)
        (show hd2) (show args2)
    );
    if T.term_eq hd1 hd2
    then T.mk_app hd1 (combine_args g b args1 args2)
    else def ()
  )
  | _ -> def ()

and combine_args g b (args1 args2:list R.argv) : T.Tac (list R.argv) =
  //combinine args, when heads are equal, 
  //the quals must be equal and the lengths must be equal
  match args1, args2 with
  | (a1, v1)::args1, (a2, v2)::args2 ->
    (combine_terms true g b (a1, a2), v1)::combine_args g b args1 args2
  | _ -> []

let guard_with_pure then_ b (pred: term) n (acc: slprop) : slprop =
  match inspect_term acc with
  | Tm_IsUnreachable -> acc
  | _ ->
    tm_with_pure
      (mk_imp (RT.eq2 u0 tm_bool b (if then_ then tm_true else tm_false)) pred)
      n acc

(* Guard every pure fact of a branch's postcondition by the condition under
   which that branch was taken, so that the other branch can prove it too. *)
let rec guard_branch_slprop (then_:bool) (b:term) (p:slprop) : T.Tac slprop =
  match inspect_term p with
  | Tm_WithPure pred n body ->
    guard_with_pure then_ b pred n (guard_branch_slprop then_ b body)
  | Tm_ExistsSL u bnd body ->
    tm_exists_sl u bnd (guard_branch_slprop then_ b body)
  | Tm_Star l r ->
    tm_star (guard_branch_slprop then_ b l) (guard_branch_slprop then_ b r)
  | Tm_Pure _ -> (
    match fst (guard_pures then_ b [p]) with
    | [q] -> q
    | _ -> p
  )
  | _ -> p

let guard_branch_post #g (b:term) (then_:bool) (p:post_hint_for_env g)
: T.Tac (q:post_hint_for_env g { q.effect_annot == p.effect_annot })
= let x = fresh g in
  let post = open_term_nv p.post (ppname_default, x) in
  let post = guard_branch_slprop then_ b post in
  { p with post = close_term post x }

let is_emp (p:slprop) : bool =
  match inspect_term p with
  | Tm_Emp -> true
  | _ -> false

(* Does [t] mention none of the variables in [xs]? *)
let indep_of (xs:list var) (t:term) : bool =
  let fvs = freevars t in
  List.Tot.for_all (fun x -> not (x `Set.mem` fvs)) xs

(* Strip a branch's postcondition down to a flat list of conjuncts, collecting
   the [exists*] binders and [with_pure] guards it sat under. Both wrappers
   distribute over [**] in the direction a join needs:

     exists* x. (A ** R x)  |-  A ** (exists* x. R x)    (x not free in A)
     with_pure p (A ** R)   |-  A ** with_pure p R

   so any conjunct returned here that does not mention a hoisted variable may
   be moved out of the wrappers, and hence out of the conditional. *)
let rec hoist_binders (g:env) (post:slprop)
: T.Tac (env & list (universe & binder & var) & list (term & ppname) & list slprop)
= match inspect_term post with
  | Tm_Star l r ->
    let g, bs1, gs1, cs1 = hoist_binders g l in
    let g, bs2, gs2, cs2 = hoist_binders g r in
    g, bs1@bs2, gs1@gs2, cs1@cs2
  | Tm_ExistsSL u b body ->
    let x = fresh g in
    let g = push_binding g x b.binder_ppname b.binder_ty in
    let body = open_term_nv body (b.binder_ppname, x) in
    let g, bs, gs, cs = hoist_binders g body in
    g, (u, b, x)::bs, gs, cs
  | Tm_WithPure p n body ->
    (* The body lives under a proof-irrelevant [squash p] binder; open it, as
       the prover does, so we can see the conjuncts inside. *)
    let g, bs, gs, cs = hoist_binders g (open_term' body unit_const 0) in
    g, bs, (p, n)::gs, cs
  | Tm_Emp -> g, [], [], []
  | _ -> g, [], [], [post]

let rec rewrap_guards (gs:list (term & ppname)) (p:slprop) : slprop =
  match gs with
  | [] -> p
  | (pred, n)::gs -> tm_with_pure pred n (rewrap_guards gs p)

(* If [t] is exactly one of the hoisted variables, its binder. *)
let hoisted_binder (bs:list (universe & binder & var)) (t:term)
: option (universe & binder)
= match is_var t with
  | None -> None
  | Some nm ->
    let rec find bs =
      match bs with
      | [] -> None
      | (u, b, x)::bs -> if x = nm.nm_index then Some (u, b) else find bs
    in
    find bs

(* Anti-unify two matched conjuncts that agree except at argument positions
   where each side has one of its own hoisted variables, replacing every such
   position by a single binder quantified outside the conditional:

     exists* x. F .. x ..  |-  exists* z. F .. z ..

   holds of each branch separately, so the result is above both. Returns [None]
   unless the two are of exactly that shape -- same head, same number of
   arguments, and every differing argument a hoisted variable on both sides
   with the same binder type -- in which case the pair stays inside the
   conditional. *)
(* Is [t] a variable of [g], of the same type as [b], mentioning none of [xs]? *)
let same_type_as_binder (g:env) (xs:list var) (b:binder) (t:term) : bool =
  match is_var t with
  | None -> false
  | Some nm ->
    indep_of xs t &&
    (match lookup g nm.nm_index with
     | None -> false
     | Some ty -> T.term_eq ty b.binder_ty)

(* An argument position where the two sides differ in shape, one of them a
   term over its own branch's hoisted variables and the other a term of the
   environment. Example: a cell set under a branch-local test to a value read
   through a branch-local witness, against a cell the other branch left alone
   or set to a constant. Generalize the position over a fresh binder, typed as
   the head's parameter at that position (computed from the type of [pre], the
   head applied to the arguments before it). Both sides are checked against
   that type when their branches are proved against the joined postcondition,
   which instantiates the binder with them. Positions of type [slprop] are left
   alone: generalizing them would forget the resource. *)
let generalize_arg_by_type (g:env) (xs1 xs2:list var) (pre:R.term) (t1 t2:R.term)
: T.Tac (option (env & list (universe & binder & var) & R.term))
= if not ((not (indep_of xs1 t1) && indep_of xs2 t2) ||
          (indep_of xs1 t1 && not (indep_of xs2 t2)))
  then None
  else
    let param_ty : option R.term =
      match RU.try_quietly (fun () -> compute_term_type g pre) with
      | None -> None
      | Some (| _, _, ty |) ->
        match R.inspect_ln_unascribe (RU.whnf_lax (elab_env g) ty) with
        | R.Tv_Arrow b _ -> Some (R.inspect_binder b).sort
        | _ -> None
    in
    match param_ty with
    | None -> None
    | Some ty ->
      if T.term_eq (RU.deep_compress_safe ty) tm_slprop
      then None
      else
        match RU.try_quietly (fun () -> check_universe g ty) with
        | None -> None
        | Some u ->
          let x = fresh g in
          let b = mk_binder_ppname ty ppname_default in
          let g = push_binding g x b.binder_ppname ty in
          Some (g, [(u, b, x)], term_of_no_name_var x)

(* Anti-unify two terms that agree except where each side has one of its own
   hoisted variables, replacing every such position by a single fresh binder,
   returned alongside. Descends through applications, since the interesting
   positions are usually one wrapper down -- an [exists*] binder is erased, so
   what a conjunct actually mentions is [reveal w] rather than [w].

   Returns [None] unless the two are of exactly that shape. *)
let rec generalize_term (g:env)
                        (bs1 bs2:list (universe & binder & var))
                        (xs1 xs2:list var)
                        (t1 t2:R.term)
: T.Tac (option (env & list (universe & binder & var) & R.term))
= if T.term_eq t1 t2 && indep_of xs1 t1 && indep_of xs2 t1
  then Some (g, [], t1)
  else
    match hoisted_binder bs1 t1, hoisted_binder bs2 t2 with
    | Some (u1, b1), Some (u2, b2) ->
      if T.term_eq b1.binder_ty b2.binder_ty
      then
        let x = fresh g in
        let g = push_binding g x b1.binder_ppname b1.binder_ty in
        Some (g, [(u1, b1, x)], term_of_no_name_var x)
      else None
    (* Only one branch bound this position; the other kept whatever was there
       on entry, or computed it from its own hoisted variables (a branch that
       stores [f w] where the other stores its binder [z]). Generalizing over
       both is still an upper bound. We take the type from the binder side
       rather than the typechecker: a variable of the environment is checked
       against it here, and a term over the other branch's own hoisted
       variables is checked when that branch is proved against the joined
       postcondition, which instantiates the new binder with it. *)
    | Some (u1, b1), None ->
      if same_type_as_binder g xs2 b1 t2 || not (indep_of xs2 t2)
      then
        let x = fresh g in
        let g = push_binding g x b1.binder_ppname b1.binder_ty in
        Some (g, [(u1, b1, x)], term_of_no_name_var x)
      else None
    | None, Some (u2, b2) ->
      if same_type_as_binder g xs1 b2 t1 || not (indep_of xs1 t1)
      then
        let x = fresh g in
        let g = push_binding g x b2.binder_ppname b2.binder_ty in
        Some (g, [(u2, b2, x)], term_of_no_name_var x)
      else None
    | _ ->
      let hd1, args1 = T.collect_app_ln t1 in
      let hd2, args2 = T.collect_app_ln t2 in
      if Nil? args1
      || not (T.term_eq hd1 hd2)
      || not (List.Tot.length args1 = List.Tot.length args2)
      then None
      else (
        match generalize_args g bs1 bs2 xs1 xs2 hd1 [] args1 args2 with
        | None -> None
        | Some (g, bs, args) -> Some (g, bs, T.mk_app hd1 args)
      )

and generalize_args (g:env)
                    (bs1 bs2:list (universe & binder & var))
                    (xs1 xs2:list var)
                    (hd:R.term) (pre:list R.argv)
                    (args1 args2:list R.argv)
: T.Tac (option (env & list (universe & binder & var) & list R.argv))
= match args1, args2 with
  | [], [] -> Some (g, [], [])
  | (a1, qual)::args1', (a2, _)::args2' -> (
    let a =
      match generalize_term g bs1 bs2 xs1 xs2 a1 a2 with
      | Some r -> Some r
      | None -> generalize_arg_by_type g xs1 xs2 (T.mk_app hd pre) a1 a2
    in
    match a with
    | None -> None
    | Some (g, bnd, a) -> (
      match generalize_args g bs1 bs2 xs1 xs2 hd (pre @ [(a, qual)]) args1' args2' with
      | None -> None
      | Some (g, bs, args) -> Some (g, bnd@bs, (a, qual)::args)
    )
  )
  | _ -> None

let generalize_pair (g:env)
                    (bs1 bs2:list (universe & binder & var))
                    (xs1 xs2:list var)
                    (p q:slprop)
: T.Tac (option (env & list (universe & binder & var) & slprop))
= match inspect_term p, inspect_term q with
  | Tm_FStar f1, Tm_FStar f2 -> (
    match generalize_term g bs1 bs2 xs1 xs2 f1 f2 with
    | None -> None
    | Some (g, bs, t) ->
      (* Belt and braces: never let a hoisted variable escape its binder, and
         do not accept a generalization that says nothing at all. *)
      if Cons? bs && indep_of xs1 t && indep_of xs2 t
      then Some (g, bs, t)
      else None
  )
  | _ -> None

(* A [with_pure] guard that mentions no hoisted variable can leave the branch,
   as the branch-guarded pure fact it is: [with_pure p q |- pure p ** q]. The
   rest stay where they were. *)
let guard_hoisted_pures (then_:bool) (b:term) (xs:list var) (gs:list (term & ppname))
: T.Tac (list slprop & list (term & ppname))
= let liftable, gs = List.Tot.partition (fun (pred, _) -> indep_of xs pred) gs in
  let as_pure (g:term & ppname) : T.Tac slprop =
    let pred, _ = g in
    pack_term_view (Tm_Pure pred) (T.range_of_term pred)
  in
  let guarded, _ = guard_pures then_ b (T.map as_pure liftable) in
  guarded, gs

(* Does [c] mention a hoisted variable that some other conjunct of its branch
   also mentions? Generalizing [c] would then cut it loose from that conjunct:
   the new binder says nothing about the variable the other conjunct still
   names. [all] lists every conjunct of the branch, [c] among them, and its
   [with_pure] guards: generalizing past a fact about the variable loses the
   fact as well. *)
let shares_hoisted (xs:list var) (all:list term) (c:term) : bool =
  List.Tot.existsb
    (fun x ->
      not (indep_of [x] c) &&
      List.Tot.length (List.Tot.filter (fun t -> not (indep_of [x] t)) all) > 1)
    xs

(* Split the matched pairs into those that can be taken out of the conditional
   -- combined as usual, or generalized over a fresh binder -- and those that
   have to go back into the branch they came from. With [linked], a pair whose
   hoisted variables are shared with other conjuncts of its branch is not
   generalized, so that it stays with them. *)
let rec salvage_matches (linked:bool) (all1 all2:list term)
                        (g:env) (b:term)
                        (bs1 bs2:list (universe & binder & var))
                        (xs1 xs2:list var)
                        (matches:list (slprop & slprop))
: T.Tac (env & list (universe & binder & var) & list slprop & list slprop & list slprop)
= match matches with
  | [] -> g, [], [], [], []
  | (c1, c2)::matches ->
    let salvage_rest g = salvage_matches linked all1 all2 g b bs1 bs2 xs1 xs2 matches in
    if indep_of xs1 c1 && indep_of xs2 c2
    then (
      let c = combine_terms true g b (c1, c2) in
      let g, newbs, lifted, kept1, kept2 = salvage_rest g in
      g, newbs, c::lifted, kept1, kept2
    )
    else (
      let gen =
        if linked && (shares_hoisted xs1 all1 c1 || shares_hoisted xs2 all2 c2)
        then None
        else generalize_pair g bs1 bs2 xs1 xs2 c1 c2
      in
      match gen with
      | Some (g, bs, c) ->
        let g, newbs, lifted, kept1, kept2 = salvage_rest g in
        g, bs@newbs, c::lifted, kept1, kept2
      | None ->
        let g, newbs, lifted, kept1, kept2 = salvage_rest g in
        g, newbs, lifted, c1::kept1, c2::kept2
    )

(* What the branches do not agree on. With no [pick], it stays under the
   condition. Otherwise it is the part of the picked branch alone, with that
   branch's pure facts guarded by its condition. Everything the branches did
   agree on is joined as usual. A caller that picks must still prove the
   result of both branches. *)
let leftover (pick:option bool) (b:term) (p1 p2:slprop) : T.Tac slprop =
  match pick with
  | None -> RT.mk_if b p1 p2
  | Some true -> guard_branch_slprop true b p1
  | Some false -> guard_branch_slprop false b p2

(* Does a conjunct of [p], below its top-level stars, bind or guard
   anything? Such a conjunct has to be opened before the two branches can be
   compared conjunct by conjunct: matched whole, two [with_pure]s that differ
   in a single conjunct would be kept apart entirely. *)
let rec needs_hoist (p:slprop) : T.Tac bool =
  match inspect_term p with
  | Tm_Star l r -> if needs_hoist l then true else needs_hoist r
  | Tm_ExistsSL .. | Tm_WithPure .. -> true
  | _ -> false

let join_hoisted (pick:option bool) (linked:bool) g b (p1 p2:slprop)
: T.Tac slprop
= (* At least one branch's postcondition is existentially quantified or
     guarded by a [with_pure], at the top or below a star. The first is the
     shape a branch takes as soon as it binds the result of a call. Rather
     than give up on the whole thing, strip the binders and guards off
     both sides and salvage what does not depend on them: a conjunct the
     branch never touched comes straight out, and a conjunct that differs
     only in a bound value comes out under a single new binder. What is left
     over -- and only that -- stays under the conditional. *)
  let g1, bs1, gs1, cs1 = hoist_binders g p1 in
  let g2, bs2, gs2, cs2 = hoist_binders g1 p2 in
  let xs1 = List.Tot.map (fun (_, _, x) -> x) bs1 in
  let xs2 = List.Tot.map (fun (_, _, x) -> x) bs2 in
  let matches, cs1, cs2 = partition_matches g2 cs1 cs2 in
  Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf
      "Hoisted %d and %d binders.\nMatches: %s\nRemaining ps=%s\nRemaining qs=%s\n"
        (List.Tot.length bs1)
        (List.Tot.length bs2)
        (show matches)
        (show cs1)
        (show cs2)
  );
  (* Each matched pair either survives the hoisting -- as it stands, or
     generalized over a fresh binder -- or goes back into its own branch. *)
  let all1 = List.Tot.map fst gs1 @ cs1 @ List.Tot.map fst matches in
  let all2 = List.Tot.map fst gs2 @ cs2 @ List.Tot.map snd matches in
  let g2, newbs, lifted, kept1, kept2 =
    salvage_matches linked all1 all2 g2 b bs1 bs2 xs1 xs2 matches in
  if Nil? lifted
  then leftover pick b p1 p2 // nothing was salvaged; keep the term as it was
  else
    (* An unmatched conjunct that mentions no bound variable is still
       one-sided, so it is guarded by the branch condition, exactly as in the
       unquantified case. *)
    let indep1, dep1 = List.Tot.partition (indep_of xs1) (cs1@kept1) in
    let indep2, dep2 = List.Tot.partition (indep_of xs2) (cs2@kept2) in
    let gpures1, gs1 = guard_hoisted_pures true b xs1 gs1 in
    let gpures2, gs2 = guard_hoisted_pures false b xs2 gs2 in
    let pures1, indep1 = guard_pures true b indep1 in
    let pures2, indep2 = guard_pures false b indep2 in
    let pures1 = gpures1@pures1 in
    let pures2 = gpures2@pures2 in
    let rest1 = close_hoisted_exists bs1 (rewrap_guards gs1 (list_as_slprop (indep1@dep1))) in
    let rest2 = close_hoisted_exists bs2 (rewrap_guards gs2 (list_as_slprop (indep2@dep2))) in
    let remaining =
      if is_emp rest1 && is_emp rest2
      then []
      else [leftover pick b rest1 rest2]
    in
    close_hoisted_exists newbs (list_as_slprop (remaining@pures1@pures2@lifted))

let rec join_slprop (pick:option bool) (linked:bool) g b (ex1 ex2:list (universe & binder)) (p1 p2:slprop)
: T.Tac slprop
= match inspect_term p1, inspect_term p2 with
  | Tm_IsUnreachable, _ -> p2
  | _, Tm_IsUnreachable -> p1

  | Tm_WithPure pred1 n1 p1, _ ->
    guard_with_pure true b pred1 n1 <| join_slprop pick linked g b ex1 ex1 p1 p2
  | _, Tm_WithPure pred2 n2 p2 ->
    guard_with_pure false b pred2 n2 <| join_slprop pick linked g b ex1 ex1 p1 p2

  | Tm_ForallSL .., _
  | _, Tm_ForallSL .. ->
    //Not doing anything interesting to share binders
    leftover pick b p1 p2

  | Tm_ExistsSL .., _
  | _, Tm_ExistsSL .. ->
    join_hoisted pick linked g b p1 p2

  | _ ->
    if needs_hoist p1 || needs_hoist p2
    then join_hoisted pick linked g b p1 p2
    else
    let open Pulse.Show in
    let p1s, p2s = slprop_as_list p1, slprop_as_list p2 in
    let matches, p1s, p2s = partition_matches g p1s p2s in
    Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
      Printf.sprintf
        "Matches: %s\nRemaining ps=%s\nRemaining qs=%s\n"
          (show matches)
          (show p1s)
          (show p2s)
    );
    let matched = T.map (fun x -> combine_terms true g b x) matches in
    let pures1, p1s = guard_pures true b p1s in
    let pures2, p2s = guard_pures false b p2s in
    match p1s, p2s with
    | [], [] -> list_as_slprop (pures1@pures2@matched)
    | _ ->
      let remaining = leftover pick b (list_as_slprop p1s) (list_as_slprop p2s) in
      list_as_slprop (remaining::pures1@pures2@matched)

let join_post_candidate (pick:option bool) (linked:bool) #g #hyp #b
    (p1:post_hint_for_env (g_with_eq g hyp b tm_true))
    (p2:post_hint_for_env (g_with_eq g hyp b tm_false))
: T.Tac term
= Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf "Joining postconditions:\n%s\nand\n%s\n"
      (T.term_to_string p1.post)
      (T.term_to_string p2.post)
  );
  let x = fresh g in
  let g' = push_binding g x ppname_default p1.ret_ty in
  let p1_post = open_term_nv p1.post (ppname_default, x) in
  let p1_post = normalize_slprop g' p1_post true in
  let p2_post = open_term_nv p2.post (ppname_default, x) in
  let p2_post = normalize_slprop g' p2_post true in
  let joined_post = join_slprop pick linked g' b [] [] p1_post p2_post in
  let joined_post = close_term joined_post x in
  Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf "Inferred joint postcondition:\n%s\n"
      (T.term_to_string joined_post)
  );
  joined_post

let st_ghost_as_atomic_matches_post_hint
  (c:comp { C_STGhost? c })
  (post:post_hint_t { EffectAnnotAtomicOrGhost? post.effect_annot })
  : Lemma (requires comp_post_matches_hint c (PostHint post))
          (ensures comp_post_matches_hint (st_ghost_as_atomic c) (PostHint post)) = ()

(* This matches the effects of the two branches, without
necessarily matching inames. *)
#push-options "--z3rlimit_factor 8"
#restart-solver
open Pulse.Checker.Base
(* NB: g_then and g_else are equal except for containing one extra
hypothesis according to which branch was taken. *)
let rec join_comps
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (post:post_hint_t)
  : T.TacH comp_st
         (requires
            comp_post_matches_hint c_then (PostHint post) /\
            comp_post_matches_hint c_else (PostHint post) /\
            comp_pre c_then == comp_pre c_else)
         (ensures fun c ->
           st_comp_of_comp c == st_comp_of_comp c_then /\
           comp_post_matches_hint c (PostHint post))
= let g = g_then in
  assert (st_comp_of_comp c_then == st_comp_of_comp c_else);
  match c_then, c_else with
  | C_STAtomic inames obs1 st, C_STAtomic _ obs2 _ ->
    let obs = join_obs obs1 obs2 in
    let c = C_STAtomic inames obs st in


    c
  | C_STGhost _ _, C_STGhost _ _
  | C_STDiv _, C_STDiv _
  | C_ST _, C_ST _ -> c_then

  | _ ->
    assert (EffectAnnotAtomicOrGhost? post.effect_annot);
    match c_then, c_else with
    | C_STGhost _ _, C_STAtomic _ _ _ ->

      st_ghost_as_atomic_matches_post_hint c_then post;
      join_comps g_then e_then (st_ghost_as_atomic c_then) g_else e_else c_else post

    | C_STAtomic _ _ _, C_STGhost _ _ ->

      st_ghost_as_atomic_matches_post_hint c_else post;
      join_comps g_then e_then c_then g_else e_else (st_ghost_as_atomic c_else) post
#pop-options
