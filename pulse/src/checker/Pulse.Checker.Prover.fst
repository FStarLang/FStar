(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.Prover
open Pulse.Checker.Base
open Pulse.Checker.Pure
open Pulse.Typing.Combinators
open Pulse.Typing
open Pulse.Show
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Syntax.Naming
open Pulse.Checker.Prover.Util
open Pulse.Checker.Prover.Normalize
open FStar.List { (@) }
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2

type head_id =
  | FVarHead of R.name
  | VarHead of nat
  | MatchHead

instance show_head_id : tac_showable head_id = {
  show = (function 
    | FVarHead x -> Printf.sprintf "(FVar %s)" (show x)
    | VarHead i -> Printf.sprintf "(Var %d)" i
    | MatchHead -> "<match>")
}
noeq type slprop_view =
  | Pure : term -> slprop_view
  | WithPure : term -> ppname -> body: term -> slprop_view // body is opened with ()
  | Exists : u: universe -> b: binder -> body: term -> slprop_view
  | Atom : head: head_id -> mkeys: option (list term) -> t: slprop -> slprop_view
  | Unknown : slprop -> slprop_view

instance showable_slprop_view : tac_showable slprop_view = {
  show = (function
  | Pure p -> Printf.sprintf "(Pure %s)" (show p)
  | WithPure t x b -> Printf.sprintf "(WithPure %s %s %s)" (show t) (show (T.unseal x.name)) (show b)
  | Exists u x b -> Printf.sprintf "(exists* (%s). %s)" (Pulse.Syntax.Printer.binder_to_string x) (show b)
  | Atom head keys t -> Printf.sprintf "(Atom {head=%s; keys=%s} %s)" (show head) (show keys) (show t)
  | Unknown p -> Printf.sprintf "(Unknown %s)" (show p)
  );
}

let elab_slprop (p: slprop_view) : slprop =
  match p with
  | Pure p -> tm_pure p
  | Exists u b body -> tm_exists_sl u b body
  | Atom _ _ t -> t
  | WithPure p n b -> tm_with_pure p n b
  | Unknown p -> p

let rec elab_slprops (ps: list slprop_view) : slprop =
  match ps with
  | [] -> tm_emp
  | [p] -> elab_slprop p
  | p::ps -> elab_slprop p `tm_star` elab_slprops ps

let slprop_eqv (p q: slprop) : prop =
  forall g. squash (slprop_equiv g p q)

let slprop_eqv_intro #p #q (h: (g:env -> slprop_equiv g p q)) : squash (slprop_eqv p q) = admit ()
let slprop_eqv_refl (p: slprop) : squash (slprop_eqv p p) = slprop_eqv_intro fun g -> VE_Refl g p
let slprop_eqv_trans (p q r: slprop) : Lemma (requires slprop_eqv p q /\ slprop_eqv q r) (ensures slprop_eqv p r) = admit ()
let slprop_eqv_star p1 q1 p2 q2 : Lemma (requires slprop_eqv p1 p2 /\ slprop_eqv q1 q2) (ensures slprop_eqv (tm_star p1 q1) (tm_star p2 q2)) = admit ()
let elab_slprops_append ps qs : squash (elab_slprops (ps@qs) `slprop_eqv` (elab_slprops ps `tm_star` elab_slprops qs)) = admit ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit_factor 4"
#restart-solver
let rec inspect_slprop (g: env) (p: slprop) : T.Tac (v:list slprop_view { elab_slprops v `slprop_eqv` p }) =
  slprop_eqv_refl p;
  match inspect_term p with
  | Tm_Pure p -> [Pure p]
  | Tm_WithPure a n b ->
    assume tm_with_pure a n (open_term' b unit_const 0) `slprop_eqv` p;
    [WithPure a n (open_term' b unit_const 0)]
  | Tm_ExistsSL u b body -> [Exists u b body]
  | Tm_Emp -> []
  | Tm_Star a b ->
    let a' = inspect_slprop g a in
    let b' = inspect_slprop g b in
    elab_slprops_append a' b'; assert elab_slprops (a' @ b') `slprop_eqv` (elab_slprops a' `tm_star` elab_slprops b');
    slprop_eqv_star (elab_slprops a') (elab_slprops b') a b; assert (elab_slprops a' `tm_star` elab_slprops b') `slprop_eqv` tm_star a b;
    slprop_eqv_trans (elab_slprops (a' @ b')) (elab_slprops a' `tm_star` elab_slprops b') (tm_star a b); assert elab_slprops (a' @ b') `slprop_eqv` tm_star a b;
    a' @ b'
  | _ ->
    match T.hua p with
    | Some (h, _, _) ->
      let h = R.inspect_fv h in
      let mkeys = Pulse.Checker.Prover.Match.MKeys.get_mkeys g p in
      [Atom (FVarHead h) mkeys p]
    | None ->
      let hd, _ = R.collect_app_ln p in
      match R.inspect_ln hd with
      | R.Tv_Var x ->
        let x = R.inspect_namedv x in
        [Atom (VarHead x.uniq) None p]
      | _ ->
        match R.inspect_ln p with
        | R.Tv_Match sc _ _ ->
          let sc = RU.deep_compress_safe sc in
          if RU.no_uvars_in_term sc then
            [Atom MatchHead (Some [sc]) p]
          else
            [Unknown p]
        | _ ->
          [Unknown p]
#pop-options

let cont_elab g ps g' ps' =
  frame: list slprop_view -> continuation_elaborator g (elab_slprops (frame @ ps)) g' (elab_slprops (frame @ ps'))

let cont_elab_refl g ps ps' (h: slprop_equiv g (elab_slprops ps) (elab_slprops ps')) : cont_elab g ps g ps' = 
  fun frame -> k_elab_equiv (k_elab_unit g (elab_slprops (frame @ ps))) (VE_Refl _ _) (RU.magic ())

let cont_elab_trans #g1 (#g2: env { g2 `env_extends` g1 }) (#g3: env { g3 `env_extends` g2 }) #ps1 #ps2 #ps2' #ps3
    (k1: cont_elab g1 ps1 g2 ps2)
    (k2: cont_elab g2 ps2' g3 ps3)
    (h: slprop_equiv g2 (elab_slprops ps2) (elab_slprops ps2')) :
    cont_elab g1 ps1 g3 ps3 =
  fun frame -> k_elab_trans (k1 frame) (k_elab_equiv (k2 frame) (RU.magic ()) (VE_Refl _ _))

let cont_elab_equiv #g1 #ps1 #ps1' #g2 #ps2 #ps2'
    (k: cont_elab g1 ps1 g2 ps2)
    (h1: slprop_equiv g1 (elab_slprops ps1) (elab_slprops ps1'))
    (h2: slprop_equiv g2 (elab_slprops ps2) (elab_slprops ps2')) :
    cont_elab g1 ps1' g2 ps2' =
  fun frame -> k_elab_equiv (k frame) (RU.magic ()) (RU.magic ())

let cont_elab_frame #g #ps #g' #ps' (k: cont_elab g ps g' ps') frame :
    cont_elab g (frame @ ps) g' (frame @ ps') =
  fun frame' -> k_elab_equiv (k (frame' @ frame)) (RU.magic()) (RU.magic())

let prover_result (g: env) (ctxt goals: list slprop_view) =
  g':env { env_extends g' g } &
  ctxt': list slprop_view &
  goals': list slprop_view &
  solved: list slprop_view &
  (g'': env { env_extends g' g } -> T.Tac
    (cont_elab g ctxt g' (solved @ ctxt') &
    (cont_elab g'' (solved @ goals') g'' goals)))

let prover_result_join #g #ctxt #goals #g1 #ctxt1 #goals1
    (r: prover_result g ctxt goals { let (| g1', ctxt1', goals1', _, _ |) = r in g1' == g1 /\ ctxt1' == ctxt1 /\ goals1' == goals1 })
    (r1: prover_result g1 ctxt1 goals1) :
    prover_result g ctxt goals =
  let (| g1, ctxt1, goals1, solved1, k1 |) = r in
  let (| g2, ctxt2, goals2, solved2, k2 |) = r1 in
  (| g2, ctxt2, goals2, solved1 @ solved2, fun g3 ->
    let before1, after1 = k1 g3 in
    let before2, after2 = k2 g3 in
    (fun frame ->
      let h1: slprop_equiv g1 (elab_slprops ((frame @ solved1) @ ctxt1)) (elab_slprops (frame @ solved1 @ ctxt1)) = RU.magic () in
      let h2: slprop_equiv g2 (elab_slprops ((frame @ solved1) @ solved2 @ ctxt2)) (elab_slprops (frame @ (solved1 @ solved2) @ ctxt2)) = RU.magic () in
      k_elab_trans (before1 frame) (k_elab_equiv (before2 (frame @ solved1)) h1 h2)),
    (fun frame ->
      let h1: slprop_equiv g3 (elab_slprops ((frame @ solved1) @ solved2 @ goals2)) (elab_slprops (frame @ (solved1 @ solved2) @ goals2)) = RU.magic () in
      let h2: slprop_equiv g3 (elab_slprops ((frame @ solved1) @ goals1)) (elab_slprops (frame @ solved1 @ goals1)) = RU.magic () in
      k_elab_trans (k_elab_equiv (after2 (frame @ solved1)) h1 h2) (after1 frame))
    <: T.Tac _ |)

let prove_first (g: env) (ctxt goals: list slprop_view)
    (k: (goal: slprop_view -> T.Tac (option (prover_result g ctxt [goal])))) :
    T.Tac (option (prover_result g ctxt goals)) =
  let goals0 = goals in
  let rec go (goals_left_rev: list slprop_view) (goals: list slprop_view { List.rev goals_left_rev @ goals == goals0 }) :
      T.Tac (option (prover_result g ctxt goals0)) =
    match goals with
    | [] -> None
    | goal::goals ->
      match k goal with
      | Some (| g', ctxt', goals', solved, res |) ->
        Some (| g', ctxt', List.rev goals_left_rev @ goals' @ goals, solved, fun g'' ->
          let before, after = res g'' in
          before,
          (fun frame ->
            let h1 : slprop_equiv g''
              (elab_slprops ((frame @ List.Tot.Base.rev goals_left_rev @ goals) @ solved @ goals'))
              (elab_slprops (frame @ solved @ List.Tot.Base.rev goals_left_rev @ goals' @ goals)) = RU.magic () in
            let h2 : slprop_equiv g''
              (elab_slprops ((frame @ List.Tot.Base.rev goals_left_rev @ goals) @ [goal]))
              (elab_slprops (frame @ goals0)) = RU.magic () in
            k_elab_equiv (after (frame @ List.rev goals_left_rev @ goals)) h1 h2) |)
      | None ->
        assert List.rev goals_left_rev @ (goal::goals) == goals0;
        assume List.rev (goal::goals_left_rev) @ goals == goals0;
        go (goal::goals_left_rev) goals in
  go [] goals

let deep_compress_st_comp (c:st_comp) : st_comp =
  { u = c.u; res = RU.deep_compress_safe c.res; pre = RU.deep_compress_safe c.pre; post = RU.deep_compress_safe c.post }

let deep_compress_comp (c:comp {stateful_comp c}) : comp =
  with_st_comp c (deep_compress_st_comp (st_comp_of_comp c))

let continuation_elaborator_with_bind_nondep (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_slprop)
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             g
             (tm_star (comp_post c1) ctxt)) =
  let x = fresh g in
  admit ();
  continuation_elaborator_with_bind (RU.deep_compress_safe ctxt) #(deep_compress_comp c1) e1_typing ctxt_pre1_typing (ppname_default, x)

let tot_typing_tm_unit (g: env) : tot_typing g tm_unit (tm_type u0) = RU.magic ()

let intro_pure (g: env) (frame: slprop) (p: term) :
    continuation_elaborator g frame g (frame `tm_star` tm_pure p) =
  fun post t ->
  let g = push_context g "check_intro_pure" (RU.range_of_term p) in
  let p_typing: tot_typing g p tm_prop = RU.magic() in // implied by t2_typing
  let pv = check_prop_validity g p p_typing in
  let frame_typ : tot_typing g frame tm_slprop = RU.magic () in // implied by t2_typing
  let h: tot_typing g (tm_star frame (comp_pre (comp_intro_pure p))) tm_slprop = RU.magic () in
  debug_prover g (fun _ -> Printf.sprintf "intro_pure p=%s\nframe=%s\n" (show p) (show frame));
  k_elab_equiv (continuation_elaborator_with_bind_nondep frame (T_IntroPure g p p_typing pv) h) (RU.magic ()) (RU.magic ())
    post t

let is_uvar (t:term) : bool =
  match R.inspect_ln t with
  | R.Tv_Uvar .. -> true
  | _ -> false

// solve `pure (t == ?u)` via unification
let is_eq_unif (g: env) (p: term) : Dv (option (term & term)) =
  match is_eq2 (RU.deep_compress_safe p) with
  | Some (_, lhs, rhs) ->
    if is_uvar lhs || is_uvar rhs then
      Some (lhs, rhs)
    else
      None
  | None -> None
let pure_eq_unif (g: env) (p: term) skip_eq_uvar : Dv bool =
  match is_eq_unif g p with
  | Some (lhs, rhs) ->
    if skip_eq_uvar then
      true
    else (
      ignore (RU.teq_nosmt_force (elab_env g) lhs rhs);
      false
    )
  | None -> false

// skip_eq_uvar to support (assert foo. with pure (foo == ....))
let prove_pure (g: env) (ctxt: list slprop_view) (skip_eq_uvar: bool) (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | Pure p ->
    debug_prover g (fun _ -> Printf.sprintf "prove_pure p=%s (skip? %b)" (show p) skip_eq_uvar);

    if pure_eq_unif g p skip_eq_uvar then None else begin
    debug_prover g (fun _ -> Printf.sprintf "prove_pure p=%s success" (show p));

    Some (| g, ctxt, [], [], fun g'' ->
      cont_elab_refl g ctxt ([] @ ctxt) (VE_Refl _ _),
      (fun frame ->
        let h1: slprop_equiv g'' (elab_slprops frame) (elab_slprops (frame @ [] @ [])) = RU.magic () in
        let h2: slprop_equiv g'' (tm_star (elab_slprops frame) (tm_pure p)) (elab_slprops (frame @ [goal])) = RU.magic () in
        k_elab_equiv (intro_pure g'' (elab_slprops frame) p) h1 h2)
      <: T.Tac _ |)
    end
  | _ -> None

// let foo = u2

let intro_with_pure (g: env) (frame: slprop) (p: term) (n: ppname) (v: term) :
    continuation_elaborator g (frame `tm_star` v) g (frame `tm_star` tm_with_pure p n v) =
  fun post t ->
  let g = push_context g "check_intro_with_pure" (RU.range_of_term p) in
  let p_typing: tot_typing g p tm_prop = RU.magic() in // implied by t2_typing
  let pv = check_prop_validity g p p_typing in
  let frame_typ : tot_typing g frame tm_slprop = RU.magic () in // implied by t2_typing
  let ty = mk_squash u0 p in
  let st = wtag (Some STT_Ghost) (Tm_ST { t = tm_unknown; args = [] }) in
  let c = C_STGhost tm_emp_inames { u=u0; res=tm_unit; pre=v; post=tm_with_pure p n v } in
  let typing: st_typing g st c = RU.magic () in
  let h: tot_typing g (tm_star frame (comp_pre c)) tm_slprop = RU.magic () in
  debug_prover g (fun _ -> Printf.sprintf "intro_pure p=%s\nframe=%s\n" (show p) (show frame));
  k_elab_equiv (continuation_elaborator_with_bind_nondep frame typing h) (RU.magic ()) (RU.magic ())
    post t

let prove_with_pure (g: env) (ctxt: list slprop_view) skip_eq_uvar (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | WithPure p n v ->
    if pure_eq_unif g p skip_eq_uvar then None else

    Some (| g, ctxt, [Unknown v], [], fun g'' ->
      cont_elab_refl g ctxt ([] @ ctxt) (VE_Refl _ _),
      (fun frame ->
        let h1: slprop_equiv g'' (tm_star (elab_slprops frame) v) (elab_slprops (frame @ [Unknown v] @ [])) = RU.magic () in
        let h2: slprop_equiv g'' (tm_star (elab_slprops frame) (tm_with_pure p n v))
          (elab_slprops (frame @ [goal])) = RU.magic () in
        k_elab_equiv (intro_with_pure g'' (elab_slprops frame) p n v) h1 h2)
      <: T.Tac _ |)
  | _ -> None

let intro_exists (g: env) (frame: slprop) (u: universe) (b: binder) (body: slprop) (e: term) :
    continuation_elaborator g (frame `tm_star` open_term' body e 0) g (frame `tm_star` tm_exists_sl u b body) =
  fun post t ->
  let g = push_context g "check_intro_exists" (RU.range_of_term body) in
  let frame_typ : tot_typing g frame tm_slprop = RU.magic () in // implied by t2_typing
  let binder_ty_typ : tot_typing g b.binder_ty (tm_type u) = RU.magic() in // implied by t2_typing
  let tm_ex_typ : tot_typing g (tm_exists_sl u b body) tm_slprop = RU.magic() in // implied by t2_typing
  let e_typ = core_check_term' g e T.E_Ghost b.binder_ty (fun _ -> let open Pulse.PP in
    [text "Cannot find witness for" ^/^ pp (tm_exists_sl u b body)]) in
  let h1: tot_typing g (tm_star frame (comp_pre (comp_intro_exists u b body e))) tm_slprop = RU.magic () in
  let h2: slprop_equiv g (tm_star frame (comp_pre (comp_intro_exists u b body e))) (tm_star frame (open_term' body e 0)) = RU.magic () in
  let h3: slprop_equiv g (tm_star (comp_post (comp_intro_exists u b body e)) frame) (tm_star frame (tm_exists_sl u b body)) = RU.magic () in
  debug_prover g (fun _ -> Printf.sprintf "intro_exists %s\nframe=%s\n" (show (tm_exists_sl u b body)) (show frame));
  k_elab_equiv (continuation_elaborator_with_bind_nondep frame (T_IntroExists g u b body e binder_ty_typ tm_ex_typ e_typ) h1) h2 h3
    post t

let mk_uvar (g: env) (ty: term) : T.Tac term =
  // TODO
  fst (tc_term_phase1_with_type g tm_unknown ty)

let prove_exists (g: env) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | Exists u b body ->
    let e = mk_uvar g b.binder_ty in // unnecessarily restrictive environment for uvar
    Some (| g, ctxt, [Unknown (open_term' body e 0)], [], fun g'' ->
      cont_elab_refl g ctxt ([] @ ctxt) (VE_Refl _ _),
      (fun frame ->
        let h1: slprop_equiv g'' (tm_star (elab_slprops frame) (open_term' body e 0)) (elab_slprops (frame @ [] @ [Unknown (open_term' body e 0)])) = RU.magic () in
        let h2: slprop_equiv g'' (tm_star (elab_slprops frame) (tm_exists_sl u b body)) (elab_slprops (frame @ [goal])) = RU.magic () in
        k_elab_equiv (intro_exists g'' (elab_slprops frame) u b body e) h1 h2)
      <: T.Tac _ |)
  | _ -> None

let unpack_and_norm_goal (g: env) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | Unknown goal ->
    let (| goal', goal_eq_goal' |) = normalize_slprop g goal false in
    let goal'' = inspect_slprop g goal' in
    (match goal'' with
    | [Unknown _] -> None
    | _ -> Some (| g, ctxt, goal'', [], fun g' ->
      let h: slprop_equiv g' (elab_slprops ([] @ goal'')) (elab_slprops [Unknown goal]) = RU.magic () in
      cont_elab_refl _ _ _ (VE_Refl _ _), cont_elab_refl _ _ _ h
      <: T.Tac _ |))
  | _ -> None

let prover_result_samegoals g ctxt goals =
  r:prover_result g ctxt goals { let (| _, _, goals', _, _ |) = r in goals' == goals }

let prover_result_nogoals g ctxt =
  prover_result_samegoals g ctxt []

let elim_first' (g: env) (ctxt0 goals: list slprop_view)
    (k: (ctxt: slprop_view -> T.Tac (option (prover_result_nogoals g [ctxt])))) :
    T.Tac (option (prover_result_samegoals g ctxt0 goals)) =
  let rec go (ctxt_left_rev: list slprop_view) (ctxt: list slprop_view { List.rev ctxt_left_rev @ ctxt == ctxt0 }) :
      T.Tac (option (prover_result_samegoals g ctxt0 goals)) =
    match ctxt with
    | [] -> None
    | c::ctxt ->
      match k c with
      | Some (| g', ctxt', goals', solved, res |) ->
        assert goals' == [];
        Some (| g', List.rev ctxt_left_rev @ ctxt' @ ctxt, goals, solved, fun g'' ->
          let before, after = res g'' in
          let h1: slprop_equiv g (elab_slprops ((List.Tot.Base.rev ctxt_left_rev @ ctxt) @ [c])) (elab_slprops ctxt0) = RU.magic () in
          let h2: slprop_equiv g' (elab_slprops ((List.Tot.Base.rev ctxt_left_rev @ ctxt) @ solved @ ctxt'))
            (elab_slprops (solved @ List.Tot.Base.rev ctxt_left_rev @ ctxt' @ ctxt)) = RU.magic () in
          let h3: slprop_equiv g'' (elab_slprops (goals @ solved @ goals')) (elab_slprops (solved @ goals)) = RU.magic () in
          let h4: slprop_equiv g'' (elab_slprops (goals @ [])) (elab_slprops goals) = RU.magic () in
          cont_elab_equiv (cont_elab_frame before (List.rev ctxt_left_rev @ ctxt)) h1 h2,
          cont_elab_equiv (cont_elab_frame after goals) h3 h4 |)
      | None ->
        assert List.rev ctxt_left_rev @ (c::ctxt) == ctxt0;
        assume List.rev (c::ctxt_left_rev) @ ctxt == ctxt0;
        go (c::ctxt_left_rev) ctxt in
  go [] ctxt0

let elim_first (g: env) (ctxt0 goals: list slprop_view)
    (k: (ctxt: slprop_view -> T.Tac (option (prover_result_nogoals g [ctxt])))) :
    T.Tac (option (prover_result g ctxt0 goals)) =
  match elim_first' g ctxt0 goals k with
  | Some r -> Some r
  | None -> None

let unpack_and_norm_ctxt (g: env) (ctxt: slprop_view) :
    T.Tac (option (prover_result_nogoals g [ctxt])) =
  match ctxt with
  | Unknown ctxt ->
    let (| ctxt', ctxt_eq_ctxt' |) = normalize_slprop g ctxt false in
    let ctxt'' = inspect_slprop g ctxt' in
    (match ctxt'' with
    | [Unknown _] -> None
    | _ -> Some (| g, ctxt'', [], [], fun g' ->
      let h: slprop_equiv g ctxt (elab_slprops ([] @ ctxt'')) = RU.magic () in
      cont_elab_refl _ _ _ h, cont_elab_refl _ _ _ (VE_Refl _ _)
      <: T.Tac _ |))
  | _ -> None

let elim_pure (g: env) (frame: slprop) (p: term) (x: nvar { ~(Set.mem (snd x) (dom g)) })
    (g': env { g' == push_binding g (snd x) (fst x) (mk_squash u0 p) }) :
    continuation_elaborator g (frame `tm_star` tm_pure p) g' frame = fun post t ->
  let ty = mk_squash u0 p in
  let st = wtag (Some STT_Ghost) (Tm_ST { t = tm_unknown; args = [] }) in
  let c = C_STGhost tm_emp_inames { u=u0; res=ty; pre=tm_pure p; post=tm_emp } in
  let typing: st_typing g st c = RU.magic () in
  let h: tot_typing g (tm_star frame (comp_pre c)) tm_slprop = RU.magic () in
  let h2: slprop_equiv g' (tm_star (open_term_nv (comp_post c) x) frame) frame = RU.magic () in
  let k: continuation_elaborator g (tm_star frame (tm_pure p)) g' (tm_star tm_emp frame) =
    continuation_elaborator_with_bind frame typing h x in
  k_elab_equiv k (VE_Refl _ _) h2 post t

let elim_pure_step (g: env) (ctxt: slprop_view) :
    T.Tac (option (prover_result_nogoals g [ctxt])) =
  match ctxt with
  | Pure p ->
    let x = ppname_default, fresh g in
    let ty = mk_squash u0 p in
    let g' = push_binding g (snd x) (fst x) ty in
    Some (| g', [], [], [], fun g'' ->
      (fun frame ->
        let h1: slprop_equiv g (tm_star (elab_slprops frame) (tm_pure p)) (elab_slprops (frame @ [ctxt])) = RU.magic () in
        let h2: slprop_equiv g' (elab_slprops frame) (elab_slprops (frame @ [] @ [])) = RU.magic () in
      k_elab_equiv (elim_pure g (elab_slprops frame) p x g') h1 h2),
      cont_elab_refl _ _ _ (VE_Refl _ _)
      <: T.Tac _ |)
  | _ -> None

let elim_with_pure (g: env) (frame: slprop) (p: term) (x: nvar { ~(Set.mem (snd x) (dom g)) }) (v: term)
    (g': env { g' == push_binding g (snd x) (fst x) (mk_squash u0 p) }) :
    continuation_elaborator g (frame `tm_star` tm_with_pure p (fst x) v) g'
      (frame `tm_star` v) = fun post t ->
  let ty = mk_squash u0 p in
  let st = wtag (Some STT_Ghost) (Tm_ST { t = tm_unknown; args = [] }) in
  let c = C_STGhost tm_emp_inames { u=u0; res=ty; pre=tm_with_pure p (fst x) v; post=v } in
  assume open_term v (snd x) == v; // no loose bvars
  let typing: st_typing g st c = RU.magic () in
  let h: tot_typing g (tm_star frame (comp_pre c)) tm_slprop = RU.magic () in
  let h2: slprop_equiv g' (tm_star (open_term_nv (comp_post c) x) frame) (tm_star frame v) = RU.magic () in
  let k: continuation_elaborator g (tm_star frame (tm_with_pure p (fst x) v)) g' (tm_star v frame) =
    continuation_elaborator_with_bind frame typing h x in
  k_elab_equiv k (VE_Refl _ _) h2 post t

let elim_with_pure_step (g: env) (ctxt: slprop_view) :
    T.Tac (option (prover_result_nogoals g [ctxt])) =
  match ctxt with
  | WithPure p n v ->
    let x = n, fresh g in
    let ty = mk_squash u0 p in
    let g' = push_binding g (snd x) (fst x) ty in
    Some (| g', [Unknown v], [], [], fun g'' ->
      (fun frame ->
        let h1: slprop_equiv g (tm_star (elab_slprops frame) (tm_with_pure p (fst x) v)) (elab_slprops (frame @ [ctxt])) = RU.magic () in
        let h2: slprop_equiv g' (tm_star (elab_slprops frame) v) (elab_slprops (frame @ [Unknown v] @ [])) = RU.magic () in
      k_elab_equiv (elim_with_pure g (elab_slprops frame) p x v g') h1 h2),
      cont_elab_refl _ _ _ (VE_Refl _ _)
      <: T.Tac _ |)
  | _ -> None

// TODO: don't always erase
let elim_exists (g: env) (frame: slprop) u b body (x: nvar { ~(Set.mem (snd x) (dom g)) })
    (g': env { g' == push_binding g (snd x) (fst x) (mk_erased u b.binder_ty) }) :
    continuation_elaborator g (frame `tm_star` tm_exists_sl u b body)
      g' (frame `tm_star` open_term' body (mk_reveal u b.binder_ty (term_of_nvar x)) 0) = fun post t ->
  let c = comp_elim_exists u b.binder_ty body x in
  let h1: tot_typing g b.binder_ty (tm_type u) = RU.magic () in
  let h2: tot_typing g (tm_exists_sl u (as_binder b.binder_ty) body) tm_slprop = RU.magic () in
  let typing: st_typing g _ c  = T_ElimExists g u b.binder_ty body (snd x) h1 h2 in
  let h: tot_typing g (tm_star frame (comp_pre c)) tm_slprop = RU.magic () in
  let c_post_x = open_term' body (mk_reveal u b.binder_ty (term_of_nvar x)) 0 in
  assume open_term (comp_post c) (snd x) == c_post_x;
  let h2: slprop_equiv g' (tm_star c_post_x frame) (tm_star frame c_post_x) = RU.magic () in
  let k: continuation_elaborator g (tm_star frame (tm_exists_sl u b body)) g' (tm_star c_post_x frame) =
    continuation_elaborator_with_bind frame typing h x in
  k_elab_equiv k (VE_Refl _ _) h2 post t

let elim_exists_step (g: env) (ctxt: slprop_view) :
    T.Tac (option (prover_result_nogoals g [ctxt])) =
  match ctxt with
  | Exists u b body ->
    let n = "_" ^ T.unseal b.binder_ppname.name ^ string_of_int (List.length (bindings g)) in
    let n: ppname = { name = T.seal n; range = RU.range_of_term body } in
    let x = n, fresh g in
    let ty = mk_erased u b.binder_ty in
    let g' = push_binding g (snd x) (fst x) ty in
    let result = open_term' body (mk_reveal u b.binder_ty (term_of_nvar x)) 0 in
    Some (| g', [Unknown result], [], [], fun g'' ->
      (fun frame ->
        let h1: slprop_equiv g (tm_star (elab_slprops frame) (tm_exists_sl u b body)) (elab_slprops (frame @ [ctxt])) = RU.magic () in
        let h2: slprop_equiv g' (tm_star (elab_slprops frame) result) (elab_slprops (frame @ [] @ [Unknown result])) = RU.magic () in
        k_elab_equiv (elim_exists g (elab_slprops frame) u b body x g') h1 h2),
      cont_elab_refl _ _ _ (VE_Refl _ _)
      <: T.Tac _ |)
  | _ -> None

exception AbortUFTransaction of bool
let with_uf_transaction (k: unit -> T.Tac bool) : T.Tac bool =
  let open FStar.Tactics.V2 in
  try
    T.raise <| AbortUFTransaction <| k ()
  with
    | AbortUFTransaction res -> res
    | ex -> T.raise ex

let forallb (k: 'a -> T.Tac bool) (xs: list 'a) =
  not (T.existsb (fun x -> not (k x)) xs)

open Pulse.PP

module RT = FStar.Reflection.Typing
let check_slprop_equiv_ext r (g:env) (p q:slprop)
: T.Tac (slprop_equiv g p q)
= 
  let p = RU.deep_compress_safe p in
  let q = RU.deep_compress_safe q in
  let res, issues = Pulse.Typing.Util.check_equiv_now (elab_env g) p q in
  match res with
  | None -> 
    fail_doc_with_subissues g (Some r) issues [
      text "rewrite: could not prove equality of";
      pp p;
      pp q;
    ]
  | Some token ->
    VE_Ext g p q (RT.Rel_eq_token _ _ _ ())

let teq_nosmt_force_args (g: R.env) (x y: term) (fail_fast: bool) : Dv bool =
  let rec go (xs ys: list R.argv) : Dv bool =
    match xs, ys with
    | [], [] -> true
    | (x,_)::xs, (y,_)::ys ->
      if RU.teq_nosmt_force_phase1 g x y then
        go xs ys
      else (
        if not fail_fast then ignore (go xs ys);
        false
      )
    | _ -> false in
  let xh, xa = R.collect_app_ln x in
  let yh, ya = R.collect_app_ln y in
  go ((xh, R.Q_Explicit) :: xa) ((yh, R.Q_Explicit) :: ya)

let is_unamb g (cands: list (int & slprop_view)) : T.Tac bool =
  match cands with
  | [] | [_] -> true
  | (_, x)::cands ->
    let unifies x y = with_uf_transaction fun _ ->
      teq_nosmt_force_args (elab_env g) x y true in
    forallb (fun (_, y) -> unifies (elab_slprop x) (elab_slprop y)) cands

// this matches atoms when they're the only unifiable pair
// necessary for various gather like functions where you don't specify all arguments
// needed for pcm_pts_to gather, where we need to specify the order of the ambiguous arguments
// needed for mask_mext, when we need to disambiguate mkey-ambiguous resources
let prove_atom_unamb (g: env) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | Atom hd _ goal ->
    let matches_mkeys (ctxt: slprop_view) : T.Tac bool =
      match ctxt with
      | Atom hd' _ ctxt ->
        if hd <> hd' then false else (
          let r = 
            with_uf_transaction (fun _ ->
              teq_nosmt_force_args (elab_env g) ctxt goal true
            )
          in
          debug_prover g (fun _ -> Printf.sprintf "Tried matching ctxt %s against goal %s, result %b" (show ctxt) (show goal) r);
          r
        )
      | _ -> false in
    let ictxt = List.Tot.mapi (fun i ctxt -> i, ctxt) ctxt in
    let cands = T.filter (fun (i, ctxt) -> matches_mkeys ctxt) ictxt in
    if Nil? cands then (
      debug_prover g (fun _ -> Printf.sprintf "prove_atom_unamb: no matches for %s in context %s\n"  (show goal) (show ctxt));
      None
    )
    else if not (is_unamb g cands) 
    then (
      debug_prover g (fun _ -> Printf.sprintf "prove_atom_unamb: no unambiguous matches for %s in context %s\n"  (show goal) (show ctxt));
      None
    )
    else
    let (i, cand) :: _ = cands in
    debug_prover g (fun _ -> Printf.sprintf "prove_atom_unamb: commiting to unify %s and %s\n" (show (elab_slprop cand)) (show goal));
    ignore (teq_nosmt_force_args (elab_env g) (elab_slprop cand) goal false);
    let rest_ctxt = List.Tot.filter (fun (j, _) -> j <> i) ictxt |> List.Tot.map snd in
    Some (| g, rest_ctxt, [], [cand], fun g' ->
      let h2: slprop_equiv g' (elab_slprop cand) goal = check_slprop_equiv_ext (RU.range_of_term goal) _ _ _ in
      let h1: slprop_equiv g (elab_slprops ctxt) (elab_slprops ([cand] @ rest_ctxt)) = RU.magic () in
      let h2: slprop_equiv g' (elab_slprops ([cand] @ [])) goal = h2 in
      cont_elab_refl _ _ _ h1,
      cont_elab_refl _ _ _ h2
      <: T.Tac _ |)
  | _ -> None

let prove_atom (g: env) (ctxt: list slprop_view) (allow_amb: bool) (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | Atom hd mkeys goal ->
    let matches_mkeys (ctxt: slprop_view) : T.Tac bool =
      match ctxt with
      | Atom hd' mkeys' ctxt ->
        if hd <> hd' then false else
        with_uf_transaction (fun _ ->
          match mkeys, mkeys' with
          | Some mkeys, Some mkeys' ->
            T.zip mkeys mkeys' |> forallb (fun (a, b) -> RU.teq_nosmt_force_phase1 (elab_env g) a b)
          | _, _ ->
            teq_nosmt_force_args (elab_env g) ctxt goal true
        )
      | _ -> false in
    let ictxt = List.Tot.mapi (fun i ctxt -> i, ctxt) ctxt in
    let cands = T.filter (fun (i, ctxt) -> matches_mkeys ctxt) ictxt in
    if Nil? cands then None else
    if (if allow_amb then false else not (is_unamb g cands)) then None else
    let (i, cand)::_ = cands in
    debug_prover g (fun _ -> Printf.sprintf "commiting to unify %s and %s\n" (show (elab_slprop cand)) (show goal));
    ignore (teq_nosmt_force_args (elab_env g) (elab_slprop cand) goal false);
    let rest_ctxt = List.Tot.filter (fun (j, _) -> j <> i) ictxt |> List.Tot.map snd in
    Some (| g, rest_ctxt, [], [cand], fun g' ->
      let h2: slprop_equiv g' (elab_slprop cand) goal = check_slprop_equiv_ext (RU.range_of_term goal) _ _ _ in
      let h1: slprop_equiv g (elab_slprops ctxt) (elab_slprops ([cand] @ rest_ctxt)) = RU.magic () in
      let h2: slprop_equiv g' (elab_slprops ([cand] @ [])) goal = h2 in
      cont_elab_refl _ _ _ h1,
      cont_elab_refl _ _ _ h2
      <: T.Tac _
    |)
  | _ -> None

let rec first_some #a (ks: list (unit -> T.Tac (option a))) : T.Tac (option a) =
  match ks with
  | [] -> None
  | k::ks ->
    match k () with
    | Some res -> Some res
    | None -> first_some ks

let show_slprops ps =
  String.concat "\n" (T.map (fun p -> show (elab_slprop p)) ps)

let rec try_prove_core (g: env) (ctxt goals: list slprop_view) allow_amb : T.Tac (prover_result g ctxt goals) =
  let noop () : prover_result g ctxt goals =
    (| g, ctxt, goals, [], fun g'' ->
      cont_elab_refl g _ _ (VE_Refl _ _),
      cont_elab_refl g'' ([] @ goals) goals (VE_Refl _ _)
      <: T.Tac _ |) in
  match goals with
  | [] -> noop ()
  | goals ->
    debug_prover g (fun _ -> Printf.sprintf "proving\n%s\n from\n%s\n" (show_slprops goals) (show_slprops ctxt));
    let step : option (prover_result g ctxt goals) =
      first_some [
        (fun _ -> elim_first g ctxt goals (unpack_and_norm_ctxt g));
        (fun _ -> elim_first g ctxt goals (elim_pure_step g));
        (fun _ -> elim_first g ctxt goals (elim_with_pure_step g));
        (fun _ -> elim_first g ctxt goals (elim_exists_step g));
        (fun _ -> prove_first g ctxt goals (prove_pure g ctxt true));
        (fun _ -> prove_first g ctxt goals (prove_with_pure g ctxt true));
        (fun _ -> prove_first g ctxt goals (prove_exists g ctxt));
        (fun _ -> prove_first g ctxt goals (unpack_and_norm_goal g ctxt));
        (fun _ -> prove_first g ctxt goals (prove_atom_unamb g ctxt));
        (fun _ -> prove_first g ctxt goals (prove_atom g ctxt allow_amb));
        (fun _ -> prove_first g ctxt goals (prove_pure g ctxt false));
        (fun _ -> prove_first g ctxt goals (prove_with_pure g ctxt false));
      ] in
    match step with
    | Some step ->
      let (| g1, ctxt1, goals1, solved1, k1 |) = step in
      let step2 = try_prove_core g1 ctxt1 goals1 allow_amb in
      prover_result_join step step2
    | None -> noop ()

let try_prove (g: env) (ctxt goals: slprop) allow_amb : T.Tac (prover_result g [Unknown ctxt] [Unknown goals]) =
  let ctxt = RU.deep_compress_safe ctxt in
  let goals = RU.deep_compress_safe goals in
  let ss = Pulse.Checker.Prover.RewritesTo.get_subst_from_env g in
  let ctxt' = Pulse.Checker.Prover.Substs.ss_term ctxt ss in
  let goals' = Pulse.Checker.Prover.Substs.ss_term goals ss in
  let (| g1, ctxt1, goals1, solved1, k1 |) = try_prove_core g [Unknown ctxt'] [Unknown goals'] allow_amb in
  (| g1, ctxt1, goals1, solved1, fun g2 ->
    let before, after = k1 g2 in
    let h1: slprop_equiv g ctxt' ctxt = RU.magic () in
    let h2: slprop_equiv g2 goals' goals = RU.magic () in
    cont_elab_equiv before h1 (VE_Refl _ _),
    cont_elab_equiv after (VE_Refl _ _) h2 |)

let pp_slprops ts = ts
  |> List.Tot.map elab_slprop
  |> sort_terms
  |> T.map pp
  |> separate hardline

let prove rng (g: env) (ctxt goals: slprop) allow_amb :
    T.Tac (g':env { env_extends g' g } &
      ctxt': slprop &
      continuation_elaborator g ctxt g' (goals `tm_star` ctxt')) =
  let (| g', ctxt', goals', solved', k |) = try_prove g ctxt goals allow_amb in
  if Cons? goals' then
    T.fail_doc_at ([
        text (if List.length goals' > 1 then "Cannot prove any of:" else "Cannot prove:") ^^
          indent (pp_slprops goals');
        text "In the context:" ^^ indent (pp_slprops ctxt');
      ] @ (if Pulse.Config.debug_flag "initial_solver_state" then [
        text "The prover was started with goal:" ^^ indent (pp goals);
        text "and initial context:" ^^ indent (pp ctxt);
      ] else []))
    (Some rng)
  else
    let before, after = k g' in
    let h: slprop_equiv g' (elab_slprops (solved' @ ctxt')) (elab_slprops (ctxt' @ solved' @ goals')) = RU.magic () in
    let k = cont_elab_trans before (cont_elab_frame after ctxt') h [] in
    let h: slprop_equiv g' (elab_slprops (ctxt' @ [Unknown goals])) (tm_star goals (elab_slprops ctxt')) = RU.magic () in
    (| g', RU.deep_compress_safe (elab_slprops ctxt'), k_elab_equiv k (VE_Refl _ _) h |)

let prove_post_hint (#g:env) (#ctxt:slprop) (r:checker_result_t g ctxt NoHint) (post_hint:post_hint_opt g) (rng:range)
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = push_context g "prove_post_hint" rng in

  match post_hint with
  | NoHint -> r
  | TypeHint _ -> retype_checker_result post_hint r
  | PostHint post_hint ->
    let (| x, g2, (| u_ty, ty, ty_typing |), (| ctxt', ctxt'_typing |), k |) = r in

    let ppname = mk_ppname_no_range "_posth" in
    let post_hint_opened = open_term_nv post_hint.post (ppname, x) in

    // TODO: subtyping
    if not (eq_tm (RU.deep_compress_safe ty) (RU.deep_compress_safe post_hint.ret_ty))
    then
      fail_doc g (Some rng) [
        text "The return type" ^^ indent (pp ty) ^/^
        text "does not match the expected" ^^ indent (pp post_hint.ret_ty)
      ]
    else if eq_tm post_hint_opened ctxt'
    then (| x, g2, (| u_ty, ty, ty_typing |), (| ctxt', ctxt'_typing |), k |)
    else
      let (| g3, remaining_ctxt, k_post |) =
        prove rng g2 ctxt' post_hint_opened false in

      let tv = inspect_term remaining_ctxt in
      if not (Tm_Emp? tv) then
        fail_doc g (Some rng) [
          prefix 2 1 (text "Leftover resources:")
                     (align (pp remaining_ctxt));
          (if Tm_Star? tv
           then text "Did you forget to free these resources?"
           else text "Did you forget to free this resource?");
        ]
      else
        let h3: slprop_equiv g3 (tm_star post_hint_opened remaining_ctxt) post_hint_opened = RU.magic () in
        // for the typing of ty in g3, we have typing of ty in g2 above, and g3 `env_extends` g2
        let h1: universe_of g3 ty u_ty = RU.magic () in
        // for the typing of post_hint_opened, again post_hint is well-typed in g, and g3 `env_extends` g
        let h2: tot_typing g3 post_hint_opened tm_slprop = RU.magic () in
        (| x, g3, (| u_ty, ty, h1 |), (| post_hint_opened, h2 |),
          k_elab_trans k (k_elab_equiv k_post (VE_Refl _ _) h3) |)

let try_frame_pre (allow_ambiguous : bool) (#g:env)
    (#ctxt:slprop) (ctxt_typing:tot_typing g ctxt tm_slprop)
    (d:(t:st_term & c:comp_st & st_typing g t c))
    (res_ppname:ppname) :
    T.Tac (checker_result_t g ctxt NoHint) =
  let (| t, c, d |) = d in
  let (| g', ctxt', k |) = prove t.range g ctxt (comp_pre c) allow_ambiguous in
  let d: st_typing g' t c = RU.magic () in // weakening from g to g'
  let h1: tot_typing g' ctxt' tm_slprop = RU.magic() in // weakening from to g'
  checker_result_for_st_typing (k _ (| t, add_frame c ctxt', T_Frame _ _ _ ctxt' h1 d |)) res_ppname

let rec try_elim_core (g: env) (ctxt: list slprop_view) :
    T.Tac (prover_result_nogoals g ctxt) =
  let noop () : prover_result g ctxt [] =
    (| g, ctxt, [], [], fun g'' ->
      cont_elab_refl g _ _ (VE_Refl _ _),
      cont_elab_refl g'' [] [] (VE_Refl _ _)
      <: T.Tac _ |) in
  debug_prover g (fun _ -> Printf.sprintf "eliminating\n%s\n" (show_slprops ctxt));
  let step : option (prover_result_nogoals g ctxt) =
    first_some [
      (fun _ -> elim_first' g ctxt [] (unpack_and_norm_ctxt g));
      (fun _ -> elim_first' g ctxt [] (elim_pure_step g));
      (fun _ -> elim_first' g ctxt [] (elim_with_pure_step g));
      (fun _ -> elim_first' g ctxt [] (elim_exists_step g));
    ] in
  match step with
  | Some step ->
    let (| g1, ctxt1, goals1, solved1, k1 |) = step in
    let step2 = try_elim_core g1 ctxt1 in
    prover_result_join step step2
  | None -> noop ()

let elim_exists_and_pure (#g:env) (#ctxt:slprop)
    (ctxt_typing:tot_typing g ctxt tm_slprop)
    : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' tm_slprop &
            continuation_elaborator g ctxt g' ctxt') =
  let ss = Pulse.Checker.Prover.RewritesTo.get_subst_from_env g in
  let ctxt' = Pulse.Checker.Prover.Substs.ss_term ctxt ss in
  let (| g', ctxt'', goals'', solved, k |) = try_elim_core g [Unknown ctxt'] in
  let h: tot_typing g' (elab_slprops ctxt'') tm_slprop = RU.magic () in // TODO thread through prover
  let h1: slprop_equiv g (elab_slprops ([] @ [Unknown ctxt'])) ctxt = (RU.magic() <: slprop_equiv g ctxt' ctxt) in
  let h2: slprop_equiv g' (elab_slprops (ctxt'' @ solved @ goals'')) (elab_slprops ([] @ solved @ ctxt'')) = RU.magic () in
  let h3: slprop_equiv g' (elab_slprops (ctxt'' @ [])) (elab_slprops ctxt'') = RU.magic () in
  let before, after = k g' in
  (| g', elab_slprops ctxt'', h,
    k_elab_trans (k_elab_equiv (before []) h1 (VE_Refl _ _))
      (k_elab_equiv (after ctxt'') h2 h3) |)
