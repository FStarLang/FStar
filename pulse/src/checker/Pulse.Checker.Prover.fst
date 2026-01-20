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
  | WithPure t x b -> Printf.sprintf "(WithPure %s %s %s)" (show t) (show x) (show b)
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

type plem_kind_t =
  | EagerElim
  | EagerIntro
  | Intro

type plem = {
  plem_lid: R.name;
  plem_kind: plem_kind_t;
  plem_prop_head: head_id;
  plem_prop_idx: nat;
}
type plems = list plem

let mk_attr lid = R.pack_ln <| R.Tv_FVar <| R.pack_fv lid
let mk_pulse_core_attr n = mk_attr (Pulse.Reflection.Util.mk_pulse_lib_core_lid n)

let eager_elim_attr = mk_pulse_core_attr "pulse_eager_elim"
let eager_intro_attr = mk_pulse_core_attr "pulse_eager_intro"
let intro_attr = mk_pulse_core_attr "pulse_intro"

let get_fvs g (se: R.sigelt) : T.Tac (list (R.fv & list R.univ_name & R.term)) =
  match R.inspect_sigelt se with
  | R.Sg_Let _ lbs ->
    T.map (fun lb ->
        let lb = R.inspect_lb lb in
        lb.lb_fv, lb.lb_us, lb.lb_typ)
      lbs
  | R.Sg_Val nm uvs typ ->
    if Some? (RU.try_lookup_lid (fstar_env g) nm) then
      [R.pack_fv nm, uvs, typ]
    else
      []
  | R.Unk | R.Sg_Inductive .. -> []

let build_plems_from_lemma (g: env) (kind: plem_kind_t) (se: R.sigelt) : T.Tac (list plem) =
  T.concatMap (fun (fv, uvs, typ) ->
    debug_prover g (fun _ -> Printf.sprintf "build_plems_from_lemma %s\n" (show (R.inspect_fv fv)));
    let args, ty = R.collect_arr_ln_bs typ in
    match R.inspect_comp ty with
    | R.C_Total ty | R.C_GTotal ty -> (
      match Pulse.Readback.readback_comp ty with
      | Some (C_STGhost inames { pre; res; post }) ->
        if T.term_eq res tm_unit then
          let p = match kind with EagerElim -> pre | EagerIntro | Intro -> post in
          let p = inspect_slprop g p in
          let p = List.Tot.mapi (fun i p -> assume i >= 0; (i <: nat), p) p in
          T.concatMap
            (fun (i, p) ->
              match p with
              | Atom (FVarHead h) mkeys p ->
                [{
                  plem_lid = R.inspect_fv fv;
                  plem_kind = kind;
                  plem_prop_head = FVarHead h;
                  plem_prop_idx = i;
                }]
              | _ -> []
            )
            p
        else
          []
      | _ -> []
    )
    | _ -> [])
  (get_fvs g se)

let build_plems (g: env) : T.Tac plems =
  debug_prover g (fun _ -> "build_plems\n");
  T.concatMap
    (fun (kind, attr) -> T.concatMap (build_plems_from_lemma g kind) (T.lookup_attr_ses attr (fstar_env g)))
    [EagerElim, eager_elim_attr;
     EagerIntro, eager_intro_attr;
     Intro, intro_attr]

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

let cont_elab_thunk #g #ps #g' #ps' (k: unit -> T.Tac (cont_elab g ps g' ps')) : cont_elab g ps g' ps' =
  fun frame posth typing -> k () frame posth typing

let prover_result (g: env) (ctxt goals: list slprop_view) =
  g':env { env_extends g' g } &
  ctxt': list slprop_view &
  goals': list slprop_view &
  solved: list slprop_view &
  (g'': env { env_extends g'' g' } -> T.Tac
    (cont_elab g ctxt g' (solved @ ctxt') &
    (cont_elab g'' (solved @ goals') g'' goals)))

let prover_result_join #g #ctxt #goals #g1 #ctxt1 #goals1
    (r: prover_result g ctxt goals { let (| g1', ctxt1', goals1', _, _ |) = r in g1' == g1 /\ ctxt1' == ctxt1 /\ goals1' == goals1 })
    (r1: prover_result g1 ctxt1 goals1) :
    prover_result g ctxt goals =
  let (| g1, ctxt1, goals1, solved1, k1 |) = r in
  let (| g2, ctxt2, goals2, solved2, k2 |) = r1 in
  (| g2, ctxt2, goals2, solved1 @ solved2, fun (g3: env { env_extends g3 g2 }) ->
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
        Some (| g', ctxt', List.rev goals_left_rev @ goals' @ goals, solved, fun (g'': env { env_extends g'' g' }) ->
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

let continuation_elaborator_with_bind_nondep_unit (#g:env) (ctxt:term)
  (#c1:comp_st{comp_res c1 == tm_unit })
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (tm_star ctxt (comp_pre c1)) tm_slprop)
  : T.Tac (continuation_elaborator
             g
             (tm_star ctxt (comp_pre c1))
             g
             (tm_star (open_term' (comp_post c1) unit_const 0) ctxt)) =
  let c1 = with_st_comp c1 { st_comp_of_comp c1 with post = open_term' (comp_post c1) unit_const 0 } in
  let e1_typing: st_typing g e1 c1 = RU.magic () in
  continuation_elaborator_with_bind_nondep #g ctxt #c1 #e1 e1_typing ctxt_pre1_typing

let cont_elab_with_bind_nondep_unit (#g:env)
  (#c1:comp_st{comp_res c1 == tm_unit })
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (pre1_typing:tot_typing g (comp_pre c1) tm_slprop)
  : T.Tac (cont_elab
             g
             [Unknown (comp_pre c1)]
             g
             [Unknown (open_term' (comp_post c1) unit_const 0)]) =
  fun frame posth t ->
    let h1: tot_typing g (tm_star (elab_slprops frame) (comp_pre c1)) tm_slprop = RU.magic () in
    let h2: slprop_equiv g
        (tm_star (elab_slprops frame) (comp_pre c1))
        (elab_slprops (frame @ [Unknown (comp_pre c1)])) = RU.magic () in
    let h3: slprop_equiv g
        (tm_star (open_term' (comp_post c1) unit_const 0) (elab_slprops frame))
        (elab_slprops (frame @
              [Unknown (open_term' (comp_post c1) unit_const 0)])) = RU.magic () in
    k_elab_equiv (continuation_elaborator_with_bind_nondep_unit (elab_slprops frame) e1_typing h1)
      h2 h3 posth t

let tot_typing_tm_unit (g: env) : tot_typing g tm_unit (tm_type u0) = RU.magic ()

let intro_pure (g: env) (frame: slprop) (p: term) 
    (p_typing:tot_typing g p tm_prop)
    (pv:prop_validity g p):
    continuation_elaborator g frame g (frame `tm_star` tm_pure p) =
  fun post t ->
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
      let p_typing: tot_typing g'' p tm_prop = RU.magic() in // implied by t2_typing
      let pv = check_prop_validity g'' p p_typing in
      cont_elab_refl g ctxt ([] @ ctxt) (VE_Refl _ _),
      (fun frame ->
        let h1: slprop_equiv g'' (elab_slprops frame) (elab_slprops (frame @ [] @ [])) = RU.magic () in
        let h2: slprop_equiv g'' (tm_star (elab_slprops frame) (tm_pure p)) (elab_slprops (frame @ [goal])) = RU.magic () in
        k_elab_equiv 
          (intro_pure g'' (elab_slprops frame) p p_typing pv) 
          h1 h2)
      <: T.Tac _ |)
    end
  | _ -> None

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

let prove_exists (g: env) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  match goal with
  | Exists u b body ->
    // unnecessarily restrictive environment for uvar
    let e = RU.new_implicit_var "witness for exists*" (RU.range_of_term body) (elab_env g) b.binder_ty false in
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
        Some (| g', List.rev ctxt_left_rev @ ctxt' @ ctxt, goals, solved, fun (g'': env { env_extends g'' g' }) ->
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
      text "Could not prove equality of:";
      pp p;
      pp q;
    ]
  | Some token ->
    VE_Ext g p q (RT.Rel_eq_token _ _ _ ())


let on_name = R.inspect_fv (R.pack_fv <| Pulse.Reflection.Util.mk_pulse_lib_core_lid "on")
let on_head_id : head_id = FVarHead on_name

type teq_cfg = {
  teq_fail_fast: bool;
  teq_mkeys_only: bool;
  teq_noforce: bool;
  teq_match: bool;
}

let teq_cfg_full = {
  teq_fail_fast = false;
  teq_mkeys_only = false;
  teq_noforce = false;
  teq_match = true;
}

let teq_cfg_unamb =
  { teq_cfg_full with teq_fail_fast = true; teq_match = false }

let teq_cfg_first_mkeys_pass = {
  teq_fail_fast = true;
  teq_mkeys_only = true;
  teq_noforce = false;
  teq_match = true;
}

let type_of_fv (g:R.env) (fv:R.fv)
  : option R.term
  = let n = R.inspect_fv fv in
    match R.lookup_typ g n with
    | None -> None
    | Some se ->
      match R.inspect_sigelt se with
      | R.Unk -> None
      | R.Sg_Let _ lbs -> (
        List.Tot.tryPick
          (fun lb -> 
            let lbv = R.inspect_lb lb in
            if R.inspect_fv lbv.lb_fv = n
            then Some lbv.lb_typ
            else None)
          lbs
      )
      | R.Sg_Val _ _ t -> Some t
      | R.Sg_Inductive _nm _univs params typ _ -> None

let has_no_mkeys fv = 
  Pulse.Reflection.Util.fv_has_attr_string "Pulse.Lib.Core.no_mkeys" fv

let is_mkey (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Pulse"; "Lib"; "Core"; "mkey"]
  | _ -> false

let binder_is_mkey (b:R.binder) : bool =
  List.Tot.existsb is_mkey (R.inspect_binder b).attrs

let binder_is_pred (b:R.binder) : option nat =
  let doms, c = R.collect_arr_ln (R.inspect_binder b).sort in
  match R.inspect_comp c with
  | R.C_Total res | R.C_GTotal res ->
    if T.term_eq tm_slprop res then Some (List.length doms) else None
  | _ -> None

let rec has_any_mkeys_in_type (ty: R.term) : bool =
  match R.inspect_ln ty with
  | R.Tv_Arrow b c ->
    if binder_is_mkey b then true else
    (match R.inspect_comp c with
    | R.C_Total res | R.C_GTotal res -> has_any_mkeys_in_type res
    | _ -> false)
  | _ -> false

let fv_eq (a b: R.fv) : bool =
  R.inspect_fv a = R.inspect_fv b

let rec univs_eq (a b: list R.universe) : bool =
  match a, b with
  | a::a', b::b' -> T.univ_eq a b && univs_eq a' b'
  | [], [] -> true
  | _ -> false

let is_fvar_or_uinst (a: term) : option R.fv =
  match R.inspect_ln a with
  | R.Tv_FVar fv
  | R.Tv_UInst fv _ -> Some fv
  | _ -> None

let is_uvar_app (a: term): bool =
  let hd, _ = R.collect_app_ln a in
  match R.inspect_ln hd with
  | R.Tv_Uvar .. -> true
  | _ -> false

let rec teq_slprop (g: env) (cfg: teq_cfg) (a b: term) : T.Tac bool =
  debug_prover g (fun _ -> Printf.sprintf "teq_slprop %s === %s\n" (show a) (show b));
  let ah, aa = R.collect_app_ln a in
  let bh, ba = R.collect_app_ln b in
  match is_fvar_or_uinst ah, is_fvar_or_uinst bh with
  | Some fv, Some _ ->
    let head_matches = RU.teq_nosmt_force_phase1 (elab_env g) ah bh in
    if not head_matches && cfg.teq_fail_fast then false else
    let h_ty = match type_of_fv (elab_env g) fv with Some h_ty -> h_ty | None -> tm_unknown in 
    let use_mkeys =
      if has_any_mkeys_in_type h_ty then
        true
      else
        has_no_mkeys fv in
    teq_slprop_args g cfg h_ty aa ba use_mkeys
  | _ ->
    teq_slprop_base g cfg a b

and teq_slprop_args (g: env) (cfg: teq_cfg) (h_ty: term) (a b: list R.argv) (use_mkeys: bool) : T.Tac bool =
  match a, b with
  | [], [] -> true
  | _::_, [] | [], _::_ -> false
  | a::a', b::b' ->
    let h_ty, is_slprop, is_mkey =
      match R.inspect_ln h_ty with
      | R.Tv_Arrow h_ty_b h_ty_c ->
        let h_ty =
          match R.inspect_comp h_ty_c with
          | R.C_Total res | R.C_GTotal res -> res
          | _ -> tm_unknown in
        h_ty, binder_is_pred h_ty_b, binder_is_mkey h_ty_b
      | _ ->
        tm_unknown, None, true in
    let arg_matches =
      if (not cfg.teq_mkeys_only || is_mkey || not use_mkeys) then
        match is_slprop with
        | Some pred_args ->
          if not cfg.teq_mkeys_only && not is_mkey then
            // unify `SLT.pts_to t i (Seq.index ..)` with `SLT.pts_to t i (reveal ..)`
            teq_slprop_arg g cfg (fst a) (fst b)
          else
            teq_slprop_pred_arg g cfg (fst a) (fst b) pred_args
        | None -> teq_slprop_arg g cfg (fst a) (fst b)
      else
        true in
    if not arg_matches && cfg.teq_fail_fast then
      false
    else
      let rest_matches = teq_slprop_args g cfg h_ty a' b' use_mkeys in
      arg_matches && rest_matches

and teq_slprop_pred_arg (g: env) (cfg: teq_cfg) (a b: R.term) (n: nat) : T.Tac bool =
  if n = 0 then teq_slprop g cfg a b else
  // match R.inspect_ln a, R.inspect_ln b with
  // | R.Tv_Abs adom abody, R.Tv_Abs bdom bbody ->
  //   let adom = R.inspect_binder adom in
  //   let bdom = R.inspect_binder bdom in
  //   if teq_slprop_base g cfg adom.sort bdom.sort then
  //     // let x = RU.next_id () in
  //     // let g' = R.push_binding (elab_env g) { ppname = adom.ppname; sort = adom.sort; uniq = x } in
  //     let x = fresh g in
  //     let g' = push_binding g x { name = adom.ppname; range = RU.range_of_term adom.sort } adom.sort in
  //     let x = R.pack_ln (R.Tv_Var (R.pack_namedv { uniq = x; sort = T.seal adom.sort; ppname = adom.ppname })) in
  //     teq_slprop_pred_arg g' cfg' (open_term' abody x 0) (open_term' bbody x 0) (n - 1)
  //   else
  //     false
  // | _ ->
  let cfg = { cfg with teq_noforce = true } in
    teq_slprop_arg g cfg a b

and teq_slprop_arg (g: env) (cfg: teq_cfg) (a b: R.term) : T.Tac bool =
  teq_slprop_base g cfg a b

and teq_slprop_base (g: env) (cfg: teq_cfg) (a b: R.term) : T.Tac bool =
  let a_uv = is_uvar_app a in
  let b_uv = is_uvar_app b in
  if cfg.teq_match && not a_uv && b_uv then
    // disallow unifying (f ..) with ?u in matching mode
    false
  else if cfg.teq_noforce then
    RU.teq_nosmt_phase1 (elab_env g) a b
  else
    RU.teq_nosmt_force_phase1 (elab_env g) a b

let is_unamb g (cands: list (int & slprop_view)) : T.Tac bool =
  match cands with
  | [] | [_] -> true
  | (_, x)::cands ->
    let unifies x y = with_uf_transaction fun _ ->
      teq_slprop g teq_cfg_unamb x y in
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
      | Atom hd' mkeys' ctxt ->
        if hd <> hd' then false else
        with_uf_transaction fun _ ->
          teq_slprop g teq_cfg_unamb goal ctxt
      | _ -> false in
    debug_prover g (fun _ -> Printf.sprintf "prove_atom_unamb: searching for match for goal %s in ctxt %s\n" (show goal) (show ctxt));
    let ictxt = List.Tot.mapi (fun i ctxt -> i, ctxt) ctxt in
    let cands = T.filter (fun (i, ctxt) -> matches_mkeys ctxt) ictxt in
    debug_prover g (fun _ -> Printf.sprintf "prove_atom_unamb: found candidates %s\n" (show cands));
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
    let ok = teq_slprop g teq_cfg_full goal (elab_slprop cand) in
    debug_prover g (fun _ -> Printf.sprintf "prove_atom_unamb: result of unify %s and %s is %s\n" (show (elab_slprop cand)) (show goal) (show ok));
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
        with_uf_transaction fun _ ->
          teq_slprop g teq_cfg_first_mkeys_pass goal ctxt
      | _ -> false in
    let ictxt = List.Tot.mapi (fun i ctxt -> i, ctxt) ctxt in
    let cands = T.filter (fun (i, ctxt) -> matches_mkeys ctxt) ictxt in
    if Nil? cands then None else
    if (if allow_amb then false else not (is_unamb g cands)) then None else
    let (i, cand)::_ = cands in
    debug_prover g (fun _ -> Printf.sprintf "prove_atom: committed to unifying %s and %s\n" (show (elab_slprop cand)) (show goal));
    let ok = teq_slprop g teq_cfg_full goal (elab_slprop cand) in
    debug_prover g (fun _ -> Printf.sprintf "prove_atom: unified %s and %s, result is %s\n" (show (elab_slprop cand)) (show goal) (show ok));
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

noeq type penv = {
  penv_env: env;
  penv_plems: plems;
  penv_plems_enabled: bool;
  penv_allow_amb: bool;

  // for loop detection when applying intro lemmas
  penv_stack: list (R.name & list term);

  penv_steps: nat;
}

let prover_lemmas_enabled () : T.Tac bool =
  match T.ext_getv "pulse:prover_lemmas" with
  | "" | "true" -> true
  | _ -> false

let mk_penv (g: env) (allow_amb: bool) : T.Tac (pg:penv { pg.penv_env == g }) = {
  penv_env = g;
  penv_plems_enabled = prover_lemmas_enabled ();
  penv_allow_amb = allow_amb;
  penv_plems = build_plems g;
  penv_stack = [];
  penv_steps = 0;
}

let rec apply_with_uvars (g:env) (t:typ) (v:term) : T.Tac (typ & term) =
  match R.inspect_ln_unascribe t with
  | R.Tv_Arrow b c -> (
    match R.inspect_comp c with
    | R.C_Total res | R.C_GTotal res ->
      let { ppname; qual; sort } = R.inspect_binder b in
      let u = RU.new_implicit_var "value for argument in automatically applied ghost lemma"
        (T.range_of_term v) (elab_env g) sort false in
      let v = R.pack_ln <| R.Tv_App v (u, qual) in
      let res = open_term' res u 0 in
      apply_with_uvars g res v
    | _ -> t, v)
  | _ -> t, v

#push-options "--split_queries always"
let try_apply_elim_lemma (g: env) (lid: R.name) (i: nat) (ctxt: slprop_view) :
    T.Tac (option (prover_result_nogoals g [ctxt])) =
  let do_match a b =
    match a, b with
    | Atom a_hd a_mkeys a, Atom b_hd b_mkeys b ->
      with_uf_transaction fun _ ->
        teq_slprop g teq_cfg_first_mkeys_pass a b
    | _ -> false in
  let t, ty, _ = tc_term_phase1 g (R.pack_ln <| R.Tv_FVar <| R.pack_fv lid) in
  let ty, t = apply_with_uvars g ty t in
  match Pulse.Readback.readback_comp ty with
  | Some (C_STGhost inames { pre; post; res; u }) ->
    let c = C_STGhost inames { pre; post; res; u } in
    assume res == tm_unit;
    (match inspect_slprop g pre, i with
    | [pre'], 0 -> // only support elimination rules with single pre
      debug_prover g (fun _ -> Printf.sprintf "try_apply_eager_elim_lemma: ATTEMPTING %s by unifying %s and %s\n" (show lid) (show (elab_slprop ctxt)) (show pre));
      if do_match pre' ctxt then (
        debug_prover g (fun _ -> Printf.sprintf "try_apply_elim_lemma: applying %s by unifying %s and %s\n" (show lid) (show (elab_slprop ctxt)) (show pre));
        let ok = teq_slprop g teq_cfg_full pre (elab_slprop ctxt) in
        debug_prover g (fun _ -> Printf.sprintf "try_apply_elim_lemma: unified %s and %s, result is %s\n" (show (elab_slprop ctxt)) (show pre) (show ok));
        let post' = open_term' post unit_const 0 in
        Some (| g, [Unknown post'], [], [], fun g'' ->
          let typing = core_check_term g t T.E_Ghost ty in
          let t' = wtag (Some STT_Ghost) (Tm_ST { t; args=[] }) in
          let ni: non_informative g c = RU.magic () in
          let typing: st_typing g t' c = T_STGhost g t c typing ni in
          let h1: tot_typing g (comp_pre c) tm_slprop = RU.magic () in
          let h2: slprop_equiv g (elab_slprops [Unknown (comp_pre c)]) (elab_slprops [ctxt]) =
            assume elab_slprop ctxt == pre; VE_Refl _ _ in
          let h3: slprop_equiv g (elab_slprops [Unknown (open_term' (comp_post c) unit_const 0)])
            (elab_slprops ([] @ [Unknown post'])) = VE_Refl _ _ in
          let k_t = cont_elab_with_bind_nondep_unit typing h1 in
          cont_elab_equiv k_t h2 h3,
          cont_elab_refl g'' ([] @ []) [] (VE_Refl _ _) |)
      ) else
        None
    | _ -> None)
  | _ ->
    None
#pop-options

#push-options "--split_queries always"
let try_apply_eager_intro_lemma (g: env) (lid: R.name) (i: nat) ctxt (goal: slprop_view) :
    T.Tac (option (prover_result g ctxt [goal])) =
  let do_match a b =
    match a, b with
    | Atom a_hd a_mkeys a, Atom b_hd b_mkeys b ->
      debug_prover g (fun _ -> Printf.sprintf "do_match:\n%s and\n%s\n" (show a_mkeys) (show b_mkeys));
      with_uf_transaction fun _ ->
        teq_slprop g teq_cfg_first_mkeys_pass a b
    | _ -> false in
  let t, ty, _ = tc_term_phase1 g (R.pack_ln <| R.Tv_FVar <| R.pack_fv lid) in
  let ty, t = apply_with_uvars g ty t in
  match Pulse.Readback.readback_comp ty with
  | Some (C_STGhost inames { pre; post; res; u }) ->
    let c = C_STGhost inames { pre; post; res; u } in
    assume res == tm_unit;
    let post' = open_term' post unit_const 0 in
    (match inspect_slprop g post', i with
    | [post''], 0 -> // only support introduction rules with single post
      debug_prover g (fun _ -> Printf.sprintf "try_apply_eager_intro_lemma: ATTEMPTING %s by unifying %s and %s\n" (show lid) (show post) (show (elab_slprop goal)));
      if do_match post'' goal then (
        debug_prover g (fun _ -> Printf.sprintf "try_apply_eager_intro_lemma: applying %s by unifying %s and %s\n" (show lid) (show post) (show (elab_slprop goal)));
        let ok = teq_slprop g teq_cfg_full post' (elab_slprop goal) in
        debug_prover g (fun _ -> Printf.sprintf "try_apply_eager_intro_lemma: unified %s and %s, result is %s\n" (show post) (show (elab_slprop goal)) (show ok));
        Some (| g, ctxt, [Unknown pre], [], fun g'' ->
          let typing = core_check_term g'' t T.E_Ghost ty in
          let t' = wtag (Some STT_Ghost) (Tm_ST { t; args=[] }) in
          let ni: non_informative g'' c = RU.magic () in
          let typing: st_typing g'' t' c = T_STGhost g'' t c typing ni in
          let h1: tot_typing g'' (comp_pre c) tm_slprop = RU.magic () in
          let h2: slprop_equiv g'' (elab_slprops [Unknown (comp_pre c)]) (elab_slprops ([] @ [Unknown pre])) = VE_Refl _ _ in
          let h3: slprop_equiv g'' (elab_slprops [Unknown (open_term' (comp_post c) unit_const 0)]) (elab_slprops [goal]) = RU.magic () in
          let k_typing = cont_elab_with_bind_nondep_unit typing h1 in
          cont_elab_refl g ctxt ([] @ ctxt) (VE_Refl _ _),
          cont_elab_equiv k_typing h2 h3
        |)
      ) else
        None
    | _ -> None)
  | _ ->
    None
#pop-options

let eager_elim_lemma_step (g:penv) (ctxt: slprop_view) :
    T.Tac (option (prover_result_nogoals g.penv_env [ctxt])) =
  if not g.penv_plems_enabled then None else
  match ctxt with
  | Atom hd mkeys _ ->
    T.tryPick (fun plem ->
      if plem.plem_kind <> EagerElim then None else
      if plem.plem_prop_head <> hd then None else
      try_apply_elim_lemma g.penv_env plem.plem_lid plem.plem_prop_idx ctxt
    ) g.penv_plems
  | _ -> None

let eager_intro_lemma_step (g:penv) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (prover_result g.penv_env ctxt [goal])) =
  if not g.penv_plems_enabled then None else
  match goal with
  | Atom hd mkeys _ ->
    T.tryPick (fun plem ->
      if plem.plem_kind <> EagerIntro then None else
      if plem.plem_prop_head <> hd then None else
      try_apply_eager_intro_lemma g.penv_env plem.plem_lid plem.plem_prop_idx ctxt goal
    ) g.penv_plems
  | _ -> None

let already_in_stack (g:penv) stackelem : T.Tac bool =
  let (hd0, ts0) = stackelem in
  T.existsb (fun (hd, ts) ->
    if hd <> hd0 then false else
    T.zip ts ts0 |> forallb (fun (t, t0) -> T.term_eq t t0)
  ) g.penv_stack

let prover_result_is_solved #g #ctxt #goals (res: prover_result g ctxt goals) : bool =
  let (| g', ctxt', goals', solved, k |) = res in
  match goals' with [] -> true | _ -> false

let prover_result_solved g ctxt goals =
  res: prover_result g ctxt goals { prover_result_is_solved res }

let prover_result_solved_unpack #g #ctxt #goals (res: prover_result_solved g ctxt goals) :
    g':env { env_extends g' g } &
    ctxt': list slprop_view &
    cont_elab g ctxt g' (ctxt' @ goals) =
  let (| g', ctxt', goals', solved, k |) = res in
  (| g', ctxt', cont_elab_thunk fun _ ->
    let k1, k2 = k g' in
    let h: slprop_equiv g' (elab_slprops (solved @ ctxt')) (elab_slprops (ctxt' @ solved @ goals')) = RU.magic () in
    cont_elab_trans k1 (cont_elab_frame k2 ctxt') h |)

#push-options "--split_queries always --z3rlimit 10"
let try_apply_intro_lemma (g: env) (lid: R.name) (i: nat) ctxt (goal: slprop_view) :
    T.Tac (option (
      g': env &
      subgoals: list slprop_view &
      (res:prover_result_solved g' ctxt subgoals ->
        T.Tac (prover_result g ctxt [goal]))
    )) =
  let do_match a b =
    match a, b with
    | Atom a_hd a_mkeys a, Atom b_hd b_mkeys b ->
      debug_prover g (fun _ -> Printf.sprintf "do_match:\n%s and\n%s\n" (show a_mkeys) (show b_mkeys));
      with_uf_transaction fun _ ->
        teq_slprop g teq_cfg_first_mkeys_pass a b
    | _ -> false in
  let t, ty, _ = tc_term_phase1 g (R.pack_ln <| R.Tv_FVar <| R.pack_fv lid) in
  let ty, t = apply_with_uvars g ty t in
  match Pulse.Readback.readback_comp ty with
  | Some (C_STGhost inames { pre; post; res; u }) ->
    assume res == tm_unit;
    let post' = open_term' post unit_const 0 in
    let post'' = inspect_slprop g post' in
    if i >= List.length post'' then None else
    let post''_before, post''_i, post''_after = List.split3 post'' i in
    let post''_rest = post''_before @ post''_after in
    if do_match post''_i goal then (
      debug_prover g (fun _ -> Printf.sprintf "try_apply_intro_lemma: applying %s by unifying %s and %s\n" (show lid) (show post) (show (elab_slprop goal)));
      let ok = teq_slprop g teq_cfg_full post' (elab_slprop goal) in
      debug_prover g (fun _ -> Printf.sprintf "try_apply_intro_lemma: unified %s and %s, result is %s\n" (show post) (show (elab_slprop goal)) (show ok));
      Some (| g, [Unknown pre], fun subresult ->
        let (| g', ctxt', k |) = prover_result_solved_unpack subresult in
        (| g', ctxt' @ post''_rest, [], [goal], fun (g'': env { env_extends g'' g' }) ->
          let c = C_STGhost inames { pre; post; res; u } in
          let typing = core_check_term g' t T.E_Ghost ty in
          let t' = wtag (Some STT_Ghost) (Tm_ST { t; args=[] }) in
          let ni: non_informative g' c = RU.magic () in
          let typing: st_typing g' t' c = T_STGhost g' t c typing ni in
          let h1: tot_typing g' (comp_pre c) tm_slprop = RU.magic () in
          let h2: slprop_equiv g' (elab_slprops (ctxt' @ [Unknown (comp_pre c)])) (elab_slprops (ctxt' @ [Unknown pre])) =
            RU.magic () in
          let h3: slprop_equiv g'
            (elab_slprops (ctxt' @ [Unknown (open_term' (comp_post c) unit_const 0)]))
            (elab_slprops ([goal] @ ctxt' @ post''_rest)) = RU.magic () in
          let k_typing = cont_elab_with_bind_nondep_unit typing h1 in
          let k_typing = cont_elab_frame k_typing ctxt' in
          let k_typing: cont_elab g' (ctxt' @ [Unknown pre]) g' ([goal] @ ctxt' @ post''_rest) =
            cont_elab_equiv k_typing h2 h3 in
          cont_elab_trans k k_typing (VE_Refl _ _),
          cont_elab_refl g'' ([goal] @ []) [goal] (VE_Refl _ _)
          <: cont_elab g ctxt g' ([goal] @ ctxt' @ post''_rest) & cont_elab g'' ([goal] @ []) g'' [goal]
          |)
        <: T.Tac (prover_result g ctxt [goal])
        |)
    ) else
      None
  | _ ->
    None
#pop-options

let intro_lemma_main (g:penv) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (
      pg': penv &
      subgoals: list slprop_view &
      (res:prover_result_solved pg'.penv_env ctxt subgoals ->
        T.Tac (prover_result g.penv_env ctxt [goal]))
    )) =
  match goal with
  | Atom (FVarHead fv) mkeys p ->
    let hd = FVarHead fv in
    let breadcrumb = (fv, (match mkeys with Some mkeys -> mkeys | _ -> [p])) in
    T.tryPick (fun plem ->
      if plem.plem_kind <> Intro then None else
      if plem.plem_prop_head <> hd then None else
      if already_in_stack g breadcrumb then None else
      (debug_prover g.penv_env (fun _ -> Printf.sprintf "intro_lemma_main: trying to apply %s to %s\n" (show plem.plem_lid) (show p));
      match try_apply_intro_lemma g.penv_env plem.plem_lid plem.plem_prop_idx ctxt goal with
      | Some (| g', subgoals, k |) ->
        let g' = { g with penv_env = g'; penv_stack = breadcrumb :: g.penv_stack } in
        Some ((| g', subgoals, k |)
        <: (pg': penv &
          subgoals: list slprop_view &
          (res:prover_result_solved pg'.penv_env ctxt subgoals ->
            T.Tac (prover_result g.penv_env ctxt [goal]))))
      | None -> None)
    ) g.penv_plems
  | _ -> None

let intro_lemma_step
    (subprover : (pg: penv -> ctxt: list slprop_view -> goals: list slprop_view ->
      T.Tac (prover_result pg.penv_env ctxt goals)))
    (g:penv) (ctxt: list slprop_view) (goal: slprop_view) :
    T.Tac (option (prover_result g.penv_env ctxt [goal])) =
  if not g.penv_plems_enabled then None else
  match intro_lemma_main g ctxt goal with
  | None -> None
  | Some (| pg', subgoals, k |) ->
    let subresult = subprover pg' ctxt subgoals in
    if not (prover_result_is_solved subresult) then None else
    Some (k subresult)

let rec first_some #a (ks: list (unit -> T.Tac (option a))) : T.Tac (option a) =
  match ks with
  | [] -> None
  | k::ks ->
    match k () with
    | Some res -> Some res
    | None -> first_some ks

let show_slprops ps =
  String.concat "\n" (T.map (fun p -> show (elab_slprop p)) ps)

let pp_slprops ts = ts
  |> List.Tot.map elab_slprop
  |> sort_terms
  |> T.map pp
  |> separate hardline

let check_steps (pg: penv) (ctxt goals: list slprop_view) : T.Tac (pg':penv { pg'.penv_env == pg.penv_env }) =
  let pg = { pg with penv_steps = pg.penv_steps + 1 } in
  let max_steps = 10000 in
  if pg.penv_steps > max_steps then
    T.fail_doc ([
        text "Reached maximum number of steps (" ^^ text (show max_steps) ^^ text "), cannot prove:" ^^
          indent (pp_slprops goals);
        text "In the context:" ^^ indent (pp_slprops ctxt);
      ])
  else
    pg

let rec try_prove_core (pg: penv) (ctxt goals: list slprop_view) : T.Tac (prover_result pg.penv_env ctxt goals) =
  let g = pg.penv_env in
  let noop () : prover_result g ctxt goals =
    (| g, ctxt, goals, [], fun g'' ->
      cont_elab_refl g _ _ (VE_Refl _ _),
      cont_elab_refl g'' ([] @ goals) goals (VE_Refl _ _)
      <: T.Tac _ |) in
  match goals with
  | [] -> noop ()
  | goals ->
    debug_prover g (fun _ -> Printf.sprintf "proving\n%s\n from\n%s\n" (show_slprops goals) (show_slprops ctxt));
    let pg = check_steps pg ctxt goals in
    let step : option (prover_result g ctxt goals) =
      first_some [
        (fun _ -> elim_first g ctxt goals (unpack_and_norm_ctxt g));
        (fun _ -> elim_first g ctxt goals (elim_pure_step g));
        (fun _ -> elim_first g ctxt goals (elim_with_pure_step g));
        (fun _ -> elim_first g ctxt goals (elim_exists_step g));
        (fun _ -> elim_first g ctxt goals (eager_elim_lemma_step pg));
        (fun _ -> prove_first g ctxt goals (prove_pure g ctxt true));
        (fun _ -> prove_first g ctxt goals (prove_with_pure g ctxt true));
        (fun _ -> prove_first g ctxt goals (prove_exists g ctxt));
        (fun _ -> prove_first g ctxt goals (unpack_and_norm_goal g ctxt));
        (fun _ -> prove_first g ctxt goals (prove_atom_unamb g ctxt));
        (fun _ -> prove_first g ctxt goals (prove_atom g ctxt pg.penv_allow_amb));
        (fun _ -> prove_first g ctxt goals (prove_pure g ctxt false));
        (fun _ -> prove_first g ctxt goals (prove_with_pure g ctxt false));
        (fun _ -> prove_first g ctxt goals (eager_intro_lemma_step pg ctxt));

        (fun _ -> prove_first g ctxt goals (intro_lemma_step try_prove_core { pg with penv_allow_amb = false } ctxt));
      ] in
    match step with
    | Some step ->
      let (| g1, ctxt1, goals1, solved1, k1 |) = step in
      let pg1 = { pg with penv_env = g1 } in
      let step2 = try_prove_core pg1 ctxt1 goals1 in
      prover_result_join step step2
    | None ->
      noop ()

let try_prove (g: env) (ctxt goals: slprop) allow_amb : T.Tac (prover_result g [Unknown ctxt] [Unknown goals]) =
  let ctxt = RU.deep_compress_safe ctxt in
  let goals = RU.deep_compress_safe goals in
  let ss = Pulse.Checker.Prover.RewritesTo.get_subst_from_env g in
  let ctxt' = Pulse.Checker.Prover.Substs.ss_term ctxt ss in
  let goals' = Pulse.Checker.Prover.Substs.ss_term goals ss in
  let pg = mk_penv g allow_amb in
  let (| g1, ctxt1, goals1, solved1, k1 |) = try_prove_core pg [Unknown ctxt'] [Unknown goals'] in
  (| g1, ctxt1, goals1, solved1, fun (g2: env { env_extends g2 g1 }) ->
    let before, after = k1 g2 in
    let h1: slprop_equiv g ctxt' ctxt = RU.magic () in
    let h2: slprop_equiv g2 goals' goals = RU.magic () in
    cont_elab_equiv before h1 (VE_Refl _ _),
    cont_elab_equiv after (VE_Refl _ _) h2 |)

let prove rng (g: env) (ctxt goals: slprop) allow_amb :
    T.Tac (g':env { env_extends g' g } &
      ctxt': slprop &
      continuation_elaborator g ctxt g' (goals `tm_star` ctxt')) =
  let res = try_prove g ctxt goals allow_amb in
  if not (prover_result_is_solved res) then
    let (| g', ctxt', goals', solved', k |) = res in
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
    let (| g', ctxt', k |) = prover_result_solved_unpack res in
    let h: slprop_equiv g'
        (elab_slprops ([] @ ctxt' @ [Unknown goals]))
        (tm_star goals (RU.deep_compress_safe (elab_slprops ctxt'))) = RU.magic () in
    (| g', RU.deep_compress_safe (elab_slprops ctxt'), k_elab_equiv (k []) (VE_Refl _ _) h |)

#restart-solver
#push-options "--z3rlimit_factor 2"
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
#pop-options

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

let rec try_elim_core (pg: penv) (ctxt: list slprop_view) :
    T.Tac (prover_result_nogoals pg.penv_env ctxt) =
  let pg = check_steps pg ctxt [] in
  let g = pg.penv_env in
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
      (fun _ -> elim_first' g ctxt [] (eager_elim_lemma_step pg));
    ] in
  match step with
  | Some step ->
    let (| g1, ctxt1, goals1, solved1, k1 |) = step in
    let pg1 = { pg with penv_env = g1 } in
    let step2 = try_elim_core pg1 ctxt1 in
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
  let pg = mk_penv g false in
  let (| g', ctxt'', goals'', solved, k |) = try_elim_core pg [Unknown ctxt'] in
  let h: tot_typing g' (elab_slprops ctxt'') tm_slprop = RU.magic () in // TODO thread through prover
  (| g', elab_slprops ctxt'', h, fun post_hint post_hint_typ ->
    let h1: slprop_equiv g (elab_slprops ([] @ [Unknown ctxt'])) ctxt = (RU.magic() <: slprop_equiv g ctxt' ctxt) in
    let h2: slprop_equiv g' (elab_slprops (ctxt'' @ solved @ goals'')) (elab_slprops ([] @ solved @ ctxt'')) = RU.magic () in
    let h3: slprop_equiv g' (elab_slprops (ctxt'' @ [])) (elab_slprops ctxt'') = RU.magic () in
    let before, after = k g' in
    k_elab_trans (k_elab_equiv (before []) h1 (VE_Refl _ _))
      (k_elab_equiv (after ctxt'') h2 h3) post_hint post_hint_typ |)