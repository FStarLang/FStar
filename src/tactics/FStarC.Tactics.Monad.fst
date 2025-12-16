(*
   Copyright 2008-2016 Microsoft Research

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

module FStarC.Tactics.Monad

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Tactics.Types
open FStarC.Tactics.Printing
open FStarC.Tactics.Common
open FStarC.Errors.Msg

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Listlike
open FStarC.Syntax.Print {}
module Setlike = FStarC.Class.Setlike
module Listlike = FStarC.Class.Listlike

module Err     = FStarC.Errors
module Range   = FStarC.Range
module U       = FStarC.Syntax.Util
module UF      = FStarC.Syntax.Unionfind
module Env     = FStarC.TypeChecker.Env
module Rel     = FStarC.TypeChecker.Rel
module Core    = FStarC.TypeChecker.Core

let dbg_Core         = Debug.get_toggle "Core"
let dbg_CoreEq       = Debug.get_toggle "CoreEq"
let dbg_RegisterGoal = Debug.get_toggle "RegisterGoal"
let dbg_TacFail      = Debug.get_toggle "TacFail"

let goal_ctr = mk_ref 0
let get_goal_ctr () = !goal_ctr
let incr_goal_ctr () = let v = !goal_ctr in goal_ctr := v + 1; v

let is_goal_safe_as_well_typed (g:goal) =
  let uv = g.goal_ctx_uvar in
  let all_deps_resolved =
      List.for_all 
          (fun uv -> 
            match UF.find uv.ctx_uvar_head with
            | Some t -> Setlike.is_empty (FStarC.Syntax.Free.uvars t)
            | _ -> false)
          (U.ctx_uvar_typedness_deps uv)
  in
  all_deps_resolved

let register_goal (g:goal) =
  if not (Options.compat_pre_core_should_register()) then () else
  let env = goal_env g in
  if env.phase1 || Options.lax () then () else
  let uv = g.goal_ctx_uvar in
  let i = Core.incr_goal_ctr () in
  if Allow_untyped? (U.ctx_uvar_should_check g.goal_ctx_uvar) then () else
  let env = {env with gamma = uv.ctx_uvar_gamma } in
  if !dbg_CoreEq
  then Format.print1 "(%s) Registering goal\n" (show i);
  let should_register = is_goal_safe_as_well_typed g in
  if not should_register
  then (
    if !dbg_Core || !dbg_RegisterGoal
    then Format.print1 "(%s) Not registering goal since it has unresolved uvar deps\n"
                     (show i);
        
    ()
  )
  else (
    if !dbg_Core || !dbg_RegisterGoal
    then Format.print2 "(%s) Registering goal for %s\n"
                     (show i)
                     (show uv);
    let goal_ty = U.ctx_uvar_typ uv in
    match FStarC.TypeChecker.Core.compute_term_type env goal_ty
    with
    | Inl (_, _, None) -> ()  // ghost is ok
    | Inl (_, _, Some (g, tok)) ->
      //register goal intentionally admits the guard; the goal is assumed to already be well-typed
      FStarC.TypeChecker.Core.commit_guard tok
    | Inr err ->
      let msg = 
          Format.fmt2 "Failed to check initial tactic goal %s because %s"
                     (show (U.ctx_uvar_typ uv))
                     (FStarC.TypeChecker.Core.print_error_short err)
      in
      Errors.log_issue uv.ctx_uvar_range Err.Warning_FailedToCheckInitialTacticGoal msg
  )

let mk_tac (f : proofstate -> __result 'a) : tac 'a = fun ps ->
  let Success (x, ps') = f (!ps) in
  ps := ps';
  x

let run (t:tac 'a) (ps:proofstate) : __result 'a =
  let ps = mk_ref ps in
  let x = t ps in
  Success (x, !ps)

let run_safe t ps =
    run t ps

let ret (x:'a) : tac 'a =
  fun _ -> x

let bind (t1:tac 'a) (t2:'a -> tac 'b) : tac 'b =
  fun ps ->
    let x = t1 ps in
    t2 x ps

instance monad_tac : monad tac = {
    return = ret;
    bind   = bind;
}

(* Set the current proofstate *)
let set (ps:proofstate) : tac unit =
  fun ps_ref -> ps_ref := ps

(* Get the current proof state *)
let get : tac proofstate =
  fun ps -> !ps

let traise e =
  fun _ -> raise e

let do_log ps (f : unit -> unit) : unit =
  if ps.tac_verb_dbg then
    f ()

let log (f : unit -> unit) : tac unit =
  fun ps -> do_log (!ps) f

let fail_doc (msg:error_message) =
  fun ps ->
        if !dbg_TacFail then
          do_dump_proofstate (!ps) ("TACTIC FAILING: " ^ renderdoc (hd msg));
        raise <| TacticFailure (msg, None)

let fail msg = fail_doc [text msg]

let catch (t : tac 'a) : tac (either exn 'a) =
    mk_tac (fun ps ->
            let idtable = !ps.main_context.identifier_info in
            let tx = UF.new_transaction () in
            try
              let Success (a, q) = run t ps in
              UF.commit tx;
              Success (Inr a, q)
            with | m ->
                UF.rollback tx;
                ps.main_context.identifier_info := idtable;
                Success (Inl m, ps)
           )

let trytac (t : tac 'a) : tac (option 'a) =
    bind (catch t) (fun r ->
    match r with
    | Inr v -> ret (Some v)
    | Inl _ -> ret None)

let trytac_exn (t : tac 'a) : tac (option 'a) =
    mk_tac (fun ps ->
    try run (trytac t) ps
    with | Errors.Error (_, msg, _, _) ->
           do_log ps (fun () -> Format.print1 "trytac_exn error: (%s)" (Errors.rendermsg msg));
           Success (None, ps))

let rec iter_tac f l =
  match l with
  | [] -> ret ()
  | hd::tl -> f hd ;! iter_tac f tl

let rec fold_right f l x =
  match l with
  | [] -> return x
  | hd::tl ->
    let! r = fold_right f tl x in
    f hd r

exception Bad of string

(* private *)
let nwarn = mk_ref 0
let check_valid_goal g =
  if Options.defensive () then begin
    try
      let env = (goal_env g) in
      if not (Env.closed env (goal_witness g)) then
        raise (Bad "witness");
      if not (Env.closed env (goal_type g)) then
        raise (Bad "goal type");
      let rec aux e =
          match Env.pop_bv e with
          | None -> ()
          | Some (bv, e) ->
            if not (Env.closed e bv.sort) then
              raise (Bad ("bv: " ^ show bv));
            aux e
      in
      aux env
    with
     | Bad culprit ->
       if !nwarn < 5 then begin
         Err.log_issue (goal_type g)
           Errors.Warning_IllFormedGoal
           (Format.fmt2 "The following goal is ill-formed (%s). Keeping calm and carrying on...\n<%s>\n\n" culprit (goal_to_string_verbose g));
         nwarn := !nwarn + 1
       end
  end

let check_valid_goals (gs:list goal) : unit =
  if Options.defensive () then
    List.iter check_valid_goal gs

let set_goals (gs:list goal) : tac unit =
  bind get (fun ps ->
  set ({ ps with goals = gs }))

let set_smt_goals (gs:list goal) : tac unit =
  bind get (fun ps ->
  set ({ ps with smt_goals = gs }))

let cur_goals : tac (list goal) =
  bind get (fun ps ->
  ret ps.goals)

let cur_goal_maybe_solved 
  : tac goal
  = bind cur_goals (function
    | [] -> fail "No more goals"
    | hd::tl -> ret hd)

let cur_goal : tac goal =
  bind cur_goals (function
  | [] -> fail "No more goals"
  | hd::tl ->
    match check_goal_solved' hd with
    | None -> ret hd
    | Some t ->
      Format.print2 "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
              (goal_to_string_verbose hd)
              (show t);
      ret hd)

let remove_solved_goals : tac unit =
  bind cur_goals (fun gs ->
  let gs = List.filter (fun g -> not (check_goal_solved g)) gs in
  set_goals gs)

let dismiss_all : tac unit = set_goals []

let dismiss : tac unit =
    bind get (fun ps ->
    set ({ps with goals=List.tl ps.goals}))

let replace_cur (g:goal) : tac unit =
    bind get (fun ps ->
    check_valid_goal g;
    set ({ps with goals=g::(List.tl ps.goals)}))

let getopts : tac FStarC.Options.optionstate =
    bind (trytac cur_goal_maybe_solved) (function
    | Some g -> ret g.opts
    | None -> ret (FStarC.Options.peek ()))

(* Some helpers to add goals, while also perhaps checking
 * that they are well formed (see check_valid_goal and
 * the --defensive debugging option. *)
let add_goals (gs:list goal) : tac unit =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with goals=gs@ps.goals}))

let add_smt_goals (gs:list goal) : tac unit =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with smt_goals=gs@ps.smt_goals}))

let push_goals (gs:list goal) : tac unit =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with goals=ps.goals@gs}))

let push_smt_goals (gs:list goal) : tac unit =
    bind get (fun ps ->
    check_valid_goals gs;
    set ({ps with smt_goals=ps.smt_goals@gs}))
(* /helpers *)

let add_implicits (i:implicits) : tac unit =
    bind get (fun ps ->
    set ({ps with all_implicits=i@ps.all_implicits}))

let new_uvar (reason:string) (env:env) (typ:typ)
             (sc_opt:option should_check_uvar)
             (uvar_typedness_deps:list ctx_uvar)
             (rng:Range.t) 
  : tac (term & ctx_uvar) =
    let should_check = 
      match sc_opt with
      | Some sc -> sc
      | _ -> Strict
    in
    let u, ctx_uvar, g_u =
        Env.new_tac_implicit_var reason rng env typ should_check uvar_typedness_deps None false
    in
    bind (add_implicits (Listlike.to_list g_u.implicits)) (fun _ ->
    ret (u, fst ctx_uvar))

let mk_irrelevant_goal (reason:string) (env:env) (phi:typ) (sc_opt:option should_check_uvar) (rng:Range.t) opts label : tac goal =
    let typ = U.mk_squash (env.universe_of env phi) phi in
    bind (new_uvar reason env typ sc_opt [] rng) (fun (_, ctx_uvar) ->
    let goal = mk_goal env ctx_uvar opts false label in
    ret goal)

let add_irrelevant_goal' (reason:string) (env:Env.env)
                         (phi:term) 
                         (sc_opt:option should_check_uvar)
                         (rng:Range.t)
                         (opts:FStarC.Options.optionstate)
                         (label:string) : tac unit =
    bind (mk_irrelevant_goal reason env phi sc_opt rng opts label) (fun goal ->
    add_goals [goal])

let add_irrelevant_goal (base_goal:goal) (reason:string) 
                        (env:Env.env) (phi:term)
                        (sc_opt:option should_check_uvar) : tac unit =
    add_irrelevant_goal' reason env phi sc_opt
                         base_goal.goal_ctx_uvar.ctx_uvar_range
                         base_goal.opts base_goal.label

let goal_of_guard (reason:string) (e:Env.env)
                  (f:term) (sc_opt:option should_check_uvar)
                  (rng:Range.t) : tac goal =
  bind getopts (fun opts ->
  bind (mk_irrelevant_goal reason e f sc_opt rng opts "") (fun goal ->
  let goal = { goal with is_guard = true } in
  ret goal))

let wrap_err_doc (pref:error_message) (t : tac 'a) : tac 'a =
  mk_tac fun ps ->
    try run t ps with
    | TacticFailure (msg, r) ->
      raise (TacticFailure (pref @ msg, r))
    | Errors.Error (err, msg, r, ctx) ->
      raise (Errors.Error (err, pref @ msg, r, ctx))
    | e ->
      raise e

let wrap_err (pref:string) (t : tac 'a) : tac 'a =
  wrap_err_doc [text ("'" ^ pref ^ "' failed")] t

let mlog f (cont : unit -> tac 'a) : tac 'a =
  log f;!
  cont ()

let if_verbose_tac f =
  let! ps = get in
  if ps.tac_verb_dbg
  then f ()
  else ret ()

let if_verbose f = if_verbose_tac (fun _ -> f(); ret ()) 

let compress_implicits : tac unit =
    bind get (fun ps ->
    let imps = ps.all_implicits in
    let g = { Env.trivial_guard with implicits = Listlike.from_list imps } in
    let imps = Rel.resolve_implicits_tac ps.main_context g in
    let ps' = { ps with all_implicits = List.map fst imps } in
    set ps')

module N = FStarC.TypeChecker.Normalize
let get_phi (g:goal) : option term = U.un_squash (N.unfold_whnf (goal_env g) (goal_type g))
let is_irrelevant (g:goal) : bool = Some? (get_phi g)
let goal_typedness_deps (g:goal) = U.ctx_uvar_typedness_deps g.goal_ctx_uvar

let set_uvar_expected_typ (u:ctx_uvar) (t:typ)
  : unit
  = let dec = UF.find_decoration u.ctx_uvar_head in
    UF.change_decoration u.ctx_uvar_head ({dec with uvar_decoration_typ = t })

let mark_uvar_with_should_check_tag (u:ctx_uvar) (sc:should_check_uvar)
  : unit
  = let dec = UF.find_decoration u.ctx_uvar_head in
    UF.change_decoration u.ctx_uvar_head ({dec with uvar_decoration_should_check = sc })

let mark_uvar_as_already_checked (u:ctx_uvar)
  : unit
  = mark_uvar_with_should_check_tag u Already_checked

let mark_goal_implicit_already_checked (g:goal)
  : unit
  = mark_uvar_as_already_checked g.goal_ctx_uvar

let goal_with_type g t
  : goal
  = let u = g.goal_ctx_uvar in
    set_uvar_expected_typ u t;
    g


let divide (n:int) (l : tac 'a) (r : tac 'b) : tac ('a & 'b) =
  let! p = get in
  let! lgs, rgs =
    try return (List.splitAt n p.goals) with
    | _ -> fail "divide: not enough goals"
  in
  let lp = { p with goals = lgs; smt_goals = [] } in
  set lp;!
  let! a = l in
  let! lp' = get in
  let rp = { lp' with goals = rgs; smt_goals = [] } in
  set rp;!
  let! b = r in
  let! rp' = get in
  let p' = { rp' with goals = lp'.goals @ rp'.goals;
                      smt_goals = lp'.smt_goals @ rp'.smt_goals @ p.smt_goals }
  in
  set p';!
  remove_solved_goals;!
  return (a, b)

(* focus: runs f on the current goal only, and then restores all the goals *)
(* There is a user defined version as well, we just use this one internally, but can't mark it as private *)
let focus (f:tac 'a) : tac 'a =
    let! (a, _) = divide 1 f (return ()) in
    return a
