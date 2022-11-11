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

module FStar.Tactics.Monad

open FStar
open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Printing
open FStar.Tactics.Common

module O       = FStar.Options
module BU      = FStar.Compiler.Util
module Err     = FStar.Errors
module Range   = FStar.Compiler.Range
module S       = FStar.Syntax.Syntax
module U       = FStar.Syntax.Util
module UF      = FStar.Syntax.Unionfind
module Print   = FStar.Syntax.Print
module Env     = FStar.TypeChecker.Env
module Rel     = FStar.TypeChecker.Rel
module Core    = FStar.TypeChecker.Core

let goal_ctr = BU.mk_ref 0
let get_goal_ctr () = !goal_ctr
let incr_goal_ctr () = let v = !goal_ctr in goal_ctr := v + 1; v

let is_goal_safe_as_well_typed (g:goal) =
  let uv = g.goal_ctx_uvar in
  let all_deps_resolved =
      List.for_all 
          (fun uv -> 
            match UF.find uv.ctx_uvar_head with
            | Some t -> BU.set_is_empty (FStar.Syntax.Free.uvars t)
            | _ -> false)
          (U.ctx_uvar_typedness_deps uv)
  in
  all_deps_resolved

let register_goal (g:goal) =
  if not (Options.compat_pre_core_should_register()) then () else
  let env = goal_env g in
  if env.phase1 || env.lax then () else
  let uv = g.goal_ctx_uvar in
  let i = Core.incr_goal_ctr () in
  if Allow_untyped? (U.ctx_uvar_should_check g.goal_ctx_uvar) then () else
  let env = {env with gamma = uv.ctx_uvar_gamma } in
  if Env.debug env <| Options.Other "CoreEq"      
  then BU.print1 "(%s) Registering goal\n" (BU.string_of_int i);
  let should_register = is_goal_safe_as_well_typed g in
  if not should_register
  then (
    if Env.debug env <| Options.Other "Core"
    ||  Env.debug env <| Options.Other "RegisterGoal"
    then BU.print1 "(%s) Not registering goal since it has unresolved uvar deps\n"
                     (BU.string_of_int i);
        
    ()
  )
  else (
    if Env.debug env <| Options.Other "Core"
    ||  Env.debug env <| Options.Other "RegisterGoal"
    then BU.print2 "(%s) Registering goal for %s\n"
                     (BU.string_of_int i)
                     (Print.ctx_uvar_to_string uv);
    let goal_ty = U.ctx_uvar_typ uv in
    match FStar.TypeChecker.Core.compute_term_type_handle_guards env goal_ty false (fun _ _ -> true) 
    with
    | Inl _ -> ()
    | Inr err ->
      let msg = 
          BU.format2 "Failed to check initial tactic goal %s because %s"
                     (Print.term_to_string (U.ctx_uvar_typ uv))
                     (FStar.TypeChecker.Core.print_error_short err)
      in
      Errors.log_issue uv.ctx_uvar_range
                       (Err.Warning_FailedToCheckInitialTacticGoal, msg)
  )

(*
 * A record, so we can keep it somewhat encapsulated and
 * can more easily add things to it if need be.
 *)
type tac (a:Type0) = {
    tac_f : proofstate -> __result a;
}

let mk_tac (f : proofstate -> __result 'a) : tac 'a =
    { tac_f = f }

let run (t:tac 'a) (ps:proofstate) : __result 'a =
    t.tac_f ps

let run_safe t ps =
    if Options.tactics_failhard ()
    then run t ps
    else try run t ps
    with | Errors.Err (_, msg, _)
         | Errors.Error (_, msg, _, _) -> Failed (TacticFailure msg, ps)
         | e -> Failed (e, ps)

let ret (x:'a) : tac 'a =
    mk_tac (fun ps -> Success (x, ps))

let bind (t1:tac 'a) (t2:'a -> tac 'b) : tac 'b =
    mk_tac (fun ps ->
            match run t1 ps with
            | Success (a, q)  -> run (t2 a) q
            | Failed (msg, q) -> Failed (msg, q))

let (let!) t1 t2 = bind t1 t2

let idtac : tac unit = ret ()

(* Set the current proofstate *)
let set (ps:proofstate) : tac unit =
    mk_tac (fun _ -> Success ((), ps))

(* Get the current proof state *)
let get : tac proofstate =
    mk_tac (fun ps -> Success (ps, ps))

let traise e =
    mk_tac (fun ps -> Failed (e, ps))

let log ps (f : unit -> unit) : unit =
    if ps.tac_verb_dbg
    then f ()
    else ()

let fail (msg:string) =
    mk_tac (fun ps ->
        if Env.debug ps.main_context (Options.Other "TacFail") then
          do_dump_proofstate ps ("TACTIC FAILING: " ^ msg);
        Failed (TacticFailure msg, ps)
    )

let catch (t : tac 'a) : tac (either exn 'a) =
    mk_tac (fun ps ->
            let tx = UF.new_transaction () in
            match run t ps with
            | Success (a, q) ->
                UF.commit tx;
                Success (Inr a, q)
            | Failed (m, q) ->
                UF.rollback tx;
                let ps = { ps with freshness = q.freshness } in //propagate the freshness even on failures
                Success (Inl m, ps)
           )

let recover (t : tac 'a) : tac (either exn 'a) =
    mk_tac (fun ps ->
            match run t ps with
            | Success (a, q) -> Success (Inr a, q)
            | Failed (m, q)  -> Success (Inl m, q)
           )

let trytac (t : tac 'a) : tac (option 'a) =
    bind (catch t) (fun r ->
    match r with
    | Inr v -> ret (Some v)
    | Inl _ -> ret None)

let trytac_exn (t : tac 'a) : tac (option 'a) =
    mk_tac (fun ps ->
    try run (trytac t) ps
    with | Errors.Err (_, msg, _)
         | Errors.Error (_, msg, _, _) ->
           log ps (fun () -> BU.print1 "trytac_exn error: (%s)" msg);
           Success (None, ps))

let rec mapM (f : 'a -> tac 'b) (l : list 'a) : tac (list 'b) =
    match l with
    | [] -> ret []
    | x::xs ->
        bind (f x) (fun y ->
        bind (mapM f xs) (fun ys ->
        ret (y::ys)))

let rec iter_tac f l =
  match l with
  | [] -> ret ()
  | hd::tl -> f hd ;! iter_tac f tl


(* private *)
let nwarn = BU.mk_ref 0
let check_valid_goal g =
  if Options.defensive () then begin
    let b = true in
    let env = (goal_env g) in
    let b = b && Env.closed env (goal_witness g) in
    let b = b && Env.closed env (goal_type g) in
    let rec aux b e =
        match Env.pop_bv e with
        | None -> b
        | Some (bv, e) -> (
            let b = b && Env.closed e bv.sort in
            aux b e
            )
    in
    if not (aux b env) && !nwarn < 5
    then (Err.log_issue (goal_type g).pos
              (Errors.Warning_IllFormedGoal, BU.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                          (goal_to_string_verbose g));
          nwarn := !nwarn + 1)
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
      BU.print2 "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
              (goal_to_string_verbose hd)
              (Print.term_to_string t);
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

let getopts : tac FStar.Options.optionstate =
    bind (trytac cur_goal_maybe_solved) (function
    | Some g -> ret g.opts
    | None -> ret (FStar.Options.peek ()))

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
             (rng:Range.range) 
  : tac (term * ctx_uvar) =
    let should_check = 
      match sc_opt with
      | Some sc -> sc
      | _ -> Strict
    in
    let u, ctx_uvar, g_u =
        Env.new_tac_implicit_var reason rng env typ should_check uvar_typedness_deps None
    in
    bind (add_implicits g_u.implicits) (fun _ ->
    ret (u, fst (List.hd ctx_uvar)))

let mk_irrelevant_goal (reason:string) (env:env) (phi:typ) (sc_opt:option should_check_uvar) (rng:Range.range) opts label : tac goal =
    let typ = U.mk_squash (env.universe_of env phi) phi in
    bind (new_uvar reason env typ sc_opt [] rng) (fun (_, ctx_uvar) ->
    let goal = mk_goal env ctx_uvar opts false label in
    ret goal)

let add_irrelevant_goal' (reason:string) (env:Env.env)
                         (phi:term) 
                         (sc_opt:option should_check_uvar)
                         (rng:Range.range)
                         (opts:FStar.Options.optionstate)
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
                  (rng:Range.range) : tac goal =
  bind getopts (fun opts ->
  bind (mk_irrelevant_goal reason e f sc_opt rng opts "") (fun goal ->
  let goal = { goal with is_guard = true } in
  ret goal))

let wrap_err (pref:string) (t : tac 'a) : tac 'a =
    mk_tac (fun ps ->
            match run t ps with
            | Success (a, q) ->
                Success (a, q)

            | Failed (TacticFailure msg, q) ->
                Failed (TacticFailure (pref ^ ": " ^ msg), q)

            | Failed (e, q) ->
                Failed (e, q)
           )

let mlog f (cont : unit -> tac 'a) : tac 'a =
  let! ps = get in
  log ps f;
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
    let g = { Env.trivial_guard with implicits = imps } in
    let imps = Rel.resolve_implicits_tac ps.main_context g in
    let ps' = { ps with all_implicits = List.map fst imps } in
    set ps')
