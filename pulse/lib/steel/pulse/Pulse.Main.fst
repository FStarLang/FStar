module Pulse.Main

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
open FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate
open Pulse.Soundness
module Cfg = Pulse.Config
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer


let debug_main g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then T.print (s ())
  else ()
  
let main' (t:st_term) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.tot_typing g (fst r) (snd r)})
  = 
    match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse"
      then (
        T.print (Printf.sprintf "About to check pulse term:\n%s\n" (P.st_term_to_string t))
      );
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.check_tot_term g pre in
      if eq_tm ty tm_vprop
      then let pre_typing : tot_typing g pre tm_vprop = pre_typing in
           match t.term with
           | Tm_Abs _ ->
             let (| t, c, t_typing |) = Pulse.Checker.Abs.check_abs g t Pulse.Checker.check in
             //  let (| t, c, t_typing |) = check g t pre pre_typing None true in
             Pulse.Checker.Prover.debug_prover g
               (fun _ -> Printf.sprintf "\ncheck call returned in main with:\n%s\n"
                         (P.st_term_to_string t));
             debug_main g
               (fun _ -> Printf.sprintf "\nchecker call returned in main with:\n%s\nderivation=%s\n"
                         (P.st_term_to_string t)
                         (Pulse.Typing.Printer.print_st_typing t_typing));
             let refl_t = elab_comp c in
             let refl_e = elab_st_typing t_typing in
             soundness_lemma g t c t_typing;
             (refl_e, refl_t)
           | _ -> fail g (Some t.range) "main: top-level term not a Tm_Abs"
      else fail g (Some t.range) "pulse main: cannot typecheck pre at type vprop"

let join_smt_goals () : Tac unit =
  let open FStar.Tactics.V2 in
  let open FStar.List.Tot in

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals before join";

  (* Join *)
  let smt_goals = smt_goals () in
  set_goals (goals () @ smt_goals);
  set_smt_goals [];
  let n = List.Tot.length (goals ()) in
  ignore (repeat join);

  (* Heuristic rlimit setting :). Increase by 2 for every joined goal.
  Default rlimit is 5, so this is "saving" 3 rlimit units per joined
  goal. *)
  if not (Nil? (goals ())) then (
    let open FStar.Mul in
    let rlimit = get_rlimit() + (n-1)*2 in
    set_rlimit rlimit
  );

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals after join";

  ()

let main t pre : RT.dsl_tac_t = fun g ->
  (* If we will be joining goals, make sure the guards from reflection
  typing end up as SMT goals. This is anyway the default behavior but it
  doesn't hurt to be explicit. *)
  set_guard_policy SMT;

  let res = main' t pre g in

  if Cfg.join_goals && not (RU.debug_at_level g "DoNotJoin") then
    join_smt_goals();
  res

[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : RT.dsl_tac_t
  = fun env ->
      match Pulse.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col with
      | Inl st_term ->
        main st_term tm_emp env
      | Inr (msg, range) ->
        T.fail (Printf.sprintf "%s: %s"
                  (T.range_to_string range)
                  msg)
