module ControlFlowPreconditions
open Steel.ST.Util


assume
val pred (x:int) : vprop

assume
val invert (x y:int) (_:squash (y <> 0))
  : STT unit (pred x) (fun _ -> pred (x / y))

open FStar.Tactics

let test (x:int) (y:int) (x' y':int) (_:squash (y <> 0))
 = assert (eq2 #(post_t unit) ((fun _ _ -> (fun (_:unit) -> pred (x / y))) x' y') (fun _ -> pred (x / y)))
      by (trefl())

// Even this fails now, with guards being trapped immmediately, rather than delayed and sent to SMT
// let test2 (x y:int)
//   : ST unit 
//        (pred x)
//        (fun _ -> emp)
//        (requires y <> 0)
//        (ensures fun _ -> True)
//   = let _ : squash (y <> 0) = () in
//     invert x y ();
//     drop _

(*  Move a lot of Steel.Effect.Common tactics here for experimentation *)

let solve_or_delay dict : Tac bool =
  norm [];
  let f = term_as_formula' (cur_goal ()) in
  match f with
  | Comp (Eq _) l r ->
    let lnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars l) in
    let rnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars r) in
    // Only solve equality if one of the terms is completely determined
    if lnbr = 0 || rnbr = 0 
    then (
      print ("About to solve logical goal ... " ^ formula_to_string f);
      trefl ();
      true
    )
    else false

  | _ -> print "Goal not eligible yet"; false

let rec pick_next_logical (dict: _) (fuel: nat) : Tac bool =
  if fuel = 0
  then false
  else match goals () with
  | [] -> true
  | _::_ -> if solve_or_delay dict then true else (later (); pick_next_logical dict (fuel - 1))

/// Special case for logical requires/ensures goals, which correspond only to equalities
let rec resolve_tac_logical (dict: _) : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    let fuel = List.Tot.length g in
    if pick_next_logical dict fuel then resolve_tac_logical dict
    else
      // This is only for requires/ensures constraints, which are equalities
      // There should always be a scheduling of constraints, but it can happen
      // that some uvar for the type of an equality is not resolved.
      // If we reach this point, we try to simply call the unifier instead of failing directly
      solve_all_eqs fuel



let rec solve_indirection_eqs (fuel: nat) : Tac unit =
  if fuel = 0
  then ()
  else match goals () with
  | [] -> ()
  | hd::_ ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        if is_return_eq l r then later() else (
          dump "About to attempt trefl ... ";
          trefl()
        );
        solve_indirection_eqs (fuel - 1)
    | _ -> later(); solve_indirection_eqs (fuel - 1)

let init_resolve_tac' (dict: _) : Tac unit =
  // We split goals between framing goals, about slprops (slgs)
  // and goals related to requires/ensures, that depend on slprops (loggs)
  let slgs, loggs = filter_goals (goals()) in
  // print ("SL Goals: \n" ^ print_goals slgs);
  // print ("Logical goals: \n" ^ print_goals loggs);

  // We first solve the slprops
  set_goals slgs;

  dump "START";
  
  // We solve all the maybe_emp goals first: All "extra" frames are directly set to emp
  solve_maybe_emps (List.Tot.length (goals ()));

  // We first solve all indirection equalities that will not lead to imprecise unification
  // i.e. we can solve all equalities inserted by layered effects, except the ones corresponding
  // to the preconditions of a pure return
  solve_indirection_eqs (List.Tot.length (goals()));

  // To debug, it is best to look at the goals at this stage. Uncomment the next line
  // dump "initial goals";

  // We can now solve the equalities for returns
  solve_return_eqs (List.Tot.length (goals()));

  // It is important to not normalize the return_pre equalities before solving them
  // Else, we lose some variables dependencies, leading to the tactic being stuck
  // See test7 in FramingTestSuite for more explanations of what is failing
  // Once unification has been done, we can then safely normalize and remove all return_pre
  norm_return_pre (List.Tot.length (goals()));

  dump "STARTING resolve_tac";
  // Finally running the core of the tactic, scheduling and solving goals
  resolve_tac dict;

  // We now solve the requires/ensures goals, which are all equalities
  // All slprops are resolved by now
  set_goals loggs;

  resolve_tac_logical dict

[@@ resolve_implicits; framing_implicit;
    override_resolve_implicits_handler framing_implicit [`%init_resolve_tac]]
let my_init_resolve_tac () : Tac unit = 
  init_resolve_tac' []

#push-options "--no_plugins --fuel 0 --ifuel 0 --query_stats --debug ControlFlowPreconditions --debug_level Tac,TacVerbose,Core"
let test_fails (x y:int)
  : ST unit 
       (pred x)
       (fun _ -> emp)
       (requires y <> 0)
       (ensures fun _ -> True)
  = invert x y ();
    drop _
