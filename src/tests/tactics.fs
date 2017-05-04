#light "off"
module FStar.Tests.Tactics
open FStar
open FStar.Util
open FStar.Syntax.Syntax
open FStar.Tests.Pars
module S  = FStar.Syntax.Syntax
module U  = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I  = FStar.Ident
module P  = FStar.Syntax.Print
module N  = FStar.TypeChecker.Normalize
open FStar.Ident
open FStar.Range
open FStar.Tests.Util
open FStar.Tactics.Basic

let g1 =
    let env = snd (Pars.init()) in
    let tm = Pars.tc "forall (x:int). x==0 \
                            ==> (forall (y:int). y==0 \
                                             ==> x==y) /\\ \
                                (forall (z:int). z==0 \
                                             ==> x==z)" in
    let tm = N.normalize [N.Beta] env tm in
    {
      context=env;
      goal_ty=tm;
      witness=None
    }

let proofstate_of_goal g = {
    main_context=snd (Pars.init());
    main_goal=g;
    all_implicits=[];
    goals=[g];
    smt_goals=[];
    transaction=Unionfind.new_transaction()
}


let rec simplify_eq_impl : tac<unit>
    = with_cur_goal (fun goal ->
          match destruct_equality_imp goal.goal_ty with
          | Some (x, e, rhs) -> //we have x==e ==> rhs
                 //imp_intro: introduce x=e in the context; goal is rhs
            bind imp_intro (fun eq_h ->
                 //rewrite: goals become [rhs[e/x]]
            bind (rewrite eq_h) (fun _ ->
                 //clear_hd: get rid of the eq_h in the context
                 //we're left with rhs[e/x]
            bind clear (fun _ ->
            visit simplify_eq_impl)))
          | _ ->
            printfn "%s is not an equality imp" (P.term_to_string goal.goal_ty);
            fail "Not an equality implication")


let test () =
    FStar.Main.process_args() |> ignore; //set the command line args for debugging
    printfn "Goal is %s" (P.term_to_string g1.goal_ty);
    let p1 = proofstate_of_goal g1 in
    match FStar.Tactics.Basic.run (FStar.Tactics.Basic.visit simplify_eq_impl) p1 with
    | Success (_, p2) ->
      p2.goals |> List.iter (fun g ->
      printfn "Goal: %s" (P.term_to_string g.goal_ty))
    | Failed (msg, _) ->
      printfn "Tactic failed: %s" msg
