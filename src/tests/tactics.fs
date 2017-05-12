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
module BU = FStar.Util
module SC = FStar.Syntax.Const
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

let rec visit (callback:tac<unit>) : tac<unit> =
      focus_cur_goal
        (or_else callback
                (with_cur_goal (fun goal ->
                    match U.destruct_typ_as_formula goal.goal_ty with
                    | None -> begin
                      match (SS.compress goal.goal_ty).n with
                      | Tm_meta _ ->
                        map_meta (visit callback)
                      | _ ->
                        bind (mlog <| (fun _ -> BU.print1 "Not a formula, split to smt %s\n" (P.term_to_string goal.goal_ty))) (fun _ ->
                        smt)
                      end

                    | Some (U.QEx _) ->  //not yet handled
                        bind (mlog <| (fun _ -> BU.print1 "Not yet handled: exists\n\tGoal is %s\n" (P.term_to_string goal.goal_ty))) (fun _ ->
                        ret ())

                    | Some (U.QAll(xs, _, _)) ->
                      bind intros (fun binders ->
                      //printfn "At forall %s" (List.map P.bv_to_string names |> String.concat ", ");
                      seq (visit callback) (
                      bind (revert_all_hd (List.map fst binders)) (fun _ ->
                      with_cur_goal (fun goal ->
                      bind (mlog <| (fun _ -> BU.print1 "After reverting intros, goal is %s\n" (goal_to_string goal))) (fun _ ->
                      ret())))))

                    | Some (U.BaseConn(l, _))
                        when Ident.lid_equals l SC.and_lid ->
                      bind (seq split (visit callback)) (fun _ ->
                            merge_sub_goals)

                    | Some (U.BaseConn(l, _))
                        when Ident.lid_equals l SC.imp_lid ->
                      bind imp_intro (fun h ->
                      seq (visit callback) revert)

                    | Some (U.BaseConn(l, _)) ->
                      or_else trivial smt)))


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
    match FStar.Tactics.Basic.run (visit simplify_eq_impl) p1 with
    | Success (_, p2) ->
      p2.goals |> List.iter (fun g ->
      printfn "Goal: %s" (P.term_to_string g.goal_ty))
    | Failed (msg, _) ->
      printfn "Tactic failed: %s" msg
