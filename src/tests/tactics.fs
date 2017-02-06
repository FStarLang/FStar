#light "off"
module FStar.Tests.Tactics
open FStar
open FStar.Util
open FStar.Syntax.Syntax
open FStar.Tests.Pars
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module I = FStar.Ident
module P  = FStar.Syntax.Print
open FStar.Ident
open FStar.Range
open FStar.Tests.Util
open FStar.Tactics.Basic

let g1 =  {
    context=snd (Pars.init());
    goal_ty= Pars.tc "forall (x:int). x==0 \
                            ==> (forall (y:int). y==0 \
                                             ==> x==y)";
    witness=None
}

let proofstate_of_goal g = {
    main_context=snd (Pars.init());
    main_goal=g;
    all_implicits=[];
    goals=[g];
    transaction=Unionfind.new_transaction()
}
  
let test () = 
    let p1 = proofstate_of_goal g1 in
    match simplify_eq_impl p1 with
    | Success (_, p2) -> 
      p2.goals |> List.iter (fun g ->
      printfn "Goal: %s" (P.term_to_string g.goal_ty))
    | Failed (msg, _) ->
      printfn "Tactic failed: %s" msg                                    
 