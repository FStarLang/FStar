#light "off"
module FStar.Tactics.Basic
open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SC = FStar.Syntax.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util

type name = bv

(*
   f: x:int -> P
   ==================
      P
 *)
//A goal is typically of the form
//    G |- ?u : t
// where context = G
//       witness = ?u, although, more generally, witness is a partial solution and can be any term
//       goal_ty = t
type goal = {
    context :Env.env;
    witness :option<term>; //in most cases, we don't care to build a witness, e.g,. when proving a /\ b, we don't want to build AndIntro etc.
    goal_ty :term
}

type proofstate = {
    main_context : Env.env;         //the shared top-level context for all goals
    main_goal    : goal;            //this is read only; it helps keep track of the goal we started working on initially
    all_implicits: Env.implicits ;  //all the implicits currently open, partially resolved (unclear why we really need this)
    goals        : list<goal>;      //all the goals remaining to be solved
    transaction  : Unionfind.tx     //the unionfind transaction which we're currently working; to be rolled back if the tactic fails
}

type result<'a> =
    | Success of 'a * proofstate
    | Failed  of string    //error message
              * proofstate //the proofstate at time of failure

(* An exception, typically used only to simplify local data flow,
                 although, when not handled, it signifies a fatal error
                           in the tactic engine
*)
exception Failure of string

(* The main monad for tactics *)
type tac<'a> = proofstate -> result<'a>

(* monadic return *)
let ret (a:'a)
    : tac<'a>
    = fun p -> Success (a, p)

(* monadic bind *)
let bind (t1:tac<'a>)
         (t2:'a -> tac<'b>)
    : tac<'b>
    = fun p ->
        let tx = Unionfind.new_transaction () in //snapshot the state of the unionfind graph
        match t1 p with
        | Success (a, q) ->
          t2 a q
        | Failed(msg, q) ->
          Unionfind.rollback tx; //and restore the snapshot in case the tactic fails
          Failed(msg, q) //need to repack for tac<'b>

(* get : get the current proof state *)
let get : tac<proofstate> = fun p -> ret p p

let fail msg = fun p -> Failed(msg, p)

////////////////////////////////////////////////////////////////////
(* Some TRUSTED internal utilities *)

(* set : set the current proof state; shouldn't be exposed externally *)
let set p : tac<unit> = fun _ -> Success ((), p)

let solve goal solution =
    match goal.witness with
    | None ->
      failwith "Impossible"
    | Some w ->
      if Rel.teq_nosmt goal.context w solution
      then ()
      else raise (Failure(BU.format3 "%s does not solve %s : %s"
                            (Print.term_to_string solution)
                            (Print.term_to_string w)
                            (Print.term_to_string goal.goal_ty)))

let dismiss : tac<unit> =
    bind get (fun p ->
    set ({p with goals=List.tl p.goals}))

let add_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with goals=gs@p.goals}))

//Any function that directly calls these utilities is also trusted
//End: Trusted utilities
////////////////////////////////////////////////////////////////////

(* with_cur_goal: get's the current goal, Failed if none present *)
let with_cur_goal (f:goal -> tac<'a>) : tac<'a>
    = fun p ->
        match p.goals with
        | [] -> Failed ("No more goals", p)
        | hd::tl -> f hd p

(* focus_cur_goal: runs f on the current goal only, and then restores all the goals *)
let focus_cur_goal (f:tac<'a>) : tac<'a>
    = bind get (fun p ->
      match p.goals with
      | [] -> fail "No more goals"
      | hd::tl ->
        let q = {p with goals=[hd]} in
        bind (set q) (fun _ ->
        bind f       (fun a ->
        bind get     (fun q' ->
        let q2 = {q' with goals=q'.goals@tl} in
        bind (set q2) (fun _ ->
        ret a)))))

(* or_else: try t1; if it fails, try t2 *)
let or_else (t1:tac<'a>)
            (t2:tac<'a>)
    : tac<'a>
    = fun p ->
        let tx = Unionfind.new_transaction () in
        match t1 p with
        | Failed _ ->
          Unionfind.rollback tx;
          t2 p
        | q -> q

(* Applies t1 to the current head goal
   And t2 to all the the sub-goals produced by t1

   Collects the resulting goals of t2 along with the initial auxiliary goals
 *)
let seq (t1:tac<unit>)
        (t2:tac<unit>)
    : tac<unit>
    = fun p ->
        let tx = Unionfind.new_transaction () in
        let q = {p with goals=[List.hd p.goals]} in
        match t1 q with
        | Success (_, q') -> begin
              try
                  let goals = q'.goals |> List.collect (fun g ->
                      let q'' = {q' with goals=[g]} in
                      match t2 q'' with
                      | Failed (m,q3) -> raise (Failure m)
                      | Success(_,q3) -> q3.goals) in
                  Success((), ({q' with goals=goals@p.goals}))
              with
              | Failure m ->
                Unionfind.rollback tx;
                Failed(m, q)
         end
        | f ->
          Unionfind.rollback tx;
          f

let intros : tac<(list<name>)>
   = with_cur_goal (fun goal ->
         match U.destruct_typ_as_formula goal.goal_ty with
         | Some (U.QAll(bs, pats, body)) ->
           //TODO!
           //ignoring the qualifiers on bs and the pats for now
           //need to restore that!
           let names = List.map fst bs in
           let new_context = Env.push_binders goal.context bs in
           let new_goal = {
             context=new_context;
             witness=None; //body is squashed
             goal_ty=body
           } in
           bind dismiss (fun _ ->
           bind (add_goals [new_goal]) (fun _ ->
           ret names))
         | _ ->
           fail "Cannot intro this goal, expected a forall")

let intros_no_names = bind intros (fun _ -> ret ())

let imp_intro : tac<name> = failwith "Not yet implemented"

let split : tac<unit>
    = with_cur_goal (fun goal ->
        match U.destruct_typ_as_formula goal.goal_ty with
        | Some (U.BaseConn(l, args))
            when Ident.lid_equals l SC.and_lid ->
          let new_goals = args |> List.map (fun (a, _) ->
                 {goal with witness=None;
                            goal_ty=a}) in
          bind dismiss (fun _ ->
          add_goals new_goals)
        | _ ->
          fail "Cannot split this goal; expected a conjunction")

let exact (x:name)
    : tac<unit>
    = with_cur_goal (fun goal ->
        try let t = Env.lookup_bv goal.context x in
            if Rel.teq_nosmt goal.context t goal.goal_ty
            then let _ = match goal.witness with
                  | Some _ -> solve goal (S.bv_to_tm x)
                  | _ -> () in
                 dismiss
            else fail (BU.format3 "%s : %s does not exactly solve the goal %s"
                            (Print.bv_to_string x)
                            (Print.term_to_string t)
                            (Print.term_to_string goal.goal_ty))
       with _ ->
            fail (BU.format1 "Variable not found: %s" (Print.bv_to_string x)))

let rewrite (x:name) (e:term) : tac<unit>
    = with_cur_goal (fun goal ->
        try let t = Env.lookup_bv goal.context x in
            let sub_goal =
                let goal_ty = U.mk_eq t t (S.bv_to_tm x) e in
                {goal with goal_ty=U.mk_eq t t (S.bv_to_tm x) e;
                           witness=None} in //squashed equality proofs
            let goal = {goal with goal_ty=SS.subst [NT(x, e)] goal.goal_ty} in
            let new_goals = [sub_goal;goal] in
            bind dismiss (fun _ ->
            add_goals new_goals)
        with _ ->
             fail (BU.format1 "Variable not found: %s" (Print.bv_to_string x)))

let clear_hd (x:name) : tac<unit> = ret ()
let revert_hd (xs:list<name>) : tac<unit> = ret()

(* We often have VCs of the form
         forall x. x==e ==> P
   This tactic aims to recursively eliminate these equalities,
   rewrite the goal goal to
         forall x. P[e/x]
*)
let is_name x =
    match (SS.compress x).n with
    | Tm_name _ -> true
    | _ -> false

let as_name x =
    match (SS.compress x).n with
    | Tm_name x -> x
    | _ -> failwith "Not a name"

(* checks if t is of the form (x=e) ==> P *)
let destruct_equality_imp t =
    match U.destruct_typ_as_formula t with
    | Some (U.BaseConn(l, [(lhs, _); (rhs, _)]))
        when Ident.lid_equals l SC.imp_lid ->
      (match U.destruct_typ_as_formula lhs with
       | Some (U.BaseConn(eq, [(x, _); (e, _)]))
            when Ident.lid_equals eq SC.eq2_lid
            && is_name x ->
         Some (as_name x, e, rhs)
       | _ -> None)
    | _ -> None

let at_most_one (t:tac<'a>) : tac<'a> =
    bind t (fun a ->
    bind get (fun p ->
    match p.goals with
    | []
    | [_] -> ret a
    | _ -> fail "expected at most one goal remaining"))

let merge_sub_goals : tac<unit> = failwith "NYI"

let visit_strengthen (try_strengthen:tac<unit>)
    : tac<unit>
    = focus_cur_goal
        (or_else try_strengthen
                (with_cur_goal (fun goal ->
                    match U.destruct_typ_as_formula goal.goal_ty with
                    | None -> ret () //can't descend further; just return the goal unchanged

                    | Some (U.BaseConn(l, _))
                        when Ident.lid_equals l SC.and_lid ->
                      seq split
                          (bind (at_most_one try_strengthen) (fun _ ->
                                 merge_sub_goals))

                    | Some (U.QAll _) ->
                      bind intros (fun names ->
                      bind (at_most_one try_strengthen) (fun _ ->
                           (revert_hd names)))

                    | Some _ ->  //not yet handled
                        ret ())))

let rec simplify_eq_impl : tac<unit>
    = with_cur_goal (fun goal ->
      match destruct_equality_imp goal.goal_ty with
      | Some (x, e, rhs) ->
        bind imp_intro (fun eq_h ->
        bind (rewrite x e) (fun _ ->
        bind (exact eq_h) (fun _ ->
        //get rid of the eq_h in the context
        bind (clear_hd eq_h) (fun _ ->
        //dismiss the first sub-goal, i.e., prove that x=e
        //recursively visit rhs[e/x]
        visit_strengthen simplify_eq_impl))))
      | _ ->
        fail "Not an equality implication")