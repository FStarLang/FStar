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
module N = FStar.TypeChecker.Normalize

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
//        let tx = Unionfind.new_transaction () in //snapshot the state of the unionfind graph
        match t1 p with
        | Success (a, q) ->
          t2 a q
        | Failed(msg, q) ->
//          Unionfind.rollback tx; //and restore the snapshot in case the tactic fails
          Failed(msg, q) //need to repack for tac<'b>

(* get : get the current proof state *)
let get : tac<proofstate> = fun p -> ret p p

let fail msg = fun p -> 
    printfn "%s" msg;
    Failed(msg, p)

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
//        let tx = Unionfind.new_transaction () in
        match t1 p with
        | Failed _ ->
//          Unionfind.rollback tx;
          printfn "or_else: t1 failed; trying t2";
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
//        let tx = Unionfind.new_transaction () in
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
//                Unionfind.rollback tx;
                Failed(m, q)
         end
        | f ->
//          Unionfind.rollback tx;
          f

(* intros:
      corresponds to a variadic version of
      val lemma_forall_intro_gtot  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (p x)) -> Lemma (forall (x:a). p x)
*)
//Q: should it instead be
//    val forall_intro_squash_gtot_join  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (squash (p x))) -> Tot (forall (x:a). p x)
//   ?? Note the additional squash on f
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
           printfn "After intro %s, new_goal is %s" 
                    (Print.binders_to_string ", " bs)
                    (Print.term_to_string body);
           bind dismiss (fun _ ->
           bind (add_goals [new_goal]) (fun _ ->
           ret names))
         | _ ->
           fail "Cannot intro this goal, expected a forall")

let intros_no_names = bind intros (fun _ -> ret ())

let mk_squash p =
    let sq = U.fvar_const FStar.Syntax.Const.squash_lid in
    U.mk_app sq [S.as_arg p]

let un_squash t = 
    let head, args = U.head_and_args t in
    match (U.un_uinst head).n, args with 
    | Tm_fvar fv, [(p, _)] 
        when S.fv_eq_lid fv FStar.Syntax.Const.squash_lid ->
      Some p
    | Tm_refine({sort={n=Tm_fvar fv}}, p), []
        when S.fv_eq_lid fv FStar.Syntax.Const.unit_lid ->
      Some p
    | _ -> 
      None

let maybe_squash env p = 
    let q = N.normalize [N.UnfoldUntil Delta_constant] env p in
    match un_squash q with 
    | None -> p //mk_squash p
    | _ -> p

(* imp_intro:
        corresponds to
        val arrow_to_impl : #a:Type0 -> #b:Type0 -> f:(squash a -> GTot (squash b)) -> GTot (a ==> b)
*)
let imp_intro : tac<name> =
    with_cur_goal (fun goal ->
    match U.destruct_typ_as_formula goal.goal_ty with
    | Some (U.BaseConn(l, [(lhs, _); (rhs, _)]))
        when Ident.lid_equals l SC.imp_lid ->
      let name = S.new_bv None (maybe_squash goal.context lhs) in
      let new_goal = {
        context = Env.push_bv goal.context name;
        witness = None;
        goal_ty = maybe_squash goal.context rhs;
      } in
      bind dismiss (fun _ ->
      bind (add_goals [new_goal]) (fun _ ->
      ret name))
    | _ ->
      fail "Cannot intro this goal, expected an '==>'")

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
            printfn ">>>At exact, env binders are %s" (Print.binders_to_string ", " (Env.all_binders goal.context));
            if Rel.teq_nosmt goal.context t goal.goal_ty
            then let _ = match goal.witness with
                  | Some _ -> solve goal (S.bv_to_tm x)
                  | _ -> () in
                 dismiss
            else let msg = BU.format3 "%s : %s does not exactly solve the goal %s"
                            (Print.bv_to_string x)
                            (Print.term_to_string t)
                            (Print.term_to_string goal.goal_ty) in
                 printfn "%s" msg;
                 fail msg
       with e ->
            printfn "Exception %A" e;
            fail (BU.format1 "Variable not found: %s" (Print.bv_to_string x)))

let rewrite (x:name) (e:term) : tac<unit>
    = let mk_eq x e = 
        mk (Tm_app(S.mk_Tm_uinst U.teq [U_zero], //TODO: should be universe of x.sort
                          [S.iarg x.sort; 
                           S.as_arg (S.bv_to_name x);
                           S.as_arg e])) 
           None 
           Range.dummyRange 
     in
     with_cur_goal (fun goal ->
        try let t = Env.lookup_bv goal.context x in
            let sub_goal =
                {goal with goal_ty=mk_eq x e;
                           witness=None} in //squashed equality proofs
            let goal = {goal with goal_ty=SS.subst [NT(x, e)] goal.goal_ty} in
            let new_goals = [sub_goal;goal] in
            bind dismiss (fun _ ->
            add_goals new_goals)
        with _ ->
             fail (BU.format1 "Variable not found: %s" (Print.bv_to_string x)))

let clear_hd (x:name) : tac<unit> 
    = with_cur_goal (fun goal -> 
      match Env.pop_bv goal.context with 
      | None -> fail "Cannot clear_hd; empty context"
      | Some (y, env') ->
          if not (S.bv_eq x y) 
          then fail "Cannot clear_hd; head variable mismatch"
          else let fns = FStar.Syntax.Free.names goal.goal_ty in
               if Util.set_mem x fns
               then fail "Cannot clear_hd; variable appears in goal"
               else let new_goal = {goal with context=env'} in
                    bind dismiss (fun _ ->
                    add_goals [new_goal]))

let revert_hd (x:name) : tac<unit> 
    = with_cur_goal (fun goal ->
      match Env.pop_bv goal.context with 
      | None -> fail "Cannot clear_hd; empty context"
      | Some (y, env') ->
          if not (S.bv_eq x y) 
          then fail "Cannot clear_hd; head variable mismatch"
          else let fns = FStar.Syntax.Free.names goal.goal_ty in
               if not (Util.set_mem x fns)
               then clear_hd x
               else let new_goal = 
                    match un_squash x.sort, un_squash goal.goal_ty with 
                    | Some p, Some q ->
                      { goal with 
                        context = env';
                        goal_ty = U.mk_imp p q
                      }
                    | _ -> 
                      { goal with 
                        context = env';
                        goal_ty = U.mk_forall x goal.goal_ty
                      } in
               bind dismiss (fun _ -> 
               add_goals [new_goal]))

let rec revert_all_hd (xs:list<name>) 
    : tac<unit>
    = match xs with 
      | [] -> ret ()
      | x::xs -> 
        bind (revert_hd x) (fun _ ->
        revert_all_hd xs)

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
       | Some (U.BaseConn(eq, [_; (x, _); (e, _)]))
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

let merge_sub_goals : tac<unit> = 
    bind get (fun p ->
    match p.goals with 
    | g1::g2::rest -> 
        if Env.eq_gamma g1.context g2.context
        && Option.isNone g1.witness
        && Option.isNone g2.witness
        then let new_goal = { g1 with goal_ty=U.mk_conj g1.goal_ty g2.goal_ty } in
             set ({p with goals=new_goal::rest})
        else fail "Cannot merge sub-goals: incompatible contexts"
    | _ -> fail "Cannot merge sub-goals: not enough sub-goals")

let rec visit_strengthen (try_strengthen:tac<unit>)
    : tac<unit>
    = focus_cur_goal
        (or_else try_strengthen
                (with_cur_goal (fun goal ->
                    match U.destruct_typ_as_formula goal.goal_ty with
                    | None -> 
                      printfn "Not a formula, finished %s" (Print.term_to_string goal.goal_ty);

                      ret () //can't descend further; just return the goal unchanged

                    | Some (U.BaseConn(l, _))
                        when Ident.lid_equals l SC.and_lid ->
                      seq split
                          (bind (at_most_one (visit_strengthen try_strengthen)) (fun _ ->
                                 merge_sub_goals))

                    | Some (U.QAll(xs, _, _)) ->
                      bind intros (fun names ->
                      printfn "At forall %s" (List.map Print.bv_to_string names |> String.concat ", ");
                      bind (at_most_one (visit_strengthen try_strengthen)) (fun _ ->
                           (revert_all_hd names)))

                    | Some q ->  //not yet handled
                        //printfn "Not yet handled: %A" q;
                        ret ())))

let rec simplify_eq_impl : tac<unit>
    = with_cur_goal (fun goal ->
          match destruct_equality_imp goal.goal_ty with
          | Some (x, e, rhs) -> //we have x==e ==> rhs
                 //imp_intro: introduce x=e in the context; goal is rhs
            bind imp_intro (fun eq_h ->
               printfn "Introduced %s:%s" (Print.bv_to_string eq_h) (Print.term_to_string eq_h.sort);
                 //rewrite: goals become [x=e; rhs[e/x]]
            bind (rewrite x e) (fun _ ->
                 //exact: dismiss the first sub-goal, i.e., prove that x=e
            with_cur_goal (fun g ->       
                 printfn "Trying exact on %s" (Print.term_to_string g.goal_ty);
            bind (exact eq_h) (fun _ ->
                 //clear_hd: get rid of the eq_h in the context
                 //we're left with rhs[e/x]
            bind (clear_hd eq_h) (fun _ -> 
            visit_strengthen simplify_eq_impl)))))
          | _ ->
            printfn "%s is not an equality imp" (Print.term_to_string goal.goal_ty);
            fail "Not an equality implication")