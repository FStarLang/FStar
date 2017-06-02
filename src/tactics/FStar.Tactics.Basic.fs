#light "off"
module FStar.Tactics.Basic
open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Ident
open FStar.TypeChecker.Env

module SP = FStar.Syntax.Print
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module SC = FStar.Syntax.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module TcErr  = FStar.TypeChecker.Err
module N = FStar.TypeChecker.Normalize

type name = bv

let tacdbg = BU.mk_ref false

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
    witness :option<term>; //there are cases where we don't care to build a witness, e.g,. when proving a /\ b, we don't want to build AndIntro etc.
    goal_ty :term
}

type proofstate = {
    main_context : Env.env;         //the shared top-level context for all goals
    main_goal    : goal;            //this is read only; it helps keep track of the goal we started working on initially
    all_implicits: Env.implicits ;  //all the implicits currently open, partially resolved (unclear why we really need this)
    goals        : list<goal>;      //all the goals remaining to be solved
    smt_goals    : list<goal>;      //goals that have been deferred to SMT
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

(* The main monad for tactics.
 * A record, so we can keep it somewhat encapsulated and
 * can more easily add things to it if need be.
 *)
type tac<'a> = {
    tac_f : proofstate -> result<'a>;
}

let mk_tac (f : proofstate -> result<'a>) : tac<'a> =
    { tac_f = f }

let run t p = t.tac_f p

(* monadic return *)
let ret (x:'a) : tac<'a> =
    mk_tac (fun p -> Success (x, p))

(* monadic bind *)
let bind (t1:tac<'a>) (t2:'a -> tac<'b>) : tac<'b> =
    mk_tac (fun p ->
//            let tx = Unionfind.new_transaction () in //snapshot the state of the unionfind graph
            match run t1 p with
            | Success (a, q) ->
                  run (t2 a) q
            | Failed(msg, q) ->
//              Unionfind.rollback tx; //and restore the snapshot in case the tactic fails
              Failed(msg, q))

let goal_to_string (g:goal) =
    let g_binders = Env.all_binders g.context |> Print.binders_to_string ", " in
    Util.format2 "%s |- %s" g_binders (Print.term_to_string g.goal_ty)

let tacprint (s:string)        = BU.print1 "TAC>> %s\n" s
let tacprint1 (s:string) x     = BU.print1 "TAC>> %s\n" (BU.format1 s x)
let tacprint2 (s:string) x y   = BU.print1 "TAC>> %s\n" (BU.format2 s x y)
let tacprint3 (s:string) x y z = BU.print1 "TAC>> %s\n" (BU.format3 s x y z)

let dump_goal ps goal =
    tacprint (goal_to_string goal);
    ()

let dump_proofstate ps msg =
    tacprint1 "State dump (%s):" msg;
    tacprint1 "ACTIVE goals (%s):" (string_of_int (List.length ps.goals));
    List.iter (dump_goal ps) ps.goals;
    tacprint1 "SMT goals (%s):" (string_of_int (List.length ps.smt_goals));
    List.iter (dump_goal ps) ps.smt_goals;
    ()

let print_proof_state (msg:string) : tac<unit> =
    mk_tac (fun p -> dump_proofstate p msg;
                     Success ((), p))

(* get : get the current proof state *)
let get : tac<proofstate> =
    mk_tac (fun p -> Success
    (p, p))

let log ps f =
    if !tacdbg
    then f()
    else ()

let mlog f : tac<unit> =
    bind get (fun ps -> log ps f; ret ())

// TODO: print something? unclear we really want that (certainly not without a debug flag)
// TODO: annotating this fails. bug?
let fail msg =
    mk_tac (fun p -> Failed (msg, p))

////////////////////////////////////////////////////////////////////
(* Some TRUSTED internal utilities *)

(* set : set the current proof state; shouldn't be exposed externally *)
let set (p:proofstate) : tac<unit> =
    mk_tac (fun _ -> Success ((), p))

let solve goal solution =
    match goal.witness with
    | None ->
      () //proof irrelevant goal
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

let dismiss_all : tac<unit> =
    bind get (fun p ->
    set ({p with goals=[]}))

let add_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with goals=gs@p.goals}))

let add_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with smt_goals=gs@p.smt_goals}))

let replace_cur (g:goal) : tac<unit> =
    bind dismiss (fun _ ->
    add_goals [g])

let add_implicits (i:Env.implicits) : tac<unit> =
    bind get (fun p ->
    set ({p with all_implicits=i@p.all_implicits}))

//Any function that directly calls these utilities is also trusted
//End: Trusted utilities
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
(* Some utilities on goals *)
let is_true t =
    match U.destruct_typ_as_formula t with
    | Some (U.BaseConn(l, [])) -> Ident.lid_equals l SC.true_lid
    | _ -> false
let is_false t =
    match U.destruct_typ_as_formula t with
    | Some (U.BaseConn(l, [])) -> Ident.lid_equals l SC.false_lid
    | _ -> false
let conj_goals g1 g2 =
    let t1 = g1.goal_ty in
    let t2 = g2.goal_ty in
    if is_true t1 || is_false t2 then g2
    else if is_true t2 || is_false t1 then g1
    else { g1 with goal_ty=U.mk_conj t1 t2 }
////////////////////////////////////////////////////////////////////


(* with_cur_goal: get's the current goal, Failed if none present *)
let with_cur_goal (nm:string) (f:goal -> tac<'a>) : tac<'a> =
    bind get (fun p ->
    match p.goals with
    | [] -> fail "No more goals"
    | hd::tl -> f hd)

let cur_goal : tac<goal> =
    mk_tac (fun ps -> match ps.goals with
                      | hd::_ -> Success (hd,ps)
                      | _ -> Failed ("No goals left", ps))

let set_cur_goal (g:goal) : tac<unit> =
    mk_tac (fun ps -> match ps.goals with
                      | hd::tl -> Success ((), {ps with goals = g::tl})
                      | _ -> Failed ("No goals left", ps))

let replace_point e1 e2 t =
    if U.term_eq e1 t then e2 else t

let treplace env (e1:term) (e2:term) (t:term) =
    U.bottom_fold (replace_point e1 e2) t

// eq hardcoded to univ #0
let grewrite_impl (t1:typ) (t2:typ) (e1:term) (e2:term) : tac<unit> =
    bind cur_goal (fun g -> 
        let env = g.context in
        let ok = match Rel.try_teq true env t1 t2 with
                 | None -> false
                 | Some g -> Rel.is_trivial g in
        if ok // Types match
        then begin
             let goal_ty' = treplace env e1 e2 (g.goal_ty) in
             bind (set_cur_goal ({g with goal_ty = goal_ty'})) (fun _ ->
             add_goals [{ context = g.context; witness = None; goal_ty = U.mk_eq2 U_zero t1 e1 e2}])
        end
        else begin
            TcErr.add_errors env ["Ill-type rewriting requested", e1.pos];
            fail "grewrite: Ill-typed rewriting requested"
        end
    )

let smt : tac<unit> =
    with_cur_goal "smt" (fun g ->
    bind dismiss (fun _ ->
    bind (add_goals [({g with goal_ty=U.t_true})]) (fun _ -> //TODO: why add a true goal?
    add_smt_goals [g])))

(* focus_cur_goal: runs f on the current goal only, and then restores all the goals *)
let focus_cur_goal (nm:string) (f:tac<'a>) : tac<'a>
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

(* cur_goal_and_rest: runs f on the current goal only,
                      runs g on the rest of the goals
                      Collects all the remaining goals, in order sub_goals f @ sub_goals g
*)
let cur_goal_and_rest (f:tac<'a>) (g:tac<'b>) : tac<('a*option<'b>)>
    = bind get (fun p ->
          match p.goals with
          | [] -> fail "No more goals"
          | [_] ->
            bind f (fun a ->
            ret (a, None))
          | hd::tl ->
            bind dismiss_all (fun _ ->
            bind (add_goals [hd]) (fun _ ->
            bind f (fun a ->
            bind get     (fun {goals=sub_goals_f} ->
            bind dismiss_all (fun _ ->
            bind (add_goals tl) (fun _ ->
            bind g (fun b ->
            bind (add_goals sub_goals_f) (fun _ ->
            ret (a, Some b))))))))))

(* or_else: try t1; if it fails, try t2 *)
let or_else (t1:tac<'a>) (t2:tac<'a>) : tac<'a> =
    mk_tac (fun p ->
//          let tx = Unionfind.new_transaction () in
            match t1.tac_f p with
            | Failed _ ->
//              Unionfind.rollback tx;
                t2.tac_f p
            | q -> q)

(* Applies t to each of the current goals
      fails if t fails on any of the goals
      collects each result in the output list *)
(* Needs to be thunked! Otherwise it will diverge on application to t *)
let rec map (t:tac<'a>): tac<(list<'a>)> =
    mk_tac (fun ps -> run (bind (cur_goal_and_rest t (map t))
                                (function
                                 | hd, None -> ret [hd]
                                 | hd, Some tl -> ret (hd::tl))
                          ) ps)

(* map_goal_term f:
        A trusted tactic that maps each goal.goal_ty to (f goal.goal_ty)
 *)
let map_goal_term (f:term -> term) : tac<unit> =
    let aux =
        with_cur_goal "map_goal" (fun g ->
        replace_cur ({g with goal_ty=f g.goal_ty}))
    in
    bind (map aux) (fun _ -> ret ())


(* map_meta: runs the tactic f on goal g, if the goal is Tm_meta(g, annot)
             and restores the goal to Tm_meta(f g, annot)
*)
let map_meta (t:tac<'a>) : tac<'a> =
    with_cur_goal "map_meta" (fun g ->
    match (SS.compress g.goal_ty).n with
    | Tm_meta(f, annot) ->
      bind (replace_cur ({g with goal_ty=f})) (fun _ -> //remove the meta
      bind t (fun a ->                              //run t, getting a
      bind (map_goal_term (fun tm ->
            if is_true tm then tm
            else S.mk (Tm_meta(tm, annot)) None tm.pos)) //put the meta back, re-using tm.pos for the position of the meta node
           (fun _ -> ret a))) //return a
    | _ -> fail "Not a meta")


(* Applies t1 to the current head goal
   And t2 to all the the sub-goals produced by t1

   Collects the resulting goals of t2 along with the initial auxiliary goals
 *)
let seq (t1:tac<unit>)
        (t2:tac<unit>)
    : tac<unit>
    = focus_cur_goal "seq"
          (bind t1 (fun _ ->
           bind (map t2) (fun _ -> ret ())))

(* intros:
      corresponds to a variadic version of
      val lemma_forall_intro_gtot  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (p x)) -> Lemma (forall (x:a). p x)
*)
//Q: should it instead be
//    val forall_intro_squash_gtot_join  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> GTot (squash (p x))) -> Tot (forall (x:a). p x)
//   ?? Note the additional squash on f
let intros : tac<binders>
   = with_cur_goal "intros" (fun goal ->
         match U.destruct_typ_as_formula goal.goal_ty with
         | Some (U.QAll(bs, pats, body)) ->
           //TODO!
           //ignoring the qualifiers on bs and the pats for now
           //need to restore that!
           let new_context = Env.push_binders goal.context bs in
           let new_goal = {
             context=new_context;
             witness=None; //body is squashed
             goal_ty=body
           } in
//           printfn "After intro %s, new_goal is %s"
//                    (Print.binders_to_string ", " bs)
//                    (Print.term_to_string body);
           bind dismiss (fun _ ->
           bind (add_goals [new_goal]) (fun _ ->
           bind (mlog <| (fun _ -> BU.print1 "intros: %s\n" (Print.binders_to_string ", " bs))) (fun _ ->
           ret bs)))
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

(* imp_intro:
        corresponds to
        val arrow_to_impl : #a:Type0 -> #b:Type0 -> f:(squash a -> GTot (squash b)) -> GTot (a ==> b)
*)
let imp_intro : tac<binder> =
    with_cur_goal "imp_intro" (fun goal ->
    match U.destruct_typ_as_formula goal.goal_ty with
    | Some (U.BaseConn(l, [(lhs, _); (rhs, _)]))
        when Ident.lid_equals l SC.imp_lid ->
      let name = S.new_bv None lhs in //(maybe_squash goal.context lhs) in
      let new_goal = {
        context = Env.push_bv goal.context name;
        witness = None;
        goal_ty = rhs; //maybe_squash goal.context rhs;
      } in
      bind dismiss (fun _ ->
      bind (add_goals [new_goal]) (fun _ ->
      bind (mlog <| (fun _ -> BU.print1 "imp_intro: %s\n" (Print.bv_to_string name))) (fun _ ->
      ret (S.mk_binder name))))
    | _ ->
      fail "Cannot intro this goal, expected an '==>'")

let split : tac<unit>
    = with_cur_goal "split" (fun goal ->
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

let trivial
    : tac<unit>
    = with_cur_goal "trivial" (fun goal ->
      let steps = [N.Reify; N.Beta; N.UnfoldUntil Delta_constant; N.Zeta; N.Iota; N.Primops] in
      let t = N.normalize steps goal.context goal.goal_ty in
      match U.destruct_typ_as_formula t with
      | Some (U.BaseConn(l, []))
            when Ident.lid_equals l SC.true_lid ->
        bind dismiss (fun _ ->
        add_goals ([{goal with goal_ty=t}]))
      | _ -> fail "Not a trivial goal")


let apply_lemma (tm:term)
    : tac<unit>
    = with_cur_goal "apply_lemma" (fun goal ->
        try let tm, t, guard = goal.context.type_of goal.context tm in //TODO: check that the guard is trivial
            if not (U.is_lemma t)
            then fail "apply_lemma: not a lemma"
            else let bs, comp = U.arrow_formals_comp t in
                 let uvs, implicits, subst =
                    List.fold_left (fun (uvs, guard, subst) (b, aq) ->
                            let b_t = SS.subst subst b.sort in
                            let u, _, g_u = FStar.TypeChecker.Util.new_implicit_var "apply_lemma" goal.goal_ty.pos goal.context b_t in
                            (u, aq)::uvs,
                            FStar.TypeChecker.Rel.conj_guard guard g_u,
                            S.NT(b, u)::subst)
                    ([], guard, [])
                    bs
                 in
                 let uvs = List.rev uvs in
                 let comp = SS.subst_comp subst comp in
                 let pre, post =
                      let c = U.comp_to_comp_typ comp in
                      match c.effect_args with
                      | pre::post::_ -> fst pre, fst post
                      | _ -> failwith "Impossible: not a lemma" in
                 match Rel.try_teq false goal.context post goal.goal_ty with
                 | None -> fail "apply_lemma: does not unify with goal"
                 | Some g ->
                   let g = Rel.solve_deferred_constraints goal.context g |> Rel.resolve_implicits in
                   let solution = S.mk_Tm_app tm uvs None goal.context.range in
                   let implicits = implicits.implicits |> List.filter (fun (_, _, _, tm, _, _) ->
                        let hd, _ = U.head_and_args tm in
                        match (SS.compress hd).n with
                        | Tm_uvar _ -> true //still unresolved
                        | _ -> false) in
                   solve goal solution;
                   let sub_goals =
                        {goal with witness=None; goal_ty=pre} //pre-condition is proof irrelevant
                        ::(implicits |> List.map (fun (_msg, _env, _uvar, term, typ, _) ->
                                {context=goal.context;
                                 witness=Some term;
                                 goal_ty=typ}))
                   in
                   bind (add_implicits g.implicits) (fun _ ->
                   bind dismiss (fun _ ->
                   add_goals sub_goals))
         with
            _ -> fail "apply_lemma: ill-typed term")

let exact (tm:term)
    : tac<unit>
    = with_cur_goal "exact" (fun goal ->
        try let _, t, guard = goal.context.type_of goal.context tm in //TODO: check that the guard is trivial
//            printfn ">>>At exact, env binders are %s" (Print.binders_to_string ", " (Env.all_binders goal.context));
            if Rel.teq_nosmt goal.context t goal.goal_ty
            then let _ = solve goal tm in
                 replace_cur ({goal with witness=None; goal_ty=U.t_true})
            else
                 let msg = BU.format3 "%s : %s does not exactly solve the goal %s"
                            (Print.term_to_string tm)
                            (Print.term_to_string t)
                            (Print.term_to_string goal.goal_ty) in
//                 printfn "%s" msg;
                 fail msg
       with e ->
//            printfn "Exception %A" e;
            fail (BU.format1 "Term is not typeable: %s" (Print.term_to_string tm)))

let rewrite (h:binder) : tac<unit>
    = with_cur_goal "rewrite" (fun goal ->
      bind (mlog <| (fun _ -> BU.print2 "+++Rewrite %s : %s\n" (Print.bv_to_string (fst h)) (Print.term_to_string (fst h).sort))) (fun _ ->
      match U.destruct_typ_as_formula (fst <| Env.lookup_bv goal.context (fst h)) with
      | Some (U.BaseConn(l, [_; (x, _); (e, _)]))
                when Ident.lid_equals l SC.eq2_lid ->
        (match (SS.compress x).n with
         | Tm_name x ->
           let goal = {goal with goal_ty=SS.subst [NT(x, e)] goal.goal_ty} in
           replace_cur goal
         | _ ->
           fail "Not an equality hypothesis with a variable on the LHS")
      | _ -> fail "Not an equality hypothesis"))

let clear : tac<unit>
    = with_cur_goal "clear" (fun goal ->
      match Env.pop_bv goal.context with
      | None -> fail "Cannot clear; empty context"
      | Some (x, env') ->
          let fns = FStar.Syntax.Free.names goal.goal_ty in
          if Util.set_mem x fns
          then fail "Cannot clear; variable appears in goal"
          else let new_goal = {goal with context=env'} in
               bind dismiss (fun _ ->
               add_goals [new_goal]))

let clear_hd (x:name) : tac<unit>
    = with_cur_goal "clear_hd" (fun goal ->
      match Env.pop_bv goal.context with
      | None -> fail "Cannot clear_hd; empty context"
      | Some (y, env') ->
          if not (S.bv_eq x y)
          then fail "Cannot clear_hd; head variable mismatch"
          else clear)

let revert : tac<unit>
    = with_cur_goal "revert" (fun goal ->
      match Env.pop_bv goal.context with
      | None -> fail "Cannot revert; empty context"
      | Some (x, env') ->
        let fvs = FStar.Syntax.Free.names goal.goal_ty in
        let new_goal =
            if Util.set_mem x fvs
            then { goal with
                     context = env';
                     goal_ty = U.mk_forall (FStar.TypeChecker.TcTerm.universe_of env' x.sort)
                                           x
                                           goal.goal_ty
                 }
            else { goal with
                     context = env';
                     goal_ty = U.mk_imp x.sort goal.goal_ty
                 }
         in
        bind dismiss (fun _ -> add_goals [new_goal]))

let revert_hd (x:name) : tac<unit>
    = with_cur_goal "revert_hd" (fun goal ->
      match Env.pop_bv goal.context with
      | None -> fail "Cannot revert_hd; empty context"
      | Some (y, env') ->
          if not (S.bv_eq x y)
          then fail (Util.format2 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                                (Print.bv_to_string x)
                                (Print.bv_to_string y))
          else revert)

let rec revert_all_hd (xs:list<name>)
    : tac<unit>
    = match xs with
      | [] -> ret ()
      | x::xs ->
        bind (revert_all_hd xs) (fun _ ->
        revert_hd x)

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
       | Some (U.BaseConn(eq, [(x, _); (e, _)])) //NS: The mk_eq using in TypeChecker.Util.add_equality_to_post_condition is not instantiating the type and universe properly. FIX IT! TODO
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
            then set ({p with goals=conj_goals g1 g2::rest})
            else let g1_binders = Env.all_binders g1.context |> Print.binders_to_string ", " in
                 let g2_binders = Env.all_binders g2.context |> Print.binders_to_string ", " in
                 fail (BU.format3 "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n"
                            (goal_to_string g1)
                            (goal_to_string g2)
                            (Env.eq_gamma g1.context g2.context |> BU.string_of_bool))
        | _ ->
         let goals = p.goals |> List.map (fun x -> Print.term_to_string x.goal_ty) |> String.concat "\n\t" in
         fail (BU.format1 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s" goals))

let rec visit (callback:tac<unit>) : tac<unit> =
      focus_cur_goal "visit_strengthen"
        (or_else callback
                (with_cur_goal "visit_strengthen_else" (fun goal ->
                    match U.destruct_typ_as_formula goal.goal_ty with
                    | None -> begin
                      match (SS.compress goal.goal_ty).n with
                      | Tm_meta _ ->
                        map_meta (visit callback)
                      | _ ->
                        bind (mlog <| (fun _ -> BU.print1 "Not a formula, split to smt %s\n" (Print.term_to_string goal.goal_ty))) (fun _ ->
                        smt)
                      end

                    | Some (U.QEx _) ->  //not yet handled
                        bind (mlog <| (fun _ -> BU.print1 "Not yet handled: exists\n\tGoal is %s\n" (Print.term_to_string goal.goal_ty))) (fun _ ->
                        ret ())

                    | Some (U.QAll(xs, _, _)) ->
                      bind intros (fun binders ->
                      //printfn "At forall %s" (List.map Print.bv_to_string names |> String.concat ", ");
                      seq (visit callback) (
                      bind (revert_all_hd (List.map fst binders)) (fun _ ->
                      with_cur_goal "inner" (fun goal ->
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

// Should probably be moved somewhere else
type order = | Lt | Eq | Gt

let order_binder (x:binder) (y:binder) : order =
    let n = S.order_bv (fst x) (fst y) in
    if n < 0 then Lt
    else if n = 0 then Eq
    else Gt


let proofstate_of_goal_ty env g =
    let g =
        {
          context=env;
          goal_ty=N.normalize [N.Beta] env g;
          witness=None
        } in
    {
        main_context=env;
        main_goal=g;
        all_implicits=[];
        goals=[g];
        smt_goals=[];
        transaction=Unionfind.new_transaction()
    }
