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

(* The main monad for tactics *)
type tac<'a> = {
    tac_f:proofstate -> result<'a>;
    tac_name:string;
    kernel:bool;
}

let as_tac name b f = {
    tac_f=f;
    tac_name=name;
    kernel=b;
}

let kernel_tac n t = {tac_f=t; tac_name=n; kernel=true}
let user_tac n t = {tac_f=t; tac_name=n; kernel=false}
let name_tac n t = {t with tac_name=n; kernel=false}

let run t p = t.tac_f p

let debug p msg =
    printfn "TAC (ngoals=%d, maingoal=%s, rest=%s):\n\tTAC>> %s\n"
        (List.length p.goals)
        (match p.goals with [] -> "[]" | _ -> Print.term_to_string (List.hd p.goals).goal_ty)
        (match p.goals with [] -> "" | _ -> List.tl p.goals |> List.map (fun x -> Print.term_to_string x.goal_ty) |> String.concat ";;")
        msg

(* monadic return *)
let ret (a:'a)
    : tac<'a>
    = kernel_tac "return" (fun p -> Success (a, p))

(* monadic bind *)
let bind (t1:tac<'a>)
         (t2:'a -> tac<'b>)
    : tac<'b>
    = kernel_tac "bind"
        (fun p ->
//        let tx = Unionfind.new_transaction () in //snapshot the state of the unionfind graph
            if not t1.kernel then debug p t1.tac_name;
            match t1.tac_f p with
            | Success (a, q) ->
              let t2 = t2 a in
              if not t2.kernel then debug q t2.tac_name;
              t2.tac_f q
            | Failed(msg, q) ->
            if not t1.kernel then debug p (BU.format1 "%s failed!" t1.tac_name);
    //          Unionfind.rollback tx; //and restore the snapshot in case the tactic fails
              Failed(msg, q)) //need to repack for tac<'b>

(* get : get the current proof state *)
let get : tac<proofstate> = kernel_tac "get" (fun p -> Success(p, p))

let fail msg = kernel_tac "fail" (fun p ->
    printfn ">>>>>%s" msg;
    Failed(msg, p))

let show = kernel_tac "show" (fun p -> debug p "debug"; Success((), p))
////////////////////////////////////////////////////////////////////
(* Some TRUSTED internal utilities *)

(* set : set the current proof state; shouldn't be exposed externally *)
let set p : tac<unit> = kernel_tac "set" (fun _ -> Success ((), p))

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

let dismiss_all : tac<unit> =
    bind get (fun p ->
    set ({p with goals=[]}))

let add_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with goals=gs@p.goals}))

let add_smt_goals (gs:list<goal>) : tac<unit> =
    bind get (fun p ->
    set ({p with smt_goals=gs@p.smt_goals}))

let replace (g:goal) : tac<unit> =
    bind dismiss (fun _ ->
    add_goals [g])

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
let with_cur_goal (nm:string) (f:goal -> tac<'a>) : tac<'a>
    = name_tac nm (bind get (fun p ->
        match p.goals with
        | [] -> fail "No more goals"
        | hd::tl -> f hd))

let smt : tac<unit> =
    with_cur_goal "smt" (fun g ->
    bind dismiss (fun _ ->
    bind (add_goals [({g with goal_ty=U.t_true})]) (fun _ ->
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
let or_else (t1:tac<'a>)
            (t2:tac<'a>)
    : tac<'a>
    = kernel_tac "or_else" (fun p ->
//        let tx = Unionfind.new_transaction () in
        debug p (BU.format1 "or_else: trying %s" t1.tac_name);
        match t1.tac_f p with
        | Failed _ ->
//          Unionfind.rollback tx;
          debug p (BU.format2 "or_else: %s failed; trying %s" t1.tac_name t2.tac_name);
          t2.tac_f p
        | q -> q)

(* Applies t to each of the current goals
      fails if t fails on any of the goals
      collects each result in the output list *)
let rec map (t:tac<'a>): tac<(list<'a>)> =
    user_tac "map"
        (fun p ->
          run ((bind (cur_goal_and_rest t (map t))
                     (function
                          | hd, None -> ret [hd]
                          | hd, Some tl -> ret (hd::tl)))) p)

(* map_goal_term f:
        A trusted tactic that maps each goal.goal_ty to (f goal.goal_ty)
 *)
let private map_goal_term (f:term -> term) : tac<unit> =
    let aux =
        with_cur_goal "map_goal" (fun g ->
        replace {g with goal_ty=f g.goal_ty})
    in
    bind (map aux) (fun _ -> ret ())


(* map_meta: runs the tactic f on goal g, if the goal is Tm_meta(g, annot)
             and restores the goal to Tm_meta(f g, annot)
*)
let map_meta (t:tac<'a>) : tac<'a> =
    with_cur_goal "map_meta" (fun g ->
    match (SS.compress g.goal_ty).n with
    | Tm_meta(f, annot) ->
      bind (replace ({g with goal_ty=f})) (fun _ -> //remove the meta
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
           ret bs))
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
    with_cur_goal "imp_intro" (fun goal ->
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
    = with_cur_goal "split" (fun goal ->
        match U.destruct_typ_as_formula goal.goal_ty with
        | Some (U.BaseConn(l, args))
            when Ident.lid_equals l SC.and_lid ->
          let new_goals = args |> List.map (fun (a, _) ->
                 {goal with witness=None;
                            goal_ty=a}) in
          bind dismiss (fun _ ->
          bind (add_goals new_goals) (fun _ ->
          show))
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


let exact (x:name)
    : tac<unit>
    = with_cur_goal "exact" (fun goal ->
        try let t = Env.lookup_bv goal.context x in
//            printfn ">>>At exact, env binders are %s" (Print.binders_to_string ", " (Env.all_binders goal.context));
            if Rel.teq_nosmt goal.context t goal.goal_ty
            then let _ = match goal.witness with
                  | Some _ -> solve goal (S.bv_to_tm x)
                  | _ -> () in
                 dismiss
            else
                 let msg = BU.format3 "%s : %s does not exactly solve the goal %s"
                            (Print.bv_to_string x)
                            (Print.term_to_string t)
                            (Print.term_to_string goal.goal_ty) in
//                 printfn "%s" msg;
                 fail msg
       with e ->
//            printfn "Exception %A" e;
            fail (BU.format1 "Variable not found: %s" (Print.bv_to_string x)))

let rewrite (x:name) (e:term) : tac<unit>
    = let mk_eq (env:FStar.TypeChecker.Env.env) x e =
        U.mk_eq2 (env.universe_of env x.sort) x.sort (S.bv_to_name x) e
     in
     with_cur_goal "rewrite" (fun goal ->
        try let t = Env.lookup_bv goal.context x in
            let sub_goal =
                {goal with goal_ty=mk_eq goal.context x e;
                           witness=None} in //squashed equality proofs
            let goal = {goal with goal_ty=SS.subst [NT(x, e)] goal.goal_ty} in
            let new_goals = [sub_goal;goal] in
            bind dismiss (fun _ ->
            add_goals new_goals)
        with _ ->
             fail (BU.format1 "Variable not found: %s" (Print.bv_to_string x)))

let clear_hd (x:name) : tac<unit>
    = with_cur_goal "clear_hd" (fun goal ->
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

let revert : tac<unit>
    = with_cur_goal "revert" (fun goal ->
      match Env.pop_bv goal.context with
      | None -> fail "Cannot clear_hd; empty context"
      | Some (x, env') ->
        let fns = FStar.Syntax.Free.names goal.goal_ty in
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

let revert_hd (x:name) : tac<unit>
    = with_cur_goal "revert_hd" (fun goal ->
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
    name_tac "merge_sub_goals"
    (bind get (fun p ->
        match p.goals with
        | g1::g2::rest ->
            if Env.eq_gamma g1.context g2.context
            && Option.isNone g1.witness
            && Option.isNone g2.witness
            then set ({p with goals=conj_goals g1 g2::rest})
            else fail "Cannot merge sub-goals: incompatible contexts"
        | _ ->
         let goals = p.goals |> List.map (fun x -> Print.term_to_string x.goal_ty) |> String.concat "\n\t" in
         fail (BU.format1 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s" goals)))

let rec visit (callback:tac<unit>)
    : tac<unit>
    = focus_cur_goal "visit_strengthen"
        (or_else callback
                (with_cur_goal "visit_strengthen_else" (fun goal ->
                    match U.destruct_typ_as_formula goal.goal_ty with
                    | None -> begin
                      match (SS.compress goal.goal_ty).n with
                      | Tm_meta _ ->
                        map_meta (visit callback)
                      | _ ->
                        printfn "Not a formula, split to smt %s" (Print.term_to_string goal.goal_ty);
                        smt
                      end

                    | Some (U.QEx _) ->  //not yet handled
                        BU.print1 "Not yet handled: exists\n\tGoal is %s\n" (Print.term_to_string goal.goal_ty);
                        ret ()

                    | Some (U.QAll(xs, _, _)) ->
                      bind intros (fun binders ->
                      //printfn "At forall %s" (List.map Print.bv_to_string names |> String.concat ", ");
                      bind (visit callback) (fun _ ->
                           (revert_all_hd (List.map fst binders))))

                    | Some (U.BaseConn(l, _))
                        when Ident.lid_equals l SC.and_lid ->
                      bind (seq split (visit callback)) (fun _ ->
                            merge_sub_goals)

                    | Some (U.BaseConn(l, _))
                        when Ident.lid_equals l SC.imp_lid ->
                      bind imp_intro (fun h ->
                      bind (visit callback) (fun _ ->
                      revert_hd h))

                    | Some (U.BaseConn(l, _)) ->
                      or_else trivial smt)))

let fstar_tactics_lid s = Ident.lid_of_path (["FStar"; "Tactics"]@[s]) Range.dummyRange
let by_tactic_lid = fstar_tactics_lid "by_tactic"
let lid_as_tm l = S.lid_as_fv l Delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid s)
let fstar_tactics_term   = mk_tactic_lid_as_term "term"
let fstar_tactics_env    = mk_tactic_lid_as_term "env"
let fstar_tactics_binder = mk_tactic_lid_as_term "binder"
let fstar_tactics_binders= mk_tactic_lid_as_term "binders"
let fstar_tactics_goal   = mk_tactic_lid_as_term "goal"
let fstar_tactics_goals  = mk_tactic_lid_as_term "goals"
let fstar_tactics_Failed = S.fv_to_tm (S.lid_as_fv (fstar_tactics_lid "Failed") Delta_constant (Some Data_ctor))
let fstar_tactics_Success= S.fv_to_tm (S.lid_as_fv (fstar_tactics_lid "Success") Delta_constant (Some Data_ctor))
let lid_Mktuple2 = U.mk_tuple_data_lid 2 Range.dummyRange

let embed_binder (b:binder) : term = S.bv_to_name (fst b)
let unembed_binder (t:term) : binder =
    let t = U.unascribe t in
    match t.n with
    | Tm_name bv -> S.mk_binder bv
    | _ -> failwith "Not an embedded binder"

let embed_pair (x:('a * 'b)) (embed_a:'a -> term) (t_a:term) (embed_b:'b -> term) (t_b:term) : term =
    S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm lid_Mktuple2) [U_zero;U_zero])
                [S.iarg t_a;
                 S.iarg t_b;
                 S.as_arg (embed_a (fst x));
                 S.as_arg (embed_b (snd x))]
                None
                Range.dummyRange

let unembed_pair (pair:term) (unembed_a:term -> 'a) (unembed_b:term -> 'b) : ('a * 'b) =
    let pairs = U.unascribe pair in
    let hd, args = U.head_and_args pair in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_; _; (a, _); (b, _)] when S.fv_eq_lid fv lid_Mktuple2 ->
      unembed_a a, unembed_b b
    | _ -> failwith "Not an embedded pair"


let rec embed_list (l:list<'a>) (embed_a: ('a -> term)) (t_a:term) : term =
    match l with
    | [] -> S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm FStar.Syntax.Const.nil_lid) [U_zero])
                        [S.iarg t_a]
                        None
                        Range.dummyRange
    | hd::tl ->
            S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm FStar.Syntax.Const.cons_lid) [U_zero])
                        [S.iarg t_a;
                         S.as_arg (embed_a hd);
                         S.as_arg (embed_list tl embed_a t_a)]
                        None
                        Range.dummyRange

let rec unembed_list (l:term) (unembed_a: (term -> 'a)) : list<'a> =
    let l = U.unascribe l in
    let hd, args = U.head_and_args l in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, _
        when S.fv_eq_lid fv SC.nil_lid -> []

    | Tm_fvar fv, [_t; (hd, _); (tl, _)]
        when S.fv_eq_lid fv SC.cons_lid ->
      unembed_a hd :: unembed_list tl unembed_a

    | _ ->
      failwith (BU.format1 "Not an embedded list: %s" (Print.term_to_string l))

let embed_binders l = embed_list l embed_binder fstar_tactics_binder
let unembed_binders t = unembed_list t unembed_binder

let embed_env (env:Env.env) : term = embed_list (Env.all_binders env) embed_binder fstar_tactics_binder

let unembed_env (env:Env.env) (embedded_env:term) : Env.env =
    let binders = unembed_list embedded_env unembed_binder in
    Env.push_binders env binders

let embed_goal (g:goal) : term =
    embed_pair (g.context, g.goal_ty) embed_env fstar_tactics_env (fun x -> x) fstar_tactics_term

let unembed_goal (env:Env.env) (t:term) : goal =
    let env, goal_ty = unembed_pair t (unembed_env env) (fun x -> x) in
    {
      context = env;
      goal_ty = goal_ty;
      witness = None //TODO: sort this out for proof-relevant goals
    }

let embed_goals (l:list<goal>) : term = embed_list l embed_goal fstar_tactics_goal
let unembed_goals (env:Env.env) (egs:term) : list<goal> = unembed_list egs (unembed_goal env)

type state = list<goal> * list<goal>

let embed_state (s:state) : term =
    embed_pair s embed_goals fstar_tactics_goals embed_goals fstar_tactics_goals

let unembed_state (env:Env.env) (s:term) : state =
    let s = U.unascribe s in
    unembed_pair s (unembed_goals env) (unembed_goals env)

let embed_unit (u:unit) : term = SC.exp_unit
let unembed_unit (_:term) :unit = ()

let embed_string (s:string) : term =
    let bytes = BU.unicode_of_string s in
    S.mk (Tm_constant(FStar.Const.Const_string(bytes, Range.dummyRange)))
         None
         Range.dummyRange

let unembed_string (t:term) : string =
    let t = U.unascribe t in
    match t.n with
    | Tm_constant(FStar.Const.Const_string(bytes, _)) ->
      BU.string_of_unicode bytes
    | _ ->
      failwith "Not an embedded string"

let embed_result (res:result<'a>) (embed_a:'a -> term) (t_a:typ) : term =
    match res with
    | Failed (msg, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_string msg);
                   S.as_arg (embed_state (ps.goals, ps.smt_goals))]
                  None
                  Range.dummyRange
    | Success (a, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_a a);
                   S.as_arg (embed_state (ps.goals, ps.smt_goals))]
                  None
                  Range.dummyRange

let unembed_result (env:Env.env) (res:term) : either<state, (string * state)> =
    let res = U.unascribe res in
    let hd, args = U.head_and_args res in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_t; _unit; (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid "Success") ->
      Inl (unembed_state env embedded_state)

    | Tm_fvar fv, [_t; (embedded_string, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid "Failed") ->
      Inr (unembed_string embedded_string, unembed_state env embedded_state)

    | _ -> failwith (BU.format1 "Not an embedded result: %s" (Print.term_to_string res))

let mk_tactic_interpretation (ps:proofstate) (env:Env.env) (t:tac<'a>) (embed_a:'a -> term) (t_a:typ) (args:args) : term =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [_unit; (embedded_state, _)] ->
    printfn "Reached forall_intro_interpretation, goals are: %s" (Print.term_to_string embedded_state);
    let goals, smt_goals = unembed_state env embedded_state in
    let ps = {ps with goals=goals; smt_goals=smt_goals} in
    let res = run t ps in
    embed_result res embed_a t_a
  | _ ->
    failwith ("Unexpected application of 'forall_intro'")

let primitive_steps ps env : list<N.primitive_step> =
    [{N.name=fstar_tactics_lid "forall_intros";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation ps env intros embed_binders fstar_tactics_binders};

     {N.name=fstar_tactics_lid "smt";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation ps env smt embed_unit FStar.TypeChecker.Common.t_unit};

     {N.name=fstar_tactics_lid "revert";
      N.arity=2;
      N.interpretation=mk_tactic_interpretation ps env revert embed_unit FStar.TypeChecker.Common.t_unit}]

let evaluate_user_tactic : tac<unit>
    = with_cur_goal "evaluate_user_tactic" (fun goal ->
      bind get (fun proof_state ->
          let hd, args = U.head_and_args goal.goal_ty in
          match (U.un_uinst hd).n, args with
          | Tm_fvar fv, [(tactic, _); (assertion, _)]
                when S.fv_eq_lid fv by_tactic_lid ->
            (* We're making (reify (tactic ()) [(goal)] *)
            let tm = S.mk_Tm_app (U.mk_reify (S.mk_Tm_app tactic [S.as_arg SC.exp_unit] None Range.dummyRange))
                                 [S.as_arg (embed_state ([{goal with goal_ty=assertion}], []))]
                                 None
                                 Range.dummyRange in
            let steps = [N.Reify; N.Beta; N.UnfoldUntil Delta_constant; N.Zeta; N.Iota; N.Primops] in
            printfn "Starting normalizer with %s" (Print.term_to_string tm);
            Options.set_option "debug_level" (Options.List [Options.String "Norm"]);
            let result = N.normalize_with_primitive_steps (primitive_steps proof_state goal.context) steps goal.context tm in
            Options.set_option "debug_level" (Options.List []);
            printfn "Reduced tactic: got %s" (Print.term_to_string result);
            begin match unembed_result goal.context result with
                | Inl (goals, smt_goals) ->
                  bind dismiss (fun _ ->
                  bind (add_goals goals) (fun _ ->
                  add_smt_goals smt_goals))

                | Inr (msg, (goals, smt_goals)) ->
                  bind dismiss (fun _ ->
                  bind (add_goals goals) (fun _ ->
                  bind (add_smt_goals smt_goals) (fun _ ->
                  fail msg)))
            end
          | _ ->
            fail "Not a user tactic"))

let rec simplify_eq_impl : tac<unit>
    = with_cur_goal "simplify_eq_impl" (fun goal ->
          match destruct_equality_imp goal.goal_ty with
          | Some (x, e, rhs) -> //we have x==e ==> rhs
                 //imp_intro: introduce x=e in the context; goal is rhs
            bind imp_intro (fun eq_h ->
               printfn "Introduced %s:%s" (Print.bv_to_string eq_h) (Print.term_to_string eq_h.sort);
                 //rewrite: goals become [x=e; rhs[e/x]]
            bind (rewrite x e) (fun _ ->
                 //exact: dismiss the first sub-goal, i.e., prove that x=e
            bind (exact eq_h) (fun _ ->
                 //clear_hd: get rid of the eq_h in the context
                 //we're left with rhs[e/x]
            bind (clear_hd eq_h) (fun _ ->
            visit simplify_eq_impl))))
          | _ ->
            printfn "%s is not an equality imp" (Print.term_to_string goal.goal_ty);
            fail "Not an equality implication")

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

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term)> =
    if Ident.lid_equals
            (Env.current_module env)
            FStar.Syntax.Const.prims_lid
    || BU.starts_with (Ident.string_of_lid (Env.current_module env)) "FStar."
    then [env, goal]
    else let _ = printfn "About to preprocess %s\n" (Print.term_to_string goal) in
         let p = proofstate_of_goal_ty env goal in
         match run (visit evaluate_user_tactic) p with
         | Success (_, p2) ->
           (p2.goals @ p2.smt_goals) |> List.map (fun g ->
             printfn "Got goal: %s" (Print.term_to_string g.goal_ty);
             g.context, g.goal_ty)
         | Failed (msg, _) ->
           printfn "Tactic failed: %s" msg;
           printfn "Got goal: %s" (Print.term_to_string goal);
           [env, goal]
