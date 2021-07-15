#light "off"
module FStar.Tactics.Hooks

open FStar
open FStar.All
open FStar.Util
open FStar.Range
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Tactics.Types
open FStar.Tactics.Basic
open FStar.Tactics.Interpreter

module BU      = FStar.Util
module Range   = FStar.Range
module Err     = FStar.Errors
module O       = FStar.Options
module PC      = FStar.Parser.Const
module S       = FStar.Syntax.Syntax
module SS      = FStar.Syntax.Subst
module U       = FStar.Syntax.Util
module Print   = FStar.Syntax.Print
module N       = FStar.TypeChecker.Normalize
module Env     = FStar.TypeChecker.Env
module TcUtil  = FStar.TypeChecker.Util
module TcRel   = FStar.TypeChecker.Rel
module RE      = FStar.Reflection.Embeddings

let run_tactic_on_typ
        (rng_tac : Range.range) (rng_goal : Range.range)
        (tactic:term) (env:Env.env) (typ:term)
                    : list<goal> // remaining goals
                    * term // witness
                    =
    let rng = range_of_rng (use_range rng_goal) (use_range rng_tac) in
    let ps, w = proofstate_of_goal_ty rng env typ in
    let gs, _res = run_tactic_on_ps rng_tac rng_goal false e_unit () e_unit tactic ps in
    gs, w

let run_tactic_on_all_implicits
        (rng_tac : Range.range) (rng_goal : Range.range)
        (tactic:term) (env:Env.env) (imps:Env.implicits)
    : list<goal> // remaining goals
    =
    let ps, _ = proofstate_of_all_implicits rng_goal env imps in
    let goals, () =
      run_tactic_on_ps
        (Env.get_range env)
        rng_goal
        true
        e_unit
        ()
        e_unit
        tactic
        ps
    in
    goals

// Polarity
type pol =
    | Pos
    | Neg
    | Both // traversing both polarities at once

// Result of traversal
type tres_m<'a> =
    | Unchanged of 'a
    | Simplified of 'a * list<goal>
    | Dual of 'a * 'a * list<goal>

type tres = tres_m<term>

let tpure x = Unchanged x

let flip p = match p with
    | Pos -> Neg
    | Neg -> Pos
    | Both -> Both

let getprop (e:Env.env) (t:term) : option<term> =
    let tn = N.normalize [Env.Weak; Env.HNF; Env.UnfoldUntil delta_constant] e t in
    U.un_squash tn

let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : tres =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with

    // with_tactic marker
    | Tm_fvar fv, [(tactic, None); (assertion, None)]
            when S.fv_eq_lid fv PC.by_tactic_lid ->
        begin match pol with
        | Pos ->
            let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
            Simplified (FStar.Syntax.Util.t_true, gs)

        | Both ->
            let gs, _ = run_tactic_on_typ tactic.pos assertion.pos tactic e assertion in
            Dual (assertion, FStar.Syntax.Util.t_true, gs)

        | Neg ->
            // Peel away tactics in negative positions, they're assumptions!
            Simplified (assertion, [])
        end

    // spinoff marker: simply spin off a query independently.
    // So, equivalent to `with_tactic idtac` without importing the (somewhat heavy) tactics module
    | Tm_fvar fv, [(assertion, None)]
            when S.fv_eq_lid fv PC.spinoff_lid ->
        begin  match pol with
        | Pos ->
            Simplified (FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])

        | Both ->
            Dual (assertion, FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])

        | Neg ->
            Simplified (assertion, [])
        end

    // rewrite_with_tactic marker
    | Tm_fvar fv, [(tactic, None); (typ, Some (Implicit false)); (tm, None)]
            when S.fv_eq_lid fv PC.rewrite_by_tactic_lid ->

        // Create a new uvar that must be equal to the initial term
        let uvtm, _, g_imp = Env.new_implicit_var_aux "rewrite_with_tactic RHS" tm.pos e typ Allow_untyped None in

        let u = e.universe_of e typ in
        // eq2 is squashed already, so it's in Type0
        let goal = U.mk_squash U_zero (U.mk_eq2 u typ tm uvtm) in
        let gs, _ = run_tactic_on_typ tactic.pos tm.pos tactic e goal in

        // Ensure that rewriting did not leave goals
        let _ =
          match gs with
          | [] -> ()
          | _ ->
            Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "rewrite_with_tactic left open goals") typ.pos
        in

        // abort if the uvar was not solved
        let g_imp = TcRel.resolve_implicits_tac e g_imp in
        report_implicits tm.pos g_imp.implicits;

        // If the rewriting succeeded, we return the generated uvar, which is now
        // a synthesized term
        Simplified (uvtm, [])

    | _ ->
        Unchanged t

let explode (t : tres_m<'a>) : 'a * 'a * list<goal> =
    match t with
    | Unchanged t -> (t, t, [])
    | Simplified (t, gs) -> (t, t, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)

let comb1 (f : 'a -> 'b) : tres_m<'a> -> tres_m<'b> = function
    | Unchanged t -> Unchanged (f t)
    | Simplified (t, gs) -> Simplified (f t, gs)
    | Dual (tn, tp, gs) -> Dual (f tn, f tp, gs)

let comb2 (f : 'a -> 'b -> 'c ) (x : tres_m<'a>) (y : tres_m<'b>) : tres_m<'c> =
    match x, y with
    | Unchanged t1, Unchanged t2 ->
        Unchanged (f t1 t2)

    | Unchanged t1, Simplified (t2, gs)
    | Simplified (t1, gs), Unchanged t2 ->
        Simplified (f t1 t2, gs)

    | Simplified (t1, gs1), Simplified (t2, gs2) ->
        Simplified (f t1 t2, gs1@gs2)

    | _ ->
        let (n1, p1, gs1) = explode x in
        let (n2, p2, gs2) = explode y in
        Dual (f n1 n2, f p1 p2, gs1@gs2)

let comb_list (rs : list<tres_m<'a>>) : tres_m<list<'a>> =
    let rec aux rs acc =
        match rs with
        | [] -> acc
        | hd::tl -> aux tl (comb2 (fun l r -> l::r) hd acc)
    in
    aux (List.rev rs) (tpure [])

let emit (gs : list<goal>) (m : tres_m<'a>) : tres_m<'a> =
    comb2 (fun () x -> x) (Simplified ((), gs)) m

let rec traverse (f: pol -> Env.env -> term -> tres) (pol:pol) (e:Env.env) (t:term) : tres =
    let r =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let tr = traverse f pol e t in
                             comb1 (fun t' -> Tm_uinst (t', us)) tr

        | Tm_meta (t, m) -> let tr = traverse f pol e t in
                            comb1 (fun t' -> Tm_meta (t', m)) tr

        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.imp_lid ->
               // ==> is specialized to U_zero
               let x = S.new_bv None p in
               let r1 = traverse f (flip pol)  e                p in
               let r2 = traverse f       pol  (Env.push_bv e x) q in
               comb2 (fun l r -> (U.mk_imp l r).n) r1 r2

        (* p <==> q is special, each side is bipolar *)
        (* So we traverse its arguments with pol = Both, and negative and positive versions *)
        (* of p and q *)
        (* then we return (in general) (p- ==> q+) /\ (q- ==> p+) *)
        (* But if neither side ran tactics, we just keep p <==> q *)
        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.iff_lid ->
               // <==> is specialized to U_zero
               let xp = S.new_bv None p in
               let xq = S.new_bv None q in
               let r1 = traverse f Both (Env.push_bv e xq) p in
               let r2 = traverse f Both (Env.push_bv e xp) q in
               // Should be flipping the tres, I think
               begin match r1, r2 with
               | Unchanged _, Unchanged _ ->
                  comb2 (fun l r -> (U.mk_iff l r).n) r1 r2
               | _ ->
                  let (pn, pp, gs1) = explode r1 in
                  let (qn, qp, gs2) = explode r2 in
                  let t = U.mk_conj (U.mk_imp pn qp) (U.mk_imp qn pp) in
                  Simplified (t.n, gs1@gs2)
               end

        | Tm_app (hd, args) ->
                let r0 = traverse f pol e hd in
                let r1 = List.fold_right (fun (a, q) r ->
                                              let r' = traverse f pol e a in
                                              comb2 (fun a args -> (a, q)::args) r' r)
                                                 args (tpure []) in
                comb2 (fun hd args -> Tm_app (hd, args)) r0 r1

        | Tm_abs (bs, t, k) ->
                // TODO: traverse k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let r0 = List.map (fun b ->
                                     let r = traverse f (flip pol) e b.binder_bv.sort in
                                     comb1 (fun s' -> ({b with binder_bv={ b.binder_bv with sort = s' }})) r
                                  ) bs
                in
                let rbs = comb_list r0 in
                let rt = traverse f pol e' topen in
                comb2 (fun bs t -> (U.abs bs t k).n) rbs rt

        | Tm_ascribed (t, asc, ef) ->
            // TODO: traverse the types?
            comb1 (fun t -> Tm_ascribed (t, asc, ef)) (traverse f pol e t)

        | Tm_match (sc, asc_opt, brs) ->  //AR: not traversing the return annotation
            comb2 (fun sc brs -> Tm_match (sc, asc_opt, brs))
                  (traverse f pol e sc)
                  (comb_list (List.map (fun br -> let (pat, w, exp) = SS.open_branch br in
                                                  let bvs = S.pat_bvs pat in
                                                  let e = Env.push_bvs e bvs in
                                                  let r = traverse f pol e exp in
                                                  comb1 (fun exp -> SS.close_branch (pat, w, exp)) r) brs))

        | x ->
            tpure x in
    match r with
    | Unchanged tn' ->
        f pol e ({ t with n = tn' })

    | Simplified (tn', gs) ->
        emit gs (f pol e ({ t with n = tn' }))

    | Dual (tn, tp, gs) ->
        let rp = f pol e ({ t with n = tp }) in
        let (_, p', gs') = explode rp in
        Dual ({t with n = tn}, p', gs@gs')

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term * O.optionstate)> =
  Errors.with_ctx "While preprocessing VC with a tactic" (fun () ->
    tacdbg := Env.debug env (O.Other "Tac");
    if !tacdbg then
        BU.print2 "About to preprocess %s |= %s\n"
                        (Env.all_binders env |> Print.binders_to_string ",")
                        (Print.term_to_string goal);
    let initial = (1, []) in
    // This match should never fail
    let (t', gs) =
        match traverse by_tactic_interp Pos env goal with
        | Unchanged t' -> (t', [])
        | Simplified (t', gs) -> (t', gs)
        | _ -> failwith "preprocess: impossible, traverse returned a Dual"
    in
    if !tacdbg then
        BU.print2 "Main goal simplified to: %s |- %s\n"
                (Env.all_binders env |> Print.binders_to_string ", ")
                (Print.term_to_string t');
    let s = initial in
    let s = List.fold_left (fun (n,gs) g ->
                 let phi = match getprop (goal_env g) (goal_type g) with
                           | None ->
                                Err.raise_error (Err.Fatal_TacticProofRelevantGoal,
                                    (BU.format1 "Tactic returned proof-relevant goal: %s" (Print.term_to_string (goal_type g)))) env.range
                           | Some phi -> phi
                 in
                 if !tacdbg then
                     BU.print2 "Got goal #%s: %s\n" (string_of_int n) (Print.term_to_string (goal_type g));
                 let label =
                    if get_label g = ""
                    then "Could not prove goal #" ^ string_of_int n
                    else "Could not prove goal #" ^ string_of_int n ^ " (" ^ get_label g ^ ")"
                 in
                 let gt' = TcUtil.label label  goal.pos phi in
                 (n+1, (goal_env g, gt', g.opts)::gs)) s gs in
    let (_, gs) = s in
    let gs = List.rev gs in (* Return new VCs in same order as goals *)
    // Use default opts for main goal
    (env, t', O.peek ()) :: gs
  )

let synthesize (env:Env.env) (typ:typ) (tau:term) : term =
  Errors.with_ctx "While synthesizing term with a tactic" (fun () ->
    // Don't run the tactic (and end with a magic) when nosynth is set, cf. issue #73 in fstar-mode.el
    if env.nosynth
    then mk_Tm_app (TcUtil.fvar_const env PC.magic_lid) [S.as_arg U.exp_unit] typ.pos
    else begin
    tacdbg := Env.debug env (O.Other "Tac");

    let gs, w = run_tactic_on_typ tau.pos typ.pos tau env typ in
    // Check that all goals left are irrelevant and provable
    // TODO: It would be nicer to combine all of these into a guard and return
    // that to TcTerm, but the varying environments make it awkward.
    List.iter (fun g ->
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !tacdbg then
              BU.print1 "Synthesis left a goal: %s\n" (Print.term_to_string vc);
            let guard = { guard_f = NonTrivial vc
                        ; deferred_to_tac = []
                        ; deferred = []
                        ; univ_ineqs = [], []
                        ; implicits = [] } in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "synthesis left open goals") typ.pos) gs;
    w
    end
  )

let solve_implicits (env:Env.env) (tau:term) (imps:Env.implicits) : unit =
  Errors.with_ctx "While solving implicits with a tactic" (fun () ->
    if env.nosynth then () else
    begin
    tacdbg := Env.debug env (O.Other "Tac");

    let gs = run_tactic_on_all_implicits tau.pos (Env.get_range env) tau env imps in
    // Check that all goals left are irrelevant and provable
    // TODO: It would be nicer to combine all of these into a guard and return
    // that to TcTerm, but the varying environments make it awkward.
    gs |> List.iter (fun g ->
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !tacdbg then
              BU.print1 "Synthesis left a goal: %s\n" (Print.term_to_string vc);
            let guard = { guard_f = NonTrivial vc
                        ; deferred_to_tac = []
                        ; deferred = []
                        ; univ_ineqs = [], []
                        ; implicits = [] } in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "synthesis left open goals")
                            (Env.get_range env));
    ()
    end
  )

let splice (env:Env.env) (rng:Range.range) (tau:term) : list<sigelt> =
  Errors.with_ctx "While running splice with a tactic" (fun () ->
    if env.nosynth then [] else begin
    tacdbg := Env.debug env (O.Other "Tac");

    let typ = S.t_decls in // running with goal type FStar.Reflection.Data.decls
    let ps = proofstate_of_goals tau.pos env [] [] in
    let gs, sigelts = run_tactic_on_ps tau.pos tau.pos false
                                  e_unit ()
                                  (e_list RE.e_sigelt) tau ps in

    // Check that all goals left are irrelevant. We don't need to check their
    // validity, as we will typecheck the witness independently.
    // TODO: Do not retypecheck and do just like `synth`. But that's hard.. what to do for inductives,
    // for instance? We would need to reflect *all* of F* static semantics into Meta-F*, and
    // that is a ton of work.
    if List.existsML (fun g -> not (Option.isSome (getprop (goal_env g) (goal_type g)))) gs
        then Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "splice left open goals") typ.pos;

    if !tacdbg then
      BU.print1 "splice: got decls = %s\n"
                 (FStar.Common.string_of_list Print.sigelt_to_string sigelts);

    let sigelts = sigelts |> List.map (fun se ->
        (* Check for bare Sig_datacon and Sig_inductive_typ, and abort if so. *)
        begin match se.sigel with
        | Sig_datacon _
        | Sig_inductive_typ _ ->
          Err.raise_error (Err.Error_BadSplice,
                           (BU.format1 "Tactic returned bad sigelt: %s\nIf you wanted to splice an inductive type, call `pack` providing a `Sg_Inductive` to get a proper sigelt." (Print.sigelt_to_string_short se))) rng
        | _ -> ()
        end;
        { se with sigrng = rng })
    in
    sigelts
    end
  )

let mpreprocess (env:Env.env) (tau:term) (tm:term) : term =
  Errors.with_ctx "While preprocessing a definition with a tactic" (fun () ->
    if env.nosynth then tm else begin
    tacdbg := Env.debug env (O.Other "Tac");
    let ps = proofstate_of_goals tm.pos env [] [] in
    let gs, tm = run_tactic_on_ps tau.pos tm.pos false RE.e_term tm RE.e_term tau ps in
    tm
    end
  )

let postprocess (env:Env.env) (tau:term) (typ:term) (tm:term) : term =
  Errors.with_ctx "While postprocessing a definition with a tactic" (fun () ->
    if env.nosynth then tm else begin
    tacdbg := Env.debug env (O.Other "Tac");
    let uvtm, _, g_imp = Env.new_implicit_var_aux "postprocess RHS" tm.pos env typ Allow_untyped None in

    let u = env.universe_of env typ in
    // eq2 is squashed already, so it's in Type0
    let goal = U.mk_squash U_zero (U.mk_eq2 u typ tm uvtm) in
    let gs, w = run_tactic_on_typ tau.pos tm.pos tau env goal in
    // see comment in `synthesize`
    List.iter (fun g ->
        match getprop (goal_env g) (goal_type g) with
        | Some vc ->
            begin
            if !tacdbg then
              BU.print1 "Postprocessing left a goal: %s\n" (Print.term_to_string vc);
            let guard = { guard_f = NonTrivial vc
                        ; deferred_to_tac = []
                        ; deferred = []
                        ; univ_ineqs = [], []
                        ; implicits = [] } in
            TcRel.force_trivial_guard (goal_env g) guard
            end
        | None ->
            Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, "postprocessing left open goals") typ.pos) gs;
    (* abort if the uvar was not solved *)
    let g_imp = TcRel.resolve_implicits_tac env g_imp in
    report_implicits tm.pos g_imp.implicits;

    uvtm
    end
  )
