module FStar.TypeChecker.Normalize.Unfolding

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.TypeChecker.Cfg
open FStar.TypeChecker.Env
open FStar.Syntax.Print

module Common = FStar.TypeChecker.Common
module BU = FStar.Compiler.Util
module Path = FStar.Compiler.Path
module PC = FStar.Parser.Const
module Print = FStar.Syntax.Print
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module TEQ = FStar.TypeChecker.TermEqAndSimplify

open FStar.Class.Show

(* Max number of warnings to print in a single run.
Initialized in Normalize.normalize *)
let plugin_unfold_warn_ctr : ref int = BU.mk_ref 0

let should_unfold cfg should_reify fv qninfo : should_unfold_res =
    let attrs =
      match Env.attrs_of_qninfo qninfo with
      | None -> []
      | Some ats -> ats
    in
    let quals =
      match Env.quals_of_qninfo qninfo with
      | None -> []
      | Some quals -> quals
    in
    (* unfold or not, fully or not, reified or not *)
    let yes   = true  , false , false in
    let no    = false , false , false in
    let fully = true  , true  , false in
    let reif  = true  , false , true in

    let yesno b = if b then yes else no in
    let fullyno b = if b then fully else no in
    let comb_or l = List.fold_right (fun (a,b,c) (x,y,z) -> (a||x, b||y, c||z)) l (false, false, false) in

    let default_unfolding () =
        log_unfolding cfg (fun () -> BU.print3 "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                                               (show fv)
                                               (show (Env.delta_depth_of_fv cfg.tcenv fv))
                                               (show cfg.delta_level));
        yesno <| (cfg.delta_level |> BU.for_some (function
             | NoDelta -> false
             | InliningDelta
             | Eager_unfolding_only -> true
             | Unfold l -> Common.delta_depth_greater_than (Env.delta_depth_of_fv cfg.tcenv fv) l))
    in
    let res =
    match qninfo,
          cfg.steps.unfold_only,
          cfg.steps.unfold_fully,
          cfg.steps.unfold_attr,
          cfg.steps.unfold_qual,
          cfg.steps.unfold_namespace
    with
    // We unfold dm4f actions if and only if we are reifying
    | _ when Env.qninfo_is_action qninfo ->
        let b = should_reify cfg in
        log_unfolding cfg (fun () -> BU.print2 "should_unfold: For DM4F action %s, should_reify = %s\n"
                                               (show fv)
                                               (show b));
        if b then reif else no

    // If it is handled primitively, then don't unfold
    | _ when Option.isSome (find_prim_step cfg fv) ->
        log_unfolding cfg (fun () -> BU.print_string " >> It's a primop, not unfolding\n");
        no

    // Don't unfold HasMaskedEffect
    | Some (Inr ({sigquals=qs; sigel=Sig_let {lbs=(is_rec, _)}}, _), _), _, _, _, _, _ when
            List.contains HasMaskedEffect qs ->
        log_unfolding cfg (fun () -> BU.print_string " >> HasMaskedEffect, not unfolding\n");
        no

    // Recursive lets may only be unfolded when Zeta is on
    | Some (Inr ({sigquals=qs; sigel=Sig_let {lbs=(is_rec, _)}}, _), _), _, _, _, _, _ when
            is_rec && not cfg.steps.zeta && not cfg.steps.zeta_full ->
        log_unfolding cfg (fun () -> BU.print_string " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
        no

    // We're doing selectively unfolding, assume it to not unfold unless it meets the criteria
    | _, Some _, _, _, _, _
    | _, _, Some _, _, _, _
    | _, _, _, Some _, _, _
    | _, _, _, _, Some _, _
    | _, _, _, _, _, Some _ ->
        log_unfolding cfg (fun () -> BU.print1 "should_unfold: Reached a %s with selective unfolding\n"
                                               (show fv));
        // How does the following code work?
        // We are doing selective unfolding so, by default, we assume everything
        // should *not* be unfolded unless it meets *at least one* of the criteria.
        // So we check exactly that, that this `fv` meets some criteria that is presently
        // being used. Note that in `None`, we default to `no`, otherwise everything would
        // unfold (unless we had all criteria present at once, which is unlikely)

        let meets_some_criterion =
            comb_or [
            (if cfg.steps.for_extraction
             then yesno <| Option.isSome (Env.lookup_definition_qninfo [Eager_unfolding_only; InliningDelta] fv.fv_name.v qninfo)
             else no)
           ;(match cfg.steps.unfold_only with
             | None -> no
             | Some lids -> yesno <| BU.for_some (fv_eq_lid fv) lids)
           ;(match cfg.steps.unfold_attr with
             | None -> no
             | Some lids -> yesno <| BU.for_some (fun at -> BU.for_some (fun lid -> U.is_fvar lid at) lids) attrs)
           ;(match cfg.steps.unfold_fully with
             | None -> no
             | Some lids -> fullyno <| BU.for_some (fv_eq_lid fv) lids)
           ;(match cfg.steps.unfold_qual with
             | None -> no
             | Some qs ->
               yesno <|
               BU.for_some
                 (fun q ->
                   BU.for_some
                     (fun qual -> Print.qual_to_string qual = q) // kinda funny
                     quals)
               qs)
           ;(match cfg.steps.unfold_namespace with
             | None -> no
             | Some namespaces ->
               (* Check if the variable is under some of the modules in [ns].
               Essentially we check if there is a component in ns that is a prefix of
               the (printed) lid. But, to prevent unfolding `ABCD.def` when we
               are trying to unfold `AB`, we append a single `.` to both before checking,
               so `AB` only unfold lids under the `AB` module and its submodules. *)
               let p : list string = Ident.path_of_lid (lid_of_fv fv) in
               let r : bool = Path.search_forest p namespaces in
               yesno <| r
             )
           ]
        in
        meets_some_criterion

    // UnfoldTac means never unfold FVs marked [@"tac_opaque"]
    | _, _, _, _, _, _ when cfg.steps.unfold_tac && BU.for_some (TEQ.eq_tm_bool cfg.tcenv U.tac_opaque_attr) attrs ->
        log_unfolding cfg (fun () -> BU.print_string " >> tac_opaque, not unfolding\n");
        no

    // Nothing special, just check the depth
    | _ ->
        default_unfolding()
    in
    log_unfolding cfg (fun () -> BU.print3 "should_unfold: For %s (%s), unfolding res = %s\n"
                    (show fv)
                    (show (S.range_of_fv fv))
                    (show res)
                    );
    let r =
      match res with
      | false, _, _ -> Should_unfold_no
      | true, false, false -> Should_unfold_yes
      | true, true, false -> Should_unfold_fully
      | true, false, true -> Should_unfold_reify
      | _ ->
        failwith <| BU.format1 "Unexpected unfolding result: %s" (show res)
    in
    if cfg.steps.unfold_tac                             // If running a tactic,
       && not (Options.no_plugins ())                   // haven't explicitly disabled plugins
       && (r <> Should_unfold_no)                       // actually unfolding this fvar
       && BU.for_some (U.is_fvar PC.plugin_attr) attrs  // it is a plugin
       && !plugin_unfold_warn_ctr > 0                   // and we haven't raised too many warnings
    then begin
      // then warn about it
      let msg = BU.format1 "Unfolding name which is marked as a plugin: %s"
                                    (Print.fv_to_string fv) in
      Errors.log_issue fv.fv_name.p
                       (Errors.Warning_UnfoldPlugin, msg);
      plugin_unfold_warn_ctr := !plugin_unfold_warn_ctr - 1
    end;
    r
