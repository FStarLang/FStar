module FStarC.TypeChecker.Normalize.Unfolding

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.TypeChecker.Cfg
open FStarC.TypeChecker.Env
open FStarC.Syntax.Print

module Common = FStarC.TypeChecker.Common
module BU = FStarC.Util
module Path = FStarC.Path
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util

open FStarC.Class.Show

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
    (* unfold or not, fully or not, reified or not, only once or not *)
    let yes   = true  , false , false, false in
    let no    = false , false , false, false in
    let fully = true  , true  , false, false in
    let reif  = true  , false , true,  false  in
    let once  = true  , false , false, true in

    let yesno b = if b then yes else no in
    let fullyno b = if b then fully else no in
    let comb_or l = List.fold_right (fun (a,b,c,d) (x,y,z,w) -> (a||x, b||y, c||z, d||w)) l (false, false, false, false) in

    let default_unfolding () =
        log_unfolding cfg (fun () -> Format.print3 "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                                               (show fv)
                                               (show (Env.delta_depth_of_fv cfg.tcenv fv))
                                               (show cfg.delta_level));
        yesno <| (cfg.delta_level |> BU.for_some (function
             | NoDelta -> false
             | InliningDelta
             | Eager_unfolding_only -> true
             | Unfold l -> Common.delta_depth_greater_than (Env.delta_depth_of_fv cfg.tcenv fv) l))
    in
    let selective_unfold =
      Some? cfg.steps.unfold_only ||
      Some? cfg.steps.unfold_once ||
      Some? cfg.steps.unfold_fully ||
      Some? cfg.steps.unfold_attr ||
      Some? cfg.steps.unfold_qual ||
      Some? cfg.steps.unfold_namespace
    in
    let res : bool & bool & bool & bool =
    match qninfo, selective_unfold with
    // We unfold dm4f actions if and only if we are reifying
    | _ when Env.qninfo_is_action qninfo ->
        let b = should_reify cfg in
        log_unfolding cfg (fun () -> Format.print2 "should_unfold: For DM4F action %s, should_reify = %s\n"
                                               (show fv)
                                               (show b));
        if b then reif else no

    // If it is handled primitively, then don't unfold
    | _ when Some? (find_prim_step cfg fv) ->
        log_unfolding cfg (fun () -> Format.print_string " >> It's a primop, not unfolding\n");
        no

    // Don't unfold HasMaskedEffect
    | Some (Inr ({sigquals=qs; sigel=Sig_let {lbs=(is_rec, _)}}, _), _), _ when
            List.contains HasMaskedEffect qs ->
        log_unfolding cfg (fun () -> Format.print_string " >> HasMaskedEffect, not unfolding\n");
        no

    // Unfoldonce. NB: this is before the zeta case, so we unfold even if zeta is off
    | _, true when Some? cfg.steps.unfold_once && BU.for_some (fv_eq_lid fv) (Some?.v cfg.steps.unfold_once) ->
        log_unfolding cfg (fun () -> Format.print_string " >> UnfoldOnce\n");
        once

    | Some (Inr ({sigattrs=attrs}, _), _), _ when cfg.steps.for_extraction && Some? (BU.find_map attrs Parser.Const.ExtractAs.is_extract_as_attr) ->
        log_unfolding cfg (fun () -> Format.print_string " >> Has extract_as attribute and we're extracting, unfold!");
        yes

    // Recursive lets may only be unfolded when Zeta is on
    | Some (Inr ({sigquals=qs; sigel=Sig_let {lbs=(is_rec, _)}}, _), _), _ when
            is_rec && not cfg.steps.zeta && not cfg.steps.zeta_full ->
        log_unfolding cfg (fun () -> Format.print_string " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
        no

    // We're doing selectively unfolding, assume it to not unfold unless it meets the criteria
    | _, true ->
        log_unfolding cfg (fun () -> Format.print1 "should_unfold: Reached a %s with selective unfolding\n"
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
             then yesno <| Some? (Env.lookup_definition_qninfo [Eager_unfolding_only; InliningDelta] fv.fv_name qninfo)
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
                     (fun qual -> show qual = q) // kinda funny
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

    // Check for DontUnfoldAttribute: if any attribute of the definitions is blacklisted,
    // do not unfold.
    // NB: Using specific attributes like UnfoldOnly will override this. This gives more
    // control to the user if they *really* want to unfold one of these.
    | _ when Some? cfg.steps.dont_unfold_attr
      && List.existsb (fun fa -> U.has_attribute attrs fa) (Some?.v cfg.steps.dont_unfold_attr) ->
        log_unfolding cfg (fun () -> Format.print_string " >> forbidden by attribute, not unfolding\n");
        no

    // Nothing special, just check the depth
    | _ ->
        default_unfolding()
    in
    log_unfolding cfg (fun () -> Format.print3 "should_unfold: For %s (%s), unfolding res = %s\n"
                    (show fv)
                    (show (S.range_of_fv fv))
                    (show res)
                    );
    let r =
      match res with
      | false, _, _, _ -> Should_unfold_no
      | true, false, false, false -> Should_unfold_yes
      | true, false, false, true -> Should_unfold_once
      | true, true, false, false -> Should_unfold_fully
      | true, false, true, false -> Should_unfold_reify
      | _ ->
        failwith <| Format.fmt1 "Unexpected unfolding result: %s" (show res)
    in
    r
