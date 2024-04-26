open Prims
let (plugin_unfold_warn_ctr : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_no -> true | uu___ -> false
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_yes -> true | uu___ -> false
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_fully -> true | uu___ -> false
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_reify -> true | uu___ -> false
let (should_unfold :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_TypeChecker_Cfg.cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg ->
    fun should_reify ->
      fun fv ->
        fun qninfo ->
          let attrs =
            let uu___ = FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
            match uu___ with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some ats -> ats in
          let quals =
            let uu___ = FStar_TypeChecker_Env.quals_of_qninfo qninfo in
            match uu___ with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some quals1 -> quals1 in
          let yes = (true, false, false) in
          let no = (false, false, false) in
          let fully = (true, true, false) in
          let reif = (true, false, true) in
          let yesno b = if b then yes else no in
          let fullyno b = if b then fully else no in
          let comb_or l =
            FStar_Compiler_List.fold_right
              (fun uu___ ->
                 fun uu___1 ->
                   match (uu___, uu___1) with
                   | ((a, b, c), (x, y, z)) -> ((a || x), (b || y), (c || z)))
              l (false, false, false) in
          let default_unfolding uu___ =
            FStar_TypeChecker_Cfg.log_unfolding cfg
              (fun uu___2 ->
                 let uu___3 =
                   FStar_Class_Show.show FStar_Syntax_Print.showable_fv fv in
                 let uu___4 =
                   let uu___5 =
                     FStar_TypeChecker_Env.delta_depth_of_fv
                       cfg.FStar_TypeChecker_Cfg.tcenv fv in
                   FStar_Class_Show.show
                     FStar_Syntax_Syntax.showable_delta_depth uu___5 in
                 let uu___5 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.show_list
                        FStar_TypeChecker_Env.showable_delta_level)
                     cfg.FStar_TypeChecker_Cfg.delta_level in
                 FStar_Compiler_Util.print3
                   "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                   uu___3 uu___4 uu___5);
            (let uu___2 =
               FStar_Compiler_Util.for_some
                 (fun uu___3 ->
                    match uu___3 with
                    | FStar_TypeChecker_Env.NoDelta -> false
                    | FStar_TypeChecker_Env.InliningDelta -> true
                    | FStar_TypeChecker_Env.Eager_unfolding_only -> true
                    | FStar_TypeChecker_Env.Unfold l ->
                        let uu___4 =
                          FStar_TypeChecker_Env.delta_depth_of_fv
                            cfg.FStar_TypeChecker_Cfg.tcenv fv in
                        FStar_TypeChecker_Common.delta_depth_greater_than
                          uu___4 l) cfg.FStar_TypeChecker_Cfg.delta_level in
             yesno uu___2) in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify cfg in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu___1 ->
                    let uu___2 =
                      FStar_Class_Show.show FStar_Syntax_Print.showable_fv fv in
                    let uu___3 =
                      FStar_Class_Show.show
                        (FStar_Class_Show.printableshow
                           FStar_Class_Printable.printable_bool) b in
                    FStar_Compiler_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu___2 uu___3);
               if b then reif else no)
            else
              if
                (let uu___ = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                 FStar_Compiler_Option.isSome uu___)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu___1 ->
                      FStar_Compiler_Util.print_string
                        " >> It's a primop, not unfolding\n");
                 no)
              else
                (match (qninfo,
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_namespace))
                 with
                 | (FStar_Pervasives_Native.Some
                    (FStar_Pervasives.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          { FStar_Syntax_Syntax.lbs1 = (is_rec, uu___);
                            FStar_Syntax_Syntax.lids1 = uu___1;_};
                        FStar_Syntax_Syntax.sigrng = uu___2;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu___3;
                        FStar_Syntax_Syntax.sigattrs = uu___4;
                        FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
                        FStar_Syntax_Syntax.sigopts = uu___6;_},
                      uu___7),
                     uu___8),
                    uu___9, uu___10, uu___11, uu___12, uu___13) when
                     FStar_Compiler_List.contains
                       FStar_Syntax_Syntax.HasMaskedEffect qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___15 ->
                           FStar_Compiler_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Pervasives.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          { FStar_Syntax_Syntax.lbs1 = (is_rec, uu___);
                            FStar_Syntax_Syntax.lids1 = uu___1;_};
                        FStar_Syntax_Syntax.sigrng = uu___2;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu___3;
                        FStar_Syntax_Syntax.sigattrs = uu___4;
                        FStar_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
                        FStar_Syntax_Syntax.sigopts = uu___6;_},
                      uu___7),
                     uu___8),
                    uu___9, uu___10, uu___11, uu___12, uu___13) when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___15 ->
                           FStar_Compiler_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu___, FStar_Pervasives_Native.Some uu___1, uu___2,
                    uu___3, uu___4, uu___5) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___7 ->
                           let uu___8 =
                             FStar_Class_Show.show
                               FStar_Syntax_Print.showable_fv fv in
                           FStar_Compiler_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___8);
                      (let meets_some_criterion =
                         let uu___7 =
                           let uu___8 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___9 =
                                 let uu___10 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Compiler_Option.isSome uu___10 in
                               yesno uu___9
                             else no in
                           let uu___9 =
                             let uu___10 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___11 =
                                     FStar_Compiler_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   yesno uu___11 in
                             let uu___11 =
                               let uu___12 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___13 =
                                       FStar_Compiler_Util.for_some
                                         (fun at ->
                                            FStar_Compiler_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     yesno uu___13 in
                               let uu___13 =
                                 let uu___14 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___15 =
                                         FStar_Compiler_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       fullyno uu___15 in
                                 let uu___15 =
                                   let uu___16 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___17 =
                                           FStar_Compiler_Util.for_some
                                             (fun q ->
                                                FStar_Compiler_Util.for_some
                                                  (fun qual ->
                                                     let uu___18 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___18 = q) quals) qs in
                                         yesno uu___17 in
                                   let uu___17 =
                                     let uu___18 =
                                       match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_namespace
                                       with
                                       | FStar_Pervasives_Native.None -> no
                                       | FStar_Pervasives_Native.Some
                                           namespaces ->
                                           let p =
                                             let uu___19 =
                                               FStar_Syntax_Syntax.lid_of_fv
                                                 fv in
                                             FStar_Ident.path_of_lid uu___19 in
                                           let r =
                                             FStar_Compiler_Path.search_forest
                                               (FStar_Class_Ord.ord_eq
                                                  FStar_Class_Ord.ord_string)
                                               p namespaces in
                                           yesno r in
                                     [uu___18] in
                                   uu___16 :: uu___17 in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         comb_or uu___7 in
                       meets_some_criterion))
                 | (uu___, uu___1, FStar_Pervasives_Native.Some uu___2,
                    uu___3, uu___4, uu___5) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___7 ->
                           let uu___8 =
                             FStar_Class_Show.show
                               FStar_Syntax_Print.showable_fv fv in
                           FStar_Compiler_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___8);
                      (let meets_some_criterion =
                         let uu___7 =
                           let uu___8 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___9 =
                                 let uu___10 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Compiler_Option.isSome uu___10 in
                               yesno uu___9
                             else no in
                           let uu___9 =
                             let uu___10 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___11 =
                                     FStar_Compiler_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   yesno uu___11 in
                             let uu___11 =
                               let uu___12 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___13 =
                                       FStar_Compiler_Util.for_some
                                         (fun at ->
                                            FStar_Compiler_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     yesno uu___13 in
                               let uu___13 =
                                 let uu___14 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___15 =
                                         FStar_Compiler_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       fullyno uu___15 in
                                 let uu___15 =
                                   let uu___16 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___17 =
                                           FStar_Compiler_Util.for_some
                                             (fun q ->
                                                FStar_Compiler_Util.for_some
                                                  (fun qual ->
                                                     let uu___18 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___18 = q) quals) qs in
                                         yesno uu___17 in
                                   let uu___17 =
                                     let uu___18 =
                                       match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_namespace
                                       with
                                       | FStar_Pervasives_Native.None -> no
                                       | FStar_Pervasives_Native.Some
                                           namespaces ->
                                           let p =
                                             let uu___19 =
                                               FStar_Syntax_Syntax.lid_of_fv
                                                 fv in
                                             FStar_Ident.path_of_lid uu___19 in
                                           let r =
                                             FStar_Compiler_Path.search_forest
                                               (FStar_Class_Ord.ord_eq
                                                  FStar_Class_Ord.ord_string)
                                               p namespaces in
                                           yesno r in
                                     [uu___18] in
                                   uu___16 :: uu___17 in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         comb_or uu___7 in
                       meets_some_criterion))
                 | (uu___, uu___1, uu___2, FStar_Pervasives_Native.Some
                    uu___3, uu___4, uu___5) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___7 ->
                           let uu___8 =
                             FStar_Class_Show.show
                               FStar_Syntax_Print.showable_fv fv in
                           FStar_Compiler_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___8);
                      (let meets_some_criterion =
                         let uu___7 =
                           let uu___8 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___9 =
                                 let uu___10 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Compiler_Option.isSome uu___10 in
                               yesno uu___9
                             else no in
                           let uu___9 =
                             let uu___10 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___11 =
                                     FStar_Compiler_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   yesno uu___11 in
                             let uu___11 =
                               let uu___12 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___13 =
                                       FStar_Compiler_Util.for_some
                                         (fun at ->
                                            FStar_Compiler_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     yesno uu___13 in
                               let uu___13 =
                                 let uu___14 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___15 =
                                         FStar_Compiler_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       fullyno uu___15 in
                                 let uu___15 =
                                   let uu___16 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___17 =
                                           FStar_Compiler_Util.for_some
                                             (fun q ->
                                                FStar_Compiler_Util.for_some
                                                  (fun qual ->
                                                     let uu___18 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___18 = q) quals) qs in
                                         yesno uu___17 in
                                   let uu___17 =
                                     let uu___18 =
                                       match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_namespace
                                       with
                                       | FStar_Pervasives_Native.None -> no
                                       | FStar_Pervasives_Native.Some
                                           namespaces ->
                                           let p =
                                             let uu___19 =
                                               FStar_Syntax_Syntax.lid_of_fv
                                                 fv in
                                             FStar_Ident.path_of_lid uu___19 in
                                           let r =
                                             FStar_Compiler_Path.search_forest
                                               (FStar_Class_Ord.ord_eq
                                                  FStar_Class_Ord.ord_string)
                                               p namespaces in
                                           yesno r in
                                     [uu___18] in
                                   uu___16 :: uu___17 in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         comb_or uu___7 in
                       meets_some_criterion))
                 | (uu___, uu___1, uu___2, uu___3,
                    FStar_Pervasives_Native.Some uu___4, uu___5) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___7 ->
                           let uu___8 =
                             FStar_Class_Show.show
                               FStar_Syntax_Print.showable_fv fv in
                           FStar_Compiler_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___8);
                      (let meets_some_criterion =
                         let uu___7 =
                           let uu___8 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___9 =
                                 let uu___10 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Compiler_Option.isSome uu___10 in
                               yesno uu___9
                             else no in
                           let uu___9 =
                             let uu___10 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___11 =
                                     FStar_Compiler_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   yesno uu___11 in
                             let uu___11 =
                               let uu___12 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___13 =
                                       FStar_Compiler_Util.for_some
                                         (fun at ->
                                            FStar_Compiler_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     yesno uu___13 in
                               let uu___13 =
                                 let uu___14 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___15 =
                                         FStar_Compiler_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       fullyno uu___15 in
                                 let uu___15 =
                                   let uu___16 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___17 =
                                           FStar_Compiler_Util.for_some
                                             (fun q ->
                                                FStar_Compiler_Util.for_some
                                                  (fun qual ->
                                                     let uu___18 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___18 = q) quals) qs in
                                         yesno uu___17 in
                                   let uu___17 =
                                     let uu___18 =
                                       match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_namespace
                                       with
                                       | FStar_Pervasives_Native.None -> no
                                       | FStar_Pervasives_Native.Some
                                           namespaces ->
                                           let p =
                                             let uu___19 =
                                               FStar_Syntax_Syntax.lid_of_fv
                                                 fv in
                                             FStar_Ident.path_of_lid uu___19 in
                                           let r =
                                             FStar_Compiler_Path.search_forest
                                               (FStar_Class_Ord.ord_eq
                                                  FStar_Class_Ord.ord_string)
                                               p namespaces in
                                           yesno r in
                                     [uu___18] in
                                   uu___16 :: uu___17 in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         comb_or uu___7 in
                       meets_some_criterion))
                 | (uu___, uu___1, uu___2, uu___3, uu___4,
                    FStar_Pervasives_Native.Some uu___5) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___7 ->
                           let uu___8 =
                             FStar_Class_Show.show
                               FStar_Syntax_Print.showable_fv fv in
                           FStar_Compiler_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___8);
                      (let meets_some_criterion =
                         let uu___7 =
                           let uu___8 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___9 =
                                 let uu___10 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Compiler_Option.isSome uu___10 in
                               yesno uu___9
                             else no in
                           let uu___9 =
                             let uu___10 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___11 =
                                     FStar_Compiler_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   yesno uu___11 in
                             let uu___11 =
                               let uu___12 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___13 =
                                       FStar_Compiler_Util.for_some
                                         (fun at ->
                                            FStar_Compiler_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     yesno uu___13 in
                               let uu___13 =
                                 let uu___14 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___15 =
                                         FStar_Compiler_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       fullyno uu___15 in
                                 let uu___15 =
                                   let uu___16 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___17 =
                                           FStar_Compiler_Util.for_some
                                             (fun q ->
                                                FStar_Compiler_Util.for_some
                                                  (fun qual ->
                                                     let uu___18 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___18 = q) quals) qs in
                                         yesno uu___17 in
                                   let uu___17 =
                                     let uu___18 =
                                       match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_namespace
                                       with
                                       | FStar_Pervasives_Native.None -> no
                                       | FStar_Pervasives_Native.Some
                                           namespaces ->
                                           let p =
                                             let uu___19 =
                                               FStar_Syntax_Syntax.lid_of_fv
                                                 fv in
                                             FStar_Ident.path_of_lid uu___19 in
                                           let r =
                                             FStar_Compiler_Path.search_forest
                                               (FStar_Class_Ord.ord_eq
                                                  FStar_Class_Ord.ord_string)
                                               p namespaces in
                                           yesno r in
                                     [uu___18] in
                                   uu___16 :: uu___17 in
                                 uu___14 :: uu___15 in
                               uu___12 :: uu___13 in
                             uu___10 :: uu___11 in
                           uu___8 :: uu___9 in
                         comb_or uu___7 in
                       meets_some_criterion))
                 | (uu___, uu___1, uu___2, uu___3, uu___4, uu___5) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Compiler_Util.for_some
                          (FStar_TypeChecker_TermEqAndSimplify.eq_tm_bool
                             cfg.FStar_TypeChecker_Cfg.tcenv
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___7 ->
                           FStar_Compiler_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | uu___ -> default_unfolding ()) in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu___1 ->
               let uu___2 =
                 FStar_Class_Show.show FStar_Syntax_Print.showable_fv fv in
               let uu___3 =
                 let uu___4 = FStar_Syntax_Syntax.range_of_fv fv in
                 FStar_Class_Show.show FStar_Compiler_Range_Ops.show_range
                   uu___4 in
               let uu___4 =
                 FStar_Class_Show.show
                   (FStar_Class_Show.show_tuple3
                      (FStar_Class_Show.printableshow
                         FStar_Class_Printable.printable_bool)
                      (FStar_Class_Show.printableshow
                         FStar_Class_Printable.printable_bool)
                      (FStar_Class_Show.printableshow
                         FStar_Class_Printable.printable_bool)) res in
               FStar_Compiler_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n" uu___2
                 uu___3 uu___4);
          (let r =
             match res with
             | (false, uu___1, uu___2) -> Should_unfold_no
             | (true, false, false) -> Should_unfold_yes
             | (true, true, false) -> Should_unfold_fully
             | (true, false, true) -> Should_unfold_reify
             | uu___1 ->
                 let uu___2 =
                   let uu___3 =
                     FStar_Class_Show.show
                       (FStar_Class_Show.show_tuple3
                          (FStar_Class_Show.printableshow
                             FStar_Class_Printable.printable_bool)
                          (FStar_Class_Show.printableshow
                             FStar_Class_Printable.printable_bool)
                          (FStar_Class_Show.printableshow
                             FStar_Class_Printable.printable_bool)) res in
                   FStar_Compiler_Util.format1
                     "Unexpected unfolding result: %s" uu___3 in
                 FStar_Compiler_Effect.failwith uu___2 in
           (let uu___2 =
              ((((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                   &&
                   (let uu___3 = FStar_Options.no_plugins () in
                    Prims.op_Negation uu___3))
                  && (r <> Should_unfold_no))
                 &&
                 (FStar_Compiler_Util.for_some
                    (FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr)
                    attrs))
                &&
                (let uu___3 =
                   FStar_Compiler_Effect.op_Bang plugin_unfold_warn_ctr in
                 uu___3 > Prims.int_zero) in
            if uu___2
            then
              let msg =
                let uu___3 = FStar_Syntax_Print.fv_to_string fv in
                FStar_Compiler_Util.format1
                  "Unfolding name which is marked as a plugin: %s" uu___3 in
              (FStar_Errors.log_issue
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                 (FStar_Errors_Codes.Warning_UnfoldPlugin, msg);
               (let uu___4 =
                  let uu___5 =
                    FStar_Compiler_Effect.op_Bang plugin_unfold_warn_ctr in
                  uu___5 - Prims.int_one in
                FStar_Compiler_Effect.op_Colon_Equals plugin_unfold_warn_ctr
                  uu___4))
            else ());
           r)