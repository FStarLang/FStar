open Prims
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_once 
  | Should_unfold_fully 
  | Should_unfold_reify 
let uu___is_Should_unfold_no (projectee : should_unfold_res) : Prims.bool=
  match projectee with | Should_unfold_no -> true | uu___ -> false
let uu___is_Should_unfold_yes (projectee : should_unfold_res) : Prims.bool=
  match projectee with | Should_unfold_yes -> true | uu___ -> false
let uu___is_Should_unfold_once (projectee : should_unfold_res) : Prims.bool=
  match projectee with | Should_unfold_once -> true | uu___ -> false
let uu___is_Should_unfold_fully (projectee : should_unfold_res) : Prims.bool=
  match projectee with | Should_unfold_fully -> true | uu___ -> false
let uu___is_Should_unfold_reify (projectee : should_unfold_res) : Prims.bool=
  match projectee with | Should_unfold_reify -> true | uu___ -> false
let should_unfold (cfg : FStarC_TypeChecker_Cfg.cfg)
  (should_reify : FStarC_TypeChecker_Cfg.cfg -> Prims.bool)
  (fv : FStarC_Syntax_Syntax.fv) (qninfo : FStarC_TypeChecker_Env.qninfo) :
  should_unfold_res=
  let attrs =
    let uu___ = FStarC_TypeChecker_Env.attrs_of_qninfo qninfo in
    match uu___ with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some ats -> ats in
  let quals =
    let uu___ = FStarC_TypeChecker_Env.quals_of_qninfo qninfo in
    match uu___ with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some quals1 -> quals1 in
  let yes = (true, false, false, false) in
  let no = (false, false, false, false) in
  let fully = (true, true, false, false) in
  let reif = (true, false, true, false) in
  let once = (true, false, false, true) in
  let yesno b = if b then yes else no in
  let fullyno b = if b then fully else no in
  let comb_or l =
    FStarC_List.fold_right
      (fun uu___ uu___1 ->
         match (uu___, uu___1) with
         | ((a, b, c, d), (x, y, z, w)) ->
             ((a || x), (b || y), (c || z), (d || w))) l
      (false, false, false, false) in
  let default_unfolding uu___ =
    FStarC_TypeChecker_Cfg.log_unfolding cfg
      (fun uu___2 ->
         let uu___3 =
           FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv fv in
         let uu___4 =
           let uu___5 =
             FStarC_TypeChecker_Env.delta_depth_of_fv
               cfg.FStarC_TypeChecker_Cfg.tcenv fv in
           FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_delta_depth
             uu___5 in
         let uu___5 =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list
                FStarC_TypeChecker_Env.showable_delta_level)
             cfg.FStarC_TypeChecker_Cfg.delta_level in
         FStarC_Format.print3
           "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
           uu___3 uu___4 uu___5);
    (let uu___2 =
       FStarC_Util.for_some
         (fun uu___3 ->
            match uu___3 with
            | FStarC_TypeChecker_Env.NoDelta -> false
            | FStarC_TypeChecker_Env.InliningDelta -> true
            | FStarC_TypeChecker_Env.Eager_unfolding_only -> true
            | FStarC_TypeChecker_Env.Unfold l ->
                let uu___4 =
                  FStarC_TypeChecker_Env.delta_depth_of_fv
                    cfg.FStarC_TypeChecker_Cfg.tcenv fv in
                FStarC_TypeChecker_Common.delta_depth_greater_than uu___4 l)
         cfg.FStarC_TypeChecker_Cfg.delta_level in
     yesno uu___2) in
  let selective_unfold =
    (((((FStar_Pervasives_Native.uu___is_Some
           (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_only)
          ||
          (FStar_Pervasives_Native.uu___is_Some
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_once))
         ||
         (FStar_Pervasives_Native.uu___is_Some
            (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_fully))
        ||
        (FStar_Pervasives_Native.uu___is_Some
           (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_attr))
       ||
       (FStar_Pervasives_Native.uu___is_Some
          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_qual))
      ||
      (FStar_Pervasives_Native.uu___is_Some
         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_namespace) in
  let res =
    if FStarC_TypeChecker_Env.qninfo_is_action qninfo
    then
      let b = should_reify cfg in
      (FStarC_TypeChecker_Cfg.log_unfolding cfg
         (fun uu___1 ->
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv fv in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
            FStarC_Format.print2
              "should_unfold: For DM4F action %s, should_reify = %s\n" uu___2
              uu___3);
       if b then reif else no)
    else
      if
        (let uu___ = FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
         FStar_Pervasives_Native.uu___is_Some uu___)
      then
        (FStarC_TypeChecker_Cfg.log_unfolding cfg
           (fun uu___1 ->
              FStarC_Format.print_string " >> It's a primop, not unfolding\n");
         no)
      else
        (match (qninfo, selective_unfold) with
         | (FStar_Pervasives_Native.Some
            (FStar_Pervasives.Inr
             ({
                FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
                  { FStarC_Syntax_Syntax.lbs1 = (is_rec, uu___);
                    FStarC_Syntax_Syntax.lids1 = uu___1;_};
                FStarC_Syntax_Syntax.sigrng = uu___2;
                FStarC_Syntax_Syntax.sigquals = qs;
                FStarC_Syntax_Syntax.sigmeta = uu___3;
                FStarC_Syntax_Syntax.sigattrs = uu___4;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
                FStarC_Syntax_Syntax.sigopts = uu___6;_},
              uu___7),
             uu___8),
            uu___9) when
             FStarC_List.contains FStarC_Syntax_Syntax.HasMaskedEffect qs ->
             (FStarC_TypeChecker_Cfg.log_unfolding cfg
                (fun uu___11 ->
                   FStarC_Format.print_string
                     " >> HasMaskedEffect, not unfolding\n");
              no)
         | (uu___, true) when
             (FStar_Pervasives_Native.uu___is_Some
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_once)
               &&
               (FStarC_Util.for_some (FStarC_Syntax_Syntax.fv_eq_lid fv)
                  (FStar_Pervasives_Native.__proj__Some__item__v
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_once))
             ->
             (FStarC_TypeChecker_Cfg.log_unfolding cfg
                (fun uu___2 -> FStarC_Format.print_string " >> UnfoldOnce\n");
              once)
         | (FStar_Pervasives_Native.Some
            (FStar_Pervasives.Inr
             ({ FStarC_Syntax_Syntax.sigel = uu___;
                FStarC_Syntax_Syntax.sigrng = uu___1;
                FStarC_Syntax_Syntax.sigquals = uu___2;
                FStarC_Syntax_Syntax.sigmeta = uu___3;
                FStarC_Syntax_Syntax.sigattrs = attrs1;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
                FStarC_Syntax_Syntax.sigopts = uu___5;_},
              uu___6),
             uu___7),
            uu___8) when
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
               &&
               (let uu___9 =
                  FStarC_Util.find_map attrs1
                    FStarC_Parser_Const_ExtractAs.is_extract_as_attr in
                FStar_Pervasives_Native.uu___is_Some uu___9)
             ->
             (FStarC_TypeChecker_Cfg.log_unfolding cfg
                (fun uu___10 ->
                   FStarC_Format.print_string
                     " >> Has extract_as attribute and we're extracting, unfold!");
              yes)
         | (FStar_Pervasives_Native.Some
            (FStar_Pervasives.Inr
             ({
                FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
                  { FStarC_Syntax_Syntax.lbs1 = (is_rec, uu___);
                    FStarC_Syntax_Syntax.lids1 = uu___1;_};
                FStarC_Syntax_Syntax.sigrng = uu___2;
                FStarC_Syntax_Syntax.sigquals = qs;
                FStarC_Syntax_Syntax.sigmeta = uu___3;
                FStarC_Syntax_Syntax.sigattrs = uu___4;
                FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
                FStarC_Syntax_Syntax.sigopts = uu___6;_},
              uu___7),
             uu___8),
            uu___9) when
             (is_rec &&
                (Prims.op_Negation
                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta))
               &&
               (Prims.op_Negation
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full)
             ->
             (FStarC_TypeChecker_Cfg.log_unfolding cfg
                (fun uu___11 ->
                   FStarC_Format.print_string
                     " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
              no)
         | (uu___, true) ->
             (FStarC_TypeChecker_Cfg.log_unfolding cfg
                (fun uu___2 ->
                   let uu___3 =
                     FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv
                       fv in
                   FStarC_Format.print1
                     "should_unfold: Reached a %s with selective unfolding\n"
                     uu___3);
              (let meets_some_criterion =
                 let uu___2 =
                   let uu___3 =
                     if
                       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                     then
                       let uu___4 =
                         let uu___5 =
                           FStarC_TypeChecker_Env.lookup_definition_qninfo
                             [FStarC_TypeChecker_Env.Eager_unfolding_only;
                             FStarC_TypeChecker_Env.InliningDelta]
                             fv.FStarC_Syntax_Syntax.fv_name qninfo in
                         FStar_Pervasives_Native.uu___is_Some uu___5 in
                       yesno uu___4
                     else no in
                   let uu___4 =
                     let uu___5 =
                       match (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_only
                       with
                       | FStar_Pervasives_Native.None -> no
                       | FStar_Pervasives_Native.Some lids ->
                           let uu___6 =
                             FStarC_Util.for_some
                               (FStarC_Syntax_Syntax.fv_eq_lid fv) lids in
                           yesno uu___6 in
                     let uu___6 =
                       let uu___7 =
                         match (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_attr
                         with
                         | FStar_Pervasives_Native.None -> no
                         | FStar_Pervasives_Native.Some lids ->
                             let uu___8 =
                               FStarC_Util.for_some
                                 (fun at ->
                                    FStarC_Util.for_some
                                      (fun lid ->
                                         FStarC_Syntax_Util.is_fvar lid at)
                                      lids) attrs in
                             yesno uu___8 in
                       let uu___8 =
                         let uu___9 =
                           match (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_fully
                           with
                           | FStar_Pervasives_Native.None -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu___10 =
                                 FStarC_Util.for_some
                                   (FStarC_Syntax_Syntax.fv_eq_lid fv) lids in
                               fullyno uu___10 in
                         let uu___10 =
                           let uu___11 =
                             match (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_qual
                             with
                             | FStar_Pervasives_Native.None -> no
                             | FStar_Pervasives_Native.Some qs ->
                                 let uu___12 =
                                   FStarC_Util.for_some
                                     (fun q ->
                                        FStarC_Util.for_some
                                          (fun qual ->
                                             let uu___13 =
                                               FStarC_Class_Show.show
                                                 FStarC_Syntax_Print.showable_qualifier
                                                 qual in
                                             uu___13 = q) quals) qs in
                                 yesno uu___12 in
                           let uu___12 =
                             let uu___13 =
                               match (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_namespace
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some namespaces ->
                                   let p =
                                     let uu___14 =
                                       FStarC_Syntax_Syntax.lid_of_fv fv in
                                     FStarC_Ident.path_of_lid uu___14 in
                                   let r =
                                     FStarC_Path.search_forest
                                       (FStarC_Class_Ord.ord_eq
                                          FStarC_Class_Ord.ord_string) p
                                       namespaces in
                                   yesno r in
                             [uu___13] in
                           uu___11 :: uu___12 in
                         uu___9 :: uu___10 in
                       uu___7 :: uu___8 in
                     uu___5 :: uu___6 in
                   uu___3 :: uu___4 in
                 comb_or uu___2 in
               meets_some_criterion))
         | uu___ when
             (FStar_Pervasives_Native.uu___is_Some
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.dont_unfold_attr)
               &&
               (FStarC_List.existsb
                  (fun fa -> FStarC_Syntax_Util.has_attribute attrs fa)
                  (FStar_Pervasives_Native.__proj__Some__item__v
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.dont_unfold_attr))
             ->
             (FStarC_TypeChecker_Cfg.log_unfolding cfg
                (fun uu___2 ->
                   FStarC_Format.print_string
                     " >> forbidden by attribute, not unfolding\n");
              no)
         | uu___ -> default_unfolding ()) in
  FStarC_TypeChecker_Cfg.log_unfolding cfg
    (fun uu___1 ->
       let uu___2 =
         FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv fv in
       let uu___3 =
         let uu___4 = FStarC_Syntax_Syntax.range_of_fv fv in
         FStarC_Class_Show.show FStarC_Range_Ops.showable_range uu___4 in
       let uu___4 =
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_tuple4 FStarC_Class_Show.showable_bool
              FStarC_Class_Show.showable_bool FStarC_Class_Show.showable_bool
              FStarC_Class_Show.showable_bool) res in
       FStarC_Format.print3
         "should_unfold: For %s (%s), unfolding res = %s\n" uu___2 uu___3
         uu___4);
  (let r =
     match res with
     | (false, uu___1, uu___2, uu___3) -> Should_unfold_no
     | (true, false, false, false) -> Should_unfold_yes
     | (true, false, false, true) -> Should_unfold_once
     | (true, true, false, false) -> Should_unfold_fully
     | (true, false, true, false) -> Should_unfold_reify
     | uu___1 ->
         let uu___2 =
           let uu___3 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_tuple4 FStarC_Class_Show.showable_bool
                  FStarC_Class_Show.showable_bool
                  FStarC_Class_Show.showable_bool
                  FStarC_Class_Show.showable_bool) res in
           FStarC_Format.fmt1 "Unexpected unfolding result: %s" uu___3 in
         failwith uu___2 in
   r)
