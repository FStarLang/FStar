open Prims
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid ->
    fun t ->
      let uu____9 =
        let uu____12 =
          let uu____13 =
            let uu____28 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            let uu____29 =
              let uu____32 = FStar_Syntax_Syntax.iarg t in
              let uu____33 =
                let uu____36 =
                  let uu____37 =
                    let uu____38 =
                      let uu____41 =
                        let uu____42 =
                          let uu____43 =
                            let uu____48 =
                              let uu____49 =
                                FStar_Syntax_Print.lid_to_string lid in
                              Prims.strcat "Not yet implemented:" uu____49 in
                            (uu____48, FStar_Range.dummyRange) in
                          FStar_Const.Const_string uu____43 in
                        FStar_Syntax_Syntax.Tm_constant uu____42 in
                      FStar_Syntax_Syntax.mk uu____41 in
                    uu____38 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____37 in
                [uu____36] in
              uu____32 :: uu____33 in
            (uu____28, uu____29) in
          FStar_Syntax_Syntax.Tm_app uu____13 in
        FStar_Syntax_Syntax.mk uu____12 in
      uu____9 FStar_Pervasives_Native.None FStar_Range.dummyRange
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x -> x
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1 ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
let as_pair :
  'Auu____66 .
    'Auu____66 Prims.list ->
      ('Auu____66, 'Auu____66) FStar_Pervasives_Native.tuple2
  =
  fun uu___65_76 ->
    match uu___65_76 with
    | a::b::[] -> (a, b)
    | uu____81 -> failwith "Expected a list with 2 elements"
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x ->
    let uu____93 = FStar_Syntax_Subst.compress x in
    match uu____93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____97;
        FStar_Syntax_Syntax.vars = uu____98;_} ->
        let uu____101 =
          let uu____102 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____102 in
        (match uu____101 with
         | "KremlinPrivate" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____106;
             FStar_Syntax_Syntax.vars = uu____107;_},
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, uu____109));
              FStar_Syntax_Syntax.pos = uu____110;
              FStar_Syntax_Syntax.vars = uu____111;_},
            uu____112)::[]);
        FStar_Syntax_Syntax.pos = uu____113;
        FStar_Syntax_Syntax.vars = uu____114;_} ->
        let uu____145 =
          let uu____146 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____146 in
        (match uu____145 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | uu____149 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline", uu____150));
        FStar_Syntax_Syntax.pos = uu____151;
        FStar_Syntax_Syntax.vars = uu____152;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute", uu____155));
        FStar_Syntax_Syntax.pos = uu____156;
        FStar_Syntax_Syntax.vars = uu____157;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____161);
        FStar_Syntax_Syntax.pos = uu____162;
        FStar_Syntax_Syntax.vars = uu____163;_} -> extract_meta x1
    | uu____170 -> FStar_Pervasives_Native.None
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders :
  'Auu____183 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv, 'Auu____183) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env, Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun bs ->
      FStar_Util.fold_map
        (fun env1 ->
           fun uu____221 ->
             match uu____221 with
             | (bv, uu____231) ->
                 let uu____232 =
                   let uu____233 =
                     let uu____236 =
                       let uu____237 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____237 in
                     FStar_Pervasives_Native.Some uu____236 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____233 in
                 let uu____238 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____232, uu____238)) env bs
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,
              FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
              FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun fv ->
      fun quals ->
        fun attrs ->
          fun def ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let def1 =
              let uu____270 =
                let uu____271 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____271 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____270 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____273 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____290 -> def1 in
            let uu____291 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____302) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____323 -> ([], def2) in
            match uu____291 with
            | (bs, body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___66_344 ->
                       match uu___66_344 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | uu____345 -> false) quals in
                let uu____346 = binders_as_mlty_binders env bs in
                (match uu____346 with
                 | (env1, ml_bs) ->
                     let body1 =
                       let uu____366 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____366
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____370 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___67_375 ->
                                 match uu___67_375 with
                                 | FStar_Syntax_Syntax.Projector uu____376 ->
                                     true
                                 | uu____381 -> false)) in
                       if uu____370
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let metadata = extract_metadata attrs in
                     let td =
                       let uu____412 =
                         let uu____433 = lident_as_mlsymbol lid in
                         (assumed, uu____433, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____412] in
                     let def3 =
                       let uu____485 =
                         let uu____486 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____486 in
                       [uu____485; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____488 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___68_492 ->
                                 match uu___68_492 with
                                 | FStar_Syntax_Syntax.Assumption -> true
                                 | FStar_Syntax_Syntax.New -> true
                                 | uu____493 -> false)) in
                       if uu____488
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                     (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }[@@deriving show]
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
type inductive_family =
  {
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }[@@deriving show]
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
let (print_ifamily : inductive_family -> Prims.unit) =
  fun i ->
    let uu____632 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____633 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____634 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____635 =
      let uu____636 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d ->
                let uu____647 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____648 =
                  let uu____649 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____649 in
                Prims.strcat uu____647 uu____648)) in
      FStar_All.pipe_right uu____636 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____632 uu____633 uu____634
      uu____635
let bundle_as_inductive_families :
  'Auu____657 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____657 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env, inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          let uu____688 =
            FStar_Util.fold_map
              (fun env1 ->
                 fun se ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l, _us, bs, t, _mut_i, datas) ->
                       let uu____735 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____735 with
                        | (bs1, t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1 ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d, uu____774, t2, l', nparams,
                                           uu____778)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____783 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____783 with
                                           | (bs', body) ->
                                               let uu____816 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____816 with
                                                | (bs_params, rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____887 ->
                                                           fun uu____888 ->
                                                             match (uu____887,
                                                                    uu____888)
                                                             with
                                                             | ((b',
                                                                 uu____906),
                                                                (b,
                                                                 uu____908))
                                                                 ->
                                                                 let uu____917
                                                                   =
                                                                   let uu____924
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____924) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____917)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____926 =
                                                        let uu____929 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____929 in
                                                      FStar_All.pipe_right
                                                        uu____926
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____934 -> [])) in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____939 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____939 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____942 -> (env1, [])) env ses in
          match uu____688 with
          | (env1, ifams) -> (env1, (FStar_List.flatten ifams))
type env_t = FStar_Extraction_ML_UEnv.env[@@deriving show]
let (extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t, FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1018 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1018 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1025 =
            let uu____1026 =
              let uu____1029 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1029 in
            uu____1026.FStar_Syntax_Syntax.n in
          match uu____1025 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, uu____1033) ->
              FStar_List.map
                (fun uu____1059 ->
                   match uu____1059 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1065;
                        FStar_Syntax_Syntax.sort = uu____1066;_},
                      uu____1067) -> ppname.FStar_Ident.idText) bs
          | uu____1070 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1081 =
          let uu____1082 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1082 in
        let uu____1087 =
          let uu____1098 = lident_as_mlsymbol ctor.dname in
          let uu____1099 =
            let uu____1106 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1106 in
          (uu____1098, uu____1099) in
        (uu____1081, uu____1087) in
      let extract_one_family env1 ind =
        let uu____1154 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1154 with
        | (env2, vars) ->
            let uu____1189 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1189 with
             | (env3, ctors) ->
                 let uu____1282 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1282 with
                  | (indices, uu____1318) ->
                      let ml_params =
                        let uu____1338 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____1357 ->
                                    let uu____1362 =
                                      FStar_Util.string_of_int i in
                                    Prims.strcat "'dummyV" uu____1362)) in
                        FStar_List.append vars uu____1338 in
                      let tbody =
                        let uu____1364 =
                          FStar_Util.find_opt
                            (fun uu___69_1369 ->
                               match uu___69_1369 with
                               | FStar_Syntax_Syntax.RecordType uu____1370 ->
                                   true
                               | uu____1379 -> false) ind.iquals in
                        match uu____1364 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu____1390 = FStar_List.hd ctors in
                            (match uu____1390 with
                             | (uu____1411, c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1 ->
                                        fun uu____1450 ->
                                          match uu____1450 with
                                          | (uu____1459, ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1]) in
                                              let uu____1462 =
                                                lident_as_mlsymbol lid in
                                              (uu____1462, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1463 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1466 =
                        let uu____1485 = lident_as_mlsymbol ind.iname in
                        (false, uu____1485, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1466))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____1519, t, uu____1521, uu____1522, uu____1523);
            FStar_Syntax_Syntax.sigrng = uu____1524;
            FStar_Syntax_Syntax.sigquals = uu____1525;
            FStar_Syntax_Syntax.sigmeta = uu____1526;
            FStar_Syntax_Syntax.sigattrs = uu____1527;_}::[],
          uu____1528),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____1545 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1545 with
           | (env1, ctor) ->
               (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____1591), quals) ->
          let uu____1605 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1605 with
           | (env1, ifams) ->
               let uu____1626 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1626 with
                | (env2, td) ->
                    (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1719 -> failwith "Unexpected signature element"
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun se ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top in
      let uu____1745 =
        (let uu____1748 = FStar_Options.codegen () in
         uu____1748 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1754 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr in
           Prims.op_Negation uu____1754) in
      if uu____1745
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1775 =
                   let uu____1778 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   uu____1778.FStar_Syntax_Syntax.fv_name in
                 uu____1775.FStar_Syntax_Syntax.v in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
               let ml_name_str =
                 let uu____1783 =
                   let uu____1784 = FStar_Ident.string_of_lid fv in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1784 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1783 in
               let uu____1785 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str in
               match uu____1785 with
               | FStar_Pervasives_Native.Some (interp, arity, plugin1) ->
                   let register =
                     if plugin1
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic" in
                   let h =
                     let uu____1808 =
                       let uu____1809 =
                         let uu____1810 = FStar_Ident.lid_of_str register in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1810 in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1809 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1808 in
                   let arity1 =
                     let uu____1812 =
                       let uu____1813 =
                         let uu____1824 = FStar_Util.string_of_int arity in
                         (uu____1824, FStar_Pervasives_Native.None) in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1813 in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1812 in
                   let app =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top)
                       (FStar_Extraction_ML_Syntax.MLE_App
                          (h, [w ml_name_str; w arity1; interp])) in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None -> [] in
             FStar_List.collect mk_registration
               (FStar_Pervasives_Native.snd lbs)
         | uu____1846 -> [])
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t, FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun se ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu____1869 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1869);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1876 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1885 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1902 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1940 =
               let uu____1945 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1945 ml_name tysc
                 false false in
             match uu____1940 with
             | (g2, mangled_name) ->
                 ((let uu____1953 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1953
                   then FStar_Util.print1 "Mangled name: %s\n" mangled_name
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [lb]))))) in
           let rec extract_fv tm =
             (let uu____1967 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1967
              then
                let uu____1968 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1968
              else ());
             (let uu____1970 =
                let uu____1971 = FStar_Syntax_Subst.compress tm in
                uu____1971.FStar_Syntax_Syntax.n in
              match uu____1970 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1, uu____1979) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1986 =
                    let uu____1995 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1995 in
                  (match uu____1986 with
                   | (uu____2052, uu____2053, tysc, uu____2055) ->
                       let uu____2056 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2056, tysc))
              | uu____2057 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2083 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2083
              then
                let uu____2084 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2085 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2084
                  uu____2085
              else ());
             (let uu____2087 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2087 with
              | (a_nm, a_lid) ->
                  let lbname =
                    let uu____2103 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2103 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn),
                        ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____2129 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2129 with
                   | (a_let, uu____2141, ty) ->
                       ((let uu____2144 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2144
                         then
                           let uu____2145 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2145
                         else ());
                        (let uu____2147 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2156, mllb::[]), uu____2158) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None ->
                                    failwith "No type scheme")
                           | uu____2176 -> failwith "Impossible" in
                         match uu____2147 with
                         | (exp, tysc) ->
                             ((let uu____2188 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2188
                               then
                                 ((let uu____2190 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2190);
                                  FStar_List.iter
                                    (fun x ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2194 =
             let uu____2199 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2199 with
             | (return_tm, ty_sc) ->
                 let uu____2212 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2212 with
                  | (return_nm, return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2194 with
            | (g1, return_decl) ->
                let uu____2231 =
                  let uu____2236 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2236 with
                  | (bind_tm, ty_sc) ->
                      let uu____2249 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2249 with
                       | (bind_nm, bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2231 with
                 | (g2, bind_decl) ->
                     let uu____2268 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2268 with
                      | (g3, actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2289 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2296 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2300, t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2308 =
             let uu____2309 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___70_2313 ->
                       match uu___70_2313 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | uu____2314 -> false)) in
             Prims.op_Negation uu____2309 in
           if uu____2308
           then (g, [])
           else
             (let uu____2324 = FStar_Syntax_Util.arrow_formals t in
              match uu____2324 with
              | (bs, uu____2344) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2362 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2362)
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____2364) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2380 =
             let uu____2389 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2389 with
             | (tcenv, uu____2413, def_typ) ->
                 let uu____2419 = as_pair def_typ in (tcenv, uu____2419) in
           (match uu____2380 with
            | (tcenv, (lbdef, lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2443 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2443 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs, uu____2445) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2456 =
             let uu____2463 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2463 in
           (match uu____2456 with
            | (ml_let, uu____2473, uu____2474) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor, bindings), uu____2483) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___71_2498 ->
                            match uu___71_2498 with
                            | FStar_Syntax_Syntax.Assumption ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2501 -> FStar_Pervasives_Native.None)
                         quals in
                     let flags' = extract_metadata attrs in
                     let uu____2505 =
                       FStar_List.fold_left2
                         (fun uu____2537 ->
                            fun ml_lb ->
                              fun uu____2539 ->
                                match (uu____2537, uu____2539) with
                                | ((env, ml_lbs),
                                   { FStar_Syntax_Syntax.lbname = lbname;
                                     FStar_Syntax_Syntax.lbunivs = uu____2561;
                                     FStar_Syntax_Syntax.lbtyp = t;
                                     FStar_Syntax_Syntax.lbeff = uu____2563;
                                     FStar_Syntax_Syntax.lbdef = uu____2564;
                                     FStar_Syntax_Syntax.lbattrs = uu____2565;
                                     FStar_Syntax_Syntax.lbpos = uu____2566;_})
                                    ->
                                    let lb_lid =
                                      let uu____2592 =
                                        let uu____2595 =
                                          FStar_Util.right lbname in
                                        uu____2595.FStar_Syntax_Syntax.fv_name in
                                      uu____2592.FStar_Syntax_Syntax.v in
                                    let flags'' =
                                      let uu____2599 =
                                        let uu____2600 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____2600.FStar_Syntax_Syntax.n in
                                      match uu____2599 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (uu____2605,
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Comp
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2606;
                                                 FStar_Syntax_Syntax.effect_name
                                                   = e;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = uu____2608;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2609;
                                                 FStar_Syntax_Syntax.flags =
                                                   uu____2610;_};
                                             FStar_Syntax_Syntax.pos =
                                               uu____2611;
                                             FStar_Syntax_Syntax.vars =
                                               uu____2612;_})
                                          when
                                          let uu____2641 =
                                            FStar_Ident.string_of_lid e in
                                          uu____2641 =
                                            "FStar.HyperStack.ST.StackInline"
                                          ->
                                          [FStar_Extraction_ML_Syntax.StackInline]
                                      | uu____2642 -> [] in
                                    let meta =
                                      FStar_List.append flags1
                                        (FStar_List.append flags' flags'') in
                                    let ml_lb1 =
                                      let uu___75_2647 = ml_lb in
                                      {
                                        FStar_Extraction_ML_Syntax.mllb_name
                                          =
                                          (uu___75_2647.FStar_Extraction_ML_Syntax.mllb_name);
                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                          =
                                          (uu___75_2647.FStar_Extraction_ML_Syntax.mllb_tysc);
                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                          =
                                          (uu___75_2647.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                        FStar_Extraction_ML_Syntax.mllb_def =
                                          (uu___75_2647.FStar_Extraction_ML_Syntax.mllb_def);
                                        FStar_Extraction_ML_Syntax.mllb_meta
                                          = meta;
                                        FStar_Extraction_ML_Syntax.print_typ
                                          =
                                          (uu___75_2647.FStar_Extraction_ML_Syntax.print_typ)
                                      } in
                                    let uu____2648 =
                                      let uu____2653 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___72_2658 ->
                                                match uu___72_2658 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2659 -> true
                                                | uu____2664 -> false)) in
                                      if uu____2653
                                      then
                                        let mname =
                                          let uu____2670 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2670
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2671 =
                                          let uu____2676 =
                                            FStar_Util.right lbname in
                                          let uu____2677 =
                                            FStar_Util.must
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2676 mname uu____2677
                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2671 with
                                        | (env1, uu____2683) ->
                                            (env1,
                                              (let uu___76_2685 = ml_lb1 in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___76_2685.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___76_2685.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___76_2685.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                   =
                                                   (uu___76_2685.FStar_Extraction_ML_Syntax.mllb_meta);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___76_2685.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2689 =
                                           let uu____2690 =
                                             let uu____2695 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2695
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2690 in
                                         (uu____2689, ml_lb1)) in
                                    (match uu____2648 with
                                     | (g1, ml_lb2) ->
                                         (g1, (ml_lb2 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2505 with
                      | (g1, ml_lbs') ->
                          let uu____2726 =
                            let uu____2729 =
                              let uu____2732 =
                                let uu____2733 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2733 in
                              [uu____2732;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))] in
                            let uu____2736 = maybe_register_plugin g1 se in
                            FStar_List.append uu____2729 uu____2736 in
                          (g1, uu____2726))
                 | uu____2741 ->
                     let uu____2742 =
                       let uu____2743 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2743 in
                     failwith uu____2742))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2751, t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2756 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2756
           then
             let always_fail =
               let imp =
                 let uu____2767 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2767 with
                 | ([], t1) ->
                     let b =
                       let uu____2796 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2796 in
                     let uu____2797 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2797
                       FStar_Pervasives_Native.None
                 | (bs, t1) ->
                     let uu____2816 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2816
                       FStar_Pervasives_Native.None in
               let uu___77_2817 = se in
               let uu____2818 =
                 let uu____2819 =
                   let uu____2826 =
                     let uu____2833 =
                       let uu____2836 =
                         let uu____2837 =
                           let uu____2842 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2842 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2837;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         } in
                       [uu____2836] in
                     (false, uu____2833) in
                   (uu____2826, []) in
                 FStar_Syntax_Syntax.Sig_let uu____2819 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2818;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___77_2817.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___77_2817.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___77_2817.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___77_2817.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____2855 = extract_sig g always_fail in
             (match uu____2855 with
              | (g1, mlm) ->
                  let uu____2874 =
                    FStar_Util.find_map quals
                      (fun uu___73_2879 ->
                         match uu___73_2879 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2883 -> FStar_Pervasives_Native.None) in
                  (match uu____2874 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2891 =
                         let uu____2894 =
                           let uu____2895 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2895 in
                         let uu____2896 =
                           let uu____2899 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____2899] in
                         uu____2894 :: uu____2896 in
                       (g1, uu____2891)
                   | uu____2902 ->
                       let uu____2905 =
                         FStar_Util.find_map quals
                           (fun uu___74_2911 ->
                              match uu___74_2911 with
                              | FStar_Syntax_Syntax.Projector (l, uu____2915)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2916 -> FStar_Pervasives_Native.None) in
                       (match uu____2905 with
                        | FStar_Pervasives_Native.Some uu____2923 -> (g1, [])
                        | uu____2926 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2935 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2935 with
            | (ml_main, uu____2949, uu____2950) ->
                let uu____2951 =
                  let uu____2954 =
                    let uu____2955 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2955 in
                  [uu____2954; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____2951))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2958 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2965 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2974 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2977 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g ->
    fun m ->
      let uu____3002 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3002 FStar_Pervasives_Native.fst
let (extract' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,
        FStar_Extraction_ML_Syntax.mllib Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun m ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3044 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___78_3047 = g in
         let uu____3048 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3048;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___78_3047.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___78_3047.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___78_3047.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____3049 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____3049 with
       | (g2, sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____3078 = FStar_Options.codegen () in
             uu____3078 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin) in
           let uu____3083 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____3083
           then
             ((let uu____3091 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____3091);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,
        FStar_Extraction_ML_Syntax.mllib Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun m ->
      let uu____3165 = FStar_Options.debug_any () in
      if uu____3165
      then
        let msg =
          let uu____3173 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
          FStar_Util.format1 "Extracting module %s\n" uu____3173 in
        FStar_Util.measure_execution_time msg
          (fun uu____3181 -> extract' g m)
      else extract' g m