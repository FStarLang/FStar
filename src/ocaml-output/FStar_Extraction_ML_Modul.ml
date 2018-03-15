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
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | uu____105 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____107;
             FStar_Syntax_Syntax.vars = uu____108;_},
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, uu____110));
              FStar_Syntax_Syntax.pos = uu____111;
              FStar_Syntax_Syntax.vars = uu____112;_},
            uu____113)::[]);
        FStar_Syntax_Syntax.pos = uu____114;
        FStar_Syntax_Syntax.vars = uu____115;_} ->
        let uu____146 =
          let uu____147 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____147 in
        (match uu____146 with
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
         | uu____150 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline", uu____151));
        FStar_Syntax_Syntax.pos = uu____152;
        FStar_Syntax_Syntax.vars = uu____153;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute", uu____156));
        FStar_Syntax_Syntax.pos = uu____157;
        FStar_Syntax_Syntax.vars = uu____158;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____162);
        FStar_Syntax_Syntax.pos = uu____163;
        FStar_Syntax_Syntax.vars = uu____164;_} -> extract_meta x1
    | uu____171 -> FStar_Pervasives_Native.None
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders :
  'Auu____184 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv, 'Auu____184) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env, Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun bs ->
      FStar_Util.fold_map
        (fun env1 ->
           fun uu____222 ->
             match uu____222 with
             | (bv, uu____232) ->
                 let uu____233 =
                   let uu____234 =
                     let uu____237 =
                       let uu____238 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____238 in
                     FStar_Pervasives_Native.Some uu____237 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____234 in
                 let uu____239 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____233, uu____239)) env bs
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
              let uu____271 =
                let uu____272 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____272 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____271 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____274 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____291 -> def1 in
            let uu____292 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____303) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____324 -> ([], def2) in
            match uu____292 with
            | (bs, body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___66_345 ->
                       match uu___66_345 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | uu____346 -> false) quals in
                let uu____347 = binders_as_mlty_binders env bs in
                (match uu____347 with
                 | (env1, ml_bs) ->
                     let body1 =
                       let uu____367 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____367
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____371 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___67_376 ->
                                 match uu___67_376 with
                                 | FStar_Syntax_Syntax.Projector uu____377 ->
                                     true
                                 | uu____382 -> false)) in
                       if uu____371
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let metadata = extract_metadata attrs in
                     let td =
                       let uu____413 =
                         let uu____434 = lident_as_mlsymbol lid in
                         (assumed, uu____434, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____413] in
                     let def3 =
                       let uu____486 =
                         let uu____487 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____487 in
                       [uu____486; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____489 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___68_493 ->
                                 match uu___68_493 with
                                 | FStar_Syntax_Syntax.Assumption -> true
                                 | FStar_Syntax_Syntax.New -> true
                                 | uu____494 -> false)) in
                       if uu____489
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
    let uu____633 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____634 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____635 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____636 =
      let uu____637 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d ->
                let uu____648 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____649 =
                  let uu____650 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____650 in
                Prims.strcat uu____648 uu____649)) in
      FStar_All.pipe_right uu____637 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____633 uu____634 uu____635
      uu____636
let bundle_as_inductive_families :
  'Auu____658 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____658 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env, inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          let uu____689 =
            FStar_Util.fold_map
              (fun env1 ->
                 fun se ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l, _us, bs, t, _mut_i, datas) ->
                       let uu____736 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____736 with
                        | (bs1, t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1 ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d, uu____775, t2, l', nparams,
                                           uu____779)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____784 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____784 with
                                           | (bs', body) ->
                                               let uu____817 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____817 with
                                                | (bs_params, rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____888 ->
                                                           fun uu____889 ->
                                                             match (uu____888,
                                                                    uu____889)
                                                             with
                                                             | ((b',
                                                                 uu____907),
                                                                (b,
                                                                 uu____909))
                                                                 ->
                                                                 let uu____918
                                                                   =
                                                                   let uu____925
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____925) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____918)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____927 =
                                                        let uu____930 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____930 in
                                                      FStar_All.pipe_right
                                                        uu____927
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____935 -> [])) in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____940 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____940 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____943 -> (env1, [])) env ses in
          match uu____689 with
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
          let uu____1019 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1019 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1026 =
            let uu____1027 =
              let uu____1030 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1030 in
            uu____1027.FStar_Syntax_Syntax.n in
          match uu____1026 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, uu____1034) ->
              FStar_List.map
                (fun uu____1060 ->
                   match uu____1060 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1066;
                        FStar_Syntax_Syntax.sort = uu____1067;_},
                      uu____1068) -> ppname.FStar_Ident.idText) bs
          | uu____1071 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1082 =
          let uu____1083 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1083 in
        let uu____1088 =
          let uu____1099 = lident_as_mlsymbol ctor.dname in
          let uu____1100 =
            let uu____1107 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1107 in
          (uu____1099, uu____1100) in
        (uu____1082, uu____1088) in
      let extract_one_family env1 ind =
        let uu____1155 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1155 with
        | (env2, vars) ->
            let uu____1190 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1190 with
             | (env3, ctors) ->
                 let uu____1283 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1283 with
                  | (indices, uu____1319) ->
                      let ml_params =
                        let uu____1339 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____1358 ->
                                    let uu____1363 =
                                      FStar_Util.string_of_int i in
                                    Prims.strcat "'dummyV" uu____1363)) in
                        FStar_List.append vars uu____1339 in
                      let tbody =
                        let uu____1365 =
                          FStar_Util.find_opt
                            (fun uu___69_1370 ->
                               match uu___69_1370 with
                               | FStar_Syntax_Syntax.RecordType uu____1371 ->
                                   true
                               | uu____1380 -> false) ind.iquals in
                        match uu____1365 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu____1391 = FStar_List.hd ctors in
                            (match uu____1391 with
                             | (uu____1412, c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1 ->
                                        fun uu____1451 ->
                                          match uu____1451 with
                                          | (uu____1460, ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1]) in
                                              let uu____1463 =
                                                lident_as_mlsymbol lid in
                                              (uu____1463, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1464 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1467 =
                        let uu____1486 = lident_as_mlsymbol ind.iname in
                        (false, uu____1486, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1467))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____1520, t, uu____1522, uu____1523, uu____1524);
            FStar_Syntax_Syntax.sigrng = uu____1525;
            FStar_Syntax_Syntax.sigquals = uu____1526;
            FStar_Syntax_Syntax.sigmeta = uu____1527;
            FStar_Syntax_Syntax.sigattrs = uu____1528;_}::[],
          uu____1529),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____1546 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1546 with
           | (env1, ctor) ->
               (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____1592), quals) ->
          let uu____1606 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1606 with
           | (env1, ifams) ->
               let uu____1627 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1627 with
                | (env2, td) ->
                    (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1720 -> failwith "Unexpected signature element"
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
      let uu____1746 =
        (let uu____1749 = FStar_Options.codegen () in
         uu____1749 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1755 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr in
           Prims.op_Negation uu____1755) in
      if uu____1746
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1776 =
                   let uu____1779 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   uu____1779.FStar_Syntax_Syntax.fv_name in
                 uu____1776.FStar_Syntax_Syntax.v in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
               let ml_name_str =
                 let uu____1784 =
                   let uu____1785 = FStar_Ident.string_of_lid fv in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1785 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1784 in
               let uu____1786 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str in
               match uu____1786 with
               | FStar_Pervasives_Native.Some (interp, arity, plugin1) ->
                   let register =
                     if plugin1
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic" in
                   let h =
                     let uu____1809 =
                       let uu____1810 =
                         let uu____1811 = FStar_Ident.lid_of_str register in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1811 in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1810 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1809 in
                   let arity1 =
                     let uu____1813 =
                       let uu____1814 =
                         let uu____1825 = FStar_Util.string_of_int arity in
                         (uu____1825, FStar_Pervasives_Native.None) in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1814 in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1813 in
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
         | uu____1847 -> [])
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
           let uu____1870 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1870);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1877 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1886 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1903 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1941 =
               let uu____1946 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1946 ml_name tysc
                 false false in
             match uu____1941 with
             | (g2, mangled_name) ->
                 ((let uu____1954 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1954
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
             (let uu____1968 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1968
              then
                let uu____1969 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1969
              else ());
             (let uu____1971 =
                let uu____1972 = FStar_Syntax_Subst.compress tm in
                uu____1972.FStar_Syntax_Syntax.n in
              match uu____1971 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1, uu____1980) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1987 =
                    let uu____1996 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1996 in
                  (match uu____1987 with
                   | (uu____2053, uu____2054, tysc, uu____2056) ->
                       let uu____2057 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2057, tysc))
              | uu____2058 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2084 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2084
              then
                let uu____2085 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2086 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2085
                  uu____2086
              else ());
             (let uu____2088 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2088 with
              | (a_nm, a_lid) ->
                  let lbname =
                    let uu____2104 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2104 in
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
                  let uu____2130 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2130 with
                   | (a_let, uu____2142, ty) ->
                       ((let uu____2145 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2145
                         then
                           let uu____2146 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2146
                         else ());
                        (let uu____2148 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2157, mllb::[]), uu____2159) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None ->
                                    failwith "No type scheme")
                           | uu____2177 -> failwith "Impossible" in
                         match uu____2148 with
                         | (exp, tysc) ->
                             ((let uu____2189 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2189
                               then
                                 ((let uu____2191 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2191);
                                  FStar_List.iter
                                    (fun x ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2195 =
             let uu____2200 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2200 with
             | (return_tm, ty_sc) ->
                 let uu____2213 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2213 with
                  | (return_nm, return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2195 with
            | (g1, return_decl) ->
                let uu____2232 =
                  let uu____2237 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2237 with
                  | (bind_tm, ty_sc) ->
                      let uu____2250 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2250 with
                       | (bind_nm, bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2232 with
                 | (g2, bind_decl) ->
                     let uu____2269 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2269 with
                      | (g3, actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2290 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2297 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2301, t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2309 =
             let uu____2310 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___70_2314 ->
                       match uu___70_2314 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | uu____2315 -> false)) in
             Prims.op_Negation uu____2310 in
           if uu____2309
           then (g, [])
           else
             (let uu____2325 = FStar_Syntax_Util.arrow_formals t in
              match uu____2325 with
              | (bs, uu____2345) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2363 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2363)
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____2365) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2381 =
             let uu____2390 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2390 with
             | (tcenv, uu____2414, def_typ) ->
                 let uu____2420 = as_pair def_typ in (tcenv, uu____2420) in
           (match uu____2381 with
            | (tcenv, (lbdef, lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2444 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2444 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs, uu____2446) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2457 =
             let uu____2464 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2464 in
           (match uu____2457 with
            | (ml_let, uu____2474, uu____2475) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor, bindings), uu____2484) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___71_2499 ->
                            match uu___71_2499 with
                            | FStar_Syntax_Syntax.Assumption ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2502 -> FStar_Pervasives_Native.None)
                         quals in
                     let flags' = extract_metadata attrs in
                     let uu____2506 =
                       FStar_List.fold_left2
                         (fun uu____2538 ->
                            fun ml_lb ->
                              fun uu____2540 ->
                                match (uu____2538, uu____2540) with
                                | ((env, ml_lbs),
                                   { FStar_Syntax_Syntax.lbname = lbname;
                                     FStar_Syntax_Syntax.lbunivs = uu____2562;
                                     FStar_Syntax_Syntax.lbtyp = t;
                                     FStar_Syntax_Syntax.lbeff = uu____2564;
                                     FStar_Syntax_Syntax.lbdef = uu____2565;
                                     FStar_Syntax_Syntax.lbattrs = uu____2566;
                                     FStar_Syntax_Syntax.lbpos = uu____2567;_})
                                    ->
                                    let lb_lid =
                                      let uu____2593 =
                                        let uu____2596 =
                                          FStar_Util.right lbname in
                                        uu____2596.FStar_Syntax_Syntax.fv_name in
                                      uu____2593.FStar_Syntax_Syntax.v in
                                    let flags'' =
                                      let uu____2600 =
                                        let uu____2601 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____2601.FStar_Syntax_Syntax.n in
                                      match uu____2600 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (uu____2606,
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Comp
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2607;
                                                 FStar_Syntax_Syntax.effect_name
                                                   = e;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = uu____2609;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2610;
                                                 FStar_Syntax_Syntax.flags =
                                                   uu____2611;_};
                                             FStar_Syntax_Syntax.pos =
                                               uu____2612;
                                             FStar_Syntax_Syntax.vars =
                                               uu____2613;_})
                                          when
                                          let uu____2642 =
                                            FStar_Ident.string_of_lid e in
                                          uu____2642 =
                                            "FStar.HyperStack.ST.StackInline"
                                          ->
                                          [FStar_Extraction_ML_Syntax.StackInline]
                                      | uu____2643 -> [] in
                                    let meta =
                                      FStar_List.append flags1
                                        (FStar_List.append flags' flags'') in
                                    let ml_lb1 =
                                      let uu___75_2648 = ml_lb in
                                      {
                                        FStar_Extraction_ML_Syntax.mllb_name
                                          =
                                          (uu___75_2648.FStar_Extraction_ML_Syntax.mllb_name);
                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                          =
                                          (uu___75_2648.FStar_Extraction_ML_Syntax.mllb_tysc);
                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                          =
                                          (uu___75_2648.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                        FStar_Extraction_ML_Syntax.mllb_def =
                                          (uu___75_2648.FStar_Extraction_ML_Syntax.mllb_def);
                                        FStar_Extraction_ML_Syntax.mllb_meta
                                          = meta;
                                        FStar_Extraction_ML_Syntax.print_typ
                                          =
                                          (uu___75_2648.FStar_Extraction_ML_Syntax.print_typ)
                                      } in
                                    let uu____2649 =
                                      let uu____2654 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___72_2659 ->
                                                match uu___72_2659 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2660 -> true
                                                | uu____2665 -> false)) in
                                      if uu____2654
                                      then
                                        let mname =
                                          let uu____2671 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2671
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2672 =
                                          let uu____2677 =
                                            FStar_Util.right lbname in
                                          let uu____2678 =
                                            FStar_Util.must
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2677 mname uu____2678
                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2672 with
                                        | (env1, uu____2684) ->
                                            (env1,
                                              (let uu___76_2686 = ml_lb1 in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___76_2686.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___76_2686.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___76_2686.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                   =
                                                   (uu___76_2686.FStar_Extraction_ML_Syntax.mllb_meta);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___76_2686.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2690 =
                                           let uu____2691 =
                                             let uu____2696 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2696
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2691 in
                                         (uu____2690, ml_lb1)) in
                                    (match uu____2649 with
                                     | (g1, ml_lb2) ->
                                         (g1, (ml_lb2 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2506 with
                      | (g1, ml_lbs') ->
                          let uu____2727 =
                            let uu____2730 =
                              let uu____2733 =
                                let uu____2734 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2734 in
                              [uu____2733;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))] in
                            let uu____2737 = maybe_register_plugin g1 se in
                            FStar_List.append uu____2730 uu____2737 in
                          (g1, uu____2727))
                 | uu____2742 ->
                     let uu____2743 =
                       let uu____2744 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2744 in
                     failwith uu____2743))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2752, t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2757 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2757
           then
             let always_fail =
               let imp =
                 let uu____2768 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2768 with
                 | ([], t1) ->
                     let b =
                       let uu____2797 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2797 in
                     let uu____2798 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2798
                       FStar_Pervasives_Native.None
                 | (bs, t1) ->
                     let uu____2817 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2817
                       FStar_Pervasives_Native.None in
               let uu___77_2818 = se in
               let uu____2819 =
                 let uu____2820 =
                   let uu____2827 =
                     let uu____2834 =
                       let uu____2837 =
                         let uu____2838 =
                           let uu____2843 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2843 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2838;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         } in
                       [uu____2837] in
                     (false, uu____2834) in
                   (uu____2827, []) in
                 FStar_Syntax_Syntax.Sig_let uu____2820 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2819;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___77_2818.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___77_2818.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___77_2818.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___77_2818.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____2856 = extract_sig g always_fail in
             (match uu____2856 with
              | (g1, mlm) ->
                  let uu____2875 =
                    FStar_Util.find_map quals
                      (fun uu___73_2880 ->
                         match uu___73_2880 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2884 -> FStar_Pervasives_Native.None) in
                  (match uu____2875 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2892 =
                         let uu____2895 =
                           let uu____2896 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2896 in
                         let uu____2897 =
                           let uu____2900 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____2900] in
                         uu____2895 :: uu____2897 in
                       (g1, uu____2892)
                   | uu____2903 ->
                       let uu____2906 =
                         FStar_Util.find_map quals
                           (fun uu___74_2912 ->
                              match uu___74_2912 with
                              | FStar_Syntax_Syntax.Projector (l, uu____2916)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2917 -> FStar_Pervasives_Native.None) in
                       (match uu____2906 with
                        | FStar_Pervasives_Native.Some uu____2924 -> (g1, [])
                        | uu____2927 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2936 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____2936 with
            | (ml_main, uu____2950, uu____2951) ->
                let uu____2952 =
                  let uu____2955 =
                    let uu____2956 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2956 in
                  [uu____2955; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____2952))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2959 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2966 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2975 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2978 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g ->
    fun m ->
      let uu____3003 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3003 FStar_Pervasives_Native.fst
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
      (let uu____3045 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___78_3048 = g in
         let uu____3049 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3049;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___78_3048.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___78_3048.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___78_3048.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____3050 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____3050 with
       | (g2, sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____3079 = FStar_Options.codegen () in
             uu____3079 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin) in
           let uu____3084 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____3084
           then
             ((let uu____3092 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____3092);
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
      let uu____3166 = FStar_Options.debug_any () in
      if uu____3166
      then
        let msg =
          let uu____3174 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
          FStar_Util.format1 "Extracting module %s\n" uu____3174 in
        FStar_Util.measure_execution_time msg
          (fun uu____3182 -> extract' g m)
      else extract' g m