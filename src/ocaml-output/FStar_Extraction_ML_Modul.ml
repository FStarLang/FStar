open Prims
let fail_exp:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun lid  ->
    fun t  ->
      let uu____11 =
        let uu____14 =
          let uu____15 =
            let uu____30 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            let uu____31 =
              let uu____34 = FStar_Syntax_Syntax.iarg t in
              let uu____35 =
                let uu____38 =
                  let uu____39 =
                    let uu____40 =
                      let uu____43 =
                        let uu____44 =
                          let uu____45 =
                            let uu____50 =
                              let uu____51 =
                                FStar_Syntax_Print.lid_to_string lid in
                              Prims.strcat "Not yet implemented:" uu____51 in
                            (uu____50, FStar_Range.dummyRange) in
                          FStar_Const.Const_string uu____45 in
                        FStar_Syntax_Syntax.Tm_constant uu____44 in
                      FStar_Syntax_Syntax.mk uu____43 in
                    uu____40 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
                [uu____38] in
              uu____34 :: uu____35 in
            (uu____30, uu____31) in
          FStar_Syntax_Syntax.Tm_app uu____15 in
        FStar_Syntax_Syntax.mk uu____14 in
      uu____11 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol:
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair:
  'Auu____72 .
    'Auu____72 Prims.list ->
      ('Auu____72,'Auu____72) FStar_Pervasives_Native.tuple2
  =
  fun uu___185_82  ->
    match uu___185_82 with
    | a::b::[] -> (a, b)
    | uu____87 -> failwith "Expected a list with 2 elements"
let is_tactic_decl:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun tac_lid  ->
    fun h  ->
      fun current_module1  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____107) ->
            let uu____112 =
              let uu____113 = FStar_Syntax_Subst.compress h' in
              uu____113.FStar_Syntax_Syntax.n in
            (match uu____112 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 ->
                 let uu____117 =
                   let uu____118 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath
                       current_module1 in
                   FStar_Util.starts_with uu____118 "FStar.Tactics" in
                 Prims.op_Negation uu____117
             | uu____119 -> false)
        | uu____120 -> false
let rec extract_meta:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____127 = FStar_Syntax_Subst.compress x in
    match uu____127 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____131;
        FStar_Syntax_Syntax.vars = uu____132;_} when
        let uu____135 =
          let uu____136 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____136 in
        uu____135 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____138;
        FStar_Syntax_Syntax.vars = uu____139;_} when
        let uu____142 =
          let uu____143 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____143 in
        uu____142 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____145;
        FStar_Syntax_Syntax.vars = uu____146;_} when
        let uu____149 =
          let uu____150 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____150 in
        uu____149 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____152;
        FStar_Syntax_Syntax.vars = uu____153;_} when
        let uu____156 =
          let uu____157 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____157 in
        uu____156 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____159;
             FStar_Syntax_Syntax.vars = uu____160;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____162));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____163;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____164;_},uu____165)::[]);
        FStar_Syntax_Syntax.pos = uu____166;
        FStar_Syntax_Syntax.vars = uu____167;_} when
        let uu____198 =
          let uu____199 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____199 in
        uu____198 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____201;
             FStar_Syntax_Syntax.vars = uu____202;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____204));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____205;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____206;_},uu____207)::[]);
        FStar_Syntax_Syntax.pos = uu____208;
        FStar_Syntax_Syntax.vars = uu____209;_} when
        let uu____240 =
          let uu____241 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____241 in
        uu____240 = "FStar.Pervasives.Comment" ->
        FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Comment s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____243));
        FStar_Syntax_Syntax.pos = uu____244;
        FStar_Syntax_Syntax.vars = uu____245;_} when data = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____249));
        FStar_Syntax_Syntax.pos = uu____250;
        FStar_Syntax_Syntax.vars = uu____251;_} when data = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____255);
        FStar_Syntax_Syntax.pos = uu____256;
        FStar_Syntax_Syntax.vars = uu____257;_} -> extract_meta x1
    | a ->
        ((let uu____266 = FStar_Syntax_Print.term_to_string a in
          FStar_Util.print1_warning
            "Unrecognized attribute (%s), valid attributes are `c_inline`, `substitute`, and `gc`.\n"
            uu____266);
         FStar_Pervasives_Native.None)
let extract_metadata:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list
  = fun metas  -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders:
  'Auu____283 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____283) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____321  ->
             match uu____321 with
             | (bv,uu____331) ->
                 let uu____332 =
                   let uu____333 =
                     let uu____336 =
                       let uu____337 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____337 in
                     FStar_Pervasives_Native.Some uu____336 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____333 in
                 let uu____338 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____332, uu____338)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let def1 =
              let uu____375 =
                let uu____376 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____376 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____375 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____378 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____395 -> def1 in
            let uu____396 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____407) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____428 -> ([], def2) in
            match uu____396 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___186_449  ->
                       match uu___186_449 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____450 -> false) quals in
                let uu____451 = binders_as_mlty_binders env bs in
                (match uu____451 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____471 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____471
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____475 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___187_480  ->
                                 match uu___187_480 with
                                 | FStar_Syntax_Syntax.Projector uu____481 ->
                                     true
                                 | uu____486 -> false)) in
                       if uu____475
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let metadata = extract_metadata attrs in
                     let td =
                       let uu____517 =
                         let uu____538 = lident_as_mlsymbol lid in
                         (assumed, uu____538, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____517] in
                     let def3 =
                       let uu____590 =
                         let uu____591 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____591 in
                       [uu____590; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____593 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___188_597  ->
                                 match uu___188_597 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____598 -> false)) in
                       if uu____593
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                     (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}[@@deriving show]
let __proj__Mkdata_constructor__item__dname:
  data_constructor -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
let __proj__Mkdata_constructor__item__dtyp:
  data_constructor -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;
  imetadata: FStar_Extraction_ML_Syntax.metadata;}[@@deriving show]
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
let __proj__Mkinductive_family__item__imetadata:
  inductive_family -> FStar_Extraction_ML_Syntax.metadata =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____746 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____747 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____748 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____749 =
      let uu____750 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____761 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____762 =
                  let uu____763 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____763 in
                Prims.strcat uu____761 uu____762)) in
      FStar_All.pipe_right uu____750 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____746 uu____747 uu____748
      uu____749
let bundle_as_inductive_families:
  'Auu____776 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____776 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____807 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____854 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____854 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____893,t2,l',nparams,uu____897)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____902 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____902 with
                                           | (bs',body) ->
                                               let uu____935 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____935 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1006  ->
                                                           fun uu____1007  ->
                                                             match (uu____1006,
                                                                    uu____1007)
                                                             with
                                                             | ((b',uu____1025),
                                                                (b,uu____1027))
                                                                 ->
                                                                 let uu____1036
                                                                   =
                                                                   let uu____1043
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____1043) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1036)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____1045 =
                                                        let uu____1048 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1048 in
                                                      FStar_All.pipe_right
                                                        uu____1045
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1053 -> [])) in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____1058 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1058 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1061 -> (env1, [])) env ses in
          match uu____807 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
type env_t = FStar_Extraction_ML_UEnv.env[@@deriving show]
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1139 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1139 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1146 =
            let uu____1147 =
              let uu____1150 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1150 in
            uu____1147.FStar_Syntax_Syntax.n in
          match uu____1146 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1154) ->
              FStar_List.map
                (fun uu____1180  ->
                   match uu____1180 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1186;
                        FStar_Syntax_Syntax.sort = uu____1187;_},uu____1188)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1191 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1202 =
          let uu____1203 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1203 in
        let uu____1208 =
          let uu____1219 = lident_as_mlsymbol ctor.dname in
          let uu____1220 =
            let uu____1227 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1227 in
          (uu____1219, uu____1220) in
        (uu____1202, uu____1208) in
      let extract_one_family env1 ind =
        let uu____1275 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1275 with
        | (env2,vars) ->
            let uu____1310 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1310 with
             | (env3,ctors) ->
                 let uu____1403 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1403 with
                  | (indices,uu____1439) ->
                      let ml_params =
                        let uu____1459 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1478  ->
                                    let uu____1483 =
                                      FStar_Util.string_of_int i in
                                    Prims.strcat "'dummyV" uu____1483)) in
                        FStar_List.append vars uu____1459 in
                      let tbody =
                        let uu____1485 =
                          FStar_Util.find_opt
                            (fun uu___189_1490  ->
                               match uu___189_1490 with
                               | FStar_Syntax_Syntax.RecordType uu____1491 ->
                                   true
                               | uu____1500 -> false) ind.iquals in
                        match uu____1485 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1511 = FStar_List.hd ctors in
                            (match uu____1511 with
                             | (uu____1532,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1571  ->
                                          match uu____1571 with
                                          | (uu____1580,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1583 =
                                                lident_as_mlsymbol lid in
                                              (uu____1583, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1584 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1587 =
                        let uu____1606 = lident_as_mlsymbol ind.iname in
                        (false, uu____1606, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1587))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1640,t,uu____1642,uu____1643,uu____1644);
            FStar_Syntax_Syntax.sigrng = uu____1645;
            FStar_Syntax_Syntax.sigquals = uu____1646;
            FStar_Syntax_Syntax.sigmeta = uu____1647;
            FStar_Syntax_Syntax.sigattrs = uu____1648;_}::[],uu____1649),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1666 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1666 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1712),quals) ->
          let uu____1726 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1726 with
           | (env1,ifams) ->
               let uu____1747 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1747 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1840 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1877 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1877);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1884 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1893 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1910 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1948 =
               let uu____1953 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1953 ml_name tysc
                 false false in
             match uu____1948 with
             | (g2,mangled_name) ->
                 ((let uu____1961 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1961
                   then FStar_Util.print1 "Mangled name: %s\n" mangled_name
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____1977 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1977
              then
                let uu____1978 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1978
              else ());
             (let uu____1980 =
                let uu____1981 = FStar_Syntax_Subst.compress tm in
                uu____1981.FStar_Syntax_Syntax.n in
              match uu____1980 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1989) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1996 =
                    let uu____2005 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____2005 in
                  (match uu____1996 with
                   | (uu____2062,uu____2063,tysc,uu____2065) ->
                       let uu____2066 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2066, tysc))
              | uu____2067 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2093 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2093
              then
                let uu____2094 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2095 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2094
                  uu____2095
              else ());
             (let uu____2097 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2097 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2113 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2113 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____2139 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2139 with
                   | (a_let,uu____2151,ty) ->
                       ((let uu____2154 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2154
                         then
                           let uu____2155 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2155
                         else ());
                        (let uu____2157 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2166,uu____2167,mllb::[]),uu____2169)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2189 -> failwith "Impossible" in
                         match uu____2157 with
                         | (exp,tysc) ->
                             ((let uu____2201 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2201
                               then
                                 ((let uu____2203 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2203);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2207 =
             let uu____2212 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2212 with
             | (return_tm,ty_sc) ->
                 let uu____2225 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2225 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2207 with
            | (g1,return_decl) ->
                let uu____2244 =
                  let uu____2249 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2249 with
                  | (bind_tm,ty_sc) ->
                      let uu____2262 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2262 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2244 with
                 | (g2,bind_decl) ->
                     let uu____2281 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2281 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2302 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2306,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2314 =
             let uu____2315 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___190_2319  ->
                       match uu___190_2319 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2320 -> false)) in
             Prims.op_Negation uu____2315 in
           if uu____2314
           then (g, [])
           else
             (let uu____2330 = FStar_Syntax_Util.arrow_formals t in
              match uu____2330 with
              | (bs,uu____2350) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2368 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2368)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2370) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2386 =
             let uu____2395 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2395 with
             | (tcenv,uu____2419,def_typ) ->
                 let uu____2425 = as_pair def_typ in (tcenv, uu____2425) in
           (match uu____2386 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2449 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2449 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2451) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2498 =
                   let uu____2499 =
                     let uu____2500 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2500 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2499 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2498 in
               let lid_arg =
                 let uu____2502 =
                   let uu____2503 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2503 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2502 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2510 =
                   let uu____2511 =
                     let uu____2512 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2512 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2511 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2510 in
               let uu____2519 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               match uu____2519 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2526 =
                       let uu____2527 =
                         let uu____2534 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation] in
                         (h, uu____2534) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2527 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2526 in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> [] in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2544 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2544 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2574 =
                        let uu____2575 = FStar_Syntax_Subst.compress t in
                        uu____2575.FStar_Syntax_Syntax.n in
                      (match uu____2574 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let tac_lid =
                             let uu____2603 =
                               let uu____2606 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2606.FStar_Syntax_Syntax.fv_name in
                             uu____2603.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2608 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2608 in
                           let uu____2609 =
                             let uu____2610 = FStar_Syntax_Subst.compress h in
                             is_tactic_decl assm_lid uu____2610
                               g.FStar_Extraction_ML_UEnv.currentModule in
                           if uu____2609
                           then
                             let uu____2613 =
                               let uu____2614 = FStar_List.hd args in
                               FStar_Pervasives_Native.fst uu____2614 in
                             mk_registration tac_lid assm_lid uu____2613 bs
                           else []
                       | uu____2630 -> []))
             | uu____2631 -> [] in
           let uu____2634 =
             (tactic_registration_decl = []) ||
               (let uu____2638 = FStar_Options.codegen () in
                uu____2638 = (FStar_Pervasives_Native.Some "tactics")) in
           if uu____2634
           then
             let uu____2649 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
             (match uu____2649 with
              | (ml_let,uu____2663,uu____2664) ->
                  (match ml_let.FStar_Extraction_ML_Syntax.expr with
                   | FStar_Extraction_ML_Syntax.MLE_Let
                       ((flavor,uu____2672,bindings),uu____2674) ->
                       let uu____2687 =
                         FStar_List.fold_left2
                           (fun uu____2714  ->
                              fun ml_lb  ->
                                fun uu____2716  ->
                                  match (uu____2714, uu____2716) with
                                  | ((env,ml_lbs),{
                                                    FStar_Syntax_Syntax.lbname
                                                      = lbname;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uu____2738;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = t;
                                                    FStar_Syntax_Syntax.lbeff
                                                      = uu____2740;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____2741;_})
                                      ->
                                      let lb_lid =
                                        let uu____2763 =
                                          let uu____2766 =
                                            FStar_Util.right lbname in
                                          uu____2766.FStar_Syntax_Syntax.fv_name in
                                        uu____2763.FStar_Syntax_Syntax.v in
                                      let uu____2767 =
                                        let uu____2772 =
                                          FStar_All.pipe_right quals
                                            (FStar_Util.for_some
                                               (fun uu___191_2777  ->
                                                  match uu___191_2777 with
                                                  | FStar_Syntax_Syntax.Projector
                                                      uu____2778 -> true
                                                  | uu____2783 -> false)) in
                                        if uu____2772
                                        then
                                          let mname =
                                            let uu____2789 =
                                              mangle_projector_lid lb_lid in
                                            FStar_All.pipe_right uu____2789
                                              FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                          let uu____2790 =
                                            let uu____2795 =
                                              FStar_Util.right lbname in
                                            let uu____2796 =
                                              FStar_Util.must
                                                ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                            FStar_Extraction_ML_UEnv.extend_fv'
                                              env uu____2795 mname uu____2796
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                              false in
                                          match uu____2790 with
                                          | (env1,uu____2802) ->
                                              (env1,
                                                (let uu___195_2804 = ml_lb in
                                                 {
                                                   FStar_Extraction_ML_Syntax.mllb_name
                                                     =
                                                     (FStar_Pervasives_Native.snd
                                                        mname);
                                                   FStar_Extraction_ML_Syntax.mllb_tysc
                                                     =
                                                     (uu___195_2804.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                   FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     =
                                                     (uu___195_2804.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                   FStar_Extraction_ML_Syntax.mllb_def
                                                     =
                                                     (uu___195_2804.FStar_Extraction_ML_Syntax.mllb_def);
                                                   FStar_Extraction_ML_Syntax.print_typ
                                                     =
                                                     (uu___195_2804.FStar_Extraction_ML_Syntax.print_typ)
                                                 }))
                                        else
                                          (let uu____2808 =
                                             let uu____2809 =
                                               let uu____2814 =
                                                 FStar_Util.must
                                                   ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                               FStar_Extraction_ML_UEnv.extend_lb
                                                 env lbname t uu____2814
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                 false in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____2809 in
                                           (uu____2808, ml_lb)) in
                                      (match uu____2767 with
                                       | (g1,ml_lb1) ->
                                           (g1, (ml_lb1 :: ml_lbs)))) 
                           (g, []) bindings (FStar_Pervasives_Native.snd lbs) in
                       (match uu____2687 with
                        | (g1,ml_lbs') ->
                            let flags =
                              FStar_List.choose
                                (fun uu___192_2849  ->
                                   match uu___192_2849 with
                                   | FStar_Syntax_Syntax.Assumption  ->
                                       FStar_Pervasives_Native.Some
                                         FStar_Extraction_ML_Syntax.Assumed
                                   | FStar_Syntax_Syntax.Private  ->
                                       FStar_Pervasives_Native.Some
                                         FStar_Extraction_ML_Syntax.Private
                                   | FStar_Syntax_Syntax.NoExtract  ->
                                       FStar_Pervasives_Native.Some
                                         FStar_Extraction_ML_Syntax.NoExtract
                                   | uu____2852 ->
                                       FStar_Pervasives_Native.None) quals in
                            let flags' = extract_metadata attrs in
                            let uu____2856 =
                              let uu____2859 =
                                let uu____2862 =
                                  let uu____2863 =
                                    FStar_Extraction_ML_Util.mlloc_of_range
                                      se.FStar_Syntax_Syntax.sigrng in
                                  FStar_Extraction_ML_Syntax.MLM_Loc
                                    uu____2863 in
                                [uu____2862;
                                FStar_Extraction_ML_Syntax.MLM_Let
                                  (flavor, (FStar_List.append flags flags'),
                                    (FStar_List.rev ml_lbs'))] in
                              FStar_List.append uu____2859
                                tactic_registration_decl in
                            (g1, uu____2856))
                   | uu____2870 ->
                       let uu____2871 =
                         let uu____2872 =
                           FStar_Extraction_ML_Code.string_of_mlexpr
                             g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                         FStar_Util.format1
                           "Impossible: Translated a let to a non-let: %s"
                           uu____2872 in
                       failwith uu____2871))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2883,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2888 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2888
           then
             let always_fail =
               let imp =
                 let uu____2899 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2899 with
                 | ([],t1) ->
                     let b =
                       let uu____2928 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2928 in
                     let uu____2929 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____2929
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2948 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____2948
                       FStar_Pervasives_Native.None in
               let uu___196_2949 = se in
               let uu____2950 =
                 let uu____2951 =
                   let uu____2958 =
                     let uu____2965 =
                       let uu____2968 =
                         let uu____2969 =
                           let uu____2974 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____2974 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2969;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____2968] in
                     (false, uu____2965) in
                   (uu____2958, []) in
                 FStar_Syntax_Syntax.Sig_let uu____2951 in
               {
                 FStar_Syntax_Syntax.sigel = uu____2950;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___196_2949.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___196_2949.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___196_2949.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___196_2949.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____2985 = extract_sig g always_fail in
             (match uu____2985 with
              | (g1,mlm) ->
                  let uu____3004 =
                    FStar_Util.find_map quals
                      (fun uu___193_3009  ->
                         match uu___193_3009 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3013 -> FStar_Pervasives_Native.None) in
                  (match uu____3004 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3021 =
                         let uu____3024 =
                           let uu____3025 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3025 in
                         let uu____3026 =
                           let uu____3029 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3029] in
                         uu____3024 :: uu____3026 in
                       (g1, uu____3021)
                   | uu____3032 ->
                       let uu____3035 =
                         FStar_Util.find_map quals
                           (fun uu___194_3041  ->
                              match uu___194_3041 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3045)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3046 -> FStar_Pervasives_Native.None) in
                       (match uu____3035 with
                        | FStar_Pervasives_Native.Some uu____3053 -> (g1, [])
                        | uu____3056 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3065 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3065 with
            | (ml_main,uu____3079,uu____3080) ->
                let uu____3081 =
                  let uu____3084 =
                    let uu____3085 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3085 in
                  [uu____3084; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3081))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3088 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3095 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3104 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3107 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3135 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3135 FStar_Pervasives_Native.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3180 = FStar_Options.debug_any () in
       if uu____3180
       then
         let uu____3181 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3181
       else ());
      (let codegen_opt = FStar_Options.codegen () in
       let uu____3186 = FStar_Options.restore_cmd_line_options true in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "tactics" ->
            FStar_Options.set_option "codegen"
              (FStar_Options.String "tactics")
        | uu____3188 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name in
        let g1 =
          let uu___197_3193 = g in
          let uu____3194 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3194;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___197_3193.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___197_3193.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___197_3193.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          } in
        let uu____3195 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations in
        match uu____3195 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs in
            let is_kremlin =
              let uu____3224 = FStar_Options.codegen () in
              match uu____3224 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3227 -> false in
            let uu____3230 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
            if uu____3230
            then
              ((let uu____3238 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
                FStar_Util.print1 "Extracted module %s\n" uu____3238);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))