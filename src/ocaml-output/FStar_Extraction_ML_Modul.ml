open Prims
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____9 =
        let uu____12 =
          let uu____13 =
            let uu____28 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____29 =
              let uu____32 = FStar_Syntax_Syntax.iarg t  in
              let uu____33 =
                let uu____36 =
                  let uu____37 =
                    let uu____38 =
                      let uu____41 =
                        let uu____42 =
                          let uu____43 =
                            let uu____48 =
                              let uu____49 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____49
                               in
                            (uu____48, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____43  in
                        FStar_Syntax_Syntax.Tm_constant uu____42  in
                      FStar_Syntax_Syntax.mk uu____41  in
                    uu____38 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____37  in
                [uu____36]  in
              uu____32 :: uu____33  in
            (uu____28, uu____29)  in
          FStar_Syntax_Syntax.Tm_app uu____13  in
        FStar_Syntax_Syntax.mk uu____12  in
      uu____9 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
  
let as_pair :
  'Auu____66 .
    'Auu____66 Prims.list ->
      ('Auu____66,'Auu____66) FStar_Pervasives_Native.tuple2
  =
  fun uu___69_76  ->
    match uu___69_76 with
    | a::b::[] -> (a, b)
    | uu____81 -> failwith "Expected a list with 2 elements"
  
let (is_tactic_decl :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.mlpath -> Prims.bool)
  =
  fun tac_lid  ->
    fun h  ->
      fun current_module1  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____98) ->
            let uu____103 =
              let uu____104 = FStar_Syntax_Subst.compress h'  in
              uu____104.FStar_Syntax_Syntax.n  in
            (match uu____103 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 ->
                 let uu____108 =
                   let uu____109 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath
                       current_module1
                      in
                   FStar_Util.starts_with uu____109 "FStar.Tactics"  in
                 Prims.op_Negation uu____108
             | uu____110 -> false)
        | uu____111 -> false
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____117 = FStar_Syntax_Subst.compress x  in
    match uu____117 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____121;
        FStar_Syntax_Syntax.vars = uu____122;_} when
        let uu____125 =
          let uu____126 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____126  in
        uu____125 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____128;
        FStar_Syntax_Syntax.vars = uu____129;_} when
        let uu____132 =
          let uu____133 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____133  in
        uu____132 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____135;
        FStar_Syntax_Syntax.vars = uu____136;_} when
        let uu____139 =
          let uu____140 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____140  in
        uu____139 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____142;
        FStar_Syntax_Syntax.vars = uu____143;_} when
        let uu____146 =
          let uu____147 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____147  in
        uu____146 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____149;
             FStar_Syntax_Syntax.vars = uu____150;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____152));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____153;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____154;_},uu____155)::[]);
        FStar_Syntax_Syntax.pos = uu____156;
        FStar_Syntax_Syntax.vars = uu____157;_} when
        let uu____188 =
          let uu____189 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____189  in
        uu____188 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____191;
             FStar_Syntax_Syntax.vars = uu____192;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____194));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____195;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____196;_},uu____197)::[]);
        FStar_Syntax_Syntax.pos = uu____198;
        FStar_Syntax_Syntax.vars = uu____199;_} when
        let uu____230 =
          let uu____231 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____231  in
        uu____230 = "FStar.Pervasives.Comment" ->
        FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Comment s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____233));
        FStar_Syntax_Syntax.pos = uu____234;
        FStar_Syntax_Syntax.vars = uu____235;_} when data = "KremlinPrivate"
        -> FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____239));
        FStar_Syntax_Syntax.pos = uu____240;
        FStar_Syntax_Syntax.vars = uu____241;_} when data = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____245));
        FStar_Syntax_Syntax.pos = uu____246;
        FStar_Syntax_Syntax.vars = uu____247;_} when data = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____251);
        FStar_Syntax_Syntax.pos = uu____252;
        FStar_Syntax_Syntax.vars = uu____253;_} -> extract_meta x1
    | a -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____273 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____273) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____311  ->
             match uu____311 with
             | (bv,uu____321) ->
                 let uu____322 =
                   let uu____323 =
                     let uu____326 =
                       let uu____327 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____327  in
                     FStar_Pervasives_Native.Some uu____326  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____323  in
                 let uu____328 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____322, uu____328)) env bs
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let def1 =
              let uu____360 =
                let uu____361 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____361 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____360 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____363 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____380 -> def1  in
            let uu____381 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____392) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____413 -> ([], def2)  in
            match uu____381 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___70_434  ->
                       match uu___70_434 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____435 -> false) quals
                   in
                let uu____436 = binders_as_mlty_binders env bs  in
                (match uu____436 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____456 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____456
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____460 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___71_465  ->
                                 match uu___71_465 with
                                 | FStar_Syntax_Syntax.Projector uu____466 ->
                                     true
                                 | uu____471 -> false))
                          in
                       if uu____460
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____502 =
                         let uu____523 = lident_as_mlsymbol lid  in
                         (assumed, uu____523, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____502]  in
                     let def3 =
                       let uu____575 =
                         let uu____576 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid)
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____576  in
                       [uu____575; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____578 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___72_582  ->
                                 match uu___72_582 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____583 -> false))
                          in
                       if uu____578
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                        in
                     (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }[@@deriving show]
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
  
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
  
let (print_ifamily : inductive_family -> Prims.unit) =
  fun i  ->
    let uu____722 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____723 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____724 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____725 =
      let uu____726 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____737 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____738 =
                  let uu____739 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____739  in
                Prims.strcat uu____737 uu____738))
         in
      FStar_All.pipe_right uu____726 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____722 uu____723 uu____724
      uu____725
  
let bundle_as_inductive_families :
  'Auu____747 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____747 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____778 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____825 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____825 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____864,t2,l',nparams,uu____868)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____873 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____873 with
                                           | (bs',body) ->
                                               let uu____906 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____906 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____977  ->
                                                           fun uu____978  ->
                                                             match (uu____977,
                                                                    uu____978)
                                                             with
                                                             | ((b',uu____996),
                                                                (b,uu____998))
                                                                 ->
                                                                 let uu____1007
                                                                   =
                                                                   let uu____1014
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1014)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1007)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1016 =
                                                        let uu____1019 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1019
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1016
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1024 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____1029 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1029
                               in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1032 -> (env1, [])) env ses
             in
          match uu____778 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type env_t = FStar_Extraction_ML_UEnv.env[@@deriving show]
let (extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1108 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1108
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1115 =
            let uu____1116 =
              let uu____1119 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1119  in
            uu____1116.FStar_Syntax_Syntax.n  in
          match uu____1115 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1123) ->
              FStar_List.map
                (fun uu____1149  ->
                   match uu____1149 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1155;
                        FStar_Syntax_Syntax.sort = uu____1156;_},uu____1157)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1160 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1171 =
          let uu____1172 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1172  in
        let uu____1177 =
          let uu____1188 = lident_as_mlsymbol ctor.dname  in
          let uu____1189 =
            let uu____1196 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1196  in
          (uu____1188, uu____1189)  in
        (uu____1171, uu____1177)  in
      let extract_one_family env1 ind =
        let uu____1244 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1244 with
        | (env2,vars) ->
            let uu____1279 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1279 with
             | (env3,ctors) ->
                 let uu____1372 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1372 with
                  | (indices,uu____1408) ->
                      let ml_params =
                        let uu____1428 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1447  ->
                                    let uu____1452 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1452))
                           in
                        FStar_List.append vars uu____1428  in
                      let tbody =
                        let uu____1454 =
                          FStar_Util.find_opt
                            (fun uu___73_1459  ->
                               match uu___73_1459 with
                               | FStar_Syntax_Syntax.RecordType uu____1460 ->
                                   true
                               | uu____1469 -> false) ind.iquals
                           in
                        match uu____1454 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1480 = FStar_List.hd ctors  in
                            (match uu____1480 with
                             | (uu____1501,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1540  ->
                                          match uu____1540 with
                                          | (uu____1549,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1552 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1552, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1553 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1556 =
                        let uu____1575 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1575, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1556)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1609,t,uu____1611,uu____1612,uu____1613);
            FStar_Syntax_Syntax.sigrng = uu____1614;
            FStar_Syntax_Syntax.sigquals = uu____1615;
            FStar_Syntax_Syntax.sigmeta = uu____1616;
            FStar_Syntax_Syntax.sigattrs = uu____1617;_}::[],uu____1618),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1635 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1635 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1681),quals) ->
          let uu____1695 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1695 with
           | (env1,ifams) ->
               let uu____1716 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1716 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1809 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let uu____1832 =
        (let uu____1835 = FStar_Options.codegen ()  in
         uu____1835 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1841 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr
              in
           Prims.op_Negation uu____1841)
         in
      if uu____1832
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1862 =
                   let uu____1865 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                   uu____1865.FStar_Syntax_Syntax.fv_name  in
                 uu____1862.FStar_Syntax_Syntax.v  in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
               let ml_name_str =
                 let uu____1870 =
                   let uu____1871 = FStar_Ident.string_of_lid fv  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1871  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1870  in
               let uu____1872 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str
                  in
               match uu____1872 with
               | FStar_Pervasives_Native.Some (interp,arity) ->
                   let h =
                     let uu____1888 =
                       let uu____1889 =
                         let uu____1890 =
                           FStar_Ident.lid_of_str
                             "FStar_Tactics_Native.register_tactic"
                            in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1890
                          in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1889  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1888
                      in
                   let arity1 =
                     let uu____1892 =
                       let uu____1893 =
                         let uu____1904 = FStar_Util.string_of_int arity  in
                         (uu____1904, FStar_Pervasives_Native.None)  in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1893  in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1892  in
                   let app =
                     let uu____1922 =
                       let uu____1923 =
                         let uu____1930 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [ml_name_str; arity1; interp]
                            in
                         (h, uu____1930)  in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1923  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1922
                      in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> []  in
             FStar_List.collect mk_registration
               (FStar_Pervasives_Native.snd lbs)
         | uu____1941 -> [])
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1964 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1964);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1971 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1980 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1997 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2035 =
               let uu____2040 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2040 ml_name tysc
                 false false
                in
             match uu____2035 with
             | (g2,mangled_name) ->
                 ((let uu____2048 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____2048
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
                     }  in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [lb])))))
              in
           let rec extract_fv tm =
             (let uu____2062 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2062
              then
                let uu____2063 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2063
              else ());
             (let uu____2065 =
                let uu____2066 = FStar_Syntax_Subst.compress tm  in
                uu____2066.FStar_Syntax_Syntax.n  in
              match uu____2065 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2074) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____2081 =
                    let uu____2090 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2090  in
                  (match uu____2081 with
                   | (uu____2147,uu____2148,tysc,uu____2150) ->
                       let uu____2151 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2151, tysc))
              | uu____2152 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2178 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2178
              then
                let uu____2179 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2180 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2179
                  uu____2180
              else ());
             (let uu____2182 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2182 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2198 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2198  in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn))
                     in
                  let lbs = (false, [lb])  in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                     in
                  let uu____2224 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2224 with
                   | (a_let,uu____2236,ty) ->
                       ((let uu____2239 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2239
                         then
                           let uu____2240 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2240
                         else ());
                        (let uu____2242 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2251,mllb::[]),uu____2253) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2271 -> failwith "Impossible"  in
                         match uu____2242 with
                         | (exp,tysc) ->
                             ((let uu____2283 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2283
                               then
                                 ((let uu____2285 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2285);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2289 =
             let uu____2294 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2294 with
             | (return_tm,ty_sc) ->
                 let uu____2307 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2307 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2289 with
            | (g1,return_decl) ->
                let uu____2326 =
                  let uu____2331 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2331 with
                  | (bind_tm,ty_sc) ->
                      let uu____2344 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2344 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2326 with
                 | (g2,bind_decl) ->
                     let uu____2363 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2363 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2384 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2388,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2396 =
             let uu____2397 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___74_2401  ->
                       match uu___74_2401 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2402 -> false))
                in
             Prims.op_Negation uu____2397  in
           if uu____2396
           then (g, [])
           else
             (let uu____2412 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2412 with
              | (bs,uu____2432) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2450 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2450)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2452) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2468 =
             let uu____2477 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2477 with
             | (tcenv,uu____2501,def_typ) ->
                 let uu____2507 = as_pair def_typ  in (tcenv, uu____2507)
              in
           (match uu____2468 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp
                   in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____2531 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2531 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2533) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2544 =
             let uu____2551 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2551  in
           (match uu____2544 with
            | (ml_let,uu____2561,uu____2562) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2571) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___75_2586  ->
                            match uu___75_2586 with
                            | FStar_Syntax_Syntax.Assumption  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2589 -> FStar_Pervasives_Native.None)
                         quals
                        in
                     let flags' = extract_metadata attrs  in
                     let uu____2593 =
                       FStar_List.fold_left2
                         (fun uu____2624  ->
                            fun ml_lb  ->
                              fun uu____2626  ->
                                match (uu____2624, uu____2626) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2648;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2650;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2651;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2652;_})
                                    ->
                                    let lb_lid =
                                      let uu____2678 =
                                        let uu____2681 =
                                          FStar_Util.right lbname  in
                                        uu____2681.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____2678.FStar_Syntax_Syntax.v  in
                                    let flags'' =
                                      let uu____2685 =
                                        let uu____2686 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____2686.FStar_Syntax_Syntax.n  in
                                      match uu____2685 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (uu____2691,{
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Comp
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____2692;
                                                            FStar_Syntax_Syntax.effect_name
                                                              = e;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = uu____2694;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____2695;
                                                            FStar_Syntax_Syntax.flags
                                                              = uu____2696;_};
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____2697;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____2698;_})
                                          when
                                          let uu____2727 =
                                            FStar_Ident.string_of_lid e  in
                                          uu____2727 =
                                            "FStar.HyperStack.ST.StackInline"
                                          ->
                                          [FStar_Extraction_ML_Syntax.StackInline]
                                      | uu____2728 -> []  in
                                    let meta =
                                      FStar_List.append flags1
                                        (FStar_List.append flags' flags'')
                                       in
                                    let ml_lb1 =
                                      let uu___79_2733 = ml_lb  in
                                      {
                                        FStar_Extraction_ML_Syntax.mllb_name
                                          =
                                          (uu___79_2733.FStar_Extraction_ML_Syntax.mllb_name);
                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                          =
                                          (uu___79_2733.FStar_Extraction_ML_Syntax.mllb_tysc);
                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                          =
                                          (uu___79_2733.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                        FStar_Extraction_ML_Syntax.mllb_def =
                                          (uu___79_2733.FStar_Extraction_ML_Syntax.mllb_def);
                                        FStar_Extraction_ML_Syntax.mllb_meta
                                          = meta;
                                        FStar_Extraction_ML_Syntax.print_typ
                                          =
                                          (uu___79_2733.FStar_Extraction_ML_Syntax.print_typ)
                                      }  in
                                    let uu____2734 =
                                      let uu____2739 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___76_2744  ->
                                                match uu___76_2744 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2745 -> true
                                                | uu____2750 -> false))
                                         in
                                      if uu____2739
                                      then
                                        let mname =
                                          let uu____2756 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____2756
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____2757 =
                                          let uu____2762 =
                                            FStar_Util.right lbname  in
                                          let uu____2763 =
                                            FStar_Util.must
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2762 mname uu____2763
                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____2757 with
                                        | (env1,uu____2769) ->
                                            (env1,
                                              (let uu___80_2771 = ml_lb1  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___80_2771.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___80_2771.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___80_2771.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                   =
                                                   (uu___80_2771.FStar_Extraction_ML_Syntax.mllb_meta);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___80_2771.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2775 =
                                           let uu____2776 =
                                             let uu____2781 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2781
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2776
                                            in
                                         (uu____2775, ml_lb1))
                                       in
                                    (match uu____2734 with
                                     | (g1,ml_lb2) ->
                                         (g1, (ml_lb2 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2593 with
                      | (g1,ml_lbs') ->
                          let uu____2812 =
                            let uu____2815 =
                              let uu____2818 =
                                let uu____2819 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2819
                                 in
                              [uu____2818;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____2822 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____2815 uu____2822  in
                          (g1, uu____2812))
                 | uu____2827 ->
                     let uu____2828 =
                       let uu____2829 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2829
                        in
                     failwith uu____2828))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2837,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2842 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____2842
           then
             let always_fail =
               let imp =
                 let uu____2853 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2853 with
                 | ([],t1) ->
                     let b =
                       let uu____2882 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2882
                        in
                     let uu____2883 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2883
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2902 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2902
                       FStar_Pervasives_Native.None
                  in
               let uu___81_2903 = se  in
               let uu____2904 =
                 let uu____2905 =
                   let uu____2912 =
                     let uu____2919 =
                       let uu____2922 =
                         let uu____2923 =
                           let uu____2928 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____2928  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2923;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = []
                         }  in
                       [uu____2922]  in
                     (false, uu____2919)  in
                   (uu____2912, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2905  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2904;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___81_2903.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___81_2903.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___81_2903.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___81_2903.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2941 = extract_sig g always_fail  in
             (match uu____2941 with
              | (g1,mlm) ->
                  let uu____2960 =
                    FStar_Util.find_map quals
                      (fun uu___77_2965  ->
                         match uu___77_2965 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2969 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____2960 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2977 =
                         let uu____2980 =
                           let uu____2981 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2981  in
                         let uu____2982 =
                           let uu____2985 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2985]  in
                         uu____2980 :: uu____2982  in
                       (g1, uu____2977)
                   | uu____2988 ->
                       let uu____2991 =
                         FStar_Util.find_map quals
                           (fun uu___78_2997  ->
                              match uu___78_2997 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3001)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3002 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____2991 with
                        | FStar_Pervasives_Native.Some uu____3009 -> (g1, [])
                        | uu____3012 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3021 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3021 with
            | (ml_main,uu____3035,uu____3036) ->
                let uu____3037 =
                  let uu____3040 =
                    let uu____3041 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3041  in
                  [uu____3040; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3037))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3044 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3051 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3060 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3063 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3088 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3088 FStar_Pervasives_Native.fst
  
let (extract' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3130 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___82_3133 = g  in
         let uu____3134 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3134;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___82_3133.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___82_3133.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___82_3133.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3135 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3135 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3164 = FStar_Options.codegen ()  in
             uu____3164 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____3169 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3169
           then
             ((let uu____3177 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3177);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____3251 = FStar_Options.debug_any ()  in
      if uu____3251
      then
        let msg =
          let uu____3259 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3259  in
        FStar_Util.measure_execution_time msg
          (fun uu____3267  -> extract' g m)
      else extract' g m
  