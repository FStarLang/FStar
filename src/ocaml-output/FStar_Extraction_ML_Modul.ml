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
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____93 = FStar_Syntax_Subst.compress x  in
    match uu____93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____97;
        FStar_Syntax_Syntax.vars = uu____98;_} when
        let uu____101 =
          let uu____102 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____102  in
        uu____101 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____104;
        FStar_Syntax_Syntax.vars = uu____105;_} when
        let uu____108 =
          let uu____109 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____109  in
        uu____108 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____111;
        FStar_Syntax_Syntax.vars = uu____112;_} when
        let uu____115 =
          let uu____116 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____116  in
        uu____115 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____118;
        FStar_Syntax_Syntax.vars = uu____119;_} when
        let uu____122 =
          let uu____123 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____123  in
        uu____122 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____125;
             FStar_Syntax_Syntax.vars = uu____126;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____128));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____129;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____130;_},uu____131)::[]);
        FStar_Syntax_Syntax.pos = uu____132;
        FStar_Syntax_Syntax.vars = uu____133;_} when
        let uu____164 =
          let uu____165 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____165  in
        uu____164 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____167;
             FStar_Syntax_Syntax.vars = uu____168;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____170));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____171;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____172;_},uu____173)::[]);
        FStar_Syntax_Syntax.pos = uu____174;
        FStar_Syntax_Syntax.vars = uu____175;_} when
        let uu____206 =
          let uu____207 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____207  in
        uu____206 = "FStar.Pervasives.Comment" ->
        FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Comment s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____209));
        FStar_Syntax_Syntax.pos = uu____210;
        FStar_Syntax_Syntax.vars = uu____211;_} when data = "KremlinPrivate"
        -> FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____215));
        FStar_Syntax_Syntax.pos = uu____216;
        FStar_Syntax_Syntax.vars = uu____217;_} when data = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____221));
        FStar_Syntax_Syntax.pos = uu____222;
        FStar_Syntax_Syntax.vars = uu____223;_} when data = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____227);
        FStar_Syntax_Syntax.pos = uu____228;
        FStar_Syntax_Syntax.vars = uu____229;_} -> extract_meta x1
    | a -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____249 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____249) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____287  ->
             match uu____287 with
             | (bv,uu____297) ->
                 let uu____298 =
                   let uu____299 =
                     let uu____302 =
                       let uu____303 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____303  in
                     FStar_Pervasives_Native.Some uu____302  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____299  in
                 let uu____304 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____298, uu____304)) env bs
  
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
              let uu____336 =
                let uu____337 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____337 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____336 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____339 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____356 -> def1  in
            let uu____357 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____368) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____389 -> ([], def2)  in
            match uu____357 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___70_410  ->
                       match uu___70_410 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____411 -> false) quals
                   in
                let uu____412 = binders_as_mlty_binders env bs  in
                (match uu____412 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____432 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____432
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____436 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___71_441  ->
                                 match uu___71_441 with
                                 | FStar_Syntax_Syntax.Projector uu____442 ->
                                     true
                                 | uu____447 -> false))
                          in
                       if uu____436
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____478 =
                         let uu____499 = lident_as_mlsymbol lid  in
                         (assumed, uu____499, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____478]  in
                     let def3 =
                       let uu____551 =
                         let uu____552 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid)
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____552  in
                       [uu____551; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____554 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___72_558  ->
                                 match uu___72_558 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____559 -> false))
                          in
                       if uu____554
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
    let uu____698 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____699 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____700 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____701 =
      let uu____702 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____713 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____714 =
                  let uu____715 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____715  in
                Prims.strcat uu____713 uu____714))
         in
      FStar_All.pipe_right uu____702 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____698 uu____699 uu____700
      uu____701
  
let bundle_as_inductive_families :
  'Auu____723 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____723 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____754 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____801 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____801 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____840,t2,l',nparams,uu____844)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____849 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____849 with
                                           | (bs',body) ->
                                               let uu____882 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____882 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____953  ->
                                                           fun uu____954  ->
                                                             match (uu____953,
                                                                    uu____954)
                                                             with
                                                             | ((b',uu____972),
                                                                (b,uu____974))
                                                                 ->
                                                                 let uu____983
                                                                   =
                                                                   let uu____990
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____990)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____983)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____992 =
                                                        let uu____995 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____995
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____992
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1000 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____1005 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1005
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
                   | uu____1008 -> (env1, [])) env ses
             in
          match uu____754 with
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
          let uu____1084 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1084
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1091 =
            let uu____1092 =
              let uu____1095 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1095  in
            uu____1092.FStar_Syntax_Syntax.n  in
          match uu____1091 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1099) ->
              FStar_List.map
                (fun uu____1125  ->
                   match uu____1125 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1131;
                        FStar_Syntax_Syntax.sort = uu____1132;_},uu____1133)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1136 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1147 =
          let uu____1148 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1148  in
        let uu____1153 =
          let uu____1164 = lident_as_mlsymbol ctor.dname  in
          let uu____1165 =
            let uu____1172 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1172  in
          (uu____1164, uu____1165)  in
        (uu____1147, uu____1153)  in
      let extract_one_family env1 ind =
        let uu____1220 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1220 with
        | (env2,vars) ->
            let uu____1255 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1255 with
             | (env3,ctors) ->
                 let uu____1348 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1348 with
                  | (indices,uu____1384) ->
                      let ml_params =
                        let uu____1404 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1423  ->
                                    let uu____1428 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1428))
                           in
                        FStar_List.append vars uu____1404  in
                      let tbody =
                        let uu____1430 =
                          FStar_Util.find_opt
                            (fun uu___73_1435  ->
                               match uu___73_1435 with
                               | FStar_Syntax_Syntax.RecordType uu____1436 ->
                                   true
                               | uu____1445 -> false) ind.iquals
                           in
                        match uu____1430 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1456 = FStar_List.hd ctors  in
                            (match uu____1456 with
                             | (uu____1477,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1516  ->
                                          match uu____1516 with
                                          | (uu____1525,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1528 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1528, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1529 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1532 =
                        let uu____1551 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1551, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1532)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1585,t,uu____1587,uu____1588,uu____1589);
            FStar_Syntax_Syntax.sigrng = uu____1590;
            FStar_Syntax_Syntax.sigquals = uu____1591;
            FStar_Syntax_Syntax.sigmeta = uu____1592;
            FStar_Syntax_Syntax.sigattrs = uu____1593;_}::[],uu____1594),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1611 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1611 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1657),quals) ->
          let uu____1671 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1671 with
           | (env1,ifams) ->
               let uu____1692 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1692 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1785 -> failwith "Unexpected signature element"
  
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
           let uu____1820 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1820);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1827 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1836 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1853 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1891 =
               let uu____1896 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1896 ml_name tysc
                 false false
                in
             match uu____1891 with
             | (g2,mangled_name) ->
                 ((let uu____1904 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1904
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
             (let uu____1918 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1918
              then
                let uu____1919 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1919
              else ());
             (let uu____1921 =
                let uu____1922 = FStar_Syntax_Subst.compress tm  in
                uu____1922.FStar_Syntax_Syntax.n  in
              match uu____1921 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1930) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1937 =
                    let uu____1946 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1946  in
                  (match uu____1937 with
                   | (uu____2003,uu____2004,tysc,uu____2006) ->
                       let uu____2007 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2007, tysc))
              | uu____2008 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2034 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2034
              then
                let uu____2035 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2036 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2035
                  uu____2036
              else ());
             (let uu____2038 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2038 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2054 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2054  in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn),
                        ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                     in
                  let lbs = (false, [lb])  in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                     in
                  let uu____2080 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2080 with
                   | (a_let,uu____2092,ty) ->
                       ((let uu____2095 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2095
                         then
                           let uu____2096 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2096
                         else ());
                        (let uu____2098 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2107,mllb::[]),uu____2109) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2127 -> failwith "Impossible"  in
                         match uu____2098 with
                         | (exp,tysc) ->
                             ((let uu____2139 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2139
                               then
                                 ((let uu____2141 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2141);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2145 =
             let uu____2150 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2150 with
             | (return_tm,ty_sc) ->
                 let uu____2163 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2163 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2145 with
            | (g1,return_decl) ->
                let uu____2182 =
                  let uu____2187 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2187 with
                  | (bind_tm,ty_sc) ->
                      let uu____2200 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2200 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2182 with
                 | (g2,bind_decl) ->
                     let uu____2219 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2219 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2240 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2247 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2251,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2259 =
             let uu____2260 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___74_2264  ->
                       match uu___74_2264 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2265 -> false))
                in
             Prims.op_Negation uu____2260  in
           if uu____2259
           then (g, [])
           else
             (let uu____2275 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2275 with
              | (bs,uu____2295) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2313 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2313)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2315) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2331 =
             let uu____2340 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2340 with
             | (tcenv,uu____2364,def_typ) ->
                 let uu____2370 = as_pair def_typ  in (tcenv, uu____2370)
              in
           (match uu____2331 with
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
                let uu____2394 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2394 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2396) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
              in
           let tactic_registration_decl =
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2443 =
                   let uu____2444 =
                     let uu____2445 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2445
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2444  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2443
                  in
               let lid_arg =
                 let uu____2447 =
                   let uu____2448 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2448  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2447  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____2455 =
                   let uu____2456 =
                     let uu____2457 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____2457  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2456  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2455  in
               let uu____2464 =
                 FStar_Extraction_ML_Util.mk_interpretation_fun
                   g.FStar_Extraction_ML_UEnv.tcenv tac_lid lid_arg t bs
                  in
               match uu____2464 with
               | FStar_Pervasives_Native.Some tac_interpretation ->
                   let app =
                     let uu____2471 =
                       let uu____2472 =
                         let uu____2479 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top)
                             [lid_arg; arity; tac_interpretation]
                            in
                         (h, uu____2479)  in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2472  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____2471
                      in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> []  in
             let uu____2484 =
               let uu____2485 = FStar_Options.codegen ()  in
               uu____2485 = (FStar_Pervasives_Native.Some "tactics")  in
             if uu____2484
             then
               match FStar_Pervasives_Native.snd lbs with
               | hd1::[] ->
                   let uu____2497 =
                     FStar_Syntax_Util.arrow_formals_comp
                       hd1.FStar_Syntax_Syntax.lbtyp
                      in
                   (match uu____2497 with
                    | (bs,comp) ->
                        let t = FStar_Syntax_Util.comp_result comp  in
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            g.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name comp)
                           in
                        let uu____2528 =
                          ((FStar_Ident.lid_equals
                              FStar_Parser_Const.effect_TAC_lid eff)
                             &&
                             (let uu____2530 =
                                let uu____2531 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    g.FStar_Extraction_ML_UEnv.currentModule
                                   in
                                FStar_Util.starts_with uu____2531
                                  "FStar.Tactics"
                                 in
                              Prims.op_Negation uu____2530))
                            &&
                            (let uu____2533 =
                               let uu____2534 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   g.FStar_Extraction_ML_UEnv.currentModule
                                  in
                               FStar_Util.starts_with uu____2534
                                 "FStar.Reflection"
                                in
                             Prims.op_Negation uu____2533)
                           in
                        if uu____2528
                        then
                          let tac_lid =
                            let uu____2538 =
                              let uu____2541 =
                                FStar_Util.right
                                  hd1.FStar_Syntax_Syntax.lbname
                                 in
                              uu____2541.FStar_Syntax_Syntax.fv_name  in
                            uu____2538.FStar_Syntax_Syntax.v  in
                          let assm_lid =
                            let uu____2543 =
                              FStar_All.pipe_left FStar_Ident.id_of_text
                                (Prims.strcat "__"
                                   (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                               in
                            FStar_Ident.lid_of_ns_and_id
                              tac_lid.FStar_Ident.ns uu____2543
                             in
                          mk_registration tac_lid assm_lid t bs
                        else [])
               | uu____2545 -> []
             else []  in
           let uu____2549 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____2549 with
            | (ml_let,uu____2563,uu____2564) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2573) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___75_2588  ->
                            match uu___75_2588 with
                            | FStar_Syntax_Syntax.Assumption  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2591 -> FStar_Pervasives_Native.None)
                         quals
                        in
                     let flags' = extract_metadata attrs  in
                     let uu____2595 =
                       FStar_List.fold_left2
                         (fun uu____2627  ->
                            fun ml_lb  ->
                              fun uu____2629  ->
                                match (uu____2627, uu____2629) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2651;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2653;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2654;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2655;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____2656;_})
                                    ->
                                    let lb_lid =
                                      let uu____2682 =
                                        let uu____2685 =
                                          FStar_Util.right lbname  in
                                        uu____2685.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____2682.FStar_Syntax_Syntax.v  in
                                    let flags'' =
                                      let uu____2689 =
                                        let uu____2690 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____2690.FStar_Syntax_Syntax.n  in
                                      match uu____2689 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (uu____2695,{
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Comp
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____2696;
                                                            FStar_Syntax_Syntax.effect_name
                                                              = e;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = uu____2698;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____2699;
                                                            FStar_Syntax_Syntax.flags
                                                              = uu____2700;_};
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____2701;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____2702;_})
                                          when
                                          let uu____2731 =
                                            FStar_Ident.string_of_lid e  in
                                          uu____2731 =
                                            "FStar.HyperStack.ST.StackInline"
                                          ->
                                          [FStar_Extraction_ML_Syntax.StackInline]
                                      | uu____2732 -> []  in
                                    let meta =
                                      FStar_List.append flags1
                                        (FStar_List.append flags' flags'')
                                       in
                                    let ml_lb1 =
                                      let uu___79_2737 = ml_lb  in
                                      {
                                        FStar_Extraction_ML_Syntax.mllb_name
                                          =
                                          (uu___79_2737.FStar_Extraction_ML_Syntax.mllb_name);
                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                          =
                                          (uu___79_2737.FStar_Extraction_ML_Syntax.mllb_tysc);
                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                          =
                                          (uu___79_2737.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                        FStar_Extraction_ML_Syntax.mllb_def =
                                          (uu___79_2737.FStar_Extraction_ML_Syntax.mllb_def);
                                        FStar_Extraction_ML_Syntax.mllb_meta
                                          = meta;
                                        FStar_Extraction_ML_Syntax.print_typ
                                          =
                                          (uu___79_2737.FStar_Extraction_ML_Syntax.print_typ)
                                      }  in
                                    let uu____2738 =
                                      let uu____2743 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___76_2748  ->
                                                match uu___76_2748 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2749 -> true
                                                | uu____2754 -> false))
                                         in
                                      if uu____2743
                                      then
                                        let mname =
                                          let uu____2760 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____2760
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____2761 =
                                          let uu____2766 =
                                            FStar_Util.right lbname  in
                                          let uu____2767 =
                                            FStar_Util.must
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2766 mname uu____2767
                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____2761 with
                                        | (env1,uu____2773) ->
                                            (env1,
                                              (let uu___80_2775 = ml_lb1  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___80_2775.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___80_2775.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___80_2775.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                   =
                                                   (uu___80_2775.FStar_Extraction_ML_Syntax.mllb_meta);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___80_2775.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2779 =
                                           let uu____2780 =
                                             let uu____2785 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2785
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2780
                                            in
                                         (uu____2779, ml_lb1))
                                       in
                                    (match uu____2738 with
                                     | (g1,ml_lb2) ->
                                         (g1, (ml_lb2 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2595 with
                      | (g1,ml_lbs') ->
                          let uu____2816 =
                            let uu____2819 =
                              let uu____2822 =
                                let uu____2823 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2823
                                 in
                              [uu____2822;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____2819
                              tactic_registration_decl
                             in
                          (g1, uu____2816))
                 | uu____2828 ->
                     let uu____2829 =
                       let uu____2830 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2830
                        in
                     failwith uu____2829))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2838,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2843 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____2843
           then
             let always_fail =
               let imp =
                 let uu____2854 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2854 with
                 | ([],t1) ->
                     let b =
                       let uu____2883 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2883
                        in
                     let uu____2884 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2884
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2903 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2903
                       FStar_Pervasives_Native.None
                  in
               let uu___81_2904 = se  in
               let uu____2905 =
                 let uu____2906 =
                   let uu____2913 =
                     let uu____2920 =
                       let uu____2923 =
                         let uu____2924 =
                           let uu____2929 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____2929  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2924;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         }  in
                       [uu____2923]  in
                     (false, uu____2920)  in
                   (uu____2913, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2906  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2905;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___81_2904.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___81_2904.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___81_2904.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___81_2904.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2942 = extract_sig g always_fail  in
             (match uu____2942 with
              | (g1,mlm) ->
                  let uu____2961 =
                    FStar_Util.find_map quals
                      (fun uu___77_2966  ->
                         match uu___77_2966 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2970 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____2961 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2978 =
                         let uu____2981 =
                           let uu____2982 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2982  in
                         let uu____2983 =
                           let uu____2986 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2986]  in
                         uu____2981 :: uu____2983  in
                       (g1, uu____2978)
                   | uu____2989 ->
                       let uu____2992 =
                         FStar_Util.find_map quals
                           (fun uu___78_2998  ->
                              match uu___78_2998 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3002)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3003 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____2992 with
                        | FStar_Pervasives_Native.Some uu____3010 -> (g1, [])
                        | uu____3013 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3022 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3022 with
            | (ml_main,uu____3036,uu____3037) ->
                let uu____3038 =
                  let uu____3041 =
                    let uu____3042 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3042  in
                  [uu____3041; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3038))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3045 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3052 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3061 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3064 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let codegen_opt = FStar_Options.codegen ()  in
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (match codegen_opt with
             | FStar_Pervasives_Native.Some "tactics" ->
                 FStar_Options.set_option "codegen"
                   (FStar_Options.String "tactics")
             | uu____3085 -> ());
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3096 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3096 FStar_Pervasives_Native.fst
  
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
      (let codegen_opt = FStar_Options.codegen ()  in
       let uu____3141 = FStar_Options.restore_cmd_line_options true  in
       (match codegen_opt with
        | FStar_Pervasives_Native.Some "tactics" ->
            FStar_Options.set_option "codegen"
              (FStar_Options.String "tactics")
        | uu____3143 -> ());
       (let name =
          FStar_Extraction_ML_Syntax.mlpath_of_lident
            m.FStar_Syntax_Syntax.name
           in
        let g1 =
          let uu___82_3148 = g  in
          let uu____3149 =
            FStar_TypeChecker_Env.set_current_module
              g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
             in
          {
            FStar_Extraction_ML_UEnv.tcenv = uu____3149;
            FStar_Extraction_ML_UEnv.gamma =
              (uu___82_3148.FStar_Extraction_ML_UEnv.gamma);
            FStar_Extraction_ML_UEnv.tydefs =
              (uu___82_3148.FStar_Extraction_ML_UEnv.tydefs);
            FStar_Extraction_ML_UEnv.type_names =
              (uu___82_3148.FStar_Extraction_ML_UEnv.type_names);
            FStar_Extraction_ML_UEnv.currentModule = name
          }  in
        let uu____3150 =
          FStar_Util.fold_map extract_sig g1
            m.FStar_Syntax_Syntax.declarations
           in
        match uu____3150 with
        | (g2,sigs) ->
            let mlm = FStar_List.flatten sigs  in
            let is_kremlin =
              let uu____3179 = FStar_Options.codegen ()  in
              match uu____3179 with
              | FStar_Pervasives_Native.Some "Kremlin" -> true
              | uu____3182 -> false  in
            let uu____3185 =
              (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                 (is_kremlin ||
                    (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
                &&
                (FStar_Options.should_extract
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
               in
            if uu____3185
            then
              ((let uu____3193 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.print1 "Extracted module %s\n" uu____3193);
               (g2,
                 [FStar_Extraction_ML_Syntax.MLLib
                    [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                       (FStar_Extraction_ML_Syntax.MLLib []))]]))
            else (g2, [])))
  
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____3267 = FStar_Options.debug_any ()  in
      if uu____3267
      then
        let msg =
          let uu____3275 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3275  in
        FStar_Util.measure_execution_time msg
          (fun uu____3283  -> extract' g m)
      else extract' g m
  