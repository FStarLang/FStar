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
  fun uu___67_76  ->
    match uu___67_76 with
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
        FStar_Syntax_Syntax.vars = uu____98;_} ->
        let uu____101 =
          let uu____102 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____102  in
        (match uu____101 with
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
             FStar_Syntax_Syntax.vars = uu____108;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____110));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____111;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____112;_},uu____113)::[]);
        FStar_Syntax_Syntax.pos = uu____114;
        FStar_Syntax_Syntax.vars = uu____115;_} ->
        let uu____146 =
          let uu____147 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____147  in
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
          (FStar_Const.Const_string ("KremlinPrivate",uu____151));
        FStar_Syntax_Syntax.pos = uu____152;
        FStar_Syntax_Syntax.vars = uu____153;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____156));
        FStar_Syntax_Syntax.pos = uu____157;
        FStar_Syntax_Syntax.vars = uu____158;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____161));
        FStar_Syntax_Syntax.pos = uu____162;
        FStar_Syntax_Syntax.vars = uu____163;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____167);
        FStar_Syntax_Syntax.pos = uu____168;
        FStar_Syntax_Syntax.vars = uu____169;_} -> extract_meta x1
    | uu____176 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____189 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____189) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____227  ->
             match uu____227 with
             | (bv,uu____237) ->
                 let uu____238 =
                   let uu____239 =
                     let uu____242 =
                       let uu____243 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____243  in
                     FStar_Pervasives_Native.Some uu____242  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____239  in
                 let uu____244 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____238, uu____244)) env bs
  
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
              let uu____276 =
                let uu____277 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____277 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____276 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____279 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____296 -> def1  in
            let uu____297 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____308) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____329 -> ([], def2)  in
            match uu____297 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___68_350  ->
                       match uu___68_350 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____351 -> false) quals
                   in
                let uu____352 = binders_as_mlty_binders env bs  in
                (match uu____352 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____372 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____372
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____376 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___69_381  ->
                                 match uu___69_381 with
                                 | FStar_Syntax_Syntax.Projector uu____382 ->
                                     true
                                 | uu____387 -> false))
                          in
                       if uu____376
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____418 =
                         let uu____439 = lident_as_mlsymbol lid  in
                         (assumed, uu____439, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____418]  in
                     let def3 =
                       let uu____491 =
                         let uu____492 =
                           let uu____493 = FStar_Ident.range_of_lid lid  in
                           FStar_Extraction_ML_Util.mlloc_of_range uu____493
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____492  in
                       [uu____491; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____495 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___70_499  ->
                                 match uu___70_499 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____500 -> false))
                          in
                       if uu____495
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
    let uu____639 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____640 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____641 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____642 =
      let uu____643 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____654 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____655 =
                  let uu____656 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____656  in
                Prims.strcat uu____654 uu____655))
         in
      FStar_All.pipe_right uu____643 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____639 uu____640 uu____641
      uu____642
  
let bundle_as_inductive_families :
  'Auu____664 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____664 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____695 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____742 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____742 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____781,t2,l',nparams,uu____785)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____790 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____790 with
                                           | (bs',body) ->
                                               let uu____823 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____823 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____894  ->
                                                           fun uu____895  ->
                                                             match (uu____894,
                                                                    uu____895)
                                                             with
                                                             | ((b',uu____913),
                                                                (b,uu____915))
                                                                 ->
                                                                 let uu____924
                                                                   =
                                                                   let uu____931
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____931)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____924)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____933 =
                                                        let uu____936 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____936
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____933
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____941 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____946 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____946
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
                   | uu____949 -> (env1, [])) env ses
             in
          match uu____695 with
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
          let uu____1025 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1025
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1032 =
            let uu____1033 =
              let uu____1036 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1036  in
            uu____1033.FStar_Syntax_Syntax.n  in
          match uu____1032 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1040) ->
              FStar_List.map
                (fun uu____1066  ->
                   match uu____1066 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1072;
                        FStar_Syntax_Syntax.sort = uu____1073;_},uu____1074)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1077 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1088 =
          let uu____1089 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1089  in
        let uu____1094 =
          let uu____1105 = lident_as_mlsymbol ctor.dname  in
          let uu____1106 =
            let uu____1113 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1113  in
          (uu____1105, uu____1106)  in
        (uu____1088, uu____1094)  in
      let extract_one_family env1 ind =
        let uu____1161 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1161 with
        | (env2,vars) ->
            let uu____1196 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1196 with
             | (env3,ctors) ->
                 let uu____1289 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1289 with
                  | (indices,uu____1325) ->
                      let ml_params =
                        let uu____1345 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1364  ->
                                    let uu____1369 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1369))
                           in
                        FStar_List.append vars uu____1345  in
                      let tbody =
                        let uu____1371 =
                          FStar_Util.find_opt
                            (fun uu___71_1376  ->
                               match uu___71_1376 with
                               | FStar_Syntax_Syntax.RecordType uu____1377 ->
                                   true
                               | uu____1386 -> false) ind.iquals
                           in
                        match uu____1371 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1397 = FStar_List.hd ctors  in
                            (match uu____1397 with
                             | (uu____1418,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1457  ->
                                          match uu____1457 with
                                          | (uu____1466,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1469 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1469, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1470 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1473 =
                        let uu____1492 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1492, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1473)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1526,t,uu____1528,uu____1529,uu____1530);
            FStar_Syntax_Syntax.sigrng = uu____1531;
            FStar_Syntax_Syntax.sigquals = uu____1532;
            FStar_Syntax_Syntax.sigmeta = uu____1533;
            FStar_Syntax_Syntax.sigattrs = uu____1534;_}::[],uu____1535),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1552 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1552 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1598),quals) ->
          let uu____1612 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1612 with
           | (env1,ifams) ->
               let uu____1633 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1633 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1726 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let uu____1752 =
        (let uu____1755 = FStar_Options.codegen ()  in
         uu____1755 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1761 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr
              in
           Prims.op_Negation uu____1761)
         in
      if uu____1752
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1782 =
                   let uu____1785 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                   uu____1785.FStar_Syntax_Syntax.fv_name  in
                 uu____1782.FStar_Syntax_Syntax.v  in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
               let ml_name_str =
                 let uu____1790 =
                   let uu____1791 = FStar_Ident.string_of_lid fv  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1791  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1790  in
               let uu____1792 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str
                  in
               match uu____1792 with
               | FStar_Pervasives_Native.Some (interp,arity,plugin1) ->
                   let register =
                     if plugin1
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic"  in
                   let h =
                     let uu____1815 =
                       let uu____1816 =
                         let uu____1817 = FStar_Ident.lid_of_str register  in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1817
                          in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1816  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1815
                      in
                   let arity1 =
                     let uu____1819 =
                       let uu____1820 =
                         let uu____1831 = FStar_Util.string_of_int arity  in
                         (uu____1831, FStar_Pervasives_Native.None)  in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1820  in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1819  in
                   let app =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top)
                       (FStar_Extraction_ML_Syntax.MLE_App
                          (h, [w ml_name_str; w arity1; interp]))
                      in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> []  in
             FStar_List.collect mk_registration
               (FStar_Pervasives_Native.snd lbs)
         | uu____1853 -> [])
  
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
           let uu____1876 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1876);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1883 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1892 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1909 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1947 =
               let uu____1952 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1952 ml_name tysc
                 false false
                in
             match uu____1947 with
             | (g2,mangled_name) ->
                 ((let uu____1960 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1960
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
             (let uu____1974 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1974
              then
                let uu____1975 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1975
              else ());
             (let uu____1977 =
                let uu____1978 = FStar_Syntax_Subst.compress tm  in
                uu____1978.FStar_Syntax_Syntax.n  in
              match uu____1977 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1986) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1993 =
                    let uu____2002 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2002  in
                  (match uu____1993 with
                   | (uu____2059,uu____2060,tysc,uu____2062) ->
                       let uu____2063 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2063, tysc))
              | uu____2064 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2090 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2090
              then
                let uu____2091 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2092 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2091
                  uu____2092
              else ());
             (let uu____2094 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2094 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2110 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2110  in
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
                  let uu____2136 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2136 with
                   | (a_let,uu____2148,ty) ->
                       ((let uu____2151 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2151
                         then
                           let uu____2152 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2152
                         else ());
                        (let uu____2154 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2163,mllb::[]),uu____2165) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2183 -> failwith "Impossible"  in
                         match uu____2154 with
                         | (exp,tysc) ->
                             ((let uu____2195 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2195
                               then
                                 ((let uu____2197 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2197);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2201 =
             let uu____2206 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2206 with
             | (return_tm,ty_sc) ->
                 let uu____2219 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2219 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2201 with
            | (g1,return_decl) ->
                let uu____2238 =
                  let uu____2243 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2243 with
                  | (bind_tm,ty_sc) ->
                      let uu____2256 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2256 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2238 with
                 | (g2,bind_decl) ->
                     let uu____2275 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2275 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2296 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2309 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2313,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2321 =
             let uu____2322 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___72_2326  ->
                       match uu___72_2326 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2327 -> false))
                in
             Prims.op_Negation uu____2322  in
           if uu____2321
           then (g, [])
           else
             (let uu____2337 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2337 with
              | (bs,uu____2357) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2375 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2375)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2377) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2393 =
             let uu____2402 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2402 with
             | (tcenv,uu____2426,def_typ) ->
                 let uu____2432 = as_pair def_typ  in (tcenv, uu____2432)
              in
           (match uu____2393 with
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
                let uu____2456 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2456 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2458) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2469 =
             let uu____2476 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2476  in
           (match uu____2469 with
            | (ml_let,uu____2486,uu____2487) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2496) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___73_2511  ->
                            match uu___73_2511 with
                            | FStar_Syntax_Syntax.Assumption  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2514 -> FStar_Pervasives_Native.None)
                         quals
                        in
                     let flags' = extract_metadata attrs  in
                     let uu____2518 =
                       FStar_List.fold_left2
                         (fun uu____2550  ->
                            fun ml_lb  ->
                              fun uu____2552  ->
                                match (uu____2550, uu____2552) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2574;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2576;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2577;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2578;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____2579;_})
                                    ->
                                    let lb_lid =
                                      let uu____2605 =
                                        let uu____2608 =
                                          FStar_Util.right lbname  in
                                        uu____2608.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____2605.FStar_Syntax_Syntax.v  in
                                    let flags'' =
                                      let uu____2612 =
                                        let uu____2613 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____2613.FStar_Syntax_Syntax.n  in
                                      match uu____2612 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (uu____2618,{
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Comp
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____2619;
                                                            FStar_Syntax_Syntax.effect_name
                                                              = e;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = uu____2621;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____2622;
                                                            FStar_Syntax_Syntax.flags
                                                              = uu____2623;_};
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____2624;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____2625;_})
                                          when
                                          let uu____2654 =
                                            FStar_Ident.string_of_lid e  in
                                          uu____2654 =
                                            "FStar.HyperStack.ST.StackInline"
                                          ->
                                          [FStar_Extraction_ML_Syntax.StackInline]
                                      | uu____2655 -> []  in
                                    let meta =
                                      FStar_List.append flags1
                                        (FStar_List.append flags' flags'')
                                       in
                                    let ml_lb1 =
                                      let uu___77_2660 = ml_lb  in
                                      {
                                        FStar_Extraction_ML_Syntax.mllb_name
                                          =
                                          (uu___77_2660.FStar_Extraction_ML_Syntax.mllb_name);
                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                          =
                                          (uu___77_2660.FStar_Extraction_ML_Syntax.mllb_tysc);
                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                          =
                                          (uu___77_2660.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                        FStar_Extraction_ML_Syntax.mllb_def =
                                          (uu___77_2660.FStar_Extraction_ML_Syntax.mllb_def);
                                        FStar_Extraction_ML_Syntax.mllb_meta
                                          = meta;
                                        FStar_Extraction_ML_Syntax.print_typ
                                          =
                                          (uu___77_2660.FStar_Extraction_ML_Syntax.print_typ)
                                      }  in
                                    let uu____2661 =
                                      let uu____2666 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___74_2671  ->
                                                match uu___74_2671 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2672 -> true
                                                | uu____2677 -> false))
                                         in
                                      if uu____2666
                                      then
                                        let mname =
                                          let uu____2683 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____2683
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____2684 =
                                          let uu____2689 =
                                            FStar_Util.right lbname  in
                                          let uu____2690 =
                                            FStar_Util.must
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2689 mname uu____2690
                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____2684 with
                                        | (env1,uu____2696) ->
                                            (env1,
                                              (let uu___78_2698 = ml_lb1  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___78_2698.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___78_2698.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___78_2698.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                   =
                                                   (uu___78_2698.FStar_Extraction_ML_Syntax.mllb_meta);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___78_2698.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2702 =
                                           let uu____2703 =
                                             let uu____2708 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2708
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2703
                                            in
                                         (uu____2702, ml_lb1))
                                       in
                                    (match uu____2661 with
                                     | (g1,ml_lb2) ->
                                         (g1, (ml_lb2 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2518 with
                      | (g1,ml_lbs') ->
                          let uu____2739 =
                            let uu____2742 =
                              let uu____2745 =
                                let uu____2746 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2746
                                 in
                              [uu____2745;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____2749 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____2742 uu____2749  in
                          (g1, uu____2739))
                 | uu____2754 ->
                     let uu____2755 =
                       let uu____2756 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2756
                        in
                     failwith uu____2755))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2764,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2769 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____2769
           then
             let always_fail =
               let imp =
                 let uu____2780 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2780 with
                 | ([],t1) ->
                     let b =
                       let uu____2809 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2809
                        in
                     let uu____2810 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2810
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2829 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2829
                       FStar_Pervasives_Native.None
                  in
               let uu___79_2830 = se  in
               let uu____2831 =
                 let uu____2832 =
                   let uu____2839 =
                     let uu____2846 =
                       let uu____2849 =
                         let uu____2850 =
                           let uu____2855 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____2855  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2850;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         }  in
                       [uu____2849]  in
                     (false, uu____2846)  in
                   (uu____2839, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2832  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2831;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___79_2830.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___79_2830.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___79_2830.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___79_2830.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2868 = extract_sig g always_fail  in
             (match uu____2868 with
              | (g1,mlm) ->
                  let uu____2887 =
                    FStar_Util.find_map quals
                      (fun uu___75_2892  ->
                         match uu___75_2892 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____2896 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____2887 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____2904 =
                         let uu____2907 =
                           let uu____2908 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2908  in
                         let uu____2909 =
                           let uu____2912 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2912]  in
                         uu____2907 :: uu____2909  in
                       (g1, uu____2904)
                   | uu____2915 ->
                       let uu____2918 =
                         FStar_Util.find_map quals
                           (fun uu___76_2924  ->
                              match uu___76_2924 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2928)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____2929 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____2918 with
                        | FStar_Pervasives_Native.Some uu____2936 -> (g1, [])
                        | uu____2939 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2948 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____2948 with
            | (ml_main,uu____2962,uu____2963) ->
                let uu____2964 =
                  let uu____2967 =
                    let uu____2968 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2968  in
                  [uu____2967; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____2964))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2971 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2978 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2987 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2990 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3015 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3015 FStar_Pervasives_Native.fst
  
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
      (let uu____3057 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___80_3060 = g  in
         let uu____3061 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3061;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___80_3060.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___80_3060.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___80_3060.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3062 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3062 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3091 = FStar_Options.codegen ()  in
             uu____3091 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____3096 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3096
           then
             ((let uu____3104 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3104);
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
      let uu____3178 = FStar_Options.debug_any ()  in
      if uu____3178
      then
        let msg =
          let uu____3186 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3186  in
        FStar_Util.measure_execution_time msg
          (fun uu____3194  -> extract' g m)
      else extract' g m
  