open Prims
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____13 =
        let uu____18 =
          let uu____19 =
            let uu____34 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____35 =
              let uu____38 = FStar_Syntax_Syntax.iarg t  in
              let uu____39 =
                let uu____42 =
                  let uu____43 =
                    let uu____44 =
                      let uu____49 =
                        let uu____50 =
                          let uu____51 =
                            let uu____56 =
                              let uu____57 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____57
                               in
                            (uu____56, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____51  in
                        FStar_Syntax_Syntax.Tm_constant uu____50  in
                      FStar_Syntax_Syntax.mk uu____49  in
                    uu____44 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____43  in
                [uu____42]  in
              uu____38 :: uu____39  in
            (uu____34, uu____35)  in
          FStar_Syntax_Syntax.Tm_app uu____19  in
        FStar_Syntax_Syntax.mk uu____18  in
      uu____13 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
  
let as_pair :
  'Auu____80 .
    'Auu____80 Prims.list ->
      ('Auu____80,'Auu____80) FStar_Pervasives_Native.tuple2
  =
  fun uu___67_91  ->
    match uu___67_91 with
    | a::b::[] -> (a, b)
    | uu____96 -> failwith "Expected a list with 2 elements"
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____110 = FStar_Syntax_Subst.compress x  in
    match uu____110 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____114;
        FStar_Syntax_Syntax.vars = uu____115;_} ->
        let uu____118 =
          let uu____119 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____119  in
        (match uu____118 with
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
         | uu____122 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____124;
             FStar_Syntax_Syntax.vars = uu____125;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____127));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____128;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____129;_},uu____130)::[]);
        FStar_Syntax_Syntax.pos = uu____131;
        FStar_Syntax_Syntax.vars = uu____132;_} ->
        let uu____163 =
          let uu____164 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____164  in
        (match uu____163 with
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
         | uu____167 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____168));
        FStar_Syntax_Syntax.pos = uu____169;
        FStar_Syntax_Syntax.vars = uu____170;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____173));
        FStar_Syntax_Syntax.pos = uu____174;
        FStar_Syntax_Syntax.vars = uu____175;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____178));
        FStar_Syntax_Syntax.pos = uu____179;
        FStar_Syntax_Syntax.vars = uu____180;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____184);
        FStar_Syntax_Syntax.pos = uu____185;
        FStar_Syntax_Syntax.vars = uu____186;_} -> extract_meta x1
    | uu____193 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____211 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____211) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____251  ->
             match uu____251 with
             | (bv,uu____261) ->
                 let uu____262 =
                   let uu____263 =
                     let uu____266 =
                       let uu____267 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____267  in
                     FStar_Pervasives_Native.Some uu____266  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____263  in
                 let uu____268 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____262, uu____268)) env bs
  
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
              let uu____310 =
                let uu____311 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____311 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____310 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____313 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____330 -> def1  in
            let uu____331 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____342) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____363 -> ([], def2)  in
            match uu____331 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___68_384  ->
                       match uu___68_384 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____385 -> false) quals
                   in
                let uu____386 = binders_as_mlty_binders env bs  in
                (match uu____386 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____406 =
                         FStar_Extraction_ML_Term.translate_term_to_mlty env1
                           body
                          in
                       FStar_All.pipe_right uu____406
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____410 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___69_415  ->
                                 match uu___69_415 with
                                 | FStar_Syntax_Syntax.Projector uu____416 ->
                                     true
                                 | uu____421 -> false))
                          in
                       if uu____410
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____452 =
                         let uu____473 = lident_as_mlsymbol lid  in
                         (assumed, uu____473, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____452]  in
                     let def3 =
                       let uu____525 =
                         let uu____526 =
                           let uu____527 = FStar_Ident.range_of_lid lid  in
                           FStar_Extraction_ML_Util.mlloc_of_range uu____527
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____526  in
                       [uu____525; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____529 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___70_533  ->
                                 match uu___70_533 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____534 -> false))
                          in
                       if uu____529
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
  
let (print_ifamily : inductive_family -> unit) =
  fun i  ->
    let uu____691 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____692 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____693 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____694 =
      let uu____695 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____706 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____707 =
                  let uu____708 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____708  in
                Prims.strcat uu____706 uu____707))
         in
      FStar_All.pipe_right uu____695 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____691 uu____692 uu____693
      uu____694
  
let bundle_as_inductive_families :
  'Auu____721 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____721 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____756 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____803 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____803 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____842,t2,l',nparams,uu____846)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____851 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____851 with
                                           | (bs',body) ->
                                               let uu____884 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____884 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____955  ->
                                                           fun uu____956  ->
                                                             match (uu____955,
                                                                    uu____956)
                                                             with
                                                             | ((b',uu____974),
                                                                (b,uu____976))
                                                                 ->
                                                                 let uu____985
                                                                   =
                                                                   let uu____992
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____992)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____985)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____994 =
                                                        let uu____997 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____997
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____994
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1002 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____1007 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1007
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
                   | uu____1010 -> (env1, [])) env ses
             in
          match uu____756 with
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
          let uu____1093 =
            FStar_Extraction_ML_Term.translate_term_to_mlty env1 ctor.dtyp
             in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1093
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1100 =
            let uu____1101 =
              let uu____1104 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1104  in
            uu____1101.FStar_Syntax_Syntax.n  in
          match uu____1100 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1108) ->
              FStar_List.map
                (fun uu____1134  ->
                   match uu____1134 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1140;
                        FStar_Syntax_Syntax.sort = uu____1141;_},uu____1142)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1145 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1156 =
          let uu____1157 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1157  in
        let uu____1162 =
          let uu____1173 = lident_as_mlsymbol ctor.dname  in
          let uu____1174 =
            let uu____1181 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1181  in
          (uu____1173, uu____1174)  in
        (uu____1156, uu____1162)  in
      let extract_one_family env1 ind =
        let uu____1231 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1231 with
        | (env2,vars) ->
            let uu____1266 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1266 with
             | (env3,ctors) ->
                 let uu____1359 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1359 with
                  | (indices,uu____1395) ->
                      let ml_params =
                        let uu____1415 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1434  ->
                                    let uu____1439 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1439))
                           in
                        FStar_List.append vars uu____1415  in
                      let tbody =
                        let uu____1441 =
                          FStar_Util.find_opt
                            (fun uu___71_1446  ->
                               match uu___71_1446 with
                               | FStar_Syntax_Syntax.RecordType uu____1447 ->
                                   true
                               | uu____1456 -> false) ind.iquals
                           in
                        match uu____1441 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1467 = FStar_List.hd ctors  in
                            (match uu____1467 with
                             | (uu____1488,c_ty) ->
                                 let uu____1502 = ()  in
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1525  ->
                                          match uu____1525 with
                                          | (uu____1534,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1537 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1537, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1538 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1541 =
                        let uu____1560 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1560, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1541)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1594,t,uu____1596,uu____1597,uu____1598);
            FStar_Syntax_Syntax.sigrng = uu____1599;
            FStar_Syntax_Syntax.sigquals = uu____1600;
            FStar_Syntax_Syntax.sigmeta = uu____1601;
            FStar_Syntax_Syntax.sigattrs = uu____1602;_}::[],uu____1603),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1620 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1620 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1666),quals) ->
          let uu____1680 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1680 with
           | (env1,ifams) ->
               let uu____1701 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1701 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1794 -> failwith "Unexpected signature element"
  
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
      let uu____1825 =
        (let uu____1828 = FStar_Options.codegen ()  in
         uu____1828 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1834 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr
              in
           Prims.op_Negation uu____1834)
         in
      if uu____1825
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1856 =
                   let uu____1859 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                   uu____1859.FStar_Syntax_Syntax.fv_name  in
                 uu____1856.FStar_Syntax_Syntax.v  in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
               let ml_name_str =
                 let uu____1864 =
                   let uu____1865 = FStar_Ident.string_of_lid fv  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1865  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1864  in
               let uu____1866 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str
                  in
               match uu____1866 with
               | FStar_Pervasives_Native.Some (interp,arity,plugin) ->
                   let register =
                     if plugin
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic"  in
                   let h =
                     let uu____1889 =
                       let uu____1890 =
                         let uu____1891 = FStar_Ident.lid_of_str register  in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1891
                          in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1890  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1889
                      in
                   let arity1 =
                     let uu____1893 =
                       let uu____1894 =
                         let uu____1905 = FStar_Util.string_of_int arity  in
                         (uu____1905, FStar_Pervasives_Native.None)  in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1894  in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1893  in
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
         | uu____1927 -> [])
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      let uu____1950 =
        FStar_Extraction_ML_UEnv.debug g
          (fun u  ->
             let uu____1954 = FStar_Syntax_Print.sigelt_to_string se  in
             FStar_Util.print1 ">>>> extract_sig %s \n" uu____1954)
         in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____1961 -> extract_bundle g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____1970 ->
          extract_bundle g se
      | FStar_Syntax_Syntax.Sig_datacon uu____1987 -> extract_bundle g se
      | FStar_Syntax_Syntax.Sig_new_effect ed when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let extend_env g1 lid ml_name tm tysc =
            let uu____2030 =
              let uu____2035 =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.Delta_equational
                  FStar_Pervasives_Native.None
                 in
              FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2035 ml_name tysc
                false false
               in
            match uu____2030 with
            | (g2,mangled_name) ->
                let uu____2042 =
                  let uu____2043 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         g2.FStar_Extraction_ML_UEnv.tcenv)
                      (FStar_Options.Other "ExtractionReify")
                     in
                  if uu____2043
                  then FStar_Util.print1 "Mangled name: %s\n" mangled_name
                  else ()  in
                let lb =
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
                     (FStar_Extraction_ML_Syntax.NonRec, [lb])))
             in
          let rec extract_fv tm =
            let uu____2057 =
              let uu____2058 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2058
              then
                let uu____2059 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2059
              else ()  in
            let uu____2061 =
              let uu____2062 = FStar_Syntax_Subst.compress tm  in
              uu____2062.FStar_Syntax_Syntax.n  in
            match uu____2061 with
            | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2070) -> extract_fv tm1
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let mlp =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                let uu____2077 =
                  let uu____2086 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                     in
                  FStar_All.pipe_left FStar_Util.right uu____2086  in
                (match uu____2077 with
                 | (uu____2143,uu____2144,tysc,uu____2146) ->
                     let uu____2147 =
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                        in
                     (uu____2147, tysc))
            | uu____2148 -> failwith "Not an fv"  in
          let extract_action g1 a =
            let uu____2166 = ()  in
            let uu____2167 =
              let uu____2168 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2168
              then
                let uu____2169 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2170 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2169
                  uu____2170
              else ()  in
            let uu____2172 = FStar_Extraction_ML_UEnv.action_name ed a  in
            match uu____2172 with
            | (a_nm,a_lid) ->
                let lbname =
                  let uu____2188 =
                    FStar_Syntax_Syntax.new_bv
                      (FStar_Pervasives_Native.Some
                         ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                      FStar_Syntax_Syntax.tun
                     in
                  FStar_Util.Inl uu____2188  in
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
                let uu____2214 =
                  FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                (match uu____2214 with
                 | (a_let,uu____2226,ty) ->
                     let uu____2228 =
                       let uu____2229 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              g1.FStar_Extraction_ML_UEnv.tcenv)
                           (FStar_Options.Other "ExtractionReify")
                          in
                       if uu____2229
                       then
                         let uu____2230 =
                           FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                             a_let
                            in
                         FStar_Util.print1 "Extracted action term: %s\n"
                           uu____2230
                       else ()  in
                     let uu____2232 =
                       match a_let.FStar_Extraction_ML_Syntax.expr with
                       | FStar_Extraction_ML_Syntax.MLE_Let
                           ((uu____2241,mllb::[]),uu____2243) ->
                           (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                            with
                            | FStar_Pervasives_Native.Some tysc ->
                                ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                  tysc)
                            | FStar_Pervasives_Native.None  ->
                                failwith "No type scheme")
                       | uu____2261 -> failwith "Impossible"  in
                     (match uu____2232 with
                      | (exp,tysc) ->
                          let uu____2272 =
                            let uu____2273 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   g1.FStar_Extraction_ML_UEnv.tcenv)
                                (FStar_Options.Other "ExtractionReify")
                               in
                            if uu____2273
                            then
                              let uu____2274 =
                                let uu____2275 =
                                  FStar_Extraction_ML_Code.string_of_mlty
                                    a_nm (FStar_Pervasives_Native.snd tysc)
                                   in
                                FStar_Util.print1
                                  "Extracted action type: %s\n" uu____2275
                                 in
                              FStar_List.iter
                                (fun x  ->
                                   FStar_Util.print1 "and binders: %s\n" x)
                                (FStar_Pervasives_Native.fst tysc)
                            else ()  in
                          extend_env g1 a_lid a_nm exp tysc))
             in
          let uu____2279 =
            let uu____2284 =
              extract_fv
                (FStar_Pervasives_Native.snd
                   ed.FStar_Syntax_Syntax.return_repr)
               in
            match uu____2284 with
            | (return_tm,ty_sc) ->
                let uu____2297 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                (match uu____2297 with
                 | (return_nm,return_lid) ->
                     extend_env g return_lid return_nm return_tm ty_sc)
             in
          (match uu____2279 with
           | (g1,return_decl) ->
               let uu____2316 =
                 let uu____2321 =
                   extract_fv
                     (FStar_Pervasives_Native.snd
                        ed.FStar_Syntax_Syntax.bind_repr)
                    in
                 match uu____2321 with
                 | (bind_tm,ty_sc) ->
                     let uu____2334 =
                       FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                     (match uu____2334 with
                      | (bind_nm,bind_lid) ->
                          extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                  in
               (match uu____2316 with
                | (g2,bind_decl) ->
                    let uu____2353 =
                      FStar_Util.fold_map extract_action g2
                        ed.FStar_Syntax_Syntax.actions
                       in
                    (match uu____2353 with
                     | (g3,actions) ->
                         (g3,
                           (FStar_List.append [return_decl; bind_decl]
                              actions)))))
      | FStar_Syntax_Syntax.Sig_splice uu____2374 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect uu____2387 -> (g, [])
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2391,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____2399 =
            let uu____2400 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___72_2404  ->
                      match uu___72_2404 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2405 -> false))
               in
            Prims.op_Negation uu____2400  in
          if uu____2399
          then (g, [])
          else
            (let uu____2415 = FStar_Syntax_Util.arrow_formals t  in
             match uu____2415 with
             | (bs,uu____2435) ->
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv lid
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____2453 =
                   FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                     FStar_Pervasives_Native.None
                    in
                 extract_typ_abbrev g fv quals attrs uu____2453)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2455) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____2471 =
            let uu____2480 =
              FStar_TypeChecker_Env.open_universes_in
                g.FStar_Extraction_ML_UEnv.tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____2480 with
            | (tcenv,uu____2504,def_typ) ->
                let uu____2510 = as_pair def_typ  in (tcenv, uu____2510)
             in
          (match uu____2471 with
           | (tcenv,(lbdef,lbtyp)) ->
               let lbtyp1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp
                  in
               let lbdef1 =
                 FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                   lbtyp1
                  in
               let uu____2534 =
                 FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
               extract_typ_abbrev g uu____2534 quals
                 se.FStar_Syntax_Syntax.sigattrs lbdef1)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2536) ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____2547 =
            let uu____2554 =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Util.exp_false_bool))
                FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
               in
            FStar_Extraction_ML_Term.term_as_mlexpr g uu____2554  in
          (match uu____2547 with
           | (ml_let,uu____2564,uu____2565) ->
               (match ml_let.FStar_Extraction_ML_Syntax.expr with
                | FStar_Extraction_ML_Syntax.MLE_Let
                    ((flavor,bindings),uu____2574) ->
                    let flags1 =
                      FStar_List.choose
                        (fun uu___73_2589  ->
                           match uu___73_2589 with
                           | FStar_Syntax_Syntax.Assumption  ->
                               FStar_Pervasives_Native.Some
                                 FStar_Extraction_ML_Syntax.Assumed
                           | FStar_Syntax_Syntax.Private  ->
                               FStar_Pervasives_Native.Some
                                 FStar_Extraction_ML_Syntax.Private
                           | FStar_Syntax_Syntax.NoExtract  ->
                               FStar_Pervasives_Native.Some
                                 FStar_Extraction_ML_Syntax.NoExtract
                           | uu____2592 -> FStar_Pervasives_Native.None)
                        quals
                       in
                    let flags' = extract_metadata attrs  in
                    let uu____2596 =
                      FStar_List.fold_left2
                        (fun uu____2622  ->
                           fun ml_lb  ->
                             fun uu____2624  ->
                               match (uu____2622, uu____2624) with
                               | ((env,ml_lbs),{
                                                 FStar_Syntax_Syntax.lbname =
                                                   lbname;
                                                 FStar_Syntax_Syntax.lbunivs
                                                   = uu____2646;
                                                 FStar_Syntax_Syntax.lbtyp =
                                                   t;
                                                 FStar_Syntax_Syntax.lbeff =
                                                   uu____2648;
                                                 FStar_Syntax_Syntax.lbdef =
                                                   uu____2649;
                                                 FStar_Syntax_Syntax.lbattrs
                                                   = uu____2650;
                                                 FStar_Syntax_Syntax.lbpos =
                                                   uu____2651;_})
                                   ->
                                   let uu____2676 =
                                     FStar_All.pipe_right
                                       ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                       (FStar_List.contains
                                          FStar_Extraction_ML_Syntax.Erased)
                                      in
                                   if uu____2676
                                   then (env, ml_lbs)
                                   else
                                     (let lb_lid =
                                        let uu____2687 =
                                          let uu____2690 =
                                            FStar_Util.right lbname  in
                                          uu____2690.FStar_Syntax_Syntax.fv_name
                                           in
                                        uu____2687.FStar_Syntax_Syntax.v  in
                                      let flags'' =
                                        let uu____2694 =
                                          let uu____2695 =
                                            FStar_Syntax_Subst.compress t  in
                                          uu____2695.FStar_Syntax_Syntax.n
                                           in
                                        match uu____2694 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (uu____2700,{
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Comp
                                                            {
                                                              FStar_Syntax_Syntax.comp_univs
                                                                = uu____2701;
                                                              FStar_Syntax_Syntax.effect_name
                                                                = e;
                                                              FStar_Syntax_Syntax.result_typ
                                                                = uu____2703;
                                                              FStar_Syntax_Syntax.effect_args
                                                                = uu____2704;
                                                              FStar_Syntax_Syntax.flags
                                                                = uu____2705;_};
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____2706;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____2707;_})
                                            when
                                            let uu____2736 =
                                              FStar_Ident.string_of_lid e  in
                                            uu____2736 =
                                              "FStar.HyperStack.ST.StackInline"
                                            ->
                                            [FStar_Extraction_ML_Syntax.StackInline]
                                        | uu____2737 -> []  in
                                      let meta =
                                        FStar_List.append flags1
                                          (FStar_List.append flags' flags'')
                                         in
                                      let ml_lb1 =
                                        let uu___77_2742 = ml_lb  in
                                        {
                                          FStar_Extraction_ML_Syntax.mllb_name
                                            =
                                            (uu___77_2742.FStar_Extraction_ML_Syntax.mllb_name);
                                          FStar_Extraction_ML_Syntax.mllb_tysc
                                            =
                                            (uu___77_2742.FStar_Extraction_ML_Syntax.mllb_tysc);
                                          FStar_Extraction_ML_Syntax.mllb_add_unit
                                            =
                                            (uu___77_2742.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                          FStar_Extraction_ML_Syntax.mllb_def
                                            =
                                            (uu___77_2742.FStar_Extraction_ML_Syntax.mllb_def);
                                          FStar_Extraction_ML_Syntax.mllb_meta
                                            = meta;
                                          FStar_Extraction_ML_Syntax.print_typ
                                            =
                                            (uu___77_2742.FStar_Extraction_ML_Syntax.print_typ)
                                        }  in
                                      let uu____2743 =
                                        let uu____2748 =
                                          FStar_All.pipe_right quals
                                            (FStar_Util.for_some
                                               (fun uu___74_2753  ->
                                                  match uu___74_2753 with
                                                  | FStar_Syntax_Syntax.Projector
                                                      uu____2754 -> true
                                                  | uu____2759 -> false))
                                           in
                                        if uu____2748
                                        then
                                          let mname =
                                            let uu____2765 =
                                              mangle_projector_lid lb_lid  in
                                            FStar_All.pipe_right uu____2765
                                              FStar_Extraction_ML_Syntax.mlpath_of_lident
                                             in
                                          let uu____2766 =
                                            let uu____2771 =
                                              FStar_Util.right lbname  in
                                            let uu____2772 =
                                              FStar_Util.must
                                                ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                               in
                                            FStar_Extraction_ML_UEnv.extend_fv'
                                              env uu____2771 mname uu____2772
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                              false
                                             in
                                          match uu____2766 with
                                          | (env1,uu____2778) ->
                                              (env1,
                                                (let uu___78_2780 = ml_lb1
                                                    in
                                                 {
                                                   FStar_Extraction_ML_Syntax.mllb_name
                                                     =
                                                     (FStar_Pervasives_Native.snd
                                                        mname);
                                                   FStar_Extraction_ML_Syntax.mllb_tysc
                                                     =
                                                     (uu___78_2780.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                   FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     =
                                                     (uu___78_2780.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                   FStar_Extraction_ML_Syntax.mllb_def
                                                     =
                                                     (uu___78_2780.FStar_Extraction_ML_Syntax.mllb_def);
                                                   FStar_Extraction_ML_Syntax.mllb_meta
                                                     =
                                                     (uu___78_2780.FStar_Extraction_ML_Syntax.mllb_meta);
                                                   FStar_Extraction_ML_Syntax.print_typ
                                                     =
                                                     (uu___78_2780.FStar_Extraction_ML_Syntax.print_typ)
                                                 }))
                                        else
                                          (let uu____2784 =
                                             let uu____2785 =
                                               let uu____2790 =
                                                 FStar_Util.must
                                                   ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                  in
                                               FStar_Extraction_ML_UEnv.extend_lb
                                                 env lbname t uu____2790
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                 false
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____2785
                                              in
                                           (uu____2784, ml_lb1))
                                         in
                                      match uu____2743 with
                                      | (g1,ml_lb2) ->
                                          (g1, (ml_lb2 :: ml_lbs)))) 
                        (g, []) bindings (FStar_Pervasives_Native.snd lbs)
                       in
                    (match uu____2596 with
                     | (g1,ml_lbs') ->
                         let uu____2821 =
                           let uu____2824 =
                             let uu____2827 =
                               let uu____2828 =
                                 FStar_Extraction_ML_Util.mlloc_of_range
                                   se.FStar_Syntax_Syntax.sigrng
                                  in
                               FStar_Extraction_ML_Syntax.MLM_Loc uu____2828
                                in
                             [uu____2827;
                             FStar_Extraction_ML_Syntax.MLM_Let
                               (flavor, (FStar_List.rev ml_lbs'))]
                              in
                           let uu____2831 = maybe_register_plugin g1 se  in
                           FStar_List.append uu____2824 uu____2831  in
                         (g1, uu____2821))
                | uu____2836 ->
                    let uu____2837 =
                      let uu____2838 =
                        FStar_Extraction_ML_Code.string_of_mlexpr
                          g.FStar_Extraction_ML_UEnv.currentModule ml_let
                         in
                      FStar_Util.format1
                        "Impossible: Translated a let to a non-let: %s"
                        uu____2838
                       in
                    failwith uu____2837))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2846,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____2851 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____2855 = FStar_Extraction_ML_Term.must_erase g t  in
               Prims.op_Negation uu____2855)
             in
          if uu____2851
          then
            let always_fail =
              let imp =
                let uu____2864 = FStar_Syntax_Util.arrow_formals t  in
                match uu____2864 with
                | ([],t1) ->
                    let b =
                      let uu____2893 =
                        FStar_Syntax_Syntax.gen_bv "_"
                          FStar_Pervasives_Native.None t1
                         in
                      FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                        uu____2893
                       in
                    let uu____2894 = fail_exp lid t1  in
                    FStar_Syntax_Util.abs [b] uu____2894
                      FStar_Pervasives_Native.None
                | (bs,t1) ->
                    let uu____2913 = fail_exp lid t1  in
                    FStar_Syntax_Util.abs bs uu____2913
                      FStar_Pervasives_Native.None
                 in
              let uu___79_2914 = se  in
              let uu____2915 =
                let uu____2916 =
                  let uu____2923 =
                    let uu____2930 =
                      let uu____2933 =
                        let uu____2934 =
                          let uu____2939 =
                            FStar_Syntax_Syntax.lid_as_fv lid
                              FStar_Syntax_Syntax.Delta_constant
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____2939  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____2934;
                          FStar_Syntax_Syntax.lbunivs = [];
                          FStar_Syntax_Syntax.lbtyp = t;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_ML_lid;
                          FStar_Syntax_Syntax.lbdef = imp;
                          FStar_Syntax_Syntax.lbattrs = [];
                          FStar_Syntax_Syntax.lbpos =
                            (imp.FStar_Syntax_Syntax.pos)
                        }  in
                      [uu____2933]  in
                    (false, uu____2930)  in
                  (uu____2923, [])  in
                FStar_Syntax_Syntax.Sig_let uu____2916  in
              {
                FStar_Syntax_Syntax.sigel = uu____2915;
                FStar_Syntax_Syntax.sigrng =
                  (uu___79_2914.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___79_2914.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___79_2914.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___79_2914.FStar_Syntax_Syntax.sigattrs)
              }  in
            let uu____2952 = extract_sig g always_fail  in
            (match uu____2952 with
             | (g1,mlm) ->
                 let uu____2971 =
                   FStar_Util.find_map quals
                     (fun uu___75_2976  ->
                        match uu___75_2976 with
                        | FStar_Syntax_Syntax.Discriminator l ->
                            FStar_Pervasives_Native.Some l
                        | uu____2980 -> FStar_Pervasives_Native.None)
                    in
                 (match uu____2971 with
                  | FStar_Pervasives_Native.Some l ->
                      let uu____2988 =
                        let uu____2991 =
                          let uu____2992 =
                            FStar_Extraction_ML_Util.mlloc_of_range
                              se.FStar_Syntax_Syntax.sigrng
                             in
                          FStar_Extraction_ML_Syntax.MLM_Loc uu____2992  in
                        let uu____2993 =
                          let uu____2996 =
                            FStar_Extraction_ML_Term.ind_discriminator_body
                              g1 lid l
                             in
                          [uu____2996]  in
                        uu____2991 :: uu____2993  in
                      (g1, uu____2988)
                  | uu____2999 ->
                      let uu____3002 =
                        FStar_Util.find_map quals
                          (fun uu___76_3008  ->
                             match uu___76_3008 with
                             | FStar_Syntax_Syntax.Projector (l,uu____3012)
                                 -> FStar_Pervasives_Native.Some l
                             | uu____3013 -> FStar_Pervasives_Native.None)
                         in
                      (match uu____3002 with
                       | FStar_Pervasives_Native.Some uu____3020 -> (g1, [])
                       | uu____3023 -> (g1, mlm))))
          else (g, [])
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____3032 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
          (match uu____3032 with
           | (ml_main,uu____3046,uu____3047) ->
               let uu____3048 =
                 let uu____3051 =
                   let uu____3052 =
                     FStar_Extraction_ML_Util.mlloc_of_range
                       se.FStar_Syntax_Syntax.sigrng
                      in
                   FStar_Extraction_ML_Syntax.MLM_Loc uu____3052  in
                 [uu____3051; FStar_Extraction_ML_Syntax.MLM_Top ml_main]  in
               (g, uu____3048))
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3055 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_assume uu____3062 -> (g, [])
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3071 -> (g, [])
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3074 -> (g, [])
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____3090 =
            FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng
             in
          (g, [])
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3103 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3103 FStar_Pervasives_Native.fst
  
let (extract' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____3148 = FStar_Syntax_Syntax.reset_gensym ()  in
      let uu____3149 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___80_3152 = g  in
        let uu____3153 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.tcenv = uu____3153;
          FStar_Extraction_ML_UEnv.gamma =
            (uu___80_3152.FStar_Extraction_ML_UEnv.gamma);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___80_3152.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___80_3152.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____3154 =
        FStar_Util.fold_map extract_sig g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____3154 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____3183 = FStar_Options.codegen ()  in
            uu____3183 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          let uu____3188 =
            (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
               (is_kremlin ||
                  (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
              &&
              (FStar_Options.should_extract
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
             in
          if uu____3188
          then
            let uu____3195 =
              let uu____3196 =
                FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                 in
              FStar_Util.print1 "Extracted module %s\n" uu____3196  in
            (g2,
              [FStar_Extraction_ML_Syntax.MLLib
                 [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                    (FStar_Extraction_ML_Syntax.MLLib []))]])
          else (g2, [])
  
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____3274 = FStar_Options.debug_any ()  in
      if uu____3274
      then
        let msg =
          let uu____3282 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3282  in
        FStar_Util.measure_execution_time msg
          (fun uu____3290  -> extract' g m)
      else extract' g m
  