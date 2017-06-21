open Prims
let fail_exp lid t =
  let uu____18 =
    let uu____21 =
      let uu____22 =
        let uu____32 =
          FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        let uu____33 =
          let uu____35 = FStar_Syntax_Syntax.iarg t  in
          let uu____36 =
            let uu____38 =
              let uu____39 =
                let uu____40 =
                  let uu____43 =
                    let uu____44 =
                      let uu____45 =
                        let uu____49 =
                          let uu____50 =
                            let uu____51 =
                              FStar_Syntax_Print.lid_to_string lid  in
                            Prims.strcat "Not yet implemented:" uu____51  in
                          FStar_Bytes.string_as_unicode_bytes uu____50  in
                        (uu____49, FStar_Range.dummyRange)  in
                      FStar_Const.Const_string uu____45  in
                    FStar_Syntax_Syntax.Tm_constant uu____44  in
                  FStar_Syntax_Syntax.mk uu____43  in
                uu____40 None FStar_Range.dummyRange  in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39  in
            [uu____38]  in
          uu____35 :: uu____36  in
        (uu____32, uu____33)  in
      FStar_Syntax_Syntax.Tm_app uu____22  in
    FStar_Syntax_Syntax.mk uu____21  in
  uu____18 None FStar_Range.dummyRange 
let mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x 
let lident_as_mlsymbol : FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText 
let as_pair uu___147_88 =
  match uu___147_88 with
  | a::b::[] -> (a, b)
  | uu____92 -> failwith "Expected a list with 2 elements" 
let rec extract_attr :
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.tyattr option =
  fun x  ->
    let uu____101 = FStar_Syntax_Subst.compress x  in
    match uu____101 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.tk = uu____104;
        FStar_Syntax_Syntax.pos = uu____105;
        FStar_Syntax_Syntax.vars = uu____106;_} when
        let uu____109 =
          let uu____110 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____110  in
        uu____109 = "FStar.Pervasives.PpxDeriving" ->
        Some FStar_Extraction_ML_Syntax.PpxDeriving
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____112;
             FStar_Syntax_Syntax.pos = uu____113;
             FStar_Syntax_Syntax.vars = uu____114;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (data,uu____116));
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____117;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____118;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____119;_},uu____120)::[]);
        FStar_Syntax_Syntax.tk = uu____121;
        FStar_Syntax_Syntax.pos = uu____122;
        FStar_Syntax_Syntax.vars = uu____123;_} when
        let uu____149 =
          let uu____150 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____150  in
        uu____149 = "FStar.Pervasives.PpxDerivingConstant" ->
        Some
          (FStar_Extraction_ML_Syntax.PpxDerivingConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____152);
        FStar_Syntax_Syntax.tk = uu____153;
        FStar_Syntax_Syntax.pos = uu____154;
        FStar_Syntax_Syntax.vars = uu____155;_} -> extract_attr x1
    | a ->
        ((let uu____164 = FStar_Syntax_Print.term_to_string a  in
          let uu____165 = FStar_Syntax_Print.tag_of_term a  in
          FStar_Util.print2 "Unrecognized attribute at extraction: %s (%s)\n"
            uu____164 uu____165);
         None)
  
let extract_attrs :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.tyattr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs 
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____204  ->
         match uu____204 with
         | (bv,uu____212) ->
             let uu____213 =
               let uu____214 =
                 let uu____216 =
                   let uu____217 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                      in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____217  in
                 Some uu____216  in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____214  in
             let uu____218 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (uu____213, uu____218)) env bs
  
let extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env *
              FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let def1 =
              let uu____256 =
                let uu____257 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____257 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____256 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____259 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____269 -> def1  in
            let uu____270 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____277) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____290 -> ([], def2)  in
            match uu____270 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___148_302  ->
                       match uu___148_302 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____303 -> false) quals
                   in
                let uu____304 = binders_as_mlty_binders env bs  in
                (match uu____304 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____322 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____322
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____325 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___149_327  ->
                                 match uu___149_327 with
                                 | FStar_Syntax_Syntax.Projector uu____328 ->
                                     true
                                 | uu____331 -> false))
                          in
                       if uu____325
                       then
                         let mname = mangle_projector_lid lid  in
                         Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else None  in
                     let attrs1 = extract_attrs attrs  in
                     let td =
                       let uu____351 =
                         let uu____364 = lident_as_mlsymbol lid  in
                         (assumed, uu____364, mangled_projector, ml_bs,
                           attrs1,
                           (Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____351]  in
                     let def3 =
                       let uu____397 =
                         let uu____398 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid)
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____398  in
                       [uu____397; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____400 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___150_402  ->
                                 match uu___150_402 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____403 -> false))
                          in
                       if uu____400
                       then env1
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                        in
                     (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let __proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
  
let __proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ =
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
  iattrs: FStar_Extraction_ML_Syntax.tyattrs }
let __proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iname
  
let __proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iparams
  
let __proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__ityp
  
let __proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__idatas
  
let __proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iquals
  
let __proj__Mkinductive_family__item__iattrs :
  inductive_family -> FStar_Extraction_ML_Syntax.tyattrs =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iattrs
  
let print_ifamily : inductive_family -> Prims.unit =
  fun i  ->
    let uu____532 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____533 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____534 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____535 =
      let uu____536 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____541 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____542 =
                  let uu____543 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____543  in
                Prims.strcat uu____541 uu____542))
         in
      FStar_All.pipe_right uu____536 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____532 uu____533 uu____534
      uu____535
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____586 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____586 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____599,t2,l',nparams,uu____603) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____606 =
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____606 with
                                  | (bs',body) ->
                                      let uu____627 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
                                      (match uu____627 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____665  ->
                                                  fun uu____666  ->
                                                    match (uu____665,
                                                            uu____666)
                                                    with
                                                    | ((b',uu____676),
                                                       (b,uu____678)) ->
                                                        let uu____683 =
                                                          let uu____688 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          (b', uu____688)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____683)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____690 =
                                               let uu____693 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____693
                                                in
                                             FStar_All.pipe_right uu____690
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____698 -> []))
                      in
                   let attrs = extract_attrs se.FStar_Syntax_Syntax.sigattrs
                      in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals);
                      iattrs = attrs
                    }])
          | uu____701 -> []))
  
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____744 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____744
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____749 =
            let uu____750 =
              let uu____753 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____753  in
            uu____750.FStar_Syntax_Syntax.n  in
          match uu____749 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____756) ->
              FStar_List.map
                (fun uu____769  ->
                   match uu____769 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____773;
                        FStar_Syntax_Syntax.sort = uu____774;_},uu____775)
                       -> ppname.FStar_Ident.idText) bs
          | uu____778 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____789 =
          let uu____790 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          fst uu____790  in
        let uu____793 =
          let uu____799 = lident_as_mlsymbol ctor.dname  in
          let uu____800 =
            let uu____804 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____804  in
          (uu____799, uu____800)  in
        (uu____789, uu____793)  in
      let extract_one_family env1 ind =
        let uu____834 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____834 with
        | (env2,vars) ->
            let uu____861 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____861 with
             | (env3,ctors) ->
                 let uu____911 = FStar_Syntax_Util.arrow_formals ind.ityp  in
                 (match uu____911 with
                  | (indices,uu____933) ->
                      let ml_params =
                        let uu____948 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____963  ->
                                    let uu____966 =
                                      let uu____967 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____967  in
                                    (uu____966, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____948  in
                      let tbody =
                        let uu____971 =
                          FStar_Util.find_opt
                            (fun uu___151_973  ->
                               match uu___151_973 with
                               | FStar_Syntax_Syntax.RecordType uu____974 ->
                                   true
                               | uu____979 -> false) ind.iquals
                           in
                        match uu____971 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____986 = FStar_List.hd ctors  in
                            (match uu____986 with
                             | (uu____997,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1015  ->
                                          match uu____1015 with
                                          | (uu____1020,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id])
                                                 in
                                              let uu____1023 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1023, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1024 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1026 =
                        let uu____1038 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1038, None, ml_params, (ind.iattrs),
                          (Some tbody))
                         in
                      (env3, uu____1026)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1060,t,uu____1062,uu____1063,uu____1064);
            FStar_Syntax_Syntax.sigrng = uu____1065;
            FStar_Syntax_Syntax.sigquals = uu____1066;
            FStar_Syntax_Syntax.sigmeta = uu____1067;
            FStar_Syntax_Syntax.sigattrs = uu____1068;_}::[],uu____1069),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1078 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1078 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1105),quals) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____1116 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____1116 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1172 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1195 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1195);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1199 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1204 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1213 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1241 =
               let uu____1244 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1244 ml_name tysc
                 false false
                in
             match uu____1241 with
             | (g2,mangled_name) ->
                 ((let uu____1250 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1250
                   then
                     FStar_Util.print1 "Mangled name: %s\n"
                       (fst mangled_name)
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc = None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     }  in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb])))))
              in
           let rec extract_fv tm =
             (let uu____1262 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1262
              then
                let uu____1263 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1263
              else ());
             (let uu____1265 =
                let uu____1266 = FStar_Syntax_Subst.compress tm  in
                uu____1266.FStar_Syntax_Syntax.n  in
              match uu____1265 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1272) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1283 =
                    let uu____1288 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1288  in
                  (match uu____1283 with
                   | (uu____1317,uu____1318,tysc,uu____1320) ->
                       let uu____1321 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____1321, tysc))
              | uu____1322 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____1344 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1344
              then
                let uu____1345 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____1346 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1345
                  uu____1346
              else ());
             (let uu____1348 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____1348 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1358 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____1358  in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Syntax_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn))
                     in
                  let lbs = (false, [lb])  in
                  let action_lb =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_let
                          (lbs, FStar_Syntax_Const.exp_false_bool))) None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                     in
                  let uu____1381 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____1381 with
                   | (a_let,uu____1388,ty) ->
                       ((let uu____1391 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____1391
                         then
                           let uu____1392 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1392
                         else ());
                        (let uu____1394 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1399,uu____1400,mllb::[]),uu____1402)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1413 -> failwith "Impossible"  in
                         match uu____1394 with
                         | (exp,tysc) ->
                             ((let uu____1421 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____1421
                               then
                                 ((let uu____1423 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1423);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____1430 =
             let uu____1433 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr)  in
             match uu____1433 with
             | (return_tm,ty_sc) ->
                 let uu____1441 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____1441 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1430 with
            | (g1,return_decl) ->
                let uu____1453 =
                  let uu____1456 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr)  in
                  match uu____1456 with
                  | (bind_tm,ty_sc) ->
                      let uu____1464 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____1464 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1453 with
                 | (g2,bind_decl) ->
                     let uu____1476 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1476 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1488 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1491,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____1497 =
             let uu____1498 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1500  ->
                       match uu___152_1500 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1501 -> false))
                in
             Prims.op_Negation uu____1498  in
           if uu____1497
           then (g, [])
           else
             (let uu____1507 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1507 with
              | (bs,uu____1519) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let uu____1531 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals attrs uu____1531)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1533) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1542 =
             let uu____1547 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____1547 with
             | (tcenv,uu____1563,def_typ) ->
                 let uu____1567 = as_pair def_typ  in (tcenv, uu____1567)
              in
           (match uu____1542 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp  in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____1582 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____1582 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1584) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng
              in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1608) ->
                   let uu____1613 =
                     let uu____1614 = FStar_Syntax_Subst.compress h'  in
                     uu____1614.FStar_Syntax_Syntax.n  in
                   (match uu____1613 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1618 =
                          let uu____1619 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule
                             in
                          FStar_Util.starts_with uu____1619 "FStar.Tactics"
                           in
                        Prims.op_Negation uu____1618
                    | uu____1620 -> false)
               | uu____1621 -> false  in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1646 =
                   let uu____1647 =
                     let uu____1648 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1648
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1647  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1646
                  in
               let lid_arg =
                 let uu____1650 =
                   let uu____1651 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1651  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1650  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____1658 =
                   let uu____1659 =
                     let uu____1660 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____1660  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1659  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1658  in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs
                  in
               let app =
                 let uu____1669 =
                   let uu____1670 =
                     let uu____1674 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation]
                        in
                     (h, uu____1674)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1670  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1669
                  in
               FStar_Extraction_ML_Syntax.MLM_Top app  in
             match snd lbs with
             | hd1::[] ->
                 let uu____1680 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp
                    in
                 (match uu____1680 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp  in
                      let uu____1698 =
                        let uu____1699 = FStar_Syntax_Subst.compress t  in
                        uu____1699.FStar_Syntax_Syntax.n  in
                      (match uu____1698 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h  in
                           let tac_lid =
                             let uu____1721 =
                               let uu____1726 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname
                                  in
                               uu____1726.FStar_Syntax_Syntax.fv_name  in
                             uu____1721.FStar_Syntax_Syntax.v  in
                           let assm_lid =
                             let uu____1731 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1731
                              in
                           let uu____1732 = is_tactic_decl assm_lid h1  in
                           if uu____1732
                           then
                             let uu____1734 =
                               let uu____1735 =
                                 let uu____1738 = FStar_List.hd args  in
                                 fst uu____1738  in
                               mk_registration tac_lid assm_lid uu____1735 bs
                                in
                             [uu____1734]
                           else []
                       | uu____1750 -> []))
             | uu____1751 -> []  in
           let uu____1753 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1753 with
            | (ml_let,uu____1761,uu____1762) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1767,bindings),uu____1769) ->
                     let uu____1776 =
                       FStar_List.fold_left2
                         (fun uu____1783  ->
                            fun ml_lb  ->
                              fun uu____1785  ->
                                match (uu____1783, uu____1785) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1798;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1800;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1801;_})
                                    ->
                                    let lb_lid =
                                      let uu____1815 =
                                        let uu____1820 =
                                          FStar_Util.right lbname  in
                                        uu____1820.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1815.FStar_Syntax_Syntax.v  in
                                    let uu____1824 =
                                      let uu____1827 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1829  ->
                                                match uu___153_1829 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1830 -> true
                                                | uu____1833 -> false))
                                         in
                                      if uu____1827
                                      then
                                        let mname =
                                          let uu____1837 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1837
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1838 =
                                          let uu____1841 =
                                            FStar_Util.right lbname  in
                                          let uu____1842 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1841 mname uu____1842
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1838 with
                                        | (env1,uu____1846) ->
                                            (env1,
                                              (let uu___158_1847 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1847.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1847.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1847.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1847.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1850 =
                                           let uu____1851 =
                                             let uu____1854 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1854
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1851
                                            in
                                         (uu____1850, ml_lb))
                                       in
                                    (match uu____1824 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs)
                        in
                     (match uu____1776 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1874  ->
                                 match uu___154_1874 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1876 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1881  ->
                                 match uu___155_1881 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1886));
                                     FStar_Syntax_Syntax.tk = uu____1887;
                                     FStar_Syntax_Syntax.pos = uu____1888;
                                     FStar_Syntax_Syntax.vars = uu____1889;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1894 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let uu____1898 =
                            let uu____1900 =
                              let uu____1902 =
                                let uu____1903 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1903
                                 in
                              [uu____1902;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____1900
                              tactic_registration_decl
                             in
                          (g1, uu____1898))
                 | uu____1907 ->
                     let uu____1908 =
                       let uu____1909 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1909
                        in
                     failwith uu____1908))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1914,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1918 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1918
           then
             let always_fail =
               let imp =
                 let uu____1925 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1925 with
                 | ([],t1) ->
                     let b =
                       let uu____1944 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1944
                        in
                     let uu____1945 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____1945 None
                 | (bs,t1) ->
                     let uu____1958 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____1958 None
                  in
               let uu___159_1959 = se  in
               let uu____1960 =
                 let uu____1961 =
                   let uu____1965 =
                     let uu____1969 =
                       let uu____1971 =
                         let uu____1972 =
                           let uu____1975 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_Util.Inr uu____1975  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1972;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____1971]  in
                     (false, uu____1969)  in
                   (uu____1965, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____1961  in
               {
                 FStar_Syntax_Syntax.sigel = uu____1960;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1959.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1959.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1959.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___159_1959.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____1981 = extract_sig g always_fail  in
             (match uu____1981 with
              | (g1,mlm) ->
                  let uu____1992 =
                    FStar_Util.find_map quals
                      (fun uu___156_1994  ->
                         match uu___156_1994 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1997 -> None)
                     in
                  (match uu____1992 with
                   | Some l ->
                       let uu____2002 =
                         let uu____2004 =
                           let uu____2005 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2005  in
                         let uu____2006 =
                           let uu____2008 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2008]  in
                         uu____2004 :: uu____2006  in
                       (g1, uu____2002)
                   | uu____2010 ->
                       let uu____2012 =
                         FStar_Util.find_map quals
                           (fun uu___157_2014  ->
                              match uu___157_2014 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2017)
                                  -> Some l
                              | uu____2018 -> None)
                          in
                       (match uu____2012 with
                        | Some uu____2022 -> (g1, [])
                        | uu____2024 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2030 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____2030 with
            | (ml_main,uu____2038,uu____2039) ->
                let uu____2040 =
                  let uu____2042 =
                    let uu____2043 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2043  in
                  [uu____2042; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____2040))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2045 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2049 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2053 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2055 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2075 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2075 FStar_Pervasives.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____2103 = FStar_Options.debug_any ()  in
       if uu____2103
       then
         let uu____2104 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____2104
       else ());
      (let uu____2106 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___160_2109 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_2109.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_2109.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_2109.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____2110 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____2110 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____2127 = FStar_Options.codegen ()  in
             match uu____2127 with
             | Some "Kremlin" -> true
             | uu____2129 -> false  in
           let uu____2131 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____2131
           then
             ((let uu____2136 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____2136);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  