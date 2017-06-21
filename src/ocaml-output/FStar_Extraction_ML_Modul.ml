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
let as_pair uu___148_88 =
  match uu___148_88 with
  | a::b::[] -> (a, b)
  | uu____92 -> failwith "Expected a list with 2 elements" 
let extract_attrs attrs =
  FStar_List.choose
    (fun uu___149_114  ->
       match uu___149_114 with
       | {
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____119;
                FStar_Syntax_Syntax.pos = uu____120;
                FStar_Syntax_Syntax.vars = uu____121;_},[]);
           FStar_Syntax_Syntax.tk = uu____122;
           FStar_Syntax_Syntax.pos = uu____123;
           FStar_Syntax_Syntax.vars = uu____124;_} when
           let uu____140 =
             let uu____141 = FStar_Syntax_Syntax.lid_of_fv fv  in
             FStar_Ident.string_of_lid uu____141  in
           uu____140 = "PpxDeriving" ->
           Some FStar_Extraction_ML_Syntax.PpxDeriving
       | {
           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                FStar_Syntax_Syntax.tk = uu____143;
                FStar_Syntax_Syntax.pos = uu____144;
                FStar_Syntax_Syntax.vars = uu____145;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_constant
                                                             (FStar_Const.Const_string
                                                             (data,uu____147));
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____148;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____149;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____150;_},uu____151)::[]);
           FStar_Syntax_Syntax.tk = uu____152;
           FStar_Syntax_Syntax.pos = uu____153;
           FStar_Syntax_Syntax.vars = uu____154;_} when
           let uu____180 =
             let uu____181 = FStar_Syntax_Syntax.lid_of_fv fv  in
             FStar_Ident.string_of_lid uu____181  in
           uu____180 = "PpxDerivingConstant" ->
           Some
             (FStar_Extraction_ML_Syntax.PpxDerivingConstant
                (FStar_Util.string_of_unicode data))
       | uu____182 -> None) attrs
  
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____216  ->
         match uu____216 with
         | (bv,uu____224) ->
             let uu____225 =
               let uu____226 =
                 let uu____228 =
                   let uu____229 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                      in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____229  in
                 Some uu____228  in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____226  in
             let uu____230 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (uu____225, uu____230)) env bs
  
let extract_typ_abbrev env fv quals attrs def =
  let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
  let def1 =
    let uu____285 =
      let uu____286 = FStar_Syntax_Subst.compress def  in
      FStar_All.pipe_right uu____286 FStar_Syntax_Util.unmeta  in
    FStar_All.pipe_right uu____285 FStar_Syntax_Util.un_uinst  in
  let def2 =
    match def1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_abs uu____288 ->
        FStar_Extraction_ML_Term.normalize_abs def1
    | uu____298 -> def1  in
  let uu____299 =
    match def2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____306) ->
        FStar_Syntax_Subst.open_term bs body
    | uu____319 -> ([], def2)  in
  match uu____299 with
  | (bs,body) ->
      let assumed =
        FStar_Util.for_some
          (fun uu___150_331  ->
             match uu___150_331 with
             | FStar_Syntax_Syntax.Assumption  -> true
             | uu____332 -> false) quals
         in
      let uu____333 = binders_as_mlty_binders env bs  in
      (match uu____333 with
       | (env1,ml_bs) ->
           let body1 =
             let uu____351 = FStar_Extraction_ML_Term.term_as_mlty env1 body
                in
             FStar_All.pipe_right uu____351
               (FStar_Extraction_ML_Util.eraseTypeDeep
                  (FStar_Extraction_ML_Util.udelta_unfold env1))
              in
           let mangled_projector =
             let uu____354 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___151_356  ->
                       match uu___151_356 with
                       | FStar_Syntax_Syntax.Projector uu____357 -> true
                       | uu____360 -> false))
                in
             if uu____354
             then
               let mname = mangle_projector_lid lid  in
               Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
             else None  in
           let attrs1 = extract_attrs attrs  in
           let td =
             let uu____380 =
               let uu____393 = lident_as_mlsymbol lid  in
               (assumed, uu____393, mangled_projector, ml_bs, attrs1,
                 (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                in
             [uu____380]  in
           let def3 =
             let uu____426 =
               let uu____427 =
                 FStar_Extraction_ML_Util.mlloc_of_range
                   (FStar_Ident.range_of_lid lid)
                  in
               FStar_Extraction_ML_Syntax.MLM_Loc uu____427  in
             [uu____426; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
           let env2 =
             let uu____429 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_431  ->
                       match uu___152_431 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.New  -> true
                       | uu____432 -> false))
                in
             if uu____429
             then env1
             else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td  in
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
    let uu____561 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____562 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____563 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____564 =
      let uu____565 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____570 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____571 =
                  let uu____572 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____572  in
                Prims.strcat uu____570 uu____571))
         in
      FStar_All.pipe_right uu____565 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____561 uu____562 uu____563
      uu____564
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____615 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____615 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____628,t2,l',nparams,uu____632) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____635 =
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____635 with
                                  | (bs',body) ->
                                      let uu____656 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
                                      (match uu____656 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____694  ->
                                                  fun uu____695  ->
                                                    match (uu____694,
                                                            uu____695)
                                                    with
                                                    | ((b',uu____705),
                                                       (b,uu____707)) ->
                                                        let uu____712 =
                                                          let uu____717 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          (b', uu____717)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____712)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____719 =
                                               let uu____722 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____722
                                                in
                                             FStar_All.pipe_right uu____719
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____727 -> []))
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
          | uu____730 -> []))
  
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
          let uu____773 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____773
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____778 =
            let uu____779 =
              let uu____782 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____782  in
            uu____779.FStar_Syntax_Syntax.n  in
          match uu____778 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____785) ->
              FStar_List.map
                (fun uu____798  ->
                   match uu____798 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____802;
                        FStar_Syntax_Syntax.sort = uu____803;_},uu____804)
                       -> ppname.FStar_Ident.idText) bs
          | uu____807 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____818 =
          let uu____819 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          fst uu____819  in
        let uu____822 =
          let uu____828 = lident_as_mlsymbol ctor.dname  in
          let uu____829 =
            let uu____833 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____833  in
          (uu____828, uu____829)  in
        (uu____818, uu____822)  in
      let extract_one_family env1 ind =
        let uu____863 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____863 with
        | (env2,vars) ->
            let uu____890 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____890 with
             | (env3,ctors) ->
                 let uu____940 = FStar_Syntax_Util.arrow_formals ind.ityp  in
                 (match uu____940 with
                  | (indices,uu____962) ->
                      let ml_params =
                        let uu____977 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____992  ->
                                    let uu____995 =
                                      let uu____996 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____996  in
                                    (uu____995, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____977  in
                      let tbody =
                        let uu____1000 =
                          FStar_Util.find_opt
                            (fun uu___153_1002  ->
                               match uu___153_1002 with
                               | FStar_Syntax_Syntax.RecordType uu____1003 ->
                                   true
                               | uu____1008 -> false) ind.iquals
                           in
                        match uu____1000 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1015 = FStar_List.hd ctors  in
                            (match uu____1015 with
                             | (uu____1026,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1044  ->
                                          match uu____1044 with
                                          | (uu____1049,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id])
                                                 in
                                              let uu____1052 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1052, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1053 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1055 =
                        let uu____1067 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1067, None, ml_params, (ind.iattrs),
                          (Some tbody))
                         in
                      (env3, uu____1055)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1089,t,uu____1091,uu____1092,uu____1093);
            FStar_Syntax_Syntax.sigrng = uu____1094;
            FStar_Syntax_Syntax.sigquals = uu____1095;
            FStar_Syntax_Syntax.sigmeta = uu____1096;
            FStar_Syntax_Syntax.sigattrs = uu____1097;_}::[],uu____1098),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1107 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1107 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1134),quals) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____1145 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____1145 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1201 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1224 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1224);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1228 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1233 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1242 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1270 =
               let uu____1273 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1273 ml_name tysc
                 false false
                in
             match uu____1270 with
             | (g2,mangled_name) ->
                 ((let uu____1279 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1279
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
             (let uu____1291 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1291
              then
                let uu____1292 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1292
              else ());
             (let uu____1294 =
                let uu____1295 = FStar_Syntax_Subst.compress tm  in
                uu____1295.FStar_Syntax_Syntax.n  in
              match uu____1294 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1301) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1312 =
                    let uu____1317 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1317  in
                  (match uu____1312 with
                   | (uu____1346,uu____1347,tysc,uu____1349) ->
                       let uu____1350 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____1350, tysc))
              | uu____1351 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____1373 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1373
              then
                let uu____1374 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____1375 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1374
                  uu____1375
              else ());
             (let uu____1377 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____1377 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1387 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____1387  in
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
                  let uu____1410 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____1410 with
                   | (a_let,uu____1417,ty) ->
                       ((let uu____1420 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____1420
                         then
                           let uu____1421 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1421
                         else ());
                        (let uu____1423 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1428,uu____1429,mllb::[]),uu____1431)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1442 -> failwith "Impossible"  in
                         match uu____1423 with
                         | (exp,tysc) ->
                             ((let uu____1450 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____1450
                               then
                                 ((let uu____1452 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1452);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____1459 =
             let uu____1462 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr)  in
             match uu____1462 with
             | (return_tm,ty_sc) ->
                 let uu____1470 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____1470 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1459 with
            | (g1,return_decl) ->
                let uu____1482 =
                  let uu____1485 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr)  in
                  match uu____1485 with
                  | (bind_tm,ty_sc) ->
                      let uu____1493 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____1493 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1482 with
                 | (g2,bind_decl) ->
                     let uu____1505 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1505 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1517 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1520,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____1526 =
             let uu____1527 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___154_1529  ->
                       match uu___154_1529 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1530 -> false))
                in
             Prims.op_Negation uu____1527  in
           if uu____1526
           then (g, [])
           else
             (let uu____1536 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1536 with
              | (bs,uu____1548) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let uu____1560 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals attrs uu____1560)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1562) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1571 =
             let uu____1576 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____1576 with
             | (tcenv,uu____1592,def_typ) ->
                 let uu____1596 = as_pair def_typ  in (tcenv, uu____1596)
              in
           (match uu____1571 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp  in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____1611 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____1611 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1613) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1637) ->
                   let uu____1642 =
                     let uu____1643 = FStar_Syntax_Subst.compress h'  in
                     uu____1643.FStar_Syntax_Syntax.n  in
                   (match uu____1642 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1647 =
                          let uu____1648 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule
                             in
                          FStar_Util.starts_with uu____1648 "FStar.Tactics"
                           in
                        Prims.op_Negation uu____1647
                    | uu____1649 -> false)
               | uu____1650 -> false  in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1675 =
                   let uu____1676 =
                     let uu____1677 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1677
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1676  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1675
                  in
               let lid_arg =
                 let uu____1679 =
                   let uu____1680 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1680  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1679  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____1687 =
                   let uu____1688 =
                     let uu____1689 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____1689  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1688  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1687  in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs
                  in
               let app =
                 let uu____1698 =
                   let uu____1699 =
                     let uu____1703 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation]
                        in
                     (h, uu____1703)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1699  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1698
                  in
               FStar_Extraction_ML_Syntax.MLM_Top app  in
             match snd lbs with
             | hd1::[] ->
                 let uu____1709 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp
                    in
                 (match uu____1709 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp  in
                      let uu____1727 =
                        let uu____1728 = FStar_Syntax_Subst.compress t  in
                        uu____1728.FStar_Syntax_Syntax.n  in
                      (match uu____1727 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h  in
                           let tac_lid =
                             let uu____1750 =
                               let uu____1755 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname
                                  in
                               uu____1755.FStar_Syntax_Syntax.fv_name  in
                             uu____1750.FStar_Syntax_Syntax.v  in
                           let assm_lid =
                             let uu____1760 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1760
                              in
                           let uu____1761 = is_tactic_decl assm_lid h1  in
                           if uu____1761
                           then
                             let uu____1763 =
                               let uu____1764 =
                                 let uu____1767 = FStar_List.hd args  in
                                 fst uu____1767  in
                               mk_registration tac_lid assm_lid uu____1764 bs
                                in
                             [uu____1763]
                           else []
                       | uu____1779 -> []))
             | uu____1780 -> []  in
           let uu____1782 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1782 with
            | (ml_let,uu____1790,uu____1791) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1796,bindings),uu____1798) ->
                     let uu____1805 =
                       FStar_List.fold_left2
                         (fun uu____1812  ->
                            fun ml_lb  ->
                              fun uu____1814  ->
                                match (uu____1812, uu____1814) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1827;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1829;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1830;_})
                                    ->
                                    let lb_lid =
                                      let uu____1844 =
                                        let uu____1849 =
                                          FStar_Util.right lbname  in
                                        uu____1849.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1844.FStar_Syntax_Syntax.v  in
                                    let uu____1853 =
                                      let uu____1856 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___155_1858  ->
                                                match uu___155_1858 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1859 -> true
                                                | uu____1862 -> false))
                                         in
                                      if uu____1856
                                      then
                                        let mname =
                                          let uu____1866 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1866
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1867 =
                                          let uu____1870 =
                                            FStar_Util.right lbname  in
                                          let uu____1871 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1870 mname uu____1871
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1867 with
                                        | (env1,uu____1875) ->
                                            (env1,
                                              (let uu___160_1876 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___160_1876.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___160_1876.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___160_1876.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___160_1876.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1879 =
                                           let uu____1880 =
                                             let uu____1883 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1883
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1880
                                            in
                                         (uu____1879, ml_lb))
                                       in
                                    (match uu____1853 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs)
                        in
                     (match uu____1805 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___156_1903  ->
                                 match uu___156_1903 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1905 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___157_1910  ->
                                 match uu___157_1910 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1915));
                                     FStar_Syntax_Syntax.tk = uu____1916;
                                     FStar_Syntax_Syntax.pos = uu____1917;
                                     FStar_Syntax_Syntax.vars = uu____1918;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1923 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let uu____1927 =
                            let uu____1929 =
                              let uu____1931 =
                                let uu____1932 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1932
                                 in
                              [uu____1931;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____1929
                              tactic_registration_decl
                             in
                          (g1, uu____1927))
                 | uu____1936 ->
                     let uu____1937 =
                       let uu____1938 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1938
                        in
                     failwith uu____1937))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1943,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1947 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1947
           then
             let always_fail =
               let imp =
                 let uu____1954 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1954 with
                 | ([],t1) ->
                     let b =
                       let uu____1973 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1973
                        in
                     let uu____1974 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____1974 None
                 | (bs,t1) ->
                     let uu____1987 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____1987 None
                  in
               let uu___161_1988 = se  in
               let uu____1989 =
                 let uu____1990 =
                   let uu____1994 =
                     let uu____1998 =
                       let uu____2000 =
                         let uu____2001 =
                           let uu____2004 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_Util.Inr uu____2004  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2001;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____2000]  in
                     (false, uu____1998)  in
                   (uu____1994, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____1990  in
               {
                 FStar_Syntax_Syntax.sigel = uu____1989;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_1988.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_1988.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_1988.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_1988.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2010 = extract_sig g always_fail  in
             (match uu____2010 with
              | (g1,mlm) ->
                  let uu____2021 =
                    FStar_Util.find_map quals
                      (fun uu___158_2023  ->
                         match uu___158_2023 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____2026 -> None)
                     in
                  (match uu____2021 with
                   | Some l ->
                       let uu____2031 =
                         let uu____2033 =
                           let uu____2034 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____2034  in
                         let uu____2035 =
                           let uu____2037 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____2037]  in
                         uu____2033 :: uu____2035  in
                       (g1, uu____2031)
                   | uu____2039 ->
                       let uu____2041 =
                         FStar_Util.find_map quals
                           (fun uu___159_2043  ->
                              match uu___159_2043 with
                              | FStar_Syntax_Syntax.Projector (l,uu____2046)
                                  -> Some l
                              | uu____2047 -> None)
                          in
                       (match uu____2041 with
                        | Some uu____2051 -> (g1, [])
                        | uu____2053 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2059 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____2059 with
            | (ml_main,uu____2067,uu____2068) ->
                let uu____2069 =
                  let uu____2071 =
                    let uu____2072 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____2072  in
                  [uu____2071; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____2069))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____2074 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____2078 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____2082 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2084 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____2104 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2104 FStar_Pervasives.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____2132 = FStar_Options.debug_any ()  in
       if uu____2132
       then
         let uu____2133 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____2133
       else ());
      (let uu____2135 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___162_2138 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___162_2138.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___162_2138.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___162_2138.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____2139 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____2139 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____2156 = FStar_Options.codegen ()  in
             match uu____2156 with
             | Some "Kremlin" -> true
             | uu____2158 -> false  in
           let uu____2160 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____2160
           then
             ((let uu____2165 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____2165);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  