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
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____127  ->
         match uu____127 with
         | (bv,uu____135) ->
             let uu____136 =
               let uu____137 =
                 let uu____139 =
                   let uu____140 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                      in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____140  in
                 Some uu____139  in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____137  in
             let uu____141 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (uu____136, uu____141)) env bs
  
let extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Extraction_ML_UEnv.env *
            FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun def  ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let def1 =
            let uu____173 =
              let uu____174 = FStar_Syntax_Subst.compress def  in
              FStar_All.pipe_right uu____174 FStar_Syntax_Util.unmeta  in
            FStar_All.pipe_right uu____173 FStar_Syntax_Util.un_uinst  in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____176 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____186 -> def1  in
          let uu____187 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____194) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____207 -> ([], def2)  in
          match uu____187 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_219  ->
                     match uu___148_219 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____220 -> false) quals
                 in
              let uu____221 = binders_as_mlty_binders env bs  in
              (match uu____221 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____239 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                     FStar_All.pipe_right uu____239
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1))
                      in
                   let mangled_projector =
                     let uu____242 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_244  ->
                               match uu___149_244 with
                               | FStar_Syntax_Syntax.Projector uu____245 ->
                                   true
                               | uu____248 -> false))
                        in
                     if uu____242
                     then
                       let mname = mangle_projector_lid lid  in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None  in
                   let td =
                     let uu____264 =
                       let uu____275 = lident_as_mlsymbol lid  in
                       (assumed, uu____275, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                        in
                     [uu____264]  in
                   let def3 =
                     let uu____303 =
                       let uu____304 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid)
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____304  in
                     [uu____303; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                   let env2 =
                     let uu____306 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_308  ->
                               match uu___150_308 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____309 -> false))
                        in
                     if uu____306
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
  iquals: FStar_Syntax_Syntax.qualifier Prims.list }
let __proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iname
  
let __proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iparams
  
let __proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__ityp
  
let __proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__idatas
  
let __proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iquals
  
let print_ifamily : inductive_family -> Prims.unit =
  fun i  ->
    let uu____417 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____418 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____419 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____420 =
      let uu____421 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____426 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____427 =
                  let uu____428 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____428  in
                Prims.strcat uu____426 uu____427))
         in
      FStar_All.pipe_right uu____421 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____417 uu____418 uu____419
      uu____420
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____471 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____471 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____484,t2,l',nparams,uu____488) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____491 =
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____491 with
                                  | (bs',body) ->
                                      let uu____512 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
                                      (match uu____512 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____550  ->
                                                  fun uu____551  ->
                                                    match (uu____550,
                                                            uu____551)
                                                    with
                                                    | ((b',uu____561),
                                                       (b,uu____563)) ->
                                                        let uu____568 =
                                                          let uu____573 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          (b', uu____573)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____568)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____575 =
                                               let uu____578 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____578
                                                in
                                             FStar_All.pipe_right uu____575
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____583 -> []))
                      in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____584 -> []))
  
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
          let uu____627 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____627
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____632 =
            let uu____633 =
              let uu____636 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____636  in
            uu____633.FStar_Syntax_Syntax.n  in
          match uu____632 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____639) ->
              FStar_List.map
                (fun uu____652  ->
                   match uu____652 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____656;
                        FStar_Syntax_Syntax.sort = uu____657;_},uu____658)
                       -> ppname.FStar_Ident.idText) bs
          | uu____661 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____672 =
          let uu____673 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          fst uu____673  in
        let uu____676 =
          let uu____682 = lident_as_mlsymbol ctor.dname  in
          let uu____683 =
            let uu____687 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____687  in
          (uu____682, uu____683)  in
        (uu____672, uu____676)  in
      let extract_one_family env1 ind =
        let uu____716 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____716 with
        | (env2,vars) ->
            let uu____742 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____742 with
             | (env3,ctors) ->
                 let uu____791 = FStar_Syntax_Util.arrow_formals ind.ityp  in
                 (match uu____791 with
                  | (indices,uu____812) ->
                      let ml_params =
                        let uu____827 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____842  ->
                                    let uu____845 =
                                      let uu____846 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____846  in
                                    (uu____845, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____827  in
                      let tbody =
                        let uu____850 =
                          FStar_Util.find_opt
                            (fun uu___151_852  ->
                               match uu___151_852 with
                               | FStar_Syntax_Syntax.RecordType uu____853 ->
                                   true
                               | uu____858 -> false) ind.iquals
                           in
                        match uu____850 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____865 = FStar_List.hd ctors  in
                            (match uu____865 with
                             | (uu____876,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____894  ->
                                          match uu____894 with
                                          | (uu____899,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id])
                                                 in
                                              let uu____902 =
                                                lident_as_mlsymbol lid  in
                                              (uu____902, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____903 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____905 =
                        let uu____916 = lident_as_mlsymbol ind.iname  in
                        (false, uu____916, None, ml_params, (Some tbody))  in
                      (env3, uu____905)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____937,t,uu____939,uu____940,uu____941);
            FStar_Syntax_Syntax.sigrng = uu____942;
            FStar_Syntax_Syntax.sigquals = uu____943;
            FStar_Syntax_Syntax.sigmeta = uu____944;
            FStar_Syntax_Syntax.sigattrs = uu____945;_}::[],uu____946),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____955 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____955 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____982),quals) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____993 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____993 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1045 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1068 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1068);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1072 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1077 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1086 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1114 =
               let uu____1117 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1117 ml_name tysc
                 false false
                in
             match uu____1114 with
             | (g2,mangled_name) ->
                 ((let uu____1123 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1123
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
             (let uu____1135 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1135
              then
                let uu____1136 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1136
              else ());
             (let uu____1138 =
                let uu____1139 = FStar_Syntax_Subst.compress tm  in
                uu____1139.FStar_Syntax_Syntax.n  in
              match uu____1138 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1145) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1156 =
                    let uu____1161 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1161  in
                  (match uu____1156 with
                   | (uu____1190,uu____1191,tysc,uu____1193) ->
                       let uu____1194 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____1194, tysc))
              | uu____1195 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____1217 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1217
              then
                let uu____1218 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____1219 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1218
                  uu____1219
              else ());
             (let uu____1221 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____1221 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1231 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____1231  in
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
                  let uu____1254 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____1254 with
                   | (a_let,uu____1261,ty) ->
                       ((let uu____1264 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____1264
                         then
                           let uu____1265 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1265
                         else ());
                        (let uu____1267 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1272,uu____1273,mllb::[]),uu____1275)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1286 -> failwith "Impossible"  in
                         match uu____1267 with
                         | (exp,tysc) ->
                             ((let uu____1294 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____1294
                               then
                                 ((let uu____1296 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1296);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____1303 =
             let uu____1306 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr)  in
             match uu____1306 with
             | (return_tm,ty_sc) ->
                 let uu____1314 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____1314 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1303 with
            | (g1,return_decl) ->
                let uu____1326 =
                  let uu____1329 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr)  in
                  match uu____1329 with
                  | (bind_tm,ty_sc) ->
                      let uu____1337 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____1337 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1326 with
                 | (g2,bind_decl) ->
                     let uu____1349 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1349 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1361 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1364,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1368 =
             let uu____1369 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1371  ->
                       match uu___152_1371 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1372 -> false))
                in
             Prims.op_Negation uu____1369  in
           if uu____1368
           then (g, [])
           else
             (let uu____1378 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1378 with
              | (bs,uu____1390) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let uu____1402 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals uu____1402)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1404) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1413 =
             let uu____1418 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____1418 with
             | (tcenv,uu____1434,def_typ) ->
                 let uu____1438 = as_pair def_typ  in (tcenv, uu____1438)
              in
           (match uu____1413 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp  in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____1453 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____1453 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1455) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1479) ->
                   let uu____1484 =
                     let uu____1485 = FStar_Syntax_Subst.compress h'  in
                     uu____1485.FStar_Syntax_Syntax.n  in
                   (match uu____1484 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1489 =
                          let uu____1490 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule
                             in
                          FStar_Util.starts_with uu____1490 "FStar.Tactics"
                           in
                        Prims.op_Negation uu____1489
                    | uu____1491 -> false)
               | uu____1492 -> false  in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1517 =
                   let uu____1518 =
                     let uu____1519 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1519
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1518  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1517
                  in
               let lid_arg =
                 let uu____1521 =
                   let uu____1522 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1522  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1521  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____1529 =
                   let uu____1530 =
                     let uu____1531 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____1531  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1530  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1529  in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs
                  in
               let app =
                 let uu____1540 =
                   let uu____1541 =
                     let uu____1545 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation]
                        in
                     (h, uu____1545)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1541  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1540
                  in
               FStar_Extraction_ML_Syntax.MLM_Top app  in
             match snd lbs with
             | hd1::[] ->
                 let uu____1551 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp
                    in
                 (match uu____1551 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp  in
                      let uu____1569 =
                        let uu____1570 = FStar_Syntax_Subst.compress t  in
                        uu____1570.FStar_Syntax_Syntax.n  in
                      (match uu____1569 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h  in
                           let tac_lid =
                             let uu____1592 =
                               let uu____1597 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname
                                  in
                               uu____1597.FStar_Syntax_Syntax.fv_name  in
                             uu____1592.FStar_Syntax_Syntax.v  in
                           let assm_lid =
                             let uu____1602 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1602
                              in
                           let uu____1603 = is_tactic_decl assm_lid h1  in
                           if uu____1603
                           then
                             let uu____1605 =
                               let uu____1606 =
                                 let uu____1609 = FStar_List.hd args  in
                                 fst uu____1609  in
                               mk_registration tac_lid assm_lid uu____1606 bs
                                in
                             [uu____1605]
                           else []
                       | uu____1621 -> []))
             | uu____1622 -> []  in
           let uu____1624 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1624 with
            | (ml_let,uu____1632,uu____1633) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1638,bindings),uu____1640) ->
                     let uu____1647 =
                       FStar_List.fold_left2
                         (fun uu____1654  ->
                            fun ml_lb  ->
                              fun uu____1656  ->
                                match (uu____1654, uu____1656) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1669;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1671;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1672;_})
                                    ->
                                    let lb_lid =
                                      let uu____1686 =
                                        let uu____1691 =
                                          FStar_Util.right lbname  in
                                        uu____1691.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1686.FStar_Syntax_Syntax.v  in
                                    let uu____1695 =
                                      let uu____1698 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1700  ->
                                                match uu___153_1700 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1701 -> true
                                                | uu____1704 -> false))
                                         in
                                      if uu____1698
                                      then
                                        let mname =
                                          let uu____1708 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1708
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1709 =
                                          let uu____1712 =
                                            FStar_Util.right lbname  in
                                          let uu____1713 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1712 mname uu____1713
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1709 with
                                        | (env1,uu____1717) ->
                                            (env1,
                                              (let uu___158_1718 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1718.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1718.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1718.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1718.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1721 =
                                           let uu____1722 =
                                             let uu____1725 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1725
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1722
                                            in
                                         (uu____1721, ml_lb))
                                       in
                                    (match uu____1695 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs)
                        in
                     (match uu____1647 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1745  ->
                                 match uu___154_1745 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1747 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1752  ->
                                 match uu___155_1752 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1757));
                                     FStar_Syntax_Syntax.tk = uu____1758;
                                     FStar_Syntax_Syntax.pos = uu____1759;
                                     FStar_Syntax_Syntax.vars = uu____1760;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1765 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let uu____1769 =
                            let uu____1771 =
                              let uu____1773 =
                                let uu____1774 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1774
                                 in
                              [uu____1773;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____1771
                              tactic_registration_decl
                             in
                          (g1, uu____1769))
                 | uu____1778 ->
                     let uu____1779 =
                       let uu____1780 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1780
                        in
                     failwith uu____1779))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1785,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1789 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1789
           then
             let always_fail =
               let imp =
                 let uu____1796 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1796 with
                 | ([],t1) ->
                     let b =
                       let uu____1815 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1815
                        in
                     let uu____1816 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____1816 None
                 | (bs,t1) ->
                     let uu____1829 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____1829 None
                  in
               let uu___159_1830 = se  in
               let uu____1831 =
                 let uu____1832 =
                   let uu____1836 =
                     let uu____1840 =
                       let uu____1842 =
                         let uu____1843 =
                           let uu____1846 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_Util.Inr uu____1846  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1843;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____1842]  in
                     (false, uu____1840)  in
                   (uu____1836, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____1832  in
               {
                 FStar_Syntax_Syntax.sigel = uu____1831;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1830.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1830.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1830.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___159_1830.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____1852 = extract_sig g always_fail  in
             (match uu____1852 with
              | (g1,mlm) ->
                  let uu____1863 =
                    FStar_Util.find_map quals
                      (fun uu___156_1865  ->
                         match uu___156_1865 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1868 -> None)
                     in
                  (match uu____1863 with
                   | Some l ->
                       let uu____1873 =
                         let uu____1875 =
                           let uu____1876 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1876  in
                         let uu____1877 =
                           let uu____1879 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____1879]  in
                         uu____1875 :: uu____1877  in
                       (g1, uu____1873)
                   | uu____1881 ->
                       let uu____1883 =
                         FStar_Util.find_map quals
                           (fun uu___157_1885  ->
                              match uu___157_1885 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1888)
                                  -> Some l
                              | uu____1889 -> None)
                          in
                       (match uu____1883 with
                        | Some uu____1893 -> (g1, [])
                        | uu____1895 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1901 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____1901 with
            | (ml_main,uu____1909,uu____1910) ->
                let uu____1911 =
                  let uu____1913 =
                    let uu____1914 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1914  in
                  [uu____1913; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____1911))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1916 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1920 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1924 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1926 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1946 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____1946 FStar_Pervasives.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1974 = FStar_Options.debug_any ()  in
       if uu____1974
       then
         let uu____1975 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____1975
       else ());
      (let uu____1977 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___160_1980 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1980.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1980.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1980.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____1981 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____1981 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____1998 = FStar_Options.codegen ()  in
             match uu____1998 with
             | Some "Kremlin" -> true
             | uu____2000 -> false  in
           let uu____2002 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____2002
           then
             ((let uu____2007 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____2007);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  