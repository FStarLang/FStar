open Prims
let fail_exp lid t =
  let uu____18 =
    let uu____21 =
      let uu____22 =
        let uu____32 =
          FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
        let uu____33 =
          let uu____35 = FStar_Syntax_Syntax.iarg t in
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
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____51 in
                          FStar_Bytes.string_as_unicode_bytes uu____50 in
                        (uu____49, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____45 in
                    FStar_Syntax_Syntax.Tm_constant uu____44 in
                  FStar_Syntax_Syntax.mk uu____43 in
                uu____40 None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
            [uu____38] in
          uu____35 :: uu____36 in
        (uu____32, uu____33) in
      FStar_Syntax_Syntax.Tm_app uu____22 in
    FStar_Syntax_Syntax.mk uu____21 in
  uu____18 None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
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
                   let uu____140 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____140 in
                 Some uu____139 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____137 in
             let uu____141 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____136, uu____141)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mlmodule1
            Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun def  ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let def1 =
            let uu____173 =
              let uu____174 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____174 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____173 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____176 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____186 -> def1 in
          let uu____187 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____194) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____207 -> ([], def2) in
          match uu____187 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_219  ->
                     match uu___148_219 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____220 -> false) quals in
              let uu____221 = binders_as_mlty_binders env bs in
              (match uu____221 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____239 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____239
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____242 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_244  ->
                               match uu___149_244 with
                               | FStar_Syntax_Syntax.Projector uu____245 ->
                                   true
                               | uu____248 -> false)) in
                     if uu____242
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____264 =
                       let uu____275 = lident_as_mlsymbol lid in
                       (assumed, uu____275, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____264] in
                   let def3 =
                     let uu____303 =
                       let uu____304 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____304 in
                     [uu____303; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____306 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_308  ->
                               match uu___150_308 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____309 -> false)) in
                     if uu____306
                     then env1
                     else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                   (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}
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
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;}
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals;_} -> __fname__iquals
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____417 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____418 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____419 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____420 =
      let uu____421 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____426 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____427 =
                  let uu____428 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____428 in
                Prims.strcat uu____426 uu____427)) in
      FStar_All.pipe_right uu____421 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____417 uu____418 uu____419
      uu____420
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____471 = FStar_Syntax_Subst.open_term bs t in
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
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____491 with
                                  | (bs',body) ->
                                      let uu____512 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
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
                                                              b in
                                                          (b', uu____573) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____568)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____575 =
                                               let uu____578 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____578 in
                                             FStar_All.pipe_right uu____575
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____583 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____584 -> []))
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____627 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____627 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____632 =
            let uu____633 =
              let uu____636 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____636 in
            uu____633.FStar_Syntax_Syntax.n in
          match uu____632 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____639) ->
              FStar_List.map
                (fun uu____652  ->
                   match uu____652 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____656;
                        FStar_Syntax_Syntax.sort = uu____657;_},uu____658)
                       -> ppname.FStar_Ident.idText) bs
          | uu____661 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____672 =
          let uu____673 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____673 in
        let uu____676 =
          let uu____682 = lident_as_mlsymbol ctor.dname in
          let uu____683 =
            let uu____687 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____687 in
          (uu____682, uu____683) in
        (uu____672, uu____676) in
      let extract_one_family env1 ind =
        let uu____716 = binders_as_mlty_binders env1 ind.iparams in
        match uu____716 with
        | (env2,vars) ->
            let uu____742 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____742 with
             | (env3,ctors) ->
                 let uu____791 = FStar_Syntax_Util.arrow_formals ind.ityp in
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
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____846 in
                                    (uu____845, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____827 in
                      let tbody =
                        let uu____850 =
                          FStar_Util.find_opt
                            (fun uu___151_852  ->
                               match uu___151_852 with
                               | FStar_Syntax_Syntax.RecordType uu____853 ->
                                   true
                               | uu____858 -> false) ind.iquals in
                        match uu____850 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____865 = FStar_List.hd ctors in
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
                                                  (FStar_List.append ns [id]) in
                                              let uu____902 =
                                                lident_as_mlsymbol lid in
                                              (uu____902, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____903 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____905 =
                        let uu____916 = lident_as_mlsymbol ind.iname in
                        (false, uu____916, None, ml_params, (Some tbody)) in
                      (env3, uu____905))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____937,t,uu____939,uu____940,uu____941);
            FStar_Syntax_Syntax.sigrng = uu____942;
            FStar_Syntax_Syntax.sigquals = uu____943;
            FStar_Syntax_Syntax.sigmeta = uu____944;_}::[],uu____945),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____953 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____953 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____980),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____991 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____991 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1043 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1066 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1066);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1070 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1075 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1084 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1112 =
               let uu____1115 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1115 ml_name tysc
                 false false in
             match uu____1112 with
             | (g2,mangled_name) ->
                 ((let uu____1121 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1121
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
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____1133 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1133
              then
                let uu____1134 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1134
              else ());
             (let uu____1136 =
                let uu____1137 = FStar_Syntax_Subst.compress tm in
                uu____1137.FStar_Syntax_Syntax.n in
              match uu____1136 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1143) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1154 =
                    let uu____1159 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1159 in
                  (match uu____1154 with
                   | (uu____1188,uu____1189,tysc,uu____1191) ->
                       let uu____1192 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1192, tysc))
              | uu____1193 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1215 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1215
              then
                let uu____1216 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1217 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1216
                  uu____1217
              else ());
             (let uu____1219 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1219 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1229 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1229 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Syntax_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_let
                          (lbs, FStar_Syntax_Const.exp_false_bool))) None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____1252 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1252 with
                   | (a_let,uu____1259,ty) ->
                       ((let uu____1262 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1262
                         then
                           let uu____1263 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1263
                         else ());
                        (let uu____1265 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1270,uu____1271,mllb::[]),uu____1273)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1284 -> failwith "Impossible" in
                         match uu____1265 with
                         | (exp,tysc) ->
                             ((let uu____1292 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1292
                               then
                                 ((let uu____1294 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1294);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1301 =
             let uu____1304 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1304 with
             | (return_tm,ty_sc) ->
                 let uu____1312 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1312 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1301 with
            | (g1,return_decl) ->
                let uu____1324 =
                  let uu____1327 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1327 with
                  | (bind_tm,ty_sc) ->
                      let uu____1335 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1335 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1324 with
                 | (g2,bind_decl) ->
                     let uu____1347 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1347 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1359 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1362,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1366 =
             let uu____1367 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1369  ->
                       match uu___152_1369 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1370 -> false)) in
             Prims.op_Negation uu____1367 in
           if uu____1366
           then (g, [])
           else
             (let uu____1376 = FStar_Syntax_Util.arrow_formals t in
              match uu____1376 with
              | (bs,uu____1388) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1400 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1400)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1402,uu____1403)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1414 =
             let uu____1419 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1419 with
             | (tcenv,uu____1435,def_typ) ->
                 let uu____1439 = as_pair def_typ in (tcenv, uu____1439) in
           (match uu____1414 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1454 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1454 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1456,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1481) ->
                   let uu____1486 =
                     let uu____1487 = FStar_Syntax_Subst.compress h' in
                     uu____1487.FStar_Syntax_Syntax.n in
                   (match uu____1486 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1491 =
                          let uu____1492 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____1492 "FStar.Tactics" in
                        Prims.op_Negation uu____1491
                    | uu____1493 -> false)
               | uu____1494 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1515 =
                   let uu____1516 =
                     let uu____1517 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1517 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1516 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1515 in
               let lid_arg =
                 let uu____1519 =
                   let uu____1520 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1520 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1519 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____1527 =
                   let uu____1528 =
                     let uu____1529 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____1529 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1528 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1527 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____1538 =
                   let uu____1539 =
                     let uu____1543 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____1543) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1539 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1538 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match snd lbs with
             | hd1::[] ->
                 let uu____1549 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____1549 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____1567 =
                        let uu____1568 = FStar_Syntax_Subst.compress t in
                        uu____1568.FStar_Syntax_Syntax.n in
                      (match uu____1567 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____1590 =
                               let uu____1595 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____1595.FStar_Syntax_Syntax.fv_name in
                             uu____1590.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____1600 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1600 in
                           let uu____1601 = is_tactic_decl assm_lid h1 in
                           if uu____1601
                           then
                             let uu____1603 =
                               let uu____1604 =
                                 let uu____1605 = FStar_List.hd args in
                                 fst uu____1605 in
                               mk_registration tac_lid assm_lid uu____1604 bs in
                             [uu____1603]
                           else []
                       | uu____1617 -> []))
             | uu____1618 -> [] in
           let uu____1620 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1620 with
            | (ml_let,uu____1628,uu____1629) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1634,bindings),uu____1636) ->
                     let uu____1643 =
                       FStar_List.fold_left2
                         (fun uu____1650  ->
                            fun ml_lb  ->
                              fun uu____1652  ->
                                match (uu____1650, uu____1652) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1665;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1667;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1668;_})
                                    ->
                                    let lb_lid =
                                      let uu____1682 =
                                        let uu____1687 =
                                          FStar_Util.right lbname in
                                        uu____1687.FStar_Syntax_Syntax.fv_name in
                                      uu____1682.FStar_Syntax_Syntax.v in
                                    let uu____1691 =
                                      let uu____1694 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1696  ->
                                                match uu___153_1696 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1697 -> true
                                                | uu____1700 -> false)) in
                                      if uu____1694
                                      then
                                        let mname =
                                          let uu____1704 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1704
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1705 =
                                          let uu____1708 =
                                            FStar_Util.right lbname in
                                          let uu____1709 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1708 mname uu____1709
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1705 with
                                        | (env1,uu____1713) ->
                                            (env1,
                                              (let uu___158_1714 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1714.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1714.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1714.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1714.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1717 =
                                           let uu____1718 =
                                             let uu____1721 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1721
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1718 in
                                         (uu____1717, ml_lb)) in
                                    (match uu____1691 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1643 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1741  ->
                                 match uu___154_1741 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1743 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1748  ->
                                 match uu___155_1748 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1753));
                                     FStar_Syntax_Syntax.tk = uu____1754;
                                     FStar_Syntax_Syntax.pos = uu____1755;
                                     FStar_Syntax_Syntax.vars = uu____1756;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1761 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1765 =
                            let uu____1767 =
                              let uu____1769 =
                                let uu____1770 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1770 in
                              [uu____1769;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____1767
                              tactic_registration_decl in
                          (g1, uu____1765))
                 | uu____1774 ->
                     let uu____1775 =
                       let uu____1776 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1776 in
                     failwith uu____1775))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1781,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1785 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1785
           then
             let always_fail =
               let imp =
                 let uu____1792 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1792 with
                 | ([],t1) ->
                     let b =
                       let uu____1811 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1811 in
                     let uu____1812 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1812 None
                 | (bs,t1) ->
                     let uu____1825 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1825 None in
               let uu___159_1826 = se in
               let uu____1827 =
                 let uu____1828 =
                   let uu____1834 =
                     let uu____1838 =
                       let uu____1840 =
                         let uu____1841 =
                           let uu____1844 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1844 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1841;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1840] in
                     (false, uu____1838) in
                   (uu____1834, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1828 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1827;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1826.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1826.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1826.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1851 = extract_sig g always_fail in
             (match uu____1851 with
              | (g1,mlm) ->
                  let uu____1862 =
                    FStar_Util.find_map quals
                      (fun uu___156_1864  ->
                         match uu___156_1864 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1867 -> None) in
                  (match uu____1862 with
                   | Some l ->
                       let uu____1872 =
                         let uu____1874 =
                           let uu____1875 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1875 in
                         let uu____1876 =
                           let uu____1878 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1878] in
                         uu____1874 :: uu____1876 in
                       (g1, uu____1872)
                   | uu____1880 ->
                       let uu____1882 =
                         FStar_Util.find_map quals
                           (fun uu___157_1884  ->
                              match uu___157_1884 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1887)
                                  -> Some l
                              | uu____1888 -> None) in
                       (match uu____1882 with
                        | Some uu____1892 -> (g1, [])
                        | uu____1894 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1900 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1900 with
            | (ml_main,uu____1908,uu____1909) ->
                let uu____1910 =
                  let uu____1912 =
                    let uu____1913 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1913 in
                  [uu____1912; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1910))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1915 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1919 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1923 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1925 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1945 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1945 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1973 = FStar_Options.debug_any () in
       if uu____1973
       then
         let uu____1974 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1974
       else ());
      (let uu____1976 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_1979 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1979.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1979.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1979.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1980 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1980 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1997 = FStar_Options.codegen () in
             match uu____1997 with
             | Some "Kremlin" -> true
             | uu____1999 -> false in
           let uu____2001 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____2001
           then
             ((let uu____2006 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____2006);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))