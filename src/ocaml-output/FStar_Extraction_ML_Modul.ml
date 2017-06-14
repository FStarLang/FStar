open Prims
let fail_exp lid t =
  let uu____15 =
    let uu____18 =
      let uu____19 =
        let uu____29 =
          FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
        let uu____30 =
          let uu____32 = FStar_Syntax_Syntax.iarg t in
          let uu____33 =
            let uu____35 =
              let uu____36 =
                let uu____37 =
                  let uu____40 =
                    let uu____41 =
                      let uu____42 =
                        let uu____46 =
                          let uu____47 =
                            let uu____48 =
                              FStar_Syntax_Print.lid_to_string lid in
                            Prims.strcat "Not yet implemented:" uu____48 in
                          FStar_Bytes.string_as_unicode_bytes uu____47 in
                        (uu____46, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____42 in
                    FStar_Syntax_Syntax.Tm_constant uu____41 in
                  FStar_Syntax_Syntax.mk uu____40 in
                uu____37 None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____36 in
            [uu____35] in
          uu____32 :: uu____33 in
        (uu____29, uu____30) in
      FStar_Syntax_Syntax.Tm_app uu____19 in
    FStar_Syntax_Syntax.mk uu____18 in
  uu____15 None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol: FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair uu___148_81 =
  match uu___148_81 with
  | a::b::[] -> (a, b)
  | uu____85 -> failwith "Expected a list with 2 elements"
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____117  ->
         match uu____117 with
         | (bv,uu____125) ->
             let uu____126 =
               let uu____127 =
                 let uu____129 =
                   let uu____130 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____130 in
                 Some uu____129 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____127 in
             let uu____131 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____126, uu____131)) env bs
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
            let uu____159 =
              let uu____160 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____160 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____159 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____162 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____177 -> def1 in
          let uu____178 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____185) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____208 -> ([], def2) in
          match uu____178 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___149_220  ->
                     match uu___149_220 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____221 -> false) quals in
              let uu____222 = binders_as_mlty_binders env bs in
              (match uu____222 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____240 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____240
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____243 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_245  ->
                               match uu___150_245 with
                               | FStar_Syntax_Syntax.Projector uu____246 ->
                                   true
                               | uu____249 -> false)) in
                     if uu____243
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____265 =
                       let uu____276 = lident_as_mlsymbol lid in
                       (assumed, uu____276, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____265] in
                   let def3 =
                     let uu____304 =
                       let uu____305 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____305 in
                     [uu____304; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____307 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___151_309  ->
                               match uu___151_309 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____310 -> false)) in
                     if uu____307
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
    let uu____410 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____411 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____412 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____413 =
      let uu____414 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____419 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____420 =
                  let uu____421 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____421 in
                Prims.strcat uu____419 uu____420)) in
      FStar_All.pipe_right uu____414 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____410 uu____411 uu____412
      uu____413
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____459 = FStar_Syntax_Subst.open_term bs t in
              (match uu____459 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____472,t2,l',nparams,uu____476) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____479 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____479 with
                                  | (bs',body) ->
                                      let uu____500 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____500 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____538  ->
                                                  fun uu____539  ->
                                                    match (uu____538,
                                                            uu____539)
                                                    with
                                                    | ((b',uu____549),
                                                       (b,uu____551)) ->
                                                        let uu____556 =
                                                          let uu____561 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____561) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____556)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____563 =
                                               let uu____566 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____566 in
                                             FStar_All.pipe_right uu____563
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____571 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____572 -> []))
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
          let uu____613 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____613 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____618 =
            let uu____619 =
              let uu____622 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____622 in
            uu____619.FStar_Syntax_Syntax.n in
          match uu____618 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____625) ->
              FStar_List.map
                (fun uu____638  ->
                   match uu____638 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____642;
                        FStar_Syntax_Syntax.sort = uu____643;_},uu____644)
                       -> ppname.FStar_Ident.idText) bs
          | uu____647 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____658 =
          let uu____659 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____659 in
        let uu____662 =
          let uu____668 = lident_as_mlsymbol ctor.dname in
          let uu____669 =
            let uu____673 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____673 in
          (uu____668, uu____669) in
        (uu____658, uu____662) in
      let extract_one_family env1 ind =
        let uu____702 = binders_as_mlty_binders env1 ind.iparams in
        match uu____702 with
        | (env2,vars) ->
            let uu____728 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____728 with
             | (env3,ctors) ->
                 let uu____777 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____777 with
                  | (indices,uu____798) ->
                      let ml_params =
                        let uu____813 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____828  ->
                                    let uu____831 =
                                      let uu____832 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____832 in
                                    (uu____831, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____813 in
                      let tbody =
                        let uu____836 =
                          FStar_Util.find_opt
                            (fun uu___152_838  ->
                               match uu___152_838 with
                               | FStar_Syntax_Syntax.RecordType uu____839 ->
                                   true
                               | uu____844 -> false) ind.iquals in
                        match uu____836 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____851 = FStar_List.hd ctors in
                            (match uu____851 with
                             | (uu____862,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____880  ->
                                          match uu____880 with
                                          | (uu____885,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____888 =
                                                lident_as_mlsymbol lid in
                                              (uu____888, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____889 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____891 =
                        let uu____902 = lident_as_mlsymbol ind.iname in
                        (false, uu____902, None, ml_params, (Some tbody)) in
                      (env3, uu____891))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____923,t,uu____925,uu____926,uu____927);
            FStar_Syntax_Syntax.sigrng = uu____928;
            FStar_Syntax_Syntax.sigquals = uu____929;
            FStar_Syntax_Syntax.sigmeta = uu____930;_}::[],uu____931),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____939 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____939 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____966),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____977 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____977 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1029 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1050 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1050);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1054 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1059 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1068 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1096 =
               let uu____1099 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1099 ml_name tysc
                 false false in
             match uu____1096 with
             | (g2,mangled_name) ->
                 ((let uu____1105 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1105
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
             (let uu____1117 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1117
              then
                let uu____1118 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1118
              else ());
             (let uu____1120 =
                let uu____1121 = FStar_Syntax_Subst.compress tm in
                uu____1121.FStar_Syntax_Syntax.n in
              match uu____1120 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1127) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1138 =
                    let uu____1143 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1143 in
                  (match uu____1138 with
                   | (uu____1172,uu____1173,tysc,uu____1175) ->
                       let uu____1176 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1176, tysc))
              | uu____1177 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1199 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1199
              then
                let uu____1200 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1201 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1200
                  uu____1201
              else ());
             (let uu____1203 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1203 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1213 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1213 in
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
                  let uu____1236 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1236 with
                   | (a_let,uu____1243,ty) ->
                       ((let uu____1246 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1246
                         then
                           let uu____1247 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1247
                         else ());
                        (let uu____1249 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1254,uu____1255,mllb::[]),uu____1257)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1268 -> failwith "Impossible" in
                         match uu____1249 with
                         | (exp,tysc) ->
                             ((let uu____1276 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1276
                               then
                                 ((let uu____1278 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1278);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1285 =
             let uu____1288 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1288 with
             | (return_tm,ty_sc) ->
                 let uu____1296 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1296 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1285 with
            | (g1,return_decl) ->
                let uu____1308 =
                  let uu____1311 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1311 with
                  | (bind_tm,ty_sc) ->
                      let uu____1319 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1319 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1308 with
                 | (g2,bind_decl) ->
                     let uu____1331 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1331 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1343 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1346,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1350 =
             let uu____1351 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___153_1353  ->
                       match uu___153_1353 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1354 -> false)) in
             Prims.op_Negation uu____1351 in
           if uu____1350
           then (g, [])
           else
             (let uu____1360 = FStar_Syntax_Util.arrow_formals t in
              match uu____1360 with
              | (bs,uu____1372) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1384 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1384)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1391,uu____1392)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1403 =
             let uu____1408 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1408 with
             | (tcenv,uu____1424,def_typ) ->
                 let uu____1428 = as_pair def_typ in (tcenv, uu____1428) in
           (match uu____1403 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1443 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1443 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1445,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1460 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1460 with
            | (ml_let,uu____1468,uu____1469) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1474,bindings),uu____1476) ->
                     let uu____1483 =
                       FStar_List.fold_left2
                         (fun uu____1490  ->
                            fun ml_lb  ->
                              fun uu____1492  ->
                                match (uu____1490, uu____1492) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1505;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1507;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1508;_})
                                    ->
                                    let lb_lid =
                                      let uu____1522 =
                                        let uu____1527 =
                                          FStar_Util.right lbname in
                                        uu____1527.FStar_Syntax_Syntax.fv_name in
                                      uu____1522.FStar_Syntax_Syntax.v in
                                    let uu____1531 =
                                      let uu____1534 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___154_1536  ->
                                                match uu___154_1536 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1537 -> true
                                                | uu____1540 -> false)) in
                                      if uu____1534
                                      then
                                        let mname =
                                          let uu____1544 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1544
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1545 =
                                          let uu____1548 =
                                            FStar_Util.right lbname in
                                          let uu____1549 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1548 mname uu____1549
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1545 with
                                        | (env1,uu____1553) ->
                                            (env1,
                                              (let uu___159_1554 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___159_1554.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___159_1554.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___159_1554.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___159_1554.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1557 =
                                           let uu____1558 =
                                             let uu____1561 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1561
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1558 in
                                         (uu____1557, ml_lb)) in
                                    (match uu____1531 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1483 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___155_1581  ->
                                 match uu___155_1581 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1583 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___156_1588  ->
                                 match uu___156_1588 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1593));
                                     FStar_Syntax_Syntax.tk = uu____1594;
                                     FStar_Syntax_Syntax.pos = uu____1595;
                                     FStar_Syntax_Syntax.vars = uu____1596;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1601 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1605 =
                            let uu____1607 =
                              let uu____1608 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1608 in
                            [uu____1607;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1605))
                 | uu____1612 ->
                     let uu____1613 =
                       let uu____1614 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1614 in
                     failwith uu____1613))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1619,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1623 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1623
           then
             let always_fail =
               let imp =
                 let uu____1630 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1630 with
                 | ([],t1) ->
                     let b =
                       let uu____1649 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1649 in
                     let uu____1650 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1650 None
                 | (bs,t1) ->
                     let uu____1668 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1668 None in
               let uu___160_1674 = se in
               let uu____1675 =
                 let uu____1676 =
                   let uu____1682 =
                     let uu____1686 =
                       let uu____1688 =
                         let uu____1689 =
                           let uu____1692 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1692 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1689;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1688] in
                     (false, uu____1686) in
                   (uu____1682, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1676 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1675;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___160_1674.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___160_1674.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___160_1674.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1699 = extract_sig g always_fail in
             (match uu____1699 with
              | (g1,mlm) ->
                  let uu____1710 =
                    FStar_Util.find_map quals
                      (fun uu___157_1712  ->
                         match uu___157_1712 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1715 -> None) in
                  (match uu____1710 with
                   | Some l ->
                       let uu____1720 =
                         let uu____1722 =
                           let uu____1723 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1723 in
                         let uu____1724 =
                           let uu____1726 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1726] in
                         uu____1722 :: uu____1724 in
                       (g1, uu____1720)
                   | uu____1728 ->
                       let uu____1730 =
                         FStar_Util.find_map quals
                           (fun uu___158_1732  ->
                              match uu___158_1732 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1735)
                                  -> Some l
                              | uu____1736 -> None) in
                       (match uu____1730 with
                        | Some uu____1740 -> (g1, [])
                        | uu____1742 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1748 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1748 with
            | (ml_main,uu____1756,uu____1757) ->
                let uu____1758 =
                  let uu____1760 =
                    let uu____1761 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1761 in
                  [uu____1760; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1758))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1763 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1767 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1771 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1773 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1791 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1791 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1817 = FStar_Options.debug_any () in
       if uu____1817
       then
         let uu____1818 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1818
       else ());
      (let uu____1820 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___161_1823 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___161_1823.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___161_1823.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___161_1823.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1824 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1824 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1841 = FStar_Options.codegen () in
             match uu____1841 with
             | Some "Kremlin" -> true
             | uu____1843 -> false in
           let uu____1845 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1845
           then
             ((let uu____1850 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1850);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))