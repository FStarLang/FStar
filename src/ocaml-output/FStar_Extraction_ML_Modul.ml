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
let as_pair uu___147_81 =
  match uu___147_81 with
  | a::b::[] -> (a, b)
  | uu____85 -> failwith "Expected a list with 2 elements"
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____123  ->
         match uu____123 with
         | (bv,uu____131) ->
             let uu____132 =
               let uu____133 =
                 let uu____135 =
                   let uu____136 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____136 in
                 Some uu____135 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____133 in
             let uu____137 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____132, uu____137)) env bs
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
            let uu____161 =
              let uu____162 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____162 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____161 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____164 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____179 -> def1 in
          let uu____180 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____187) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____210 -> ([], def2) in
          match uu____180 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_223  ->
                     match uu___148_223 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____224 -> false) quals in
              let uu____225 = binders_as_mlty_binders env bs in
              (match uu____225 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____243 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____243
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____246 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_250  ->
                               match uu___149_250 with
                               | FStar_Syntax_Syntax.Projector uu____251 ->
                                   true
                               | uu____254 -> false)) in
                     if uu____246
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____270 =
                       let uu____281 = lident_as_mlsymbol lid in
                       (assumed, uu____281, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____270] in
                   let def3 =
                     let uu____309 =
                       let uu____310 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____310 in
                     [uu____309; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____312 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_315  ->
                               match uu___150_315 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____316 -> false)) in
                     if uu____312
                     then env1
                     else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                   (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;}
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____384 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____385 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____386 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____387 =
      let uu____388 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____396 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____397 =
                  let uu____398 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____398 in
                Prims.strcat uu____396 uu____397)) in
      FStar_All.pipe_right uu____388 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____384 uu____385 uu____386
      uu____387
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____447 = FStar_Syntax_Subst.open_term bs t in
              (match uu____447 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____475,t2,l',nparams,uu____479) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____482 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____482 with
                                  | (bs',body) ->
                                      let uu____503 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____503 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____546  ->
                                                  fun uu____547  ->
                                                    match (uu____546,
                                                            uu____547)
                                                    with
                                                    | ((b',uu____557),
                                                       (b,uu____559)) ->
                                                        let uu____564 =
                                                          let uu____569 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____569) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____564)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____571 =
                                               let uu____574 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____574 in
                                             FStar_All.pipe_right uu____571
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____579 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____580 -> []))
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
          let uu____621 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____621 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names =
          let uu____626 =
            let uu____627 =
              let uu____630 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____630 in
            uu____627.FStar_Syntax_Syntax.n in
          match uu____626 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____633) ->
              FStar_List.map
                (fun uu____651  ->
                   match uu____651 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____655;
                        FStar_Syntax_Syntax.sort = uu____656;_},uu____657)
                       -> ppname.FStar_Ident.idText) bs
          | uu____660 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____671 =
          let uu____672 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____672 in
        let uu____675 =
          let uu____681 = lident_as_mlsymbol ctor.dname in
          let uu____682 =
            let uu____686 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names uu____686 in
          (uu____681, uu____682) in
        (uu____671, uu____675) in
      let extract_one_family env1 ind =
        let uu____715 = binders_as_mlty_binders env1 ind.iparams in
        match uu____715 with
        | (env2,vars) ->
            let uu____741 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____741 with
             | (env3,ctors) ->
                 let uu____790 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____790 with
                  | (indices,uu____811) ->
                      let ml_params =
                        let uu____826 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____844  ->
                                    let uu____847 =
                                      let uu____848 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____848 in
                                    (uu____847, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____826 in
                      let tbody =
                        let uu____852 =
                          FStar_Util.find_opt
                            (fun uu___151_856  ->
                               match uu___151_856 with
                               | FStar_Syntax_Syntax.RecordType uu____857 ->
                                   true
                               | uu____862 -> false) ind.iquals in
                        match uu____852 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____869 = FStar_List.hd ctors in
                            (match uu____869 with
                             | (uu____880,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____905  ->
                                          match uu____905 with
                                          | (uu____910,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____913 =
                                                lident_as_mlsymbol lid in
                                              (uu____913, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____914 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____916 =
                        let uu____927 = lident_as_mlsymbol ind.iname in
                        (false, uu____927, None, ml_params, (Some tbody)) in
                      (env3, uu____916))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____948,t,uu____950,uu____951,uu____952);
            FStar_Syntax_Syntax.sigrng = uu____953;
            FStar_Syntax_Syntax.sigquals = uu____954;
            FStar_Syntax_Syntax.sigmeta = uu____955;_}::[],uu____956),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____964 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____964 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____991),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____1002 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____1002 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____1054 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1077 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1077);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1081 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1086 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1095 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1123 =
               let uu____1126 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1126 ml_name tysc
                 false false in
             match uu____1123 with
             | (g2,mangled_name) ->
                 ((let uu____1132 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1132
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
             (let uu____1144 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1144
              then
                let uu____1145 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1145
              else ());
             (let uu____1147 =
                let uu____1148 = FStar_Syntax_Subst.compress tm in
                uu____1148.FStar_Syntax_Syntax.n in
              match uu____1147 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1154) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1161 =
                    let uu____1166 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1166 in
                  (match uu____1161 with
                   | (uu____1195,uu____1196,tysc,uu____1198) ->
                       let uu____1199 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1199, tysc))
              | uu____1200 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1216 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1216
              then
                let uu____1217 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1218 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1217
                  uu____1218
              else ());
             (let uu____1220 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1220 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1230 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1230 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Syntax_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Const.exp_false_bool)) None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____1249 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1249 with
                   | (a_let,uu____1256,ty) ->
                       ((let uu____1259 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1259
                         then
                           let uu____1260 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1260
                         else ());
                        (let uu____1262 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1267,uu____1268,mllb::[]),uu____1270)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1281 -> failwith "Impossible" in
                         match uu____1262 with
                         | (exp,tysc) ->
                             ((let uu____1289 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1289
                               then
                                 ((let uu____1291 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1291);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1299 =
             let uu____1302 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1302 with
             | (return_tm,ty_sc) ->
                 let uu____1310 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1310 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1299 with
            | (g1,return_decl) ->
                let uu____1322 =
                  let uu____1325 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1325 with
                  | (bind_tm,ty_sc) ->
                      let uu____1333 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1333 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1322 with
                 | (g2,bind_decl) ->
                     let uu____1345 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1345 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1357 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1360,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1364 =
             let uu____1365 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1368  ->
                       match uu___152_1368 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1369 -> false)) in
             Prims.op_Negation uu____1365 in
           if uu____1364
           then (g, [])
           else
             (let uu____1375 = FStar_Syntax_Util.arrow_formals t in
              match uu____1375 with
              | (bs,uu____1387) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1399 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1399)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1406,uu____1407)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1418 =
             let uu____1423 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1423 with
             | (tcenv,uu____1439,def_typ) ->
                 let uu____1443 = as_pair def_typ in (tcenv, uu____1443) in
           (match uu____1418 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1458 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1458 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1460,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1475 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1475 with
            | (ml_let,uu____1483,uu____1484) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1489,bindings),uu____1491) ->
                     let uu____1498 =
                       FStar_List.fold_left2
                         (fun uu____1519  ->
                            fun ml_lb  ->
                              fun uu____1521  ->
                                match (uu____1519, uu____1521) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1534;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1536;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1537;_})
                                    ->
                                    let lb_lid =
                                      let uu____1551 =
                                        let uu____1553 =
                                          FStar_Util.right lbname in
                                        uu____1553.FStar_Syntax_Syntax.fv_name in
                                      uu____1551.FStar_Syntax_Syntax.v in
                                    let uu____1554 =
                                      let uu____1557 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1561  ->
                                                match uu___153_1561 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1562 -> true
                                                | uu____1565 -> false)) in
                                      if uu____1557
                                      then
                                        let mname =
                                          let uu____1569 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1569
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1570 =
                                          let uu____1573 =
                                            FStar_Util.right lbname in
                                          let uu____1574 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1573 mname uu____1574
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1570 with
                                        | (env1,uu____1578) ->
                                            (env1,
                                              (let uu___158_1580 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1580.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1580.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1580.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1580.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1583 =
                                           let uu____1584 =
                                             let uu____1587 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1587
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1584 in
                                         (uu____1583, ml_lb)) in
                                    (match uu____1554 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1498 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1608  ->
                                 match uu___154_1608 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1610 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1621  ->
                                 match uu___155_1621 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1626));
                                     FStar_Syntax_Syntax.tk = uu____1627;
                                     FStar_Syntax_Syntax.pos = uu____1628;
                                     FStar_Syntax_Syntax.vars = uu____1629;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1634 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1638 =
                            let uu____1640 =
                              let uu____1641 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1641 in
                            [uu____1640;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1638))
                 | uu____1645 ->
                     let uu____1646 =
                       let uu____1647 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1647 in
                     failwith uu____1646))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1652,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1656 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1656
           then
             let always_fail =
               let imp =
                 let uu____1663 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1663 with
                 | ([],t1) ->
                     let b =
                       let uu____1682 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1682 in
                     let uu____1683 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1683 None
                 | (bs,t1) ->
                     let uu____1701 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1701 None in
               let uu___159_1707 = se in
               let uu____1708 =
                 let uu____1709 =
                   let uu____1715 =
                     let uu____1719 =
                       let uu____1721 =
                         let uu____1722 =
                           let uu____1725 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1725 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1722;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1721] in
                     (false, uu____1719) in
                   (uu____1715, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1709 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1708;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1707.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1707.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1707.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1732 = extract_sig g always_fail in
             (match uu____1732 with
              | (g1,mlm) ->
                  let uu____1743 =
                    FStar_Util.find_map quals
                      (fun uu___156_1747  ->
                         match uu___156_1747 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1750 -> None) in
                  (match uu____1743 with
                   | Some l ->
                       let uu____1755 =
                         let uu____1757 =
                           let uu____1758 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1758 in
                         let uu____1759 =
                           let uu____1761 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1761] in
                         uu____1757 :: uu____1759 in
                       (g1, uu____1755)
                   | uu____1763 ->
                       let uu____1765 =
                         FStar_Util.find_map quals
                           (fun uu___157_1770  ->
                              match uu___157_1770 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1773)
                                  -> Some l
                              | uu____1774 -> None) in
                       (match uu____1765 with
                        | Some uu____1778 -> (g1, [])
                        | uu____1780 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1786 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1786 with
            | (ml_main,uu____1794,uu____1795) ->
                let uu____1796 =
                  let uu____1798 =
                    let uu____1799 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1799 in
                  [uu____1798; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1796))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1801 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1805 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1810 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1812 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1830 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1830 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1856 = FStar_Options.debug_any () in
       if uu____1856
       then
         let uu____1857 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1857
       else ());
      (let uu____1859 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_1862 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1862.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1862.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1862.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1863 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1863 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1880 = FStar_Options.codegen () in
             match uu____1880 with
             | Some "Kremlin" -> true
             | uu____1882 -> false in
           let uu____1884 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1884
           then
             ((let uu____1889 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1889);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))