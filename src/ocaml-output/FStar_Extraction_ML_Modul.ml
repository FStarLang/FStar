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
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env1  ->
       fun uu____100  ->
         match uu____100 with
         | (bv,uu____108) ->
             let uu____109 =
               let uu____110 =
                 let uu____112 =
                   let uu____113 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____113 in
                 Some uu____112 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____110 in
             let uu____114 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____109, uu____114)) env bs
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
            let uu____142 =
              let uu____143 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____143 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____142 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____145 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____160 -> def1 in
          let uu____161 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____168) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____191 -> ([], def2) in
          match uu____161 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___147_203  ->
                     match uu___147_203 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____204 -> false) quals in
              let uu____205 = binders_as_mlty_binders env bs in
              (match uu____205 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____223 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____223
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____226 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___148_228  ->
                               match uu___148_228 with
                               | FStar_Syntax_Syntax.Projector uu____229 ->
                                   true
                               | uu____232 -> false)) in
                     if uu____226
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____248 =
                       let uu____259 = lident_as_mlsymbol lid in
                       (assumed, uu____259, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____248] in
                   let def3 =
                     let uu____287 =
                       let uu____288 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____288 in
                     [uu____287; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____290 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_292  ->
                               match uu___149_292 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
                               | uu____293 -> false)) in
                     if uu____290
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
    let uu____354 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____355 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____356 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____357 =
      let uu____358 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____363 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____364 =
                  let uu____365 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____365 in
                Prims.strcat uu____363 uu____364)) in
      FStar_All.pipe_right uu____358 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____354 uu____355 uu____356
      uu____357
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,_us,bs,t,_mut_i,datas,quals1) ->
              let uu____406 = FStar_Syntax_Subst.open_term bs t in
              (match uu____406 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____419,t2,l',nparams,uu____423,uu____424)
                                 when FStar_Ident.lid_equals l l' ->
                                 let uu____429 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____429 with
                                  | (bs',body) ->
                                      let uu____450 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____450 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____486  ->
                                                  fun uu____487  ->
                                                    match (uu____486,
                                                            uu____487)
                                                    with
                                                    | ((b',uu____497),
                                                       (b,uu____499)) ->
                                                        let uu____504 =
                                                          let uu____509 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____509) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____504)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____511 =
                                               let uu____514 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____514 in
                                             FStar_All.pipe_right uu____511
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____519 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = quals1
                    }])
          | uu____520 -> []))
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
          let uu____557 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____557 in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____568 =
          let uu____569 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          Prims.fst uu____569 in
        let uu____572 =
          let uu____576 = lident_as_mlsymbol ctor.dname in
          let uu____577 = FStar_Extraction_ML_Util.argTypes mlt in
          (uu____576, uu____577) in
        (uu____568, uu____572) in
      let extract_one_family env1 ind =
        let uu____602 = binders_as_mlty_binders env1 ind.iparams in
        match uu____602 with
        | (env2,vars) ->
            let uu____628 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____628 with
             | (env3,ctors) ->
                 let uu____667 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____667 with
                  | (indices,uu____688) ->
                      let ml_params =
                        let uu____703 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____718  ->
                                    let uu____721 =
                                      let uu____722 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____722 in
                                    (uu____721, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____703 in
                      let tbody =
                        let uu____726 =
                          FStar_Util.find_opt
                            (fun uu___150_728  ->
                               match uu___150_728 with
                               | FStar_Syntax_Syntax.RecordType uu____729 ->
                                   true
                               | uu____734 -> false) ind.iquals in
                        match uu____726 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____741 = FStar_List.hd ctors in
                            (match uu____741 with
                             | (uu____748,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id]) in
                                          let uu____762 =
                                            lident_as_mlsymbol lid in
                                          (uu____762, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____763 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____765 =
                        let uu____776 = lident_as_mlsymbol ind.iname in
                        (false, uu____776, None, ml_params, (Some tbody)) in
                      (env3, uu____765))) in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               (l,uu____796,t,uu____798,uu____799,uu____800,uu____801);
             FStar_Syntax_Syntax.sigdoc = uu____802;
             FStar_Syntax_Syntax.sigrng = uu____803;_}::[],(FStar_Syntax_Syntax.ExceptionConstructor
           )::[],uu____804)
          ->
          let uu____814 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____814 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____836) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____846 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____846 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____898 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____916 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____916);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____943 =
               let uu____946 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____946 ml_name tysc
                 false false in
             match uu____943 with
             | (g2,mangled_name) ->
                 let lb =
                   {
                     FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                     FStar_Extraction_ML_Syntax.mllb_tysc = None;
                     FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                     FStar_Extraction_ML_Syntax.mllb_def = tm;
                     FStar_Extraction_ML_Syntax.print_typ = false
                   } in
                 (g2,
                   (FStar_Extraction_ML_Syntax.MLM_Let
                      (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))) in
           let rec extract_fv tm =
             let uu____960 =
               let uu____961 = FStar_Syntax_Subst.compress tm in
               uu____961.FStar_Syntax_Syntax.n in
             match uu____960 with
             | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____967) -> extract_fv tm1
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let mlp =
                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 let uu____978 =
                   let uu____983 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                   FStar_All.pipe_left FStar_Util.right uu____983 in
                 (match uu____978 with
                  | (uu____1012,uu____1013,tysc,uu____1015) ->
                      let uu____1016 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top)
                          (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                      (uu____1016, tysc))
             | uu____1017 -> failwith "Not an fv" in
           let extract_action g1 a =
             let uu____1029 = extract_fv a.FStar_Syntax_Syntax.action_defn in
             match uu____1029 with
             | (a_tm,ty_sc) ->
                 let uu____1036 = FStar_Extraction_ML_UEnv.action_name ed a in
                 (match uu____1036 with
                  | (a_nm,a_lid) -> extend_env g1 a_lid a_nm a_tm ty_sc) in
           let uu____1043 =
             let uu____1046 =
               extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1046 with
             | (return_tm,ty_sc) ->
                 let uu____1054 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1054 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1043 with
            | (g1,return_decl) ->
                let uu____1066 =
                  let uu____1069 =
                    extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1069 with
                  | (bind_tm,ty_sc) ->
                      let uu____1077 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1077 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1066 with
                 | (g2,bind_decl) ->
                     let uu____1089 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1089 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1101 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1104,t,quals) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____1109 =
             let uu____1110 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___151_1112  ->
                       match uu___151_1112 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1113 -> false)) in
             FStar_All.pipe_right uu____1110 Prims.op_Negation in
           if uu____1109
           then (g, [])
           else
             (let uu____1119 = FStar_Syntax_Util.arrow_formals t in
              match uu____1119 with
              | (bs,uu____1131) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1143 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1143)
       | FStar_Syntax_Syntax.Sig_let
           ((false ,lb::[]),uu____1150,quals,uu____1152) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____1163 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
           extract_typ_abbrev g uu____1163 quals lb.FStar_Syntax_Syntax.lbdef
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1165,quals,attrs) ->
           let elet =
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Const.exp_false_bool))) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1185 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1185 with
            | (ml_let,uu____1193,uu____1194) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1199,bindings),uu____1201) ->
                     let uu____1208 =
                       FStar_List.fold_left2
                         (fun uu____1215  ->
                            fun ml_lb  ->
                              fun uu____1217  ->
                                match (uu____1215, uu____1217) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1230;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1232;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1233;_})
                                    ->
                                    let lb_lid =
                                      let uu____1247 =
                                        let uu____1252 =
                                          FStar_Util.right lbname in
                                        uu____1252.FStar_Syntax_Syntax.fv_name in
                                      uu____1247.FStar_Syntax_Syntax.v in
                                    let uu____1256 =
                                      let uu____1259 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___152_1261  ->
                                                match uu___152_1261 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1262 -> true
                                                | uu____1265 -> false)) in
                                      if uu____1259
                                      then
                                        let mname =
                                          let uu____1269 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1269
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1270 =
                                          let uu____1273 =
                                            FStar_Util.right lbname in
                                          let uu____1274 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1273 mname uu____1274
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1270 with
                                        | (env1,uu____1278) ->
                                            (env1,
                                              (let uu___157_1279 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((Prims.snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___157_1279.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___157_1279.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___157_1279.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___157_1279.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1282 =
                                           let uu____1283 =
                                             let uu____1286 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1286
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left Prims.fst
                                             uu____1283 in
                                         (uu____1282, ml_lb)) in
                                    (match uu____1256 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (Prims.snd lbs) in
                     (match uu____1208 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___153_1306  ->
                                 match uu___153_1306 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1308 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___154_1313  ->
                                 match uu___154_1313 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1318));
                                     FStar_Syntax_Syntax.tk = uu____1319;
                                     FStar_Syntax_Syntax.pos = uu____1320;
                                     FStar_Syntax_Syntax.vars = uu____1321;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1326 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1330 =
                            let uu____1332 =
                              let uu____1333 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1333 in
                            [uu____1332;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1330))
                 | uu____1337 ->
                     let uu____1338 =
                       let uu____1339 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1339 in
                     failwith uu____1338))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1344,t,quals) ->
           let uu____1349 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1349
           then
             let always_fail =
               let imp =
                 let uu____1358 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1358 with
                 | ([],t1) -> fail_exp lid t1
                 | (bs,t1) ->
                     let uu____1390 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1390 None in
               let uu___158_1396 = se in
               let uu____1397 =
                 let uu____1398 =
                   let uu____1406 =
                     let uu____1410 =
                       let uu____1412 =
                         let uu____1413 =
                           let uu____1416 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1416 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1413;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1412] in
                     (false, uu____1410) in
                   (uu____1406, [], quals, []) in
                 FStar_Syntax_Syntax.Sig_let uu____1398 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1397;
                 FStar_Syntax_Syntax.sigdoc =
                   (uu___158_1396.FStar_Syntax_Syntax.sigdoc);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___158_1396.FStar_Syntax_Syntax.sigrng)
               } in
             let uu____1424 = extract_sig g always_fail in
             (match uu____1424 with
              | (g1,mlm) ->
                  let uu____1435 =
                    FStar_Util.find_map quals
                      (fun uu___155_1437  ->
                         match uu___155_1437 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1440 -> None) in
                  (match uu____1435 with
                   | Some l ->
                       let uu____1445 =
                         let uu____1447 =
                           let uu____1448 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1448 in
                         let uu____1449 =
                           let uu____1451 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1451] in
                         uu____1447 :: uu____1449 in
                       (g1, uu____1445)
                   | uu____1453 ->
                       let uu____1455 =
                         FStar_Util.find_map quals
                           (fun uu___156_1457  ->
                              match uu___156_1457 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1460)
                                  -> Some l
                              | uu____1461 -> None) in
                       (match uu____1455 with
                        | Some uu____1465 -> (g1, [])
                        | uu____1467 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1473 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1473 with
            | (ml_main,uu____1481,uu____1482) ->
                let uu____1483 =
                  let uu____1485 =
                    let uu____1486 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1486 in
                  [uu____1485; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1483))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1488 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1506 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1506 Prims.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1531 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___159_1534 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___159_1534.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___159_1534.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___159_1534.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1535 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1535 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1552 = FStar_Options.codegen () in
             match uu____1552 with
             | Some "Kremlin" -> true
             | uu____1554 -> false in
           let uu____1556 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1556
           then
             ((let uu____1561 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1561);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))