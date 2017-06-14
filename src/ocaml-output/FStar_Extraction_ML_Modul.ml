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
            let uu____155 =
              let uu____156 = FStar_Syntax_Subst.compress def in
              FStar_All.pipe_right uu____156 FStar_Syntax_Util.unmeta in
            FStar_All.pipe_right uu____155 FStar_Syntax_Util.un_uinst in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____158 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____173 -> def1 in
          let uu____174 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____181) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____204 -> ([], def2) in
          match uu____174 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_216  ->
                     match uu___148_216 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____217 -> false) quals in
              let uu____218 = binders_as_mlty_binders env bs in
              (match uu____218 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____236 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body in
                     FStar_All.pipe_right uu____236
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                   let mangled_projector =
                     let uu____239 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_241  ->
                               match uu___149_241 with
                               | FStar_Syntax_Syntax.Projector uu____242 ->
                                   true
                               | uu____245 -> false)) in
                     if uu____239
                     then
                       let mname = mangle_projector_lid lid in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None in
                   let td =
                     let uu____261 =
                       let uu____272 = lident_as_mlsymbol lid in
                       (assumed, uu____272, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                     [uu____261] in
                   let def3 =
                     let uu____300 =
                       let uu____301 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid) in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____301 in
                     [uu____300; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                   let env2 =
                     let uu____303 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_305  ->
                               match uu___150_305 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____306 -> false)) in
                     if uu____303
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
    let uu____374 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____375 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____376 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____377 =
      let uu____378 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____383 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____384 =
                  let uu____385 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____385 in
                Prims.strcat uu____383 uu____384)) in
      FStar_All.pipe_right uu____378 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____374 uu____375 uu____376
      uu____377
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____423 = FStar_Syntax_Subst.open_term bs t in
              (match uu____423 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____436,t2,l',nparams,uu____440) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____443 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____443 with
                                  | (bs',body) ->
                                      let uu____464 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____464 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____500  ->
                                                  fun uu____501  ->
                                                    match (uu____500,
                                                            uu____501)
                                                    with
                                                    | ((b',uu____511),
                                                       (b,uu____513)) ->
                                                        let uu____518 =
                                                          let uu____523 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____523) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____518)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____525 =
                                               let uu____528 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____528 in
                                             FStar_All.pipe_right uu____525
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____533 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____534 -> []))
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
          let uu____575 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____575 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names =
          let uu____580 =
            let uu____581 =
              let uu____584 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____584 in
            uu____581.FStar_Syntax_Syntax.n in
          match uu____580 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____587) ->
              FStar_List.map
                (fun uu____600  ->
                   match uu____600 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____604;
                        FStar_Syntax_Syntax.sort = uu____605;_},uu____606)
                       -> ppname.FStar_Ident.idText) bs
          | uu____609 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____620 =
          let uu____621 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          fst uu____621 in
        let uu____624 =
          let uu____630 = lident_as_mlsymbol ctor.dname in
          let uu____631 =
            let uu____635 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names uu____635 in
          (uu____630, uu____631) in
        (uu____620, uu____624) in
      let extract_one_family env1 ind =
        let uu____664 = binders_as_mlty_binders env1 ind.iparams in
        match uu____664 with
        | (env2,vars) ->
            let uu____690 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____690 with
             | (env3,ctors) ->
                 let uu____739 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____739 with
                  | (indices,uu____760) ->
                      let ml_params =
                        let uu____775 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____790  ->
                                    let uu____793 =
                                      let uu____794 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____794 in
                                    (uu____793, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____775 in
                      let tbody =
                        let uu____798 =
                          FStar_Util.find_opt
                            (fun uu___151_800  ->
                               match uu___151_800 with
                               | FStar_Syntax_Syntax.RecordType uu____801 ->
                                   true
                               | uu____806 -> false) ind.iquals in
                        match uu____798 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____813 = FStar_List.hd ctors in
                            (match uu____813 with
                             | (uu____824,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____842  ->
                                          match uu____842 with
                                          | (uu____847,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____850 =
                                                lident_as_mlsymbol lid in
                                              (uu____850, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____851 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____853 =
                        let uu____864 = lident_as_mlsymbol ind.iname in
                        (false, uu____864, None, ml_params, (Some tbody)) in
                      (env3, uu____853))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____885,t,uu____887,uu____888,uu____889);
            FStar_Syntax_Syntax.sigrng = uu____890;
            FStar_Syntax_Syntax.sigquals = uu____891;
            FStar_Syntax_Syntax.sigmeta = uu____892;_}::[],uu____893),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____901 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____901 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____928),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____939 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____939 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____991 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t* FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1012 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1012);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1016 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1021 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1030 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1058 =
               let uu____1061 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1061 ml_name tysc
                 false false in
             match uu____1058 with
             | (g2,mangled_name) ->
                 ((let uu____1067 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1067
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
             (let uu____1079 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1079
              then
                let uu____1080 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1080
              else ());
             (let uu____1082 =
                let uu____1083 = FStar_Syntax_Subst.compress tm in
                uu____1083.FStar_Syntax_Syntax.n in
              match uu____1082 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1089) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1096 =
                    let uu____1101 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1101 in
                  (match uu____1096 with
                   | (uu____1130,uu____1131,tysc,uu____1133) ->
                       let uu____1134 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1134, tysc))
              | uu____1135 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1151 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1151
              then
                let uu____1152 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1153 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1152
                  uu____1153
              else ());
             (let uu____1155 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1155 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1165 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1165 in
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
                  let uu____1188 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1188 with
                   | (a_let,uu____1195,ty) ->
                       ((let uu____1198 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1198
                         then
                           let uu____1199 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1199
                         else ());
                        (let uu____1201 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1206,uu____1207,mllb::[]),uu____1209)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1220 -> failwith "Impossible" in
                         match uu____1201 with
                         | (exp,tysc) ->
                             ((let uu____1228 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1228
                               then
                                 ((let uu____1230 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1230);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1237 =
             let uu____1240 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1240 with
             | (return_tm,ty_sc) ->
                 let uu____1248 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1248 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1237 with
            | (g1,return_decl) ->
                let uu____1260 =
                  let uu____1263 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1263 with
                  | (bind_tm,ty_sc) ->
                      let uu____1271 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1271 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1260 with
                 | (g2,bind_decl) ->
                     let uu____1283 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1283 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1295 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1298,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1302 =
             let uu____1303 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1305  ->
                       match uu___152_1305 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1306 -> false)) in
             Prims.op_Negation uu____1303 in
           if uu____1302
           then (g, [])
           else
             (let uu____1312 = FStar_Syntax_Util.arrow_formals t in
              match uu____1312 with
              | (bs,uu____1324) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None in
                  let uu____1336 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None in
                  extract_typ_abbrev g fv quals uu____1336)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1343,uu____1344)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1355 =
             let uu____1360 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1360 with
             | (tcenv,uu____1376,def_typ) ->
                 let uu____1380 = as_pair def_typ in (tcenv, uu____1380) in
           (match uu____1355 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1395 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1395 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1397,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Const.exp_false_bool)) None
               se.FStar_Syntax_Syntax.sigrng in
           let uu____1412 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1412 with
            | (ml_let,uu____1420,uu____1421) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1426,bindings),uu____1428) ->
                     let uu____1435 =
                       FStar_List.fold_left2
                         (fun uu____1442  ->
                            fun ml_lb  ->
                              fun uu____1444  ->
                                match (uu____1442, uu____1444) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1457;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1459;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1460;_})
                                    ->
                                    let lb_lid =
                                      let uu____1474 =
                                        let uu____1476 =
                                          FStar_Util.right lbname in
                                        uu____1476.FStar_Syntax_Syntax.fv_name in
                                      uu____1474.FStar_Syntax_Syntax.v in
                                    let uu____1477 =
                                      let uu____1480 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1482  ->
                                                match uu___153_1482 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1483 -> true
                                                | uu____1486 -> false)) in
                                      if uu____1480
                                      then
                                        let mname =
                                          let uu____1490 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1490
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1491 =
                                          let uu____1494 =
                                            FStar_Util.right lbname in
                                          let uu____1495 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1494 mname uu____1495
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1491 with
                                        | (env1,uu____1499) ->
                                            (env1,
                                              (let uu___158_1500 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1500.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1500.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1500.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1500.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1503 =
                                           let uu____1504 =
                                             let uu____1507 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1507
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1504 in
                                         (uu____1503, ml_lb)) in
                                    (match uu____1477 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs) in
                     (match uu____1435 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1527  ->
                                 match uu___154_1527 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1529 -> None) quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1534  ->
                                 match uu___155_1534 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1539));
                                     FStar_Syntax_Syntax.tk = uu____1540;
                                     FStar_Syntax_Syntax.pos = uu____1541;
                                     FStar_Syntax_Syntax.vars = uu____1542;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1547 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs in
                          let uu____1551 =
                            let uu____1553 =
                              let uu____1554 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1554 in
                            [uu____1553;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1551))
                 | uu____1558 ->
                     let uu____1559 =
                       let uu____1560 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1560 in
                     failwith uu____1559))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1565,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1569 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1569
           then
             let always_fail =
               let imp =
                 let uu____1576 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1576 with
                 | ([],t1) ->
                     let b =
                       let uu____1595 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1595 in
                     let uu____1596 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1596 None
                 | (bs,t1) ->
                     let uu____1614 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1614 None in
               let uu___159_1620 = se in
               let uu____1621 =
                 let uu____1622 =
                   let uu____1628 =
                     let uu____1632 =
                       let uu____1634 =
                         let uu____1635 =
                           let uu____1638 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None in
                           FStar_Util.Inr uu____1638 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1635;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1634] in
                     (false, uu____1632) in
                   (uu____1628, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1622 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1621;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1620.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1620.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1620.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1645 = extract_sig g always_fail in
             (match uu____1645 with
              | (g1,mlm) ->
                  let uu____1656 =
                    FStar_Util.find_map quals
                      (fun uu___156_1658  ->
                         match uu___156_1658 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1661 -> None) in
                  (match uu____1656 with
                   | Some l ->
                       let uu____1666 =
                         let uu____1668 =
                           let uu____1669 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1669 in
                         let uu____1670 =
                           let uu____1672 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1672] in
                         uu____1668 :: uu____1670 in
                       (g1, uu____1666)
                   | uu____1674 ->
                       let uu____1676 =
                         FStar_Util.find_map quals
                           (fun uu___157_1678  ->
                              match uu___157_1678 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1681)
                                  -> Some l
                              | uu____1682 -> None) in
                       (match uu____1676 with
                        | Some uu____1686 -> (g1, [])
                        | uu____1688 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1694 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1694 with
            | (ml_main,uu____1702,uu____1703) ->
                let uu____1704 =
                  let uu____1706 =
                    let uu____1707 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1707 in
                  [uu____1706; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1704))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1709 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1713 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1718 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1720 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1738 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1738 FStar_Pervasives.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env* FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1764 = FStar_Options.debug_any () in
       if uu____1764
       then
         let uu____1765 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1765
       else ());
      (let uu____1767 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_1770 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1770.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1770.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1770.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1771 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1771 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1788 = FStar_Options.codegen () in
             match uu____1788 with
             | Some "Kremlin" -> true
             | uu____1790 -> false in
           let uu____1792 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1792
           then
             ((let uu____1797 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1797);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))