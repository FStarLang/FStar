open Prims
let fail_exp lid t =
  let uu____15 =
    let uu____18 =
      let uu____19 =
        let uu____29 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
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
                uu____37 FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____36 in
            [uu____35] in
          uu____32 :: uu____33 in
        (uu____29, uu____30) in
      FStar_Syntax_Syntax.Tm_app uu____19 in
    FStar_Syntax_Syntax.mk uu____18 in
  uu____15 FStar_Pervasives_Native.None FStar_Range.dummyRange
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
                 FStar_Pervasives_Native.Some uu____129 in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____127 in
             let uu____131 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
             (uu____126, uu____131)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                          Prims.list)
            FStar_Pervasives_Native.tuple2
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
                  (fun uu___148_220  ->
                     match uu___148_220 with
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
                            (fun uu___149_245  ->
                               match uu___149_245 with
                               | FStar_Syntax_Syntax.Projector uu____246 ->
                                   true
                               | uu____249 -> false)) in
                     if uu____243
                     then
                       let mname = mangle_projector_lid lid in
                       FStar_Pervasives_Native.Some
                         ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else FStar_Pervasives_Native.None in
                   let td =
                     let uu____265 =
                       let uu____276 = lident_as_mlsymbol lid in
                       (assumed, uu____276, mangled_projector, ml_bs,
                         (FStar_Pervasives_Native.Some
                            (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
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
                            (fun uu___150_309  ->
                               match uu___150_309 with
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
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;}
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____371 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____372 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____373 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____374 =
      let uu____375 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____380 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____381 =
                  let uu____382 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____382 in
                Prims.strcat uu____380 uu____381)) in
      FStar_All.pipe_right uu____375 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____371 uu____372 uu____373
      uu____374
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____420 = FStar_Syntax_Subst.open_term bs t in
              (match uu____420 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____433,t2,l',nparams,uu____437) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____440 =
                                   FStar_Syntax_Util.arrow_formals t2 in
                                 (match uu____440 with
                                  | (bs',body) ->
                                      let uu____461 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs' in
                                      (match uu____461 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____497  ->
                                                  fun uu____498  ->
                                                    match (uu____497,
                                                            uu____498)
                                                    with
                                                    | ((b',uu____508),
                                                       (b,uu____510)) ->
                                                        let uu____515 =
                                                          let uu____520 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          (b', uu____520) in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____515)
                                               bs_params bs1 in
                                           let t3 =
                                             let uu____522 =
                                               let uu____525 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____525 in
                                             FStar_All.pipe_right uu____522
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____530 -> [])) in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____531 -> []))
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____572 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____572 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names =
          let uu____577 =
            let uu____578 =
              let uu____581 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____581 in
            uu____578.FStar_Syntax_Syntax.n in
          match uu____577 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____584) ->
              FStar_List.map
                (fun uu____597  ->
                   match uu____597 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____601;
                        FStar_Syntax_Syntax.sort = uu____602;_},uu____603)
                       -> ppname.FStar_Ident.idText) bs
          | uu____606 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____617 =
          let uu____618 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____618 in
        let uu____621 =
          let uu____627 = lident_as_mlsymbol ctor.dname in
          let uu____628 =
            let uu____632 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names uu____632 in
          (uu____627, uu____628) in
        (uu____617, uu____621) in
      let extract_one_family env1 ind =
        let uu____661 = binders_as_mlty_binders env1 ind.iparams in
        match uu____661 with
        | (env2,vars) ->
            let uu____687 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____687 with
             | (env3,ctors) ->
                 let uu____736 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____736 with
                  | (indices,uu____757) ->
                      let ml_params =
                        let uu____772 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____787  ->
                                    let uu____790 =
                                      let uu____791 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____791 in
                                    (uu____790, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____772 in
                      let tbody =
                        let uu____795 =
                          FStar_Util.find_opt
                            (fun uu___151_797  ->
                               match uu___151_797 with
                               | FStar_Syntax_Syntax.RecordType uu____798 ->
                                   true
                               | uu____803 -> false) ind.iquals in
                        match uu____795 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____810 = FStar_List.hd ctors in
                            (match uu____810 with
                             | (uu____821,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____839  ->
                                          match uu____839 with
                                          | (uu____844,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____847 =
                                                lident_as_mlsymbol lid in
                                              (uu____847, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____848 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____850 =
                        let uu____861 = lident_as_mlsymbol ind.iname in
                        (false, uu____861, FStar_Pervasives_Native.None,
                          ml_params, (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____850))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____882,t,uu____884,uu____885,uu____886);
            FStar_Syntax_Syntax.sigrng = uu____887;
            FStar_Syntax_Syntax.sigquals = uu____888;
            FStar_Syntax_Syntax.sigmeta = uu____889;_}::[],uu____890),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____898 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____898 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____925),quals) ->
          let ifams = bundle_as_inductive_families env ses quals in
          let uu____936 = FStar_Util.fold_map extract_one_family env ifams in
          (match uu____936 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____988 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1009 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1009);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1013 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1018 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1027 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1055 =
               let uu____1058 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1058 ml_name tysc
                 false false in
             match uu____1055 with
             | (g2,mangled_name) ->
                 ((let uu____1064 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____1064
                   then
                     FStar_Util.print1 "Mangled name: %s\n"
                       (FStar_Pervasives_Native.fst mangled_name)
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____1076 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1076
              then
                let uu____1077 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1077
              else ());
             (let uu____1079 =
                let uu____1080 = FStar_Syntax_Subst.compress tm in
                uu____1080.FStar_Syntax_Syntax.n in
              match uu____1079 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1086) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____1097 =
                    let uu____1102 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____1102 in
                  (match uu____1097 with
                   | (uu____1131,uu____1132,tysc,uu____1134) ->
                       let uu____1135 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____1135, tysc))
              | uu____1136 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____1152 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____1152
              then
                let uu____1153 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____1154 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1153
                  uu____1154
              else ());
             (let uu____1156 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____1156 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1166 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____1166 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_let
                          (lbs, FStar_Syntax_Util.exp_false_bool)))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____1191 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____1191 with
                   | (a_let,uu____1198,ty) ->
                       ((let uu____1201 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____1201
                         then
                           let uu____1202 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1202
                         else ());
                        (let uu____1204 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1209,uu____1210,mllb::[]),uu____1212)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____1223 -> failwith "Impossible" in
                         match uu____1204 with
                         | (exp,tysc) ->
                             ((let uu____1231 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____1231
                               then
                                 ((let uu____1233 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1233);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____1240 =
             let uu____1243 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____1243 with
             | (return_tm,ty_sc) ->
                 let uu____1251 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____1251 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____1240 with
            | (g1,return_decl) ->
                let uu____1263 =
                  let uu____1266 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____1266 with
                  | (bind_tm,ty_sc) ->
                      let uu____1274 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____1274 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____1263 with
                 | (g2,bind_decl) ->
                     let uu____1286 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____1286 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1298 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1301,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1305 =
             let uu____1306 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1308  ->
                       match uu___152_1308 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1309 -> false)) in
             Prims.op_Negation uu____1306 in
           if uu____1305
           then (g, [])
           else
             (let uu____1315 = FStar_Syntax_Util.arrow_formals t in
              match uu____1315 with
              | (bs,uu____1327) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____1339 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals uu____1339)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1346,uu____1347)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1358 =
             let uu____1363 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____1363 with
             | (tcenv,uu____1379,def_typ) ->
                 let uu____1383 = as_pair def_typ in (tcenv, uu____1383) in
           (match uu____1358 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____1398 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____1398 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1400,attrs) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let uu____1417 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____1417 with
            | (ml_let,uu____1425,uu____1426) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1431,bindings),uu____1433) ->
                     let uu____1440 =
                       FStar_List.fold_left2
                         (fun uu____1447  ->
                            fun ml_lb  ->
                              fun uu____1449  ->
                                match (uu____1447, uu____1449) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1462;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1464;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1465;_})
                                    ->
                                    let lb_lid =
                                      let uu____1479 =
                                        let uu____1484 =
                                          FStar_Util.right lbname in
                                        uu____1484.FStar_Syntax_Syntax.fv_name in
                                      uu____1479.FStar_Syntax_Syntax.v in
                                    let uu____1488 =
                                      let uu____1491 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1493  ->
                                                match uu___153_1493 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1494 -> true
                                                | uu____1497 -> false)) in
                                      if uu____1491
                                      then
                                        let mname =
                                          let uu____1501 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____1501
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____1502 =
                                          let uu____1505 =
                                            FStar_Util.right lbname in
                                          let uu____1506 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1505 mname uu____1506
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____1502 with
                                        | (env1,uu____1510) ->
                                            (env1,
                                              (let uu___158_1511 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1511.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1511.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1511.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1511.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1514 =
                                           let uu____1515 =
                                             let uu____1518 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1518
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____1515 in
                                         (uu____1514, ml_lb)) in
                                    (match uu____1488 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____1440 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1538  ->
                                 match uu___154_1538 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1540 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1545  ->
                                 match uu___155_1545 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1550));
                                     FStar_Syntax_Syntax.tk = uu____1551;
                                     FStar_Syntax_Syntax.pos = uu____1552;
                                     FStar_Syntax_Syntax.vars = uu____1553;_}
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1558 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      FStar_Pervasives_Native.None)) attrs in
                          let uu____1562 =
                            let uu____1564 =
                              let uu____1565 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1565 in
                            [uu____1564;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))] in
                          (g1, uu____1562))
                 | uu____1569 ->
                     let uu____1570 =
                       let uu____1571 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1571 in
                     failwith uu____1570))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1576,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____1580 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____1580
           then
             let always_fail =
               let imp =
                 let uu____1587 = FStar_Syntax_Util.arrow_formals t in
                 match uu____1587 with
                 | ([],t1) ->
                     let b =
                       let uu____1606 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1606 in
                     let uu____1607 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____1607
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____1625 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____1625
                       FStar_Pervasives_Native.None in
               let uu___159_1631 = se in
               let uu____1632 =
                 let uu____1633 =
                   let uu____1639 =
                     let uu____1643 =
                       let uu____1645 =
                         let uu____1646 =
                           let uu____1649 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____1649 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1646;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____1645] in
                     (false, uu____1643) in
                   (uu____1639, [], []) in
                 FStar_Syntax_Syntax.Sig_let uu____1633 in
               {
                 FStar_Syntax_Syntax.sigel = uu____1632;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1631.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1631.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1631.FStar_Syntax_Syntax.sigmeta)
               } in
             let uu____1656 = extract_sig g always_fail in
             (match uu____1656 with
              | (g1,mlm) ->
                  let uu____1667 =
                    FStar_Util.find_map quals
                      (fun uu___156_1669  ->
                         match uu___156_1669 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____1672 -> FStar_Pervasives_Native.None) in
                  (match uu____1667 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____1677 =
                         let uu____1679 =
                           let uu____1680 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1680 in
                         let uu____1681 =
                           let uu____1683 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____1683] in
                         uu____1679 :: uu____1681 in
                       (g1, uu____1677)
                   | uu____1685 ->
                       let uu____1687 =
                         FStar_Util.find_map quals
                           (fun uu___157_1689  ->
                              match uu___157_1689 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1692)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____1693 -> FStar_Pervasives_Native.None) in
                       (match uu____1687 with
                        | FStar_Pervasives_Native.Some uu____1697 -> (g1, [])
                        | uu____1699 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1705 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____1705 with
            | (ml_main,uu____1713,uu____1714) ->
                let uu____1715 =
                  let uu____1717 =
                    let uu____1718 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1718 in
                  [uu____1717; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____1715))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1720 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1724 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1728 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1730 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1748 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1748 FStar_Pervasives_Native.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1774 = FStar_Options.debug_any () in
       if uu____1774
       then
         let uu____1775 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____1775
       else ());
      (let uu____1777 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___160_1780 = g in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1780.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1780.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1780.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____1781 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____1781 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____1798 = FStar_Options.codegen () in
             match uu____1798 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____1800 -> false in
           let uu____1802 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____1802
           then
             ((let uu____1807 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____1807);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))