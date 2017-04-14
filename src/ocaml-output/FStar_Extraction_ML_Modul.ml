open Prims
let fail_exp lid t =
  let uu____15 =
    let uu____18 =
      let uu____19 =
        let uu____29 =
          FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        let uu____30 =
          let uu____32 = FStar_Syntax_Syntax.iarg t  in
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
                              FStar_Syntax_Print.lid_to_string lid  in
                            Prims.strcat "Not yet implemented:" uu____48  in
                          FStar_Bytes.string_as_unicode_bytes uu____47  in
                        (uu____46, FStar_Range.dummyRange)  in
                      FStar_Const.Const_string uu____42  in
                    FStar_Syntax_Syntax.Tm_constant uu____41  in
                  FStar_Syntax_Syntax.mk uu____40  in
                uu____37 None FStar_Range.dummyRange  in
              FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____36  in
            [uu____35]  in
          uu____32 :: uu____33  in
        (uu____29, uu____30)  in
      FStar_Syntax_Syntax.Tm_app uu____19  in
    FStar_Syntax_Syntax.mk uu____18  in
  uu____15 None FStar_Range.dummyRange 
let mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x 
let lident_as_mlsymbol : FStar_Ident.lident -> Prims.string =
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
                   let uu____113 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                      in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____113  in
                 Some uu____112  in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____110  in
             let uu____114 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (uu____109, uu____114)) env bs
  
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
            let uu____142 =
              let uu____143 = FStar_Syntax_Subst.compress def  in
              FStar_All.pipe_right uu____143 FStar_Syntax_Util.unmeta  in
            FStar_All.pipe_right uu____142 FStar_Syntax_Util.un_uinst  in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____145 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____160 -> def1  in
          let uu____161 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____168) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____191 -> ([], def2)  in
          match uu____161 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___151_203  ->
                     match uu___151_203 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____204 -> false) quals
                 in
              let uu____205 = binders_as_mlty_binders env bs  in
              (match uu____205 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____223 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                     FStar_All.pipe_right uu____223
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1))
                      in
                   let mangled_projector =
                     let uu____226 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___152_228  ->
                               match uu___152_228 with
                               | FStar_Syntax_Syntax.Projector uu____229 ->
                                   true
                               | uu____232 -> false))
                        in
                     if uu____226
                     then
                       let mname = mangle_projector_lid lid  in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None  in
                   let td =
                     let uu____248 =
                       let uu____259 = lident_as_mlsymbol lid  in
                       (assumed, uu____259, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                        in
                     [uu____248]  in
                   let def3 =
                     let uu____287 =
                       let uu____288 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid)
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____288  in
                     [uu____287; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                   let env2 =
                     let uu____290 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___153_292  ->
                               match uu___153_292 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
                               | uu____293 -> false))
                        in
                     if uu____290
                     then env1
                     else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                      in
                   (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
type inductive_family =
  {
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list }
let print_ifamily : inductive_family -> Prims.unit =
  fun i  ->
    let uu____354 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____355 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____356 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____357 =
      let uu____358 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____363 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____364 =
                  let uu____365 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____365  in
                Prims.strcat uu____363 uu____364))
         in
      FStar_All.pipe_right uu____358 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____354 uu____355 uu____356
      uu____357
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,_us,bs,t,_mut_i,datas,quals1) ->
              let uu____406 = FStar_Syntax_Subst.open_term bs t  in
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
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____429 with
                                  | (bs',body) ->
                                      let uu____450 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
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
                                                              b
                                                             in
                                                          (b', uu____509)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____504)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____511 =
                                               let uu____514 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____514
                                                in
                                             FStar_All.pipe_right uu____511
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____519 -> []))
                      in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = quals1
                    }])
          | uu____520 -> []))
  
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
          let uu____557 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____557
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____568 =
          let uu____569 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          Prims.fst uu____569  in
        let uu____572 =
          let uu____576 = lident_as_mlsymbol ctor.dname  in
          let uu____577 = FStar_Extraction_ML_Util.argTypes mlt  in
          (uu____576, uu____577)  in
        (uu____568, uu____572)  in
      let extract_one_family env1 ind =
        let uu____602 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____602 with
        | (env2,vars) ->
            let uu____628 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____628 with
             | (env3,ctors) ->
                 let uu____667 = FStar_Syntax_Util.arrow_formals ind.ityp  in
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
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____722  in
                                    (uu____721, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____703  in
                      let tbody =
                        let uu____726 =
                          FStar_Util.find_opt
                            (fun uu___154_728  ->
                               match uu___154_728 with
                               | FStar_Syntax_Syntax.RecordType uu____729 ->
                                   true
                               | uu____734 -> false) ind.iquals
                           in
                        match uu____726 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____741 = FStar_List.hd ctors  in
                            (match uu____741 with
                             | (uu____748,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id])
                                             in
                                          let uu____762 =
                                            lident_as_mlsymbol lid  in
                                          (uu____762, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____763 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____765 =
                        let uu____776 = lident_as_mlsymbol ind.iname  in
                        (false, uu____776, None, ml_params, (Some tbody))  in
                      (env3, uu____765)))
         in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               (l,uu____796,t,uu____798,uu____799,uu____800,uu____801);
             FStar_Syntax_Syntax.sigrng = uu____802;_}::[],(FStar_Syntax_Syntax.ExceptionConstructor
           )::[],uu____803)
          ->
          let uu____812 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____812 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____834) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____844 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____844 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____896 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____914 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____914);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____941 =
               let uu____944 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____944 ml_name tysc
                 false false
                in
             match uu____941 with
             | (g2,mangled_name) ->
                 let uu____949 = mangled_name  in
                 (match uu____949 with
                  | (n1,w) ->
                      (FStar_Util.print1 "Mangled name: %s\n" n1;
                       (let lb =
                          {
                            FStar_Extraction_ML_Syntax.mllb_name =
                              mangled_name;
                            FStar_Extraction_ML_Syntax.mllb_tysc = None;
                            FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                            FStar_Extraction_ML_Syntax.mllb_def = tm;
                            FStar_Extraction_ML_Syntax.print_typ = false
                          }  in
                        (g2,
                          (FStar_Extraction_ML_Syntax.MLM_Let
                             (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))))
              in
           let rec extract_fv tm =
             let uu____964 =
               let uu____965 = FStar_Syntax_Subst.compress tm  in
               uu____965.FStar_Syntax_Syntax.n  in
             match uu____964 with
             | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____971) -> extract_fv tm1
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let mlp =
                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 let uu____982 =
                   let uu____987 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                      in
                   FStar_All.pipe_left FStar_Util.right uu____987  in
                 (match uu____982 with
                  | (uu____1016,uu____1017,tysc,uu____1019) ->
                      let uu____1020 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top)
                          (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                         in
                      (uu____1020, tysc))
             | uu____1021 -> failwith "Not an fv"  in
           let rec extract_fv2 tm =
             let uu____1030 =
               let uu____1031 = FStar_Syntax_Subst.compress tm  in
               uu____1031.FStar_Syntax_Syntax.n  in
             match uu____1030 with
             | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1037) ->
                 extract_fv2 tm1
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let mlp =
                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 let uu____1048 =
                   let uu____1053 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                      in
                   FStar_All.pipe_left FStar_Util.right uu____1053  in
                 (match uu____1048 with | (a,b,tysc,d) -> (b, tysc))
             | uu____1086 -> failwith "Not an fv"  in
           let extract_action g1 a =
             let uu____1101 = FStar_Extraction_ML_UEnv.action_name ed a  in
             match uu____1101 with
             | (a_nm,a_lid) ->
                 let lbname =
                   FStar_Util.Inl
                     {
                       FStar_Syntax_Syntax.ppname = (a_lid.FStar_Ident.ident);
                       FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                       FStar_Syntax_Syntax.sort =
                         (a.FStar_Syntax_Syntax.action_defn)
                     }
                    in
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
                         (lbs, (a.FStar_Syntax_Syntax.action_defn)))) None
                     FStar_Range.dummyRange
                    in
                 let uu____1133 =
                   FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                 (match uu____1133 with
                  | (a_let,uu____1140,ty) ->
                      let uu____1142 =
                        match a_let.FStar_Extraction_ML_Syntax.expr with
                        | FStar_Extraction_ML_Syntax.MLE_Let
                            ((uu____1147,uu____1148,mllb::[]),e) ->
                            (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                             with
                             | Some tysc -> (e, tysc)
                             | None  -> failwith "No type scheme")
                         in
                      (match uu____1142 with
                       | (exp,tysc) -> extend_env g1 a_lid a_nm exp tysc))
              in
           let uu____1165 =
             let uu____1168 =
               extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr)  in
             match uu____1168 with
             | (return_tm,ty_sc) ->
                 let uu____1176 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____1176 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1165 with
            | (g1,return_decl) ->
                let uu____1188 =
                  let uu____1191 =
                    FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                  match uu____1191 with
                  | (bind_nm,bind_lid) ->
                      let uu____1198 =
                        extract_fv
                          (Prims.snd ed.FStar_Syntax_Syntax.bind_repr)
                         in
                      (match uu____1198 with
                       | (bind_tm,ty_sc) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1188 with
                 | (g2,bind_decl) ->
                     let uu____1211 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1211 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1223 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1226,t,quals) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____1231 =
             let uu____1232 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___155_1234  ->
                       match uu___155_1234 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1235 -> false))
                in
             FStar_All.pipe_right uu____1232 Prims.op_Negation  in
           if uu____1231
           then (g, [])
           else
             (let uu____1241 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1241 with
              | (bs,uu____1253) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let uu____1265 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals uu____1265)
       | FStar_Syntax_Syntax.Sig_let
           ((false ,lb::[]),uu____1272,quals,uu____1274) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____1285 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
              in
           extract_typ_abbrev g uu____1285 quals lb.FStar_Syntax_Syntax.lbdef
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1287,quals,attrs) ->
           let elet =
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Const.exp_false_bool))) None
               se.FStar_Syntax_Syntax.sigrng
              in
           let uu____1307 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1307 with
            | (ml_let,uu____1315,uu____1316) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1321,bindings),uu____1323) ->
                     let uu____1330 =
                       FStar_List.fold_left2
                         (fun uu____1337  ->
                            fun ml_lb  ->
                              fun uu____1339  ->
                                match (uu____1337, uu____1339) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1352;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1354;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1355;_})
                                    ->
                                    let lb_lid =
                                      let uu____1369 =
                                        let uu____1374 =
                                          FStar_Util.right lbname  in
                                        uu____1374.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1369.FStar_Syntax_Syntax.v  in
                                    let uu____1378 =
                                      let uu____1381 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___156_1383  ->
                                                match uu___156_1383 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1384 -> true
                                                | uu____1387 -> false))
                                         in
                                      if uu____1381
                                      then
                                        let mname =
                                          let uu____1391 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1391
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1392 =
                                          let uu____1395 =
                                            FStar_Util.right lbname  in
                                          let uu____1396 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1395 mname uu____1396
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1392 with
                                        | (env1,uu____1400) ->
                                            (env1,
                                              (let uu___161_1401 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((Prims.snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___161_1401.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___161_1401.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___161_1401.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___161_1401.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1404 =
                                           let uu____1405 =
                                             let uu____1408 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1408
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left Prims.fst
                                             uu____1405
                                            in
                                         (uu____1404, ml_lb))
                                       in
                                    (match uu____1378 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (Prims.snd lbs)
                        in
                     (match uu____1330 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___157_1428  ->
                                 match uu___157_1428 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1430 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___158_1435  ->
                                 match uu___158_1435 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1440));
                                     FStar_Syntax_Syntax.tk = uu____1441;
                                     FStar_Syntax_Syntax.pos = uu____1442;
                                     FStar_Syntax_Syntax.vars = uu____1443;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1448 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let uu____1452 =
                            let uu____1454 =
                              let uu____1455 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng
                                 in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1455
                               in
                            [uu____1454;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))]
                             in
                          (g1, uu____1452))
                 | uu____1459 ->
                     let uu____1460 =
                       let uu____1461 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1461
                        in
                     failwith uu____1460))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1466,t,quals) ->
           let uu____1471 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1471
           then
             let always_fail =
               let imp =
                 let uu____1478 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1478 with
                 | ([],t1) ->
                     let b =
                       let uu____1497 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1497
                        in
                     let uu____1498 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____1498 None
                 | (bs,t1) ->
                     let uu____1516 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____1516 None
                  in
               let uu___162_1522 = se  in
               let uu____1523 =
                 let uu____1524 =
                   let uu____1532 =
                     let uu____1536 =
                       let uu____1538 =
                         let uu____1539 =
                           let uu____1542 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_Util.Inr uu____1542  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1539;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____1538]  in
                     (false, uu____1536)  in
                   (uu____1532, [], quals, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____1524  in
               {
                 FStar_Syntax_Syntax.sigel = uu____1523;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___162_1522.FStar_Syntax_Syntax.sigrng)
               }  in
             let uu____1550 = extract_sig g always_fail  in
             (match uu____1550 with
              | (g1,mlm) ->
                  let uu____1561 =
                    FStar_Util.find_map quals
                      (fun uu___159_1563  ->
                         match uu___159_1563 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1566 -> None)
                     in
                  (match uu____1561 with
                   | Some l ->
                       let uu____1571 =
                         let uu____1573 =
                           let uu____1574 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1574  in
                         let uu____1575 =
                           let uu____1577 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____1577]  in
                         uu____1573 :: uu____1575  in
                       (g1, uu____1571)
                   | uu____1579 ->
                       let uu____1581 =
                         FStar_Util.find_map quals
                           (fun uu___160_1583  ->
                              match uu___160_1583 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1586)
                                  -> Some l
                              | uu____1587 -> None)
                          in
                       (match uu____1581 with
                        | Some uu____1591 -> (g1, [])
                        | uu____1593 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1599 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____1599 with
            | (ml_main,uu____1607,uu____1608) ->
                let uu____1609 =
                  let uu____1611 =
                    let uu____1612 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1612  in
                  [uu____1611; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____1609))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1614 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1632 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____1632 Prims.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1657 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___163_1660 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___163_1660.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___163_1660.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___163_1660.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____1661 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____1661 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____1678 = FStar_Options.codegen ()  in
             match uu____1678 with
             | Some "Kremlin" -> true
             | uu____1680 -> false  in
           let uu____1682 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____1682
           then
             ((let uu____1687 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____1687);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  