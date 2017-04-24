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
let as_pair uu___150_81 =
  match uu___150_81 with
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
                   let uu____130 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                      in
                   FStar_Extraction_ML_Syntax.MLTY_Var uu____130  in
                 Some uu____129  in
               FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____127  in
             let uu____131 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (uu____126, uu____131)) env bs
  
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
            let uu____159 =
              let uu____160 = FStar_Syntax_Subst.compress def  in
              FStar_All.pipe_right uu____160 FStar_Syntax_Util.unmeta  in
            FStar_All.pipe_right uu____159 FStar_Syntax_Util.un_uinst  in
          let def2 =
            match def1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____162 ->
                FStar_Extraction_ML_Term.normalize_abs def1
            | uu____177 -> def1  in
          let uu____178 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____185) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____208 -> ([], def2)  in
          match uu____178 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___151_220  ->
                     match uu___151_220 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____221 -> false) quals
                 in
              let uu____222 = binders_as_mlty_binders env bs  in
              (match uu____222 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____240 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                     FStar_All.pipe_right uu____240
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1))
                      in
                   let mangled_projector =
                     let uu____243 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___152_245  ->
                               match uu___152_245 with
                               | FStar_Syntax_Syntax.Projector uu____246 ->
                                   true
                               | uu____249 -> false))
                        in
                     if uu____243
                     then
                       let mname = mangle_projector_lid lid  in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None  in
                   let td =
                     let uu____265 =
                       let uu____276 = lident_as_mlsymbol lid  in
                       (assumed, uu____276, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                        in
                     [uu____265]  in
                   let def3 =
                     let uu____304 =
                       let uu____305 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid)
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____305  in
                     [uu____304; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                   let env2 =
                     let uu____307 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___153_309  ->
                               match uu___153_309 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
                               | uu____310 -> false))
                        in
                     if uu____307
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
    let uu____371 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____372 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____373 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____374 =
      let uu____375 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____380 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____381 =
                  let uu____382 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____382  in
                Prims.strcat uu____380 uu____381))
         in
      FStar_All.pipe_right uu____375 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____371 uu____372 uu____373
      uu____374
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,_us,bs,t,_mut_i,datas,quals1) ->
              let uu____423 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____423 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____436,t2,l',nparams,uu____440,uu____441)
                                 when FStar_Ident.lid_equals l l' ->
                                 let uu____446 =
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____446 with
                                  | (bs',body) ->
                                      let uu____467 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
                                      (match uu____467 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____503  ->
                                                  fun uu____504  ->
                                                    match (uu____503,
                                                            uu____504)
                                                    with
                                                    | ((b',uu____514),
                                                       (b,uu____516)) ->
                                                        let uu____521 =
                                                          let uu____526 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          (b', uu____526)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____521)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____528 =
                                               let uu____531 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____531
                                                in
                                             FStar_All.pipe_right uu____528
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____536 -> []))
                      in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = quals1
                    }])
          | uu____537 -> []))
  
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
          let uu____574 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____574
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____585 =
          let uu____586 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          Prims.fst uu____586  in
        let uu____589 =
          let uu____593 = lident_as_mlsymbol ctor.dname  in
          let uu____594 = FStar_Extraction_ML_Util.argTypes mlt  in
          (uu____593, uu____594)  in
        (uu____585, uu____589)  in
      let extract_one_family env1 ind =
        let uu____619 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____619 with
        | (env2,vars) ->
            let uu____645 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____645 with
             | (env3,ctors) ->
                 let uu____684 = FStar_Syntax_Util.arrow_formals ind.ityp  in
                 (match uu____684 with
                  | (indices,uu____705) ->
                      let ml_params =
                        let uu____720 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____735  ->
                                    let uu____738 =
                                      let uu____739 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____739  in
                                    (uu____738, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____720  in
                      let tbody =
                        let uu____743 =
                          FStar_Util.find_opt
                            (fun uu___154_745  ->
                               match uu___154_745 with
                               | FStar_Syntax_Syntax.RecordType uu____746 ->
                                   true
                               | uu____751 -> false) ind.iquals
                           in
                        match uu____743 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____758 = FStar_List.hd ctors  in
                            (match uu____758 with
                             | (uu____765,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id])
                                             in
                                          let uu____779 =
                                            lident_as_mlsymbol lid  in
                                          (uu____779, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____780 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____782 =
                        let uu____793 = lident_as_mlsymbol ind.iname  in
                        (false, uu____793, None, ml_params, (Some tbody))  in
                      (env3, uu____782)))
         in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               (l,uu____813,t,uu____815,uu____816,uu____817,uu____818);
             FStar_Syntax_Syntax.sigrng = uu____819;_}::[],(FStar_Syntax_Syntax.ExceptionConstructor
           )::[],uu____820)
          ->
          let uu____829 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____829 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____851) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____861 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____861 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____913 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____931 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____931);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____958 =
               let uu____961 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____961 ml_name tysc
                 false false
                in
             match uu____958 with
             | (g2,mangled_name) ->
                 let uu____966 = mangled_name  in
                 (match uu____966 with
                  | (n1,w) ->
                      ((let uu____972 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug
                               g2.FStar_Extraction_ML_UEnv.tcenv)
                            (FStar_Options.Other "ExtractionReify")
                           in
                        if uu____972
                        then FStar_Util.print1 "Mangled name: %s\n" n1
                        else ());
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
             (let uu____984 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____984
              then
                let uu____985 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____985
              else ());
             (let uu____987 =
                let uu____988 = FStar_Syntax_Subst.compress tm  in
                uu____988.FStar_Syntax_Syntax.n  in
              match uu____987 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____994) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1005 =
                    let uu____1010 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1010  in
                  (match uu____1005 with
                   | (uu____1039,uu____1040,tysc,uu____1042) ->
                       let uu____1043 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____1043, tysc))
              | uu____1044 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____1060 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1060
              then
                let uu____1061 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____1062 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1061
                  uu____1062
              else ());
             (let uu____1064 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____1064 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1074 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Const.exp_unit
                       in
                    FStar_Util.Inl uu____1074  in
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
                  let uu____1097 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____1097 with
                   | (a_let,uu____1104,ty) ->
                       let uu____1106 =
                         match a_let.FStar_Extraction_ML_Syntax.expr with
                         | FStar_Extraction_ML_Syntax.MLE_Let
                             ((uu____1111,uu____1112,mllb::[]),uu____1114) ->
                             (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                              with
                              | Some tysc ->
                                  ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                    tysc)
                              | None  -> failwith "No type scheme")
                         | uu____1125 -> failwith "Impossible"  in
                       (match uu____1106 with
                        | (exp,tysc) ->
                            ((let uu____1133 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug
                                     g1.FStar_Extraction_ML_UEnv.tcenv)
                                  (FStar_Options.Other "ExtractionReify")
                                 in
                              if uu____1133
                              then
                                ((let uu____1135 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      a_nm (Prims.snd tysc)
                                     in
                                  FStar_Util.print1 "Action typescheme: %s\n"
                                    uu____1135);
                                 FStar_List.iter
                                   (fun x  ->
                                      FStar_Util.print1
                                        "Action type binders: %s\n"
                                        (Prims.fst x)) (Prims.fst tysc))
                              else ());
                             extend_env g1 a_lid a_nm exp tysc))))
              in
           let uu____1142 =
             let uu____1145 =
               FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
             match uu____1145 with
             | (return_nm,return_lid) ->
                 let uu____1152 =
                   extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr)
                    in
                 (match uu____1152 with
                  | (return_tm,ty_sc) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1142 with
            | (g1,return_decl) ->
                let uu____1165 =
                  let uu____1168 =
                    FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                  match uu____1168 with
                  | (bind_nm,bind_lid) ->
                      let uu____1175 =
                        extract_fv
                          (Prims.snd ed.FStar_Syntax_Syntax.bind_repr)
                         in
                      (match uu____1175 with
                       | (bind_tm,ty_sc) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1165 with
                 | (g2,bind_decl) ->
                     let uu____1188 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1188 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1200 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1203,t,quals) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____1208 =
             let uu____1209 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___155_1211  ->
                       match uu___155_1211 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1212 -> false))
                in
             Prims.op_Negation uu____1209  in
           if uu____1208
           then (g, [])
           else
             (let uu____1218 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1218 with
              | (bs,uu____1230) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let uu____1242 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals uu____1242)
       | FStar_Syntax_Syntax.Sig_let
           ((false ,lb::[]),uu____1249,quals,uu____1251) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____1262 =
             let uu____1267 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____1267 with
             | (tcenv,uu____1283,def_typ) ->
                 let uu____1287 = as_pair def_typ  in (tcenv, uu____1287)
              in
           (match uu____1262 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp  in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____1302 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____1302 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1304,quals,attrs) ->
           let elet =
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Const.exp_false_bool))) None
               se.FStar_Syntax_Syntax.sigrng
              in
           let uu____1324 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1324 with
            | (ml_let,uu____1332,uu____1333) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1338,bindings),uu____1340) ->
                     let uu____1347 =
                       FStar_List.fold_left2
                         (fun uu____1354  ->
                            fun ml_lb  ->
                              fun uu____1356  ->
                                match (uu____1354, uu____1356) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1369;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1371;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1372;_})
                                    ->
                                    let lb_lid =
                                      let uu____1386 =
                                        let uu____1391 =
                                          FStar_Util.right lbname  in
                                        uu____1391.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1386.FStar_Syntax_Syntax.v  in
                                    let uu____1395 =
                                      let uu____1398 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___156_1400  ->
                                                match uu___156_1400 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1401 -> true
                                                | uu____1404 -> false))
                                         in
                                      if uu____1398
                                      then
                                        let mname =
                                          let uu____1408 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1408
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1409 =
                                          let uu____1412 =
                                            FStar_Util.right lbname  in
                                          let uu____1413 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1412 mname uu____1413
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1409 with
                                        | (env1,uu____1417) ->
                                            (env1,
                                              (let uu___161_1418 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((Prims.snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___161_1418.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___161_1418.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___161_1418.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___161_1418.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1421 =
                                           let uu____1422 =
                                             let uu____1425 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1425
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left Prims.fst
                                             uu____1422
                                            in
                                         (uu____1421, ml_lb))
                                       in
                                    (match uu____1395 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (Prims.snd lbs)
                        in
                     (match uu____1347 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___157_1445  ->
                                 match uu___157_1445 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1447 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___158_1452  ->
                                 match uu___158_1452 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1457));
                                     FStar_Syntax_Syntax.tk = uu____1458;
                                     FStar_Syntax_Syntax.pos = uu____1459;
                                     FStar_Syntax_Syntax.vars = uu____1460;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1465 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let uu____1469 =
                            let uu____1471 =
                              let uu____1472 =
                                FStar_Extraction_ML_Util.mlloc_of_range
                                  se.FStar_Syntax_Syntax.sigrng
                                 in
                              FStar_Extraction_ML_Syntax.MLM_Loc uu____1472
                               in
                            [uu____1471;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))]
                             in
                          (g1, uu____1469))
                 | uu____1476 ->
                     let uu____1477 =
                       let uu____1478 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1478
                        in
                     failwith uu____1477))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1483,t,quals) ->
           let uu____1488 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1488
           then
             let always_fail =
               let imp =
                 let uu____1495 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1495 with
                 | ([],t1) ->
                     let b =
                       let uu____1514 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1514
                        in
                     let uu____1515 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____1515 None
                 | (bs,t1) ->
                     let uu____1533 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____1533 None
                  in
               let uu___162_1539 = se  in
               let uu____1540 =
                 let uu____1541 =
                   let uu____1549 =
                     let uu____1553 =
                       let uu____1555 =
                         let uu____1556 =
                           let uu____1559 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_Util.Inr uu____1559  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1556;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____1555]  in
                     (false, uu____1553)  in
                   (uu____1549, [], quals, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____1541  in
               {
                 FStar_Syntax_Syntax.sigel = uu____1540;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___162_1539.FStar_Syntax_Syntax.sigrng)
               }  in
             let uu____1567 = extract_sig g always_fail  in
             (match uu____1567 with
              | (g1,mlm) ->
                  let uu____1578 =
                    FStar_Util.find_map quals
                      (fun uu___159_1580  ->
                         match uu___159_1580 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1583 -> None)
                     in
                  (match uu____1578 with
                   | Some l ->
                       let uu____1588 =
                         let uu____1590 =
                           let uu____1591 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1591  in
                         let uu____1592 =
                           let uu____1594 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____1594]  in
                         uu____1590 :: uu____1592  in
                       (g1, uu____1588)
                   | uu____1596 ->
                       let uu____1598 =
                         FStar_Util.find_map quals
                           (fun uu___160_1600  ->
                              match uu___160_1600 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1603)
                                  -> Some l
                              | uu____1604 -> None)
                          in
                       (match uu____1598 with
                        | Some uu____1608 -> (g1, [])
                        | uu____1610 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1616 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____1616 with
            | (ml_main,uu____1624,uu____1625) ->
                let uu____1626 =
                  let uu____1628 =
                    let uu____1629 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1629  in
                  [uu____1628; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____1626))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1631 ->
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
      let uu____1649 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____1649 Prims.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1675 = FStar_Options.debug_any ()  in
       if uu____1675
       then
         let uu____1676 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____1676
       else ());
      (let uu____1678 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___163_1681 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___163_1681.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___163_1681.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___163_1681.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____1682 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____1682 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____1699 = FStar_Options.codegen ()  in
             match uu____1699 with
             | Some "Kremlin" -> true
             | uu____1701 -> false  in
           let uu____1703 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____1703
           then
             ((let uu____1708 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____1708);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  