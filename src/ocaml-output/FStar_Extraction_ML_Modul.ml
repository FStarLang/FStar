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
            | uu____172 -> def1  in
          let uu____173 =
            match def2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____180) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____193 -> ([], def2)  in
          match uu____173 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___148_205  ->
                     match uu___148_205 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____206 -> false) quals
                 in
              let uu____207 = binders_as_mlty_binders env bs  in
              (match uu____207 with
               | (env1,ml_bs) ->
                   let body1 =
                     let uu____225 =
                       FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                     FStar_All.pipe_right uu____225
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env1))
                      in
                   let mangled_projector =
                     let uu____228 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___149_230  ->
                               match uu___149_230 with
                               | FStar_Syntax_Syntax.Projector uu____231 ->
                                   true
                               | uu____234 -> false))
                        in
                     if uu____228
                     then
                       let mname = mangle_projector_lid lid  in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None  in
                   let td =
                     let uu____250 =
                       let uu____261 = lident_as_mlsymbol lid  in
                       (assumed, uu____261, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                        in
                     [uu____250]  in
                   let def3 =
                     let uu____289 =
                       let uu____290 =
                         FStar_Extraction_ML_Util.mlloc_of_range
                           (FStar_Ident.range_of_lid lid)
                          in
                       FStar_Extraction_ML_Syntax.MLM_Loc uu____290  in
                     [uu____289; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                   let env2 =
                     let uu____292 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___150_294  ->
                               match uu___150_294 with
                               | FStar_Syntax_Syntax.Assumption  -> true
                               | FStar_Syntax_Syntax.New  -> true
                               | uu____295 -> false))
                        in
                     if uu____292
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
    let uu____363 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____364 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____365 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____366 =
      let uu____367 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____372 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____373 =
                  let uu____374 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____374  in
                Prims.strcat uu____372 uu____373))
         in
      FStar_All.pipe_right uu____367 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____363 uu____364 uu____365
      uu____366
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ (l,_us,bs,t,_mut_i,datas)
              ->
              let uu____412 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____412 with
               | (bs1,t1) ->
                   let datas1 =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun se1  ->
                             match se1.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____425,t2,l',nparams,uu____429) when
                                 FStar_Ident.lid_equals l l' ->
                                 let uu____432 =
                                   FStar_Syntax_Util.arrow_formals t2  in
                                 (match uu____432 with
                                  | (bs',body) ->
                                      let uu____453 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs1) bs'
                                         in
                                      (match uu____453 with
                                       | (bs_params,rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____489  ->
                                                  fun uu____490  ->
                                                    match (uu____489,
                                                            uu____490)
                                                    with
                                                    | ((b',uu____500),
                                                       (b,uu____502)) ->
                                                        let uu____507 =
                                                          let uu____512 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b
                                                             in
                                                          (b', uu____512)  in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____507)
                                               bs_params bs1
                                              in
                                           let t3 =
                                             let uu____514 =
                                               let uu____517 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 uu____517
                                                in
                                             FStar_All.pipe_right uu____514
                                               (FStar_Syntax_Subst.subst
                                                  subst1)
                                              in
                                           [{ dname = d; dtyp = t3 }]))
                             | uu____522 -> []))
                      in
                   [{
                      iname = l;
                      iparams = bs1;
                      ityp = t1;
                      idatas = datas1;
                      iquals = (se.FStar_Syntax_Syntax.sigquals)
                    }])
          | uu____523 -> []))
  
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
          let uu____564 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____564
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____569 =
            let uu____570 =
              let uu____573 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____573  in
            uu____570.FStar_Syntax_Syntax.n  in
          match uu____569 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____576) ->
              FStar_List.map
                (fun uu____589  ->
                   match uu____589 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____593;
                        FStar_Syntax_Syntax.sort = uu____594;_},uu____595)
                       -> ppname.FStar_Ident.idText) bs
          | uu____598 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____609 =
          let uu____610 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          fst uu____610  in
        let uu____613 =
          let uu____619 = lident_as_mlsymbol ctor.dname  in
          let uu____620 =
            let uu____624 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____624  in
          (uu____619, uu____620)  in
        (uu____609, uu____613)  in
      let extract_one_family env1 ind =
        let uu____653 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____653 with
        | (env2,vars) ->
            let uu____679 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____679 with
             | (env3,ctors) ->
                 let uu____728 = FStar_Syntax_Util.arrow_formals ind.ityp  in
                 (match uu____728 with
                  | (indices,uu____749) ->
                      let ml_params =
                        let uu____764 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____779  ->
                                    let uu____782 =
                                      let uu____783 =
                                        FStar_Util.string_of_int i  in
                                      Prims.strcat "'dummyV" uu____783  in
                                    (uu____782, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars uu____764  in
                      let tbody =
                        let uu____787 =
                          FStar_Util.find_opt
                            (fun uu___151_789  ->
                               match uu___151_789 with
                               | FStar_Syntax_Syntax.RecordType uu____790 ->
                                   true
                               | uu____795 -> false) ind.iquals
                           in
                        match uu____787 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____802 = FStar_List.hd ctors  in
                            (match uu____802 with
                             | (uu____813,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____831  ->
                                          match uu____831 with
                                          | (uu____836,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id])
                                                 in
                                              let uu____839 =
                                                lident_as_mlsymbol lid  in
                                              (uu____839, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____840 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____842 =
                        let uu____853 = lident_as_mlsymbol ind.iname  in
                        (false, uu____853, None, ml_params, (Some tbody))  in
                      (env3, uu____842)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____874,t,uu____876,uu____877,uu____878);
            FStar_Syntax_Syntax.sigrng = uu____879;
            FStar_Syntax_Syntax.sigquals = uu____880;
            FStar_Syntax_Syntax.sigmeta = uu____881;_}::[],uu____882),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____890 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____890 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____917),quals) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____928 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____928 with
           | (env1,td) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____980 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1001 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1001);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1005 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1010 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1019 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____1047 =
               let uu____1050 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____1050 ml_name tysc
                 false false
                in
             match uu____1047 with
             | (g2,mangled_name) ->
                 ((let uu____1056 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____1056
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
             (let uu____1068 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1068
              then
                let uu____1069 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____1069
              else ());
             (let uu____1071 =
                let uu____1072 = FStar_Syntax_Subst.compress tm  in
                uu____1072.FStar_Syntax_Syntax.n  in
              match uu____1071 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____1078) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____1089 =
                    let uu____1094 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____1094  in
                  (match uu____1089 with
                   | (uu____1123,uu____1124,tysc,uu____1126) ->
                       let uu____1127 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____1127, tysc))
              | uu____1128 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____1144 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____1144
              then
                let uu____1145 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____1146 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____1145
                  uu____1146
              else ());
             (let uu____1148 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____1148 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____1158 =
                      FStar_Syntax_Syntax.new_bv
                        (Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____1158  in
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
                  let uu____1181 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____1181 with
                   | (a_let,uu____1188,ty) ->
                       ((let uu____1191 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____1191
                         then
                           let uu____1192 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____1192
                         else ());
                        (let uu____1194 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____1199,uu____1200,mllb::[]),uu____1202)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | None  -> failwith "No type scheme")
                           | uu____1213 -> failwith "Impossible"  in
                         match uu____1194 with
                         | (exp,tysc) ->
                             ((let uu____1221 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____1221
                               then
                                 ((let uu____1223 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm (snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____1223);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (fst x)) (fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____1230 =
             let uu____1233 =
               extract_fv (snd ed.FStar_Syntax_Syntax.return_repr)  in
             match uu____1233 with
             | (return_tm,ty_sc) ->
                 let uu____1241 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____1241 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____1230 with
            | (g1,return_decl) ->
                let uu____1253 =
                  let uu____1256 =
                    extract_fv (snd ed.FStar_Syntax_Syntax.bind_repr)  in
                  match uu____1256 with
                  | (bind_tm,ty_sc) ->
                      let uu____1264 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____1264 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____1253 with
                 | (g2,bind_decl) ->
                     let uu____1276 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____1276 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____1288 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1291,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1295 =
             let uu____1296 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___152_1298  ->
                       match uu___152_1298 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____1299 -> false))
                in
             Prims.op_Negation uu____1296  in
           if uu____1295
           then (g, [])
           else
             (let uu____1305 = FStar_Syntax_Util.arrow_formals t  in
              match uu____1305 with
              | (bs,uu____1317) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let uu____1329 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals uu____1329)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____1331,uu____1332)
           when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1343 =
             let uu____1348 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____1348 with
             | (tcenv,uu____1364,def_typ) ->
                 let uu____1368 = as_pair def_typ  in (tcenv, uu____1368)
              in
           (match uu____1343 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.unfold_whnf tcenv lbtyp  in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____1383 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____1383 quals lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1385,attrs) ->
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
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____1410) ->
                   let uu____1415 =
                     let uu____1416 = FStar_Syntax_Subst.compress h'  in
                     uu____1416.FStar_Syntax_Syntax.n  in
                   (match uu____1415 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Syntax_Const.tactic_lid
                        ->
                        let uu____1420 =
                          let uu____1421 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule
                             in
                          FStar_Util.starts_with uu____1421 "FStar.Tactics"
                           in
                        Prims.op_Negation uu____1420
                    | uu____1422 -> false)
               | uu____1423 -> false  in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____1448 =
                   let uu____1449 =
                     let uu____1450 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1450
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____1449  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1448
                  in
               let lid_arg =
                 let uu____1452 =
                   let uu____1453 = FStar_Ident.string_of_lid assm_lid  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1453  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1452  in
               let tac_arity = FStar_List.length bs  in
               let arity =
                 let uu____1459 =
                   let uu____1460 =
                     let uu____1461 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1"))
                        in
                     FStar_Ident.lid_of_str uu____1461  in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____1460  in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____1459  in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs
                  in
               let app =
                 let uu____1467 =
                   let uu____1468 =
                     let uu____1472 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation]
                        in
                     (h, uu____1472)  in
                   FStar_Extraction_ML_Syntax.MLE_App uu____1468  in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____1467
                  in
               FStar_Extraction_ML_Syntax.MLM_Top app  in
             match snd lbs with
             | hd1::[] ->
                 let uu____1478 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp
                    in
                 (match uu____1478 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp  in
                      let uu____1496 =
                        let uu____1497 = FStar_Syntax_Subst.compress t  in
                        uu____1497.FStar_Syntax_Syntax.n  in
                      (match uu____1496 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h  in
                           let tac_lid =
                             let uu____1519 =
                               let uu____1524 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname
                                  in
                               uu____1524.FStar_Syntax_Syntax.fv_name  in
                             uu____1519.FStar_Syntax_Syntax.v  in
                           let assm_lid =
                             let uu____1529 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText)
                                in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____1529
                              in
                           let uu____1530 = is_tactic_decl assm_lid h1  in
                           if uu____1530
                           then
                             let uu____1532 =
                               let uu____1533 =
                                 let uu____1536 = FStar_List.hd args  in
                                 fst uu____1536  in
                               mk_registration tac_lid assm_lid uu____1533 bs
                                in
                             [uu____1532]
                           else []
                       | uu____1548 -> []))
             | uu____1549 -> []  in
           let uu____1551 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1551 with
            | (ml_let,uu____1559,uu____1560) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1565,bindings),uu____1567) ->
                     let uu____1574 =
                       FStar_List.fold_left2
                         (fun uu____1581  ->
                            fun ml_lb  ->
                              fun uu____1583  ->
                                match (uu____1581, uu____1583) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1596;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1598;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1599;_})
                                    ->
                                    let lb_lid =
                                      let uu____1613 =
                                        let uu____1618 =
                                          FStar_Util.right lbname  in
                                        uu____1618.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____1613.FStar_Syntax_Syntax.v  in
                                    let uu____1622 =
                                      let uu____1625 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___153_1627  ->
                                                match uu___153_1627 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1628 -> true
                                                | uu____1631 -> false))
                                         in
                                      if uu____1625
                                      then
                                        let mname =
                                          let uu____1635 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____1635
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____1636 =
                                          let uu____1639 =
                                            FStar_Util.right lbname  in
                                          let uu____1640 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____1639 mname uu____1640
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____1636 with
                                        | (env1,uu____1644) ->
                                            (env1,
                                              (let uu___158_1645 = ml_lb  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((snd mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___158_1645.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___158_1645.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___158_1645.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___158_1645.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____1648 =
                                           let uu____1649 =
                                             let uu____1652 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____1652
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.fst uu____1649
                                            in
                                         (uu____1648, ml_lb))
                                       in
                                    (match uu____1622 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (snd lbs)
                        in
                     (match uu____1574 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___154_1672  ->
                                 match uu___154_1672 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1674 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___155_1679  ->
                                 match uu___155_1679 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1684));
                                     FStar_Syntax_Syntax.tk = uu____1685;
                                     FStar_Syntax_Syntax.pos = uu____1686;
                                     FStar_Syntax_Syntax.vars = uu____1687;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1692 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let uu____1696 =
                            let uu____1698 =
                              let uu____1700 =
                                let uu____1701 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____1701
                                 in
                              [uu____1700;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))]
                               in
                            FStar_List.append uu____1698
                              tactic_registration_decl
                             in
                          (g1, uu____1696))
                 | uu____1705 ->
                     let uu____1706 =
                       let uu____1707 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____1707
                        in
                     failwith uu____1706))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1712,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____1716 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1716
           then
             let always_fail =
               let imp =
                 let uu____1723 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____1723 with
                 | ([],t1) ->
                     let b =
                       let uu____1742 =
                         FStar_Syntax_Syntax.gen_bv "_" None t1  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____1742
                        in
                     let uu____1743 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____1743 None
                 | (bs,t1) ->
                     let uu____1756 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____1756 None
                  in
               let uu___159_1757 = se  in
               let uu____1758 =
                 let uu____1759 =
                   let uu____1765 =
                     let uu____1769 =
                       let uu____1771 =
                         let uu____1772 =
                           let uu____1775 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           FStar_Util.Inr uu____1775  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____1772;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Syntax_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         }  in
                       [uu____1771]  in
                     (false, uu____1769)  in
                   (uu____1765, [], [])  in
                 FStar_Syntax_Syntax.Sig_let uu____1759  in
               {
                 FStar_Syntax_Syntax.sigel = uu____1758;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___159_1757.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___159_1757.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___159_1757.FStar_Syntax_Syntax.sigmeta)
               }  in
             let uu____1782 = extract_sig g always_fail  in
             (match uu____1782 with
              | (g1,mlm) ->
                  let uu____1793 =
                    FStar_Util.find_map quals
                      (fun uu___156_1795  ->
                         match uu___156_1795 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1798 -> None)
                     in
                  (match uu____1793 with
                   | Some l ->
                       let uu____1803 =
                         let uu____1805 =
                           let uu____1806 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____1806  in
                         let uu____1807 =
                           let uu____1809 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____1809]  in
                         uu____1805 :: uu____1807  in
                       (g1, uu____1803)
                   | uu____1811 ->
                       let uu____1813 =
                         FStar_Util.find_map quals
                           (fun uu___157_1815  ->
                              match uu___157_1815 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1818)
                                  -> Some l
                              | uu____1819 -> None)
                          in
                       (match uu____1813 with
                        | Some uu____1823 -> (g1, [])
                        | uu____1825 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1831 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____1831 with
            | (ml_main,uu____1839,uu____1840) ->
                let uu____1841 =
                  let uu____1843 =
                    let uu____1844 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____1844  in
                  [uu____1843; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____1841))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1846 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____1850 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____1854 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1856 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____1874 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____1874 FStar_Pervasives.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1900 = FStar_Options.debug_any ()  in
       if uu____1900
       then
         let uu____1901 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print1 "Extracting module %s\n" uu____1901
       else ());
      (let uu____1903 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___160_1906 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___160_1906.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___160_1906.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___160_1906.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____1907 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____1907 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____1924 = FStar_Options.codegen ()  in
             match uu____1924 with
             | Some "Kremlin" -> true
             | uu____1926 -> false  in
           let uu____1928 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____1928
           then
             ((let uu____1933 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____1933);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  