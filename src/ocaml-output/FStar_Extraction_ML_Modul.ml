open Prims
let fail_exp lid t =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_648 =
           FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid
             FStar_Syntax_Syntax.Delta_constant None
            in
         let _0_647 =
           let _0_646 = FStar_Syntax_Syntax.iarg t  in
           let _0_645 =
             let _0_644 =
               let _0_643 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string
                          (let _0_642 =
                             FStar_Bytes.string_as_unicode_bytes
                               (let _0_641 =
                                  FStar_Syntax_Print.lid_to_string lid  in
                                Prims.strcat "Not yet implemented:" _0_641)
                              in
                           (_0_642, FStar_Range.dummyRange))))) None
                   FStar_Range.dummyRange
                  in
               FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_643  in
             [_0_644]  in
           _0_646 :: _0_645  in
         (_0_648, _0_647)))) None FStar_Range.dummyRange
  
let mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x 
let lident_as_mlsymbol : FStar_Ident.lident -> Prims.string =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText 
let binders_as_mlty_binders env bs =
  FStar_Util.fold_map
    (fun env  ->
       fun uu____70  ->
         match uu____70 with
         | (bv,uu____78) ->
             let _0_651 =
               let _0_649 =
                 Some
                   (FStar_Extraction_ML_Syntax.MLTY_Var
                      (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv))
                  in
               FStar_Extraction_ML_UEnv.extend_ty env bv _0_649  in
             let _0_650 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
             (_0_651, _0_650)) env bs
  
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
          let def =
            let _0_653 =
              let _0_652 = FStar_Syntax_Subst.compress def  in
              FStar_All.pipe_right _0_652 FStar_Syntax_Util.unmeta  in
            FStar_All.pipe_right _0_653 FStar_Syntax_Util.un_uinst  in
          let def =
            match def.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs uu____105 ->
                FStar_Extraction_ML_Term.normalize_abs def
            | uu____120 -> def  in
          let uu____121 =
            match def.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____128) ->
                FStar_Syntax_Subst.open_term bs body
            | uu____151 -> ([], def)  in
          match uu____121 with
          | (bs,body) ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___145_163  ->
                     match uu___145_163 with
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____164 -> false) quals
                 in
              let uu____165 = binders_as_mlty_binders env bs  in
              (match uu____165 with
               | (env,ml_bs) ->
                   let body =
                     let _0_654 =
                       FStar_Extraction_ML_Term.term_as_mlty env body  in
                     FStar_All.pipe_right _0_654
                       (FStar_Extraction_ML_Util.eraseTypeDeep
                          (FStar_Extraction_ML_Util.udelta_unfold env))
                      in
                   let mangled_projector =
                     let uu____185 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___146_187  ->
                               match uu___146_187 with
                               | FStar_Syntax_Syntax.Projector uu____188 ->
                                   true
                               | uu____191 -> false))
                        in
                     if uu____185
                     then
                       let mname = mangle_projector_lid lid  in
                       Some ((mname.FStar_Ident.ident).FStar_Ident.idText)
                     else None  in
                   let td =
                     let _0_656 =
                       let _0_655 = lident_as_mlsymbol lid  in
                       (assumed, _0_655, mangled_projector, ml_bs,
                         (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev body)))
                        in
                     [_0_656]  in
                   let def =
                     let _0_657 =
                       FStar_Extraction_ML_Syntax.MLM_Loc
                         (FStar_Extraction_ML_Util.mlloc_of_range
                            (FStar_Ident.range_of_lid lid))
                        in
                     [_0_657; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                   let env =
                     let uu____235 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___147_237  ->
                               match uu___147_237 with
                               | FStar_Syntax_Syntax.Assumption 
                                 |FStar_Syntax_Syntax.New  -> true
                               | uu____238 -> false))
                        in
                     if uu____235
                     then env
                     else FStar_Extraction_ML_UEnv.extend_tydef env fv td  in
                   (env, def))
  
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
    let _0_665 = FStar_Syntax_Print.lid_to_string i.iname  in
    let _0_664 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let _0_663 = FStar_Syntax_Print.term_to_string i.ityp  in
    let _0_662 =
      let _0_661 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let _0_660 = FStar_Syntax_Print.lid_to_string d.dname  in
                let _0_659 =
                  let _0_658 = FStar_Syntax_Print.term_to_string d.dtyp  in
                  Prims.strcat " : " _0_658  in
                Prims.strcat _0_660 _0_659))
         in
      FStar_All.pipe_right _0_661 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _0_665 _0_664 _0_663 _0_662
  
let bundle_as_inductive_families env ses quals =
  FStar_All.pipe_right ses
    (FStar_List.collect
       (fun uu___149_325  ->
          match uu___149_325 with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,_us,bs,t,_mut_i,datas,quals,r) ->
              let uu____341 = FStar_Syntax_Subst.open_term bs t  in
              (match uu____341 with
               | (bs,t) ->
                   let datas =
                     FStar_All.pipe_right ses
                       (FStar_List.collect
                          (fun uu___148_351  ->
                             match uu___148_351 with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (d,uu____354,t,l',nparams,uu____358,uu____359,uu____360)
                                 when FStar_Ident.lid_equals l l' ->
                                 let uu____365 =
                                   FStar_TypeChecker_Util.arrow_formals
                                     env.FStar_Extraction_ML_UEnv.tcenv t
                                    in
                                 (match uu____365 with
                                  | (bs',body) ->
                                      let uu____371 =
                                        FStar_Util.first_N
                                          (FStar_List.length bs) bs'
                                         in
                                      (match uu____371 with
                                       | (bs_params,rest) ->
                                           let subst =
                                             FStar_List.map2
                                               (fun uu____407  ->
                                                  fun uu____408  ->
                                                    match (uu____407,
                                                            uu____408)
                                                    with
                                                    | ((b',uu____418),
                                                       (b,uu____420)) ->
                                                        FStar_Syntax_Syntax.NT
                                                          (let _0_666 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (b', _0_666)))
                                               bs_params bs
                                              in
                                           let t =
                                             let _0_668 =
                                               let _0_667 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   body
                                                  in
                                               FStar_Syntax_Util.arrow rest
                                                 _0_667
                                                in
                                             FStar_All.pipe_right _0_668
                                               (FStar_Syntax_Subst.subst
                                                  subst)
                                              in
                                           [{ dname = d; dtyp = t }]))
                             | uu____426 -> []))
                      in
                   [{
                      iname = l;
                      iparams = bs;
                      ityp = t;
                      idatas = datas;
                      iquals = quals
                    }])
          | uu____427 -> []))
  
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env ctor =
        let mlt =
          let _0_669 = FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp
             in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env) _0_669
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let _0_673 =
          FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false  in
        let _0_672 =
          let _0_671 = lident_as_mlsymbol ctor.dname  in
          let _0_670 = FStar_Extraction_ML_Util.argTypes mlt  in
          (_0_671, _0_670)  in
        (_0_673, _0_672)  in
      let extract_one_family env ind =
        let uu____497 = binders_as_mlty_binders env ind.iparams  in
        match uu____497 with
        | (env,vars) ->
            let uu____523 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env)
               in
            (match uu____523 with
             | (env,ctors) ->
                 let uu____562 =
                   FStar_TypeChecker_Util.arrow_formals
                     env.FStar_Extraction_ML_UEnv.tcenv ind.ityp
                    in
                 (match uu____562 with
                  | (indices,uu____578) ->
                      let ml_params =
                        let _0_676 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____593  ->
                                    let _0_675 =
                                      let _0_674 = FStar_Util.string_of_int i
                                         in
                                      Prims.strcat "'dummyV" _0_674  in
                                    (_0_675, (Prims.parse_int "0"))))
                           in
                        FStar_List.append vars _0_676  in
                      let tbody =
                        let uu____597 =
                          FStar_Util.find_opt
                            (fun uu___150_599  ->
                               match uu___150_599 with
                               | FStar_Syntax_Syntax.RecordType uu____600 ->
                                   true
                               | uu____605 -> false) ind.iquals
                           in
                        match uu____597 with
                        | Some (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____612 = FStar_List.hd ctors  in
                            (match uu____612 with
                             | (uu____619,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun ty  ->
                                          let lid =
                                            FStar_Ident.lid_of_ids
                                              (FStar_List.append ns [id])
                                             in
                                          let _0_677 = lident_as_mlsymbol lid
                                             in
                                          (_0_677, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____633 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let _0_679 =
                        let _0_678 = lident_as_mlsymbol ind.iname  in
                        (false, _0_678, None, ml_params, (Some tbody))  in
                      (env, _0_679)))
         in
      match se with
      | FStar_Syntax_Syntax.Sig_bundle
          ((FStar_Syntax_Syntax.Sig_datacon
           (l,uu____654,t,uu____656,uu____657,uu____658,uu____659,uu____660))::[],(FStar_Syntax_Syntax.ExceptionConstructor
           )::[],uu____661,r)
          ->
          let uu____671 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____671 with
           | (env,ctor) -> (env, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____693,r) ->
          let ifams = bundle_as_inductive_families env ses quals  in
          let uu____704 = FStar_Util.fold_map extract_one_family env ifams
             in
          (match uu____704 with
           | (env,td) -> (env, [FStar_Extraction_ML_Syntax.MLM_Ty td]))
      | uu____756 -> failwith "Unexpected signature element"
  
let rec extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let _0_680 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" _0_680);
      (match se with
       | FStar_Syntax_Syntax.Sig_bundle _
         |FStar_Syntax_Syntax.Sig_inductive_typ _
          |FStar_Syntax_Syntax.Sig_datacon _ -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____781) when
           FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g lid ml_name tm tysc =
             let mangled_name = Prims.snd ml_name  in
             let g =
               let _0_681 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g _0_681 ml_name tysc
                 false false
                in
             let lb =
               {
                 FStar_Extraction_ML_Syntax.mllb_name =
                   (mangled_name, (Prims.parse_int "0"));
                 FStar_Extraction_ML_Syntax.mllb_tysc = None;
                 FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                 FStar_Extraction_ML_Syntax.mllb_def = tm;
                 FStar_Extraction_ML_Syntax.print_typ = false
               }  in
             (g,
               (FStar_Extraction_ML_Syntax.MLM_Let
                  (FStar_Extraction_ML_Syntax.NonRec, [], [lb])))
              in
           let rec extract_fv tm =
             let uu____819 =
               (FStar_Syntax_Subst.compress tm).FStar_Syntax_Syntax.n  in
             match uu____819 with
             | FStar_Syntax_Syntax.Tm_uinst (tm,uu____823) -> extract_fv tm
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let mlp =
                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 let uu____834 =
                   let _0_682 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
                   FStar_All.pipe_left FStar_Util.right _0_682  in
                 (match uu____834 with
                  | (uu____855,tysc,uu____857) ->
                      let _0_683 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top)
                          (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                         in
                      (_0_683, tysc))
             | uu____858 -> failwith "Not an fv"  in
           let extract_action g a =
             let uu____870 = extract_fv a.FStar_Syntax_Syntax.action_defn  in
             match uu____870 with
             | (a_tm,ty_sc) ->
                 let uu____877 = FStar_Extraction_ML_UEnv.action_name ed a
                    in
                 (match uu____877 with
                  | (a_nm,a_lid) -> extend_env g a_lid a_nm a_tm ty_sc)
              in
           let uu____884 =
             let uu____887 =
               extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr)  in
             match uu____887 with
             | (return_tm,ty_sc) ->
                 let uu____895 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____895 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____884 with
            | (g,return_decl) ->
                let uu____907 =
                  let uu____910 =
                    extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____910 with
                  | (bind_tm,ty_sc) ->
                      let uu____918 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____918 with
                       | (bind_nm,bind_lid) ->
                           extend_env g bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____907 with
                 | (g,bind_decl) ->
                     let uu____930 =
                       FStar_Util.fold_map extract_action g
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____930 with
                      | (g,actions) ->
                          (g,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____942 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ
           (lid,uu____947,t,quals,uu____950) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____953 =
             let _0_684 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___151_955  ->
                       match uu___151_955 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____956 -> false))
                in
             FStar_All.pipe_right _0_684 Prims.op_Negation  in
           if uu____953
           then (g, [])
           else
             (let uu____962 =
                FStar_TypeChecker_Util.arrow_formals
                  g.FStar_Extraction_ML_UEnv.tcenv t
                 in
              match uu____962 with
              | (bs,uu____969) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant None
                     in
                  let _0_685 =
                    FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit
                      None
                     in
                  extract_typ_abbrev g fv quals _0_685)
       | FStar_Syntax_Syntax.Sig_let
           ((false ,lb::[]),uu____977,uu____978,quals,uu____980) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let _0_686 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           extract_typ_abbrev g _0_686 quals lb.FStar_Syntax_Syntax.lbdef
       | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____993,quals,attrs) ->
           let elet =
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_let
                   (lbs, FStar_Syntax_Const.exp_false_bool))) None r
              in
           let uu____1013 = FStar_Extraction_ML_Term.term_as_mlexpr g elet
              in
           (match uu____1013 with
            | (ml_let,uu____1021,uu____1022) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____1027,bindings),uu____1029) ->
                     let uu____1036 =
                       FStar_List.fold_left2
                         (fun uu____1043  ->
                            fun ml_lb  ->
                              fun uu____1045  ->
                                match (uu____1043, uu____1045) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____1058;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____1060;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____1061;_})
                                    ->
                                    let lb_lid =
                                      ((FStar_Util.right lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    let uu____1079 =
                                      let uu____1082 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___152_1084  ->
                                                match uu___152_1084 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____1085 -> true
                                                | uu____1088 -> false))
                                         in
                                      if uu____1082
                                      then
                                        let mname =
                                          let _0_687 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right _0_687
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let env =
                                          let _0_689 =
                                            FStar_Util.right lbname  in
                                          let _0_688 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env _0_689 mname _0_688
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        (env,
                                          (let uu___157_1093 = ml_lb  in
                                           {
                                             FStar_Extraction_ML_Syntax.mllb_name
                                               =
                                               ((Prims.snd mname),
                                                 (Prims.parse_int "0"));
                                             FStar_Extraction_ML_Syntax.mllb_tysc
                                               =
                                               (uu___157_1093.FStar_Extraction_ML_Syntax.mllb_tysc);
                                             FStar_Extraction_ML_Syntax.mllb_add_unit
                                               =
                                               (uu___157_1093.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                             FStar_Extraction_ML_Syntax.mllb_def
                                               =
                                               (uu___157_1093.FStar_Extraction_ML_Syntax.mllb_def);
                                             FStar_Extraction_ML_Syntax.print_typ
                                               =
                                               (uu___157_1093.FStar_Extraction_ML_Syntax.print_typ)
                                           }))
                                      else
                                        (let _0_692 =
                                           let _0_691 =
                                             let _0_690 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t _0_690
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left Prims.fst
                                             _0_691
                                            in
                                         (_0_692, ml_lb))
                                       in
                                    (match uu____1079 with
                                     | (g,ml_lb) -> (g, (ml_lb :: ml_lbs))))
                         (g, []) bindings (Prims.snd lbs)
                        in
                     (match uu____1036 with
                      | (g,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___153_1115  ->
                                 match uu___153_1115 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     Some FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     Some FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____1117 -> None) quals
                             in
                          let flags' =
                            FStar_List.choose
                              (fun uu___154_1122  ->
                                 match uu___154_1122 with
                                 | {
                                     FStar_Syntax_Syntax.n =
                                       FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_string
                                       (data,uu____1127));
                                     FStar_Syntax_Syntax.tk = uu____1128;
                                     FStar_Syntax_Syntax.pos = uu____1129;
                                     FStar_Syntax_Syntax.vars = uu____1130;_}
                                     ->
                                     Some
                                       (FStar_Extraction_ML_Syntax.Attribute
                                          (FStar_Util.string_of_unicode data))
                                 | uu____1135 ->
                                     (FStar_Util.print_warning
                                        "Warning: unrecognized, non-string attribute, bother protz for a better error message";
                                      None)) attrs
                             in
                          let _0_694 =
                            let _0_693 =
                              FStar_Extraction_ML_Syntax.MLM_Loc
                                (FStar_Extraction_ML_Util.mlloc_of_range r)
                               in
                            [_0_693;
                            FStar_Extraction_ML_Syntax.MLM_Let
                              (flavor, (FStar_List.append flags flags'),
                                (FStar_List.rev ml_lbs'))]
                             in
                          (g, _0_694))
                 | uu____1142 ->
                     failwith
                       (let _0_695 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule ml_let
                           in
                        FStar_Util.format1
                          "Impossible: Translated a let to a non-let: %s"
                          _0_695)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1147,t,quals,r) ->
           let uu____1153 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____1153
           then
             let always_fail =
               let imp =
                 let uu____1162 =
                   FStar_TypeChecker_Util.arrow_formals
                     g.FStar_Extraction_ML_UEnv.tcenv t
                    in
                 match uu____1162 with
                 | ([],t) -> fail_exp lid t
                 | (bs,t) ->
                     let _0_696 = fail_exp lid t  in
                     FStar_Syntax_Util.abs bs _0_696 None
                  in
               FStar_Syntax_Syntax.Sig_let
                 (let _0_700 =
                    let _0_699 =
                      let _0_698 =
                        let _0_697 =
                          FStar_Util.Inr
                            (FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant None)
                           in
                        {
                          FStar_Syntax_Syntax.lbname = _0_697;
                          FStar_Syntax_Syntax.lbunivs = [];
                          FStar_Syntax_Syntax.lbtyp = t;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Syntax_Const.effect_ML_lid;
                          FStar_Syntax_Syntax.lbdef = imp
                        }  in
                      [_0_698]  in
                    (false, _0_699)  in
                  (_0_700, r, [], quals, []))
                in
             let uu____1187 = extract_sig g always_fail  in
             (match uu____1187 with
              | (g,mlm) ->
                  let uu____1198 =
                    FStar_Util.find_map quals
                      (fun uu___155_1200  ->
                         match uu___155_1200 with
                         | FStar_Syntax_Syntax.Discriminator l -> Some l
                         | uu____1203 -> None)
                     in
                  (match uu____1198 with
                   | Some l ->
                       let _0_704 =
                         let _0_703 =
                           FStar_Extraction_ML_Syntax.MLM_Loc
                             (FStar_Extraction_ML_Util.mlloc_of_range r)
                            in
                         let _0_702 =
                           let _0_701 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g lid l
                              in
                           [_0_701]  in
                         _0_703 :: _0_702  in
                       (g, _0_704)
                   | uu____1209 ->
                       let uu____1211 =
                         FStar_Util.find_map quals
                           (fun uu___156_1213  ->
                              match uu___156_1213 with
                              | FStar_Syntax_Syntax.Projector (l,uu____1216)
                                  -> Some l
                              | uu____1217 -> None)
                          in
                       (match uu____1211 with
                        | Some uu____1221 -> (g, [])
                        | uu____1223 -> (g, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let uu____1230 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____1230 with
            | (ml_main,uu____1238,uu____1239) ->
                let _0_706 =
                  let _0_705 =
                    FStar_Extraction_ML_Syntax.MLM_Loc
                      (FStar_Extraction_ML_Util.mlloc_of_range r)
                     in
                  [_0_705; FStar_Extraction_ML_Syntax.MLM_Top ml_main]  in
                (g, _0_706))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____1241 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma (p,uu____1252) ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
  
let extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let _0_707 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right _0_707 Prims.fst
  
let extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib
        Prims.list)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____1282 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g =
         let uu___158_1285 = g  in
         {
           FStar_Extraction_ML_UEnv.tcenv =
             (uu___158_1285.FStar_Extraction_ML_UEnv.tcenv);
           FStar_Extraction_ML_UEnv.gamma =
             (uu___158_1285.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___158_1285.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____1286 =
         FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
          in
       match uu____1286 with
       | (g,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____1303 = FStar_Options.codegen ()  in
             match uu____1303 with
             | Some "Kremlin" -> true
             | uu____1305 -> false  in
           let uu____1307 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____1307
           then
             ((let _0_708 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" _0_708);
              (g,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g, []))
  