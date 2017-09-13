open Prims
type file =
  (Prims.string,FStar_Extraction_JavaScript_Ast.t)
    FStar_Pervasives_Native.tuple2
type env_t =
  {
  names: name Prims.list;
  module_name: Prims.string;
  import_module_names: Prims.string Prims.list;}
and name = {
  pretty: Prims.string;
  mut: Prims.bool;}
let __proj__Mkenv_t__item__names: env_t -> name Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; module_name = __fname__module_name;
        import_module_names = __fname__import_module_names;_} ->
        __fname__names
let __proj__Mkenv_t__item__module_name: env_t -> Prims.string =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; module_name = __fname__module_name;
        import_module_names = __fname__import_module_names;_} ->
        __fname__module_name
let __proj__Mkenv_t__item__import_module_names:
  env_t -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; module_name = __fname__module_name;
        import_module_names = __fname__import_module_names;_} ->
        __fname__import_module_names
let __proj__Mkname__item__pretty: name -> Prims.string =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__pretty
let __proj__Mkname__item__mut: name -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__mut
let empty: Prims.string -> env_t =
  fun module_name  -> { names = []; module_name; import_module_names = [] }
let mk_op_bin:
  Prims.string ->
    FStar_Extraction_JavaScript_Ast.op_bin FStar_Pervasives_Native.option
  =
  fun uu___147_91  ->
    match uu___147_91 with
    | "op_Addition" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSB_Plus
    | "op_Subtraction" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_Minus
    | "op_Multiply" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSB_Mult
    | "op_Division" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSB_Div
    | "op_Equality" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_Equal
    | "op_disEquality" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_NotEqual
    | "op_LessThanOrEqual" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual
    | "op_GreaterThanOrEqual" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual
    | "op_LessThan" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_LessThan
    | "op_GreaterThan" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSB_GreaterThan
    | "op_Modulus" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSB_Mod
    | uu____94 -> FStar_Pervasives_Native.None
let is_op_bin: Prims.string -> Prims.bool =
  fun op  -> (mk_op_bin op) <> FStar_Pervasives_Native.None
let mk_op_un:
  Prims.string ->
    FStar_Extraction_JavaScript_Ast.op_un FStar_Pervasives_Native.option
  =
  fun uu___148_106  ->
    match uu___148_106 with
    | "op_Negation" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSU_Not
    | "op_Minus" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JSU_Minus
    | uu____109 -> FStar_Pervasives_Native.None
let is_op_un: Prims.string -> Prims.bool =
  fun op  -> (mk_op_un op) <> FStar_Pervasives_Native.None
let mk_op_bool:
  Prims.string ->
    FStar_Extraction_JavaScript_Ast.op_log FStar_Pervasives_Native.option
  =
  fun uu___149_121  ->
    match uu___149_121 with
    | "op_AmpAmp" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSL_And
    | "op_BarBar" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JSL_Or
    | uu____124 -> FStar_Pervasives_Native.None
let is_op_bool: Prims.string -> Prims.bool =
  fun op  -> (mk_op_bool op) <> FStar_Pervasives_Native.None
let mk_standart_type:
  Prims.string ->
    FStar_Extraction_JavaScript_Ast.typ FStar_Pervasives_Native.option
  =
  fun uu___150_136  ->
    match uu___150_136 with
    | "unit" ->
        FStar_Pervasives_Native.Some FStar_Extraction_JavaScript_Ast.JST_Null
    | "bool" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JST_Boolean
    | "int" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JST_Number
    | "nat" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JST_Number
    | "string" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_JavaScript_Ast.JST_String
    | uu____139 -> FStar_Pervasives_Native.None
let is_standart_type: Prims.string -> Prims.bool =
  fun t  -> (mk_standart_type t) <> FStar_Pervasives_Native.None
let float_of_int: Prims.int -> FStar_BaseTypes.float =
  fun i  -> FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)
let isMutable:
  'Auu____154 .
    ('Auu____154,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
      Prims.bool
  =
  fun typ  ->
    match typ with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some (uu____175,ty) ->
        (match ty with
         | FStar_Extraction_ML_Syntax.MLTY_Named (uu____181,p) when
             let uu____187 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____187 = "FStar.ST.ref" -> true
         | uu____188 -> false)
let extendEnv:
  'Auu____197 .
    env_t ->
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
        ->
        ('Auu____197,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
          env_t
  =
  fun env  ->
    fun uu____220  ->
      fun typ  ->
        match uu____220 with
        | (path,n1) ->
            let path1 = FStar_String.concat "_" path in
            if (path1 = env.module_name) || (path1 = "")
            then
              let uu___151_241 = env in
              {
                names = ({ pretty = n1; mut = (isMutable typ) } ::
                  (env.names));
                module_name = (uu___151_241.module_name);
                import_module_names = (uu___151_241.import_module_names)
              }
            else
              (let n2 = Prims.strcat path1 (Prims.strcat "." n1) in
               if
                 Prims.op_Negation
                   (FStar_List.existsb (fun x  -> x = path1)
                      env.import_module_names)
               then
                 let uu___152_246 = env in
                 {
                   names = ({ pretty = n2; mut = (isMutable typ) } ::
                     (env.names));
                   module_name = (uu___152_246.module_name);
                   import_module_names = (path1 :: (env.import_module_names))
                 }
               else
                 (let uu___153_248 = env in
                  {
                    names = ({ pretty = n2; mut = (isMutable typ) } ::
                      (env.names));
                    module_name = (uu___153_248.module_name);
                    import_module_names = (uu___153_248.import_module_names)
                  }))
let addImportModule:
  env_t ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
      (Prims.string,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____266  ->
      match uu____266 with
      | (path,name) ->
          let path1 = FStar_String.concat "_" path in
          if (path1 = env.module_name) || (path1 = "")
          then (name, env)
          else
            (let name1 = Prims.strcat path1 (Prims.strcat "." name) in
             if
               Prims.op_Negation
                 (FStar_List.existsb (fun x  -> x = path1)
                    env.import_module_names)
             then
               (name1,
                 (let uu___154_297 = env in
                  {
                    names = (uu___154_297.names);
                    module_name = (uu___154_297.module_name);
                    import_module_names = (path1 ::
                      (env.import_module_names))
                  }))
             else (name1, env))
let findEnv: env_t -> Prims.string -> Prims.int =
  fun env  ->
    fun name  -> FStar_List.index (fun x  -> x.pretty = name) env.names
let isInEnv: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun name  -> FStar_List.existsb (fun x  -> x.pretty = name) env.names
let rec is_pure_expr:
  'Auu____325 .
    FStar_Extraction_ML_Syntax.mlexpr ->
      (FStar_Extraction_ML_Syntax.mlsymbol,'Auu____325)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun e  ->
    fun var  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const uu____342 -> true
      | FStar_Extraction_ML_Syntax.MLE_Name uu____343 -> true
      | FStar_Extraction_ML_Syntax.MLE_Var (n1,uu____345) ->
          n1 <> (FStar_Pervasives_Native.fst var)
      | FStar_Extraction_ML_Syntax.MLE_Proj (expr,uu____347) ->
          is_pure_expr expr var
      | FStar_Extraction_ML_Syntax.MLE_CTor (p,le) ->
          let uu____354 =
            let uu____355 = FStar_List.map (fun x  -> is_pure_expr x var) le in
            FStar_List.contains false uu____355 in
          Prims.op_Negation uu____354
      | FStar_Extraction_ML_Syntax.MLE_Tuple le ->
          let uu____363 =
            let uu____364 = FStar_List.map (fun x  -> is_pure_expr x var) le in
            FStar_List.contains false uu____364 in
          Prims.op_Negation uu____363
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____369,lne) ->
          let uu____387 =
            let uu____388 =
              FStar_List.map
                (fun uu____398  ->
                   match uu____398 with | (n1,e1) -> is_pure_expr e1 var) lne in
            FStar_List.contains false uu____388 in
          Prims.op_Negation uu____387
      | FStar_Extraction_ML_Syntax.MLE_App (uu____405,args) ->
          let uu____411 =
            let uu____412 =
              FStar_List.map (fun x  -> is_pure_expr x var) args in
            FStar_List.contains false uu____412 in
          Prims.op_Negation uu____411
      | uu____417 -> false
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____642  ->
    match uu____642 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____702 = m in
               match uu____702 with
               | ((prefix1,final),uu____723,uu____724) ->
                   FStar_String.concat "_"
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____756 = translate_module (empty m_name) m in
                FStar_Pervasives_Native.Some uu____756)
             with
             | e ->
                 ((let uu____765 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____765);
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  env_t ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 ->
      file
  =
  fun env  ->
    fun uu____767  ->
      match uu____767 with
      | (module_name,modul,uu____788) ->
          let program =
            match modul with
            | FStar_Pervasives_Native.Some (_signature,decls) ->
                let update_env uu____827 =
                  let uu___157_828 = env in
                  {
                    names = [];
                    module_name = (uu___157_828.module_name);
                    import_module_names = (uu___157_828.import_module_names)
                  } in
                let res =
                  FStar_List.filter_map
                    (fun d  -> translate_decl (update_env ()) d) decls in
                let td =
                  FStar_List.map
                    (fun uu____852  -> match uu____852 with | (x,e) -> x) res in
                let lmodules =
                  FStar_List.collect
                    (fun uu____869  ->
                       match uu____869 with | (x,e) -> e.import_module_names)
                    res in
                let lmodules1 =
                  FStar_List.fold_left
                    (fun acc  ->
                       fun m  ->
                         if FStar_List.existsb (fun x  -> x = m) acc
                         then acc
                         else m :: acc) [] lmodules in
                let create_module_imports =
                  let uu____895 =
                    let uu____896 =
                      FStar_List.map
                        (fun m  ->
                           FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration
                             (m, FStar_Pervasives_Native.None)) lmodules1 in
                    FStar_All.pipe_right uu____896
                      (fun _0_44  ->
                         FStar_Extraction_JavaScript_Ast.JSS_Block _0_44) in
                  FStar_All.pipe_right uu____895
                    (fun _0_45  ->
                       FStar_Extraction_JavaScript_Ast.JS_Statement _0_45) in
                FStar_List.append [create_module_imports] td
            | uu____905 ->
                failwith "Unexpected standalone interface or nested modules" in
          ((env.module_name), program)
and translate_decl:
  env_t ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      (FStar_Extraction_JavaScript_Ast.source_t,env_t)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (uu____924,c_flag,lfunc) ->
          let for1 uu____942 env1 =
            match uu____942 with
            | { FStar_Extraction_ML_Syntax.mllb_name = (name,uu____951);
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b;
                FStar_Extraction_ML_Syntax.mllb_def = expr;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let uu____958 =
                  if (Prims.op_Negation pt) || unit_b
                  then (FStar_Pervasives_Native.None, env1)
                  else
                    (match tys with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Pervasives_Native.None, env1)
                     | FStar_Pervasives_Native.Some (lp,ty) ->
                         let lp_generic =
                           match lp with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____999 ->
                               let uu____1000 =
                                 FStar_List.map
                                   (fun uu____1010  ->
                                      match uu____1010 with
                                      | (id,uu____1016) -> id) lp in
                               FStar_Pervasives_Native.Some uu____1000 in
                         let uu____1019 = translate_type ty lp_generic env1 in
                         (match uu____1019 with
                          | (t,env2) ->
                              ((FStar_Pervasives_Native.Some t), env2))) in
                (match uu____958 with
                 | (t,env2) ->
                     let is_private =
                       FStar_List.contains FStar_Extraction_ML_Syntax.Private
                         c_flag in
                     let uu____1047 =
                       let uu____1054 = is_pure_expr expr (name, t) in
                       if uu____1054
                       then
                         let var_decl_q =
                           if isMutable tys
                           then FStar_Extraction_JavaScript_Ast.JSV_Let
                           else FStar_Extraction_JavaScript_Ast.JSV_Const in
                         let env3 = extendEnv env2 ([], name) tys in
                         let uu____1070 = translate_expr_pure expr env3 in
                         match uu____1070 with
                         | (r,env4) ->
                             ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                 (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                      (name, t)),
                                    (FStar_Pervasives_Native.Some r)),
                                   var_decl_q)], env4)
                       else translate_expr expr (name, t) [] env2 false in
                     (match uu____1047 with
                      | (c,env3) ->
                          if is_private
                          then (c, env3)
                          else
                            ([FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration
                                ((FStar_Extraction_JavaScript_Ast.JSE_Declaration
                                    (FStar_Extraction_JavaScript_Ast.JSS_Block
                                       c)),
                                  FStar_Extraction_JavaScript_Ast.ExportValue)],
                              env3))) in
          let uu____1121 =
            FStar_List.fold_left
              (fun uu____1142  ->
                 fun x  ->
                   match uu____1142 with
                   | (r,e) ->
                       let update_env uu____1165 =
                         let uu___158_1166 = e in
                         {
                           names = [];
                           module_name = (uu___158_1166.module_name);
                           import_module_names =
                             (uu___158_1166.import_module_names)
                         } in
                       let uu____1167 = for1 x (update_env ()) in
                       (match uu____1167 with
                        | (r1,e1) ->
                            ((FStar_List.append r
                                [FStar_Extraction_JavaScript_Ast.JSS_Seq r1]),
                              e1))) ([], env) lfunc in
          (match uu____1121 with
           | (r,env1) ->
               FStar_Pervasives_Native.Some
                 ((FStar_Extraction_JavaScript_Ast.JS_Statement
                     (FStar_Extraction_JavaScript_Ast.JSS_Block r)), env1))
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____1206 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____1211,name,uu____1213,tparams,uu____1215,body)::[]) ->
          let tparams1 =
            match tparams with
            | [] -> FStar_Pervasives_Native.None
            | uu____1268 ->
                let uu____1269 =
                  FStar_List.map
                    (fun uu____1279  ->
                       match uu____1279 with | (id,uu____1285) -> id) tparams in
                FStar_Pervasives_Native.Some uu____1269 in
          let forbody body1 =
            let get_export stmt =
              FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration
                ((FStar_Extraction_JavaScript_Ast.JSE_Declaration stmt),
                  FStar_Extraction_JavaScript_Ast.ExportType) in
            match body1 with
            | FStar_Extraction_ML_Syntax.MLTD_Abbrev t ->
                let uu____1305 = translate_type t tparams1 env in
                (match uu____1305 with
                 | (t1,env1) ->
                     ((get_export
                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                            ((name, FStar_Pervasives_Native.None), tparams1,
                              t1))), env1))
            | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                let tag =
                  [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                       ("_tag", FStar_Pervasives_Native.None)),
                     (FStar_Extraction_JavaScript_Ast.JST_StringLiteral
                        ("Record", "")))] in
                let uu____1352 =
                  FStar_List.fold_left
                    (fun uu____1386  ->
                       fun uu____1387  ->
                         match (uu____1386, uu____1387) with
                         | ((r,e),(n1,t)) ->
                             let uu____1456 = translate_type t tparams1 e in
                             (match uu____1456 with
                              | (r1,e1) ->
                                  ((FStar_List.append r
                                      [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                           ((Prims.strcat "_" n1),
                                             FStar_Pervasives_Native.None)),
                                         r1)]), e1))) ([], env) fields in
                (match uu____1352 with
                 | (fields_t,env1) ->
                     ((get_export
                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                            ((name, FStar_Pervasives_Native.None), tparams1,
                              (FStar_Extraction_JavaScript_Ast.JST_Object
                                 (FStar_List.append tag fields_t))))), env1))
            | FStar_Extraction_ML_Syntax.MLTD_DType lfields ->
                let tag n1 =
                  [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                       ("_tag", FStar_Pervasives_Native.None)),
                     (FStar_Extraction_JavaScript_Ast.JST_StringLiteral
                        (n1, "")))] in
                let fields_t fields env1 =
                  FStar_List.fold_left
                    (fun uu____1622  ->
                       fun uu____1623  ->
                         match (uu____1622, uu____1623) with
                         | ((r,e),(n1,t)) ->
                             let uu____1692 = translate_type t tparams1 e in
                             (match uu____1692 with
                              | (r1,e1) ->
                                  ((FStar_List.append r
                                      [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                           ((Prims.strcat "_" n1),
                                             FStar_Pervasives_Native.None)),
                                         r1)]), e1))) ([], env1) fields in
                let uu____1739 =
                  FStar_List.fold_left
                    (fun uu____1771  ->
                       fun uu____1772  ->
                         match (uu____1771, uu____1772) with
                         | ((r,e),(n1,l)) ->
                             let uu____1847 = fields_t l e in
                             (match uu____1847 with
                              | (r1,e1) ->
                                  ((FStar_List.append r
                                      [get_export
                                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                                            ((n1,
                                               FStar_Pervasives_Native.None),
                                              tparams1,
                                              (FStar_Extraction_JavaScript_Ast.JST_Object
                                                 (FStar_List.append (
                                                    tag n1) r1))))]), e1)))
                    ([], env) lfields in
                (match uu____1739 with
                 | (lfields_t,env1) ->
                     let tparams_gen =
                       match tparams1 with
                       | FStar_Pervasives_Native.Some t ->
                           let uu____1922 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_Extraction_JavaScript_Ast.JST_Generic
                                    (x, FStar_Pervasives_Native.None)) t in
                           FStar_All.pipe_right uu____1922
                             (fun _0_46  ->
                                FStar_Pervasives_Native.Some _0_46)
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None in
                     let lnames =
                       FStar_List.map
                         (fun uu____1961  ->
                            match uu____1961 with
                            | (n1,uu____1973) ->
                                FStar_Extraction_JavaScript_Ast.JST_Generic
                                  (n1, tparams_gen)) lfields in
                     let union_t =
                       get_export
                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                            ((name, FStar_Pervasives_Native.None), tparams1,
                              (FStar_Extraction_JavaScript_Ast.JST_Union
                                 lnames))) in
                     ((FStar_Extraction_JavaScript_Ast.JSS_Block
                         (FStar_List.append lfields_t [union_t])), env1)) in
          let uu____2003 =
            match body with
            | FStar_Pervasives_Native.None  ->
                failwith "todo: translate_decl [MLM_Ty] with empty body"
            | FStar_Pervasives_Native.Some v1 -> forbody v1 in
          (match uu____2003 with
           | (body_t,env1) ->
               FStar_Pervasives_Native.Some
                 ((FStar_Extraction_JavaScript_Ast.JS_Statement body_t),
                   env1))
      | FStar_Extraction_ML_Syntax.MLM_Ty uu____2029 ->
          failwith "todo: translate_decl [MLM_Ty]"
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2036 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          FStar_Pervasives_Native.Some
            ((FStar_Extraction_JavaScript_Ast.JS_Statement
                (FStar_Extraction_JavaScript_Ast.JSS_Block [])), env)
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2058 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_expr:
  FStar_Extraction_ML_Syntax.mlexpr ->
    (FStar_Extraction_ML_Syntax.mlsymbol,FStar_Extraction_JavaScript_Ast.typ
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Extraction_JavaScript_Ast.statement_t Prims.list ->
        env_t ->
          Prims.bool ->
            (FStar_Extraction_JavaScript_Ast.statement_t Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun var  ->
      fun lstmt  ->
        fun env  ->
          fun isDecl  ->
            let get_res expr new_fv env1 =
              let is_inEnv = isInEnv env1 (FStar_Pervasives_Native.fst var) in
              let uu____2117 =
                let res e1 =
                  if is_inEnv
                  then ([FStar_Extraction_JavaScript_Ast.JSS_Block e1], env1)
                  else (e1, env1) in
                match expr with
                | FStar_Extraction_JavaScript_Ast.JSE_Assignment uu____2155
                    ->
                    if isDecl
                    then
                      (if (FStar_Pervasives_Native.fst var) = "_"
                       then
                         ((FStar_List.append
                             [FStar_Extraction_JavaScript_Ast.JSS_Expression
                                expr] lstmt), env1)
                       else
                         ((FStar_List.append
                             [FStar_Extraction_JavaScript_Ast.JSS_Expression
                                expr;
                             FStar_Extraction_JavaScript_Ast.JSS_Expression
                               (FStar_Extraction_JavaScript_Ast.JSE_Assignment
                                  ((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                      var),
                                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                       (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                         ""))))] lstmt), env1))
                    else
                      res
                        (FStar_List.append
                           [FStar_Extraction_JavaScript_Ast.JSS_Expression
                              expr;
                           FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                             (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                  var),
                                (FStar_Pervasives_Native.Some
                                   (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                      (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                        "")))),
                               FStar_Extraction_JavaScript_Ast.JSV_Let)]
                           lstmt)
                | uu____2188 ->
                    if isDecl
                    then
                      ((FStar_List.append
                          [FStar_Extraction_JavaScript_Ast.JSS_Expression
                             (FStar_Extraction_JavaScript_Ast.JSE_Assignment
                                ((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                    var), expr))] lstmt), env1)
                    else
                      res
                        (FStar_List.append
                           [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                              (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                   var), (FStar_Pervasives_Native.Some expr)),
                                FStar_Extraction_JavaScript_Ast.JSV_Let)]
                           lstmt) in
              match uu____2117 with
              | (expr1,env2) ->
                  (((match new_fv with
                     | [] -> expr1
                     | uu____2222 ->
                         if is_inEnv
                         then FStar_List.append new_fv expr1
                         else
                           FStar_List.append new_fv
                             [FStar_Extraction_JavaScript_Ast.JSS_Block expr1])),
                    env2) in
            match e.FStar_Extraction_ML_Syntax.expr with
            | x when is_pure_expr e var ->
                let uu____2237 = translate_expr_pure e env in
                (match uu____2237 with | (expr,env1) -> get_res expr [] env1)
            | FStar_Extraction_ML_Syntax.MLE_Let
                ((uu____2250,uu____2251,{
                                          FStar_Extraction_ML_Syntax.mllb_name
                                            = (name,uu____2253);
                                          FStar_Extraction_ML_Syntax.mllb_tysc
                                            = tys;
                                          FStar_Extraction_ML_Syntax.mllb_add_unit
                                            = add_unit;
                                          FStar_Extraction_ML_Syntax.mllb_def
                                            = body;
                                          FStar_Extraction_ML_Syntax.print_typ
                                            = pt;_}::[]),continuation)
                ->
                let isEqName = isInEnv env name in
                let env1 = extendEnv env ([], name) tys in
                let uu____2275 = is_pure_expr body (name, tys) in
                if uu____2275
                then
                  let var_decl_q =
                    if isMutable tys
                    then FStar_Extraction_JavaScript_Ast.JSV_Let
                    else FStar_Extraction_JavaScript_Ast.JSV_Const in
                  let uu____2288 = translate_expr_pure body env1 in
                  (match uu____2288 with
                   | (r,env2) ->
                       let uu____2301 =
                         translate_expr continuation var lstmt env2 isDecl in
                       (match uu____2301 with
                        | (c,env11) ->
                            let c1 =
                              FStar_List.append
                                [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                   (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                        (name, FStar_Pervasives_Native.None)),
                                      (FStar_Pervasives_Native.Some r)),
                                     var_decl_q)] c in
                            let env3 =
                              let uu___159_2334 = env2 in
                              {
                                names = (uu___159_2334.names);
                                module_name = (uu___159_2334.module_name);
                                import_module_names =
                                  (FStar_List.append env2.import_module_names
                                     env11.import_module_names)
                              } in
                            if isEqName
                            then
                              ([FStar_Extraction_JavaScript_Ast.JSS_Block c1],
                                env3)
                            else (c1, env3)))
                else
                  (let uu____2347 =
                     translate_expr continuation var lstmt env1 isDecl in
                   match uu____2347 with
                   | (c,env11) ->
                       let uu____2366 =
                         translate_expr body
                           (name, FStar_Pervasives_Native.None) c env1 false in
                       (match uu____2366 with
                        | (r,env2) ->
                            let env3 =
                              let uu___160_2388 = env2 in
                              {
                                names = (uu___160_2388.names);
                                module_name = (uu___160_2388.module_name);
                                import_module_names =
                                  (FStar_List.append env2.import_module_names
                                     env11.import_module_names)
                              } in
                            (r, env3)))
            | FStar_Extraction_ML_Syntax.MLE_Let uu____2391 ->
                failwith "todo: translate_expr [MLE_Let]"
            | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
                let uu____2424 =
                  FStar_List.fold_left
                    (fun uu____2455  ->
                       fun uu____2456  ->
                         match (uu____2455, uu____2456) with
                         | ((r,e1),((n1,uu____2494),t)) ->
                             let uu____2518 =
                               translate_type t FStar_Pervasives_Native.None
                                 e1 in
                             (match uu____2518 with
                              | (r1,e11) ->
                                  ((FStar_List.append r
                                      [FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                         (n1,
                                           (FStar_Pervasives_Native.Some r1))]),
                                    e11))) ([], env) args in
                (match uu____2424 with
                 | (args1,env1) ->
                     let is_failwith =
                       match body.FStar_Extraction_ML_Syntax.expr with
                       | FStar_Extraction_ML_Syntax.MLE_App (expr,uu____2553)
                           ->
                           (match expr.FStar_Extraction_ML_Syntax.expr with
                            | FStar_Extraction_ML_Syntax.MLE_Name p when
                                let uu____2559 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    p in
                                uu____2559 = "failwith" -> true
                            | uu____2560 -> false)
                       | uu____2561 -> false in
                     let uu____2562 =
                       if is_failwith
                       then
                         ((FStar_Extraction_JavaScript_Ast.JS_BodyBlock
                             [FStar_Extraction_JavaScript_Ast.JSS_Throw
                                (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                   ((FStar_Extraction_JavaScript_Ast.JSV_String
                                       "Not yet implemented!"), ""))]), env1)
                       else
                         (let uu____2572 = is_pure_expr body var in
                          if uu____2572
                          then
                            let uu____2579 = translate_expr_pure body env1 in
                            match uu____2579 with
                            | (r,env11) ->
                                ((FStar_Extraction_JavaScript_Ast.JS_BodyExpression
                                    r), env11)
                          else
                            (let uu____2591 =
                               translate_expr body
                                 ("_res", FStar_Pervasives_Native.None)
                                 [FStar_Extraction_JavaScript_Ast.JSS_Return
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                          ("_res",
                                            FStar_Pervasives_Native.None)))]
                                 env1 true in
                             match uu____2591 with
                             | (t1,env11) ->
                                 ((FStar_Extraction_JavaScript_Ast.JS_BodyBlock
                                     (FStar_List.append
                                        [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                           (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                                ("_res",
                                                  FStar_Pervasives_Native.None)),
                                              FStar_Pervasives_Native.None),
                                             FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                        t1)), env11))) in
                     (match uu____2562 with
                      | (body_t,env11) ->
                          let uu____2630 =
                            match FStar_Pervasives_Native.snd var with
                            | FStar_Pervasives_Native.None  ->
                                (FStar_Pervasives_Native.None,
                                  FStar_Pervasives_Native.None)
                            | FStar_Pervasives_Native.Some v1 ->
                                (match v1 with
                                 | FStar_Extraction_JavaScript_Ast.JST_Function
                                     (uu____2672,t2,lp) ->
                                     ((FStar_Pervasives_Native.Some t2), lp)
                                 | uu____2713 ->
                                     (FStar_Pervasives_Native.None,
                                       FStar_Pervasives_Native.None)) in
                          (match uu____2630 with
                           | (ret_t,lp_generic) ->
                               let expr =
                                 FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction
                                   (FStar_Pervasives_Native.None, args1,
                                     body_t, ret_t, lp_generic) in
                               let uu____2765 =
                                 if isDecl
                                 then
                                   ([FStar_Extraction_JavaScript_Ast.JSS_Expression
                                       (FStar_Extraction_JavaScript_Ast.JSE_Assignment
                                          ((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                              ((FStar_Pervasives_Native.fst
                                                  var),
                                                FStar_Pervasives_Native.None)),
                                            expr))], env1)
                                 else
                                   ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                       (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                            ((FStar_Pervasives_Native.fst var),
                                              FStar_Pervasives_Native.None)),
                                          (FStar_Pervasives_Native.Some expr)),
                                         FStar_Extraction_JavaScript_Ast.JSV_Const)],
                                     env1) in
                               (match uu____2765 with
                                | (expr1,env2) ->
                                    let env3 =
                                      let uu___161_2812 = env2 in
                                      {
                                        names = (uu___161_2812.names);
                                        module_name =
                                          (uu___161_2812.module_name);
                                        import_module_names =
                                          (FStar_List.append
                                             env2.import_module_names
                                             env11.import_module_names)
                                      } in
                                    ((FStar_List.append expr1 lstmt), env3)))))
            | FStar_Extraction_ML_Syntax.MLE_If (cond,s1,s2) ->
                let uu____2822 = translate_expr s1 var [] env true in
                (match uu____2822 with
                 | (r1,env1) ->
                     let s11 = FStar_Extraction_JavaScript_Ast.JSS_Block r1 in
                     let uu____2842 =
                       match s2 with
                       | FStar_Pervasives_Native.Some v1 ->
                           let uu____2856 = translate_expr v1 var [] env true in
                           (match uu____2856 with
                            | (r2,env2) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Extraction_JavaScript_Ast.JSS_Block
                                       r2)), env2))
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Pervasives_Native.None, env) in
                     (match uu____2842 with
                      | (s21,env2) ->
                          let uu____2891 =
                            let uu____2898 = is_pure_expr cond var in
                            if uu____2898
                            then
                              let uu____2907 = translate_expr_pure cond env in
                              match uu____2907 with
                              | (c1,envc) ->
                                  ([FStar_Extraction_JavaScript_Ast.JSS_If
                                      (c1, s11, s21)], envc)
                            else
                              (let uu____2925 =
                                 translate_expr cond
                                   ("_cond", FStar_Pervasives_Native.None)
                                   [FStar_Extraction_JavaScript_Ast.JSS_If
                                      ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                          ("_cond",
                                            FStar_Pervasives_Native.None)),
                                        s11, s21)] env true in
                               match uu____2925 with
                               | (c1,envc) ->
                                   ((FStar_List.append
                                       [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                          (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                               ("_cond",
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Extraction_JavaScript_Ast.JST_Boolean))),
                                             FStar_Pervasives_Native.None),
                                            FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                       c1), envc)) in
                          (match uu____2891 with
                           | (c,env3) ->
                               let uu____2974 =
                                 if isDecl
                                 then (c, env3)
                                 else
                                   ((FStar_List.append
                                       [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                          (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                               var),
                                             FStar_Pervasives_Native.None),
                                            FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                       c), env3) in
                               (match uu____2974 with
                                | (c1,env4) ->
                                    let env5 =
                                      let uu___162_3013 = env4 in
                                      {
                                        names = (uu___162_3013.names);
                                        module_name =
                                          (uu___162_3013.module_name);
                                        import_module_names =
                                          (FStar_List.append
                                             env4.import_module_names
                                             (FStar_List.append
                                                env1.import_module_names
                                                env2.import_module_names))
                                      } in
                                    ((FStar_List.append c1 lstmt), env5)))))
            | FStar_Extraction_ML_Syntax.MLE_Raise uu____3016 ->
                failwith "todo: translate_expr [MLE_Raise]"
            | FStar_Extraction_ML_Syntax.MLE_Try uu____3029 ->
                failwith "todo: translate_expr [MLE_Try]"
            | FStar_Extraction_ML_Syntax.MLE_Coerce (in_e,t,uu____3052) ->
                let lp_generic =
                  match FStar_Pervasives_Native.snd var with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some v1 ->
                      (match v1 with
                       | FStar_Extraction_JavaScript_Ast.JST_Function
                           (uu____3071,uu____3072,lp) -> lp
                       | uu____3106 -> FStar_Pervasives_Native.None) in
                let uu____3109 = translate_type t lp_generic env in
                (match uu____3109 with
                 | (t1,env1) ->
                     let var1 =
                       ((FStar_Pervasives_Native.fst var),
                         (FStar_Pervasives_Native.Some t1)) in
                     translate_expr in_e var1 lstmt env1 isDecl)
            | FStar_Extraction_ML_Syntax.MLE_Match (e_in,lb) ->
                let match_e =
                  let uu____3162 =
                    let uu____3163 = FStar_Extraction_ML_Syntax.gensym () in
                    FStar_Pervasives_Native.fst uu____3163 in
                  (uu____3162, FStar_Pervasives_Native.None) in
                let uu____3170 =
                  let uu____3177 = is_pure_expr e_in var in
                  if uu____3177
                  then
                    let uu____3186 = translate_expr_pure e_in env in
                    match uu____3186 with
                    | (r1,env1) ->
                        let uu____3199 =
                          translate_match lb
                            (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                               match_e) var env1 in
                        (match uu____3199 with
                         | (r2,env2) ->
                             let env3 =
                               let uu___163_3213 = env1 in
                               {
                                 names = (uu___163_3213.names);
                                 module_name = (uu___163_3213.module_name);
                                 import_module_names =
                                   (FStar_List.append
                                      env1.import_module_names
                                      env2.import_module_names)
                               } in
                             ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                 (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                      match_e),
                                    (FStar_Pervasives_Native.Some r1)),
                                   FStar_Extraction_JavaScript_Ast.JSV_Const);
                              r2], env3))
                  else
                    (let uu____3225 =
                       translate_match lb
                         (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                            match_e) var env in
                     match uu____3225 with
                     | (r2,env2) ->
                         let uu____3238 =
                           translate_expr e_in match_e [r2] env true in
                         (match uu____3238 with
                          | (r1,env1) ->
                              let env3 =
                                let uu___164_3258 = env1 in
                                {
                                  names = (uu___164_3258.names);
                                  module_name = (uu___164_3258.module_name);
                                  import_module_names =
                                    (FStar_List.append
                                       env1.import_module_names
                                       env2.import_module_names)
                                } in
                              ((FStar_List.append
                                  [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                     (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                          match_e),
                                        FStar_Pervasives_Native.None),
                                       FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                  r1), env3))) in
                (match uu____3170 with
                 | (c,env1) ->
                     let c1 = [FStar_Extraction_JavaScript_Ast.JSS_Block c] in
                     let uu____3284 =
                       if isDecl
                       then (c1, env1)
                       else
                         ((FStar_List.append
                             [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                     var), FStar_Pervasives_Native.None),
                                  FStar_Extraction_JavaScript_Ast.JSV_Let)]
                             c1), env1) in
                     (match uu____3284 with
                      | (c2,env2) -> ((FStar_List.append c2 lstmt), env2)))
            | FStar_Extraction_ML_Syntax.MLE_Seq ls ->
                let rec translate_seq l env1 acc =
                  match l with
                  | [] -> failwith "Empty list in [MLE_Seq]"
                  | x::[] ->
                      let uu____3364 = translate_expr x var [] env1 isDecl in
                      (match uu____3364 with
                       | (r,env2) -> ((FStar_List.append acc r), env2))
                  | hd1::tl1 ->
                      let uu____3389 =
                        translate_expr hd1
                          ("_", FStar_Pervasives_Native.None) [] env1 true in
                      (match uu____3389 with
                       | (r,e1) ->
                           translate_seq tl1 e1 (FStar_List.append acc r)) in
                let uu____3410 = translate_seq ls env [] in
                (match uu____3410 with
                 | (r,env1) -> ((FStar_List.append r lstmt), env1))
            | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
                let uu____3437 = create_pure_args args var env in
                (match uu____3437 with
                 | (args1,new_fv,env1) ->
                     let uu____3465 = translate_arg_app e1 args1 var env1 in
                     (match uu____3465 with
                      | (expr,env2) -> get_res expr new_fv env2))
            | FStar_Extraction_ML_Syntax.MLE_CTor ((path,c),lexpr) ->
                let uu____3495 = create_pure_args lexpr var env in
                (match uu____3495 with
                 | (lexpr1,new_fv,env1) ->
                     let expr =
                       match c with
                       | x when (x = "Cons") || (x = "Nil") ->
                           (match lexpr1 with
                            | [] ->
                                FStar_Extraction_JavaScript_Ast.JSE_Array
                                  FStar_Pervasives_Native.None
                            | hd1::tl1 ->
                                FStar_Extraction_JavaScript_Ast.JSE_Call
                                  ((FStar_Extraction_JavaScript_Ast.JSE_Member
                                      ((FStar_Extraction_JavaScript_Ast.JSE_Array
                                          (FStar_Pervasives_Native.Some [hd1])),
                                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                           ("concat",
                                             FStar_Pervasives_Native.None)))),
                                    tl1))
                       | x when (x = "Some") || (x = "None") ->
                           (match lexpr1 with
                            | [] ->
                                FStar_Extraction_JavaScript_Ast.JSE_Literal
                                  (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                    "")
                            | hd1::tl1 ->
                                FStar_List.nth lexpr1 (Prims.parse_int "0"))
                       | uu____3542 ->
                           let uu____3543 =
                             let uu____3546 =
                               FStar_List.mapi
                                 (fun i  ->
                                    fun x  ->
                                      let uu____3554 =
                                        let uu____3561 =
                                          let uu____3562 =
                                            let uu____3569 =
                                              let uu____3570 =
                                                FStar_Util.string_of_int i in
                                              Prims.strcat "_" uu____3570 in
                                            (uu____3569,
                                              FStar_Pervasives_Native.None) in
                                          FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                            uu____3562 in
                                        (uu____3561, x,
                                          FStar_Extraction_JavaScript_Ast.JSO_Init) in
                                      FStar_Extraction_JavaScript_Ast.JSPO_Property
                                        uu____3554) lexpr1 in
                             FStar_List.append
                               [FStar_Extraction_JavaScript_Ast.JSPO_Property
                                  ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                      ("_tag",
                                        (FStar_Pervasives_Native.Some
                                           FStar_Extraction_JavaScript_Ast.JST_String))),
                                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                       ((FStar_Extraction_JavaScript_Ast.JSV_String
                                           c), "")),
                                    FStar_Extraction_JavaScript_Ast.JSO_Init)]
                               uu____3546 in
                           FStar_Extraction_JavaScript_Ast.JSE_Object
                             uu____3543 in
                     get_res expr new_fv env1)
            | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
                let uu____3593 =
                  FStar_List.fold_left
                    (fun uu____3630  ->
                       fun uu____3631  ->
                         match (uu____3630, uu____3631) with
                         | ((lexpr,lnew_fv,e1),(id,x)) ->
                             let uu____3697 = create_pure_args [x] var e1 in
                             (match uu____3697 with
                              | (expr,fv,e11) ->
                                  let uu____3729 =
                                    let uu____3732 =
                                      let uu____3735 =
                                        let uu____3736 =
                                          let uu____3743 =
                                            FStar_List.nth expr
                                              (Prims.parse_int "0") in
                                          ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                              ((Prims.strcat "_" id),
                                                FStar_Pervasives_Native.None)),
                                            uu____3743,
                                            FStar_Extraction_JavaScript_Ast.JSO_Init) in
                                        FStar_Extraction_JavaScript_Ast.JSPO_Property
                                          uu____3736 in
                                      [uu____3735] in
                                    FStar_List.append lexpr uu____3732 in
                                  (uu____3729,
                                    (FStar_List.append fv lnew_fv), e11)))
                    ([], [], env) fields in
                (match uu____3593 with
                 | (create_fields,new_fv,env1) ->
                     let expr =
                       FStar_Extraction_JavaScript_Ast.JSE_Object
                         (FStar_List.append
                            [FStar_Extraction_JavaScript_Ast.JSPO_Property
                               ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                   ("_tag",
                                     (FStar_Pervasives_Native.Some
                                        FStar_Extraction_JavaScript_Ast.JST_String))),
                                 (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                    ((FStar_Extraction_JavaScript_Ast.JSV_String
                                        "Record"), "")),
                                 FStar_Extraction_JavaScript_Ast.JSO_Init)]
                            create_fields) in
                     get_res expr new_fv env1)
            | FStar_Extraction_ML_Syntax.MLE_Tuple lexp ->
                let uu____3777 =
                  FStar_List.fold_left
                    (fun uu____3807  ->
                       fun x  ->
                         match uu____3807 with
                         | (lexpr,lnew_fv,e1) ->
                             let uu____3840 = create_pure_args [x] var e1 in
                             (match uu____3840 with
                              | (expr,fv,e11) ->
                                  ((FStar_List.append lexpr expr),
                                    (FStar_List.append fv lnew_fv), e11)))
                    ([], [], env) lexp in
                (match uu____3777 with
                 | (create_fields,new_fv,env1) ->
                     let expr =
                       FStar_Extraction_JavaScript_Ast.JSE_Array
                         (FStar_Pervasives_Native.Some create_fields) in
                     get_res expr new_fv env1)
            | uu____3900 -> failwith "todo: translation ml-expr"
and create_pure_args:
  FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
    (FStar_Extraction_ML_Syntax.mlsymbol,FStar_Extraction_JavaScript_Ast.typ
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      env_t ->
        (FStar_Extraction_JavaScript_Ast.expression_t Prims.list,FStar_Extraction_JavaScript_Ast.statement_t
                                                                   Prims.list,
          env_t) FStar_Pervasives_Native.tuple3
  =
  fun args  ->
    fun var  ->
      fun env  ->
        FStar_List.fold_left
          (fun uu____3942  ->
             fun x  ->
               match uu____3942 with
               | (lexpr,lnew_fv,e) ->
                   (match x.FStar_Extraction_ML_Syntax.expr with
                    | FStar_Extraction_ML_Syntax.MLE_CTor
                        ((path,c),uu____3987) when
                        (c = "Nil") || (c = "None") ->
                        let uu____4002 = translate_expr_pure x e in
                        (match uu____4002 with
                         | (r1,e1) ->
                             let uu____4019 =
                               translate_type
                                 x.FStar_Extraction_ML_Syntax.mlty
                                 FStar_Pervasives_Native.None e1 in
                             (match uu____4019 with
                              | (t1,e11) ->
                                  ((FStar_List.append lexpr
                                      [FStar_Extraction_JavaScript_Ast.JSE_TypeCast
                                         (r1, t1)]), lnew_fv, e11)))
                    | uu____4042 ->
                        let uu____4043 = is_pure_expr x var in
                        if uu____4043
                        then
                          let uu____4056 = translate_expr_pure x e in
                          (match uu____4056 with
                           | (r1,e1) ->
                               ((FStar_List.append lexpr [r1]), lnew_fv, e1))
                        else
                          (let fv_x =
                             let uu____4079 =
                               FStar_Extraction_ML_Syntax.gensym () in
                             FStar_Pervasives_Native.fst uu____4079 in
                           let uu____4084 =
                             match x.FStar_Extraction_ML_Syntax.expr with
                             | FStar_Extraction_ML_Syntax.MLE_Var uu____4097
                                 ->
                                 let uu____4098 = translate_expr_pure x e in
                                 (match uu____4098 with
                                  | (r1,e1) ->
                                      ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                          (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                               (fv_x,
                                                 FStar_Pervasives_Native.None)),
                                             (FStar_Pervasives_Native.Some r1)),
                                            FStar_Extraction_JavaScript_Ast.JSV_Const)],
                                        e1))
                             | uu____4123 ->
                                 translate_expr x
                                   (fv_x, FStar_Pervasives_Native.None) []
                                   env false in
                           match uu____4084 with
                           | (c,e1) ->
                               ((FStar_List.append lexpr
                                   [FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                      (fv_x, FStar_Pervasives_Native.None)]),
                                 (FStar_List.append c lnew_fv), e1))))
          ([], [], env) args
and translate_arg_app:
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_JavaScript_Ast.expression_t Prims.list ->
      (FStar_Extraction_ML_Syntax.mlsymbol,FStar_Extraction_JavaScript_Ast.typ
                                             FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        env_t ->
          (FStar_Extraction_JavaScript_Ast.expression_t,env_t)
            FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun args  ->
      fun var  ->
        fun env  ->
          match e.FStar_Extraction_ML_Syntax.expr with
          | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
              is_op_bin op ->
              let uu____4171 =
                let uu____4172 =
                  let uu____4179 = FStar_Util.must (mk_op_bin op) in
                  let uu____4180 = FStar_List.nth args (Prims.parse_int "0") in
                  let uu____4181 = FStar_List.nth args (Prims.parse_int "1") in
                  (uu____4179, uu____4180, uu____4181) in
                FStar_Extraction_JavaScript_Ast.JSE_Binary uu____4172 in
              (uu____4171, env)
          | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
              is_op_bool op ->
              let uu____4185 =
                let uu____4186 =
                  let uu____4193 = FStar_Util.must (mk_op_bool op) in
                  let uu____4194 = FStar_List.nth args (Prims.parse_int "0") in
                  let uu____4195 = FStar_List.nth args (Prims.parse_int "1") in
                  (uu____4193, uu____4194, uu____4195) in
                FStar_Extraction_JavaScript_Ast.JSE_Logical uu____4186 in
              (uu____4185, env)
          | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
              is_op_un op ->
              let uu____4199 =
                let uu____4200 =
                  let uu____4205 = FStar_Util.must (mk_op_un op) in
                  let uu____4206 = FStar_List.nth args (Prims.parse_int "0") in
                  (uu____4205, uu____4206) in
                FStar_Extraction_JavaScript_Ast.JSE_Unary uu____4200 in
              (uu____4199, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____4210 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4210 = "FStar.Buffer.op_Array_Access") ||
                (let uu____4212 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4212 = "FStar.Buffer.index")
              ->
              let uu____4213 =
                let uu____4214 =
                  let uu____4219 = FStar_List.nth args (Prims.parse_int "0") in
                  let uu____4220 =
                    let uu____4221 =
                      FStar_List.nth args (Prims.parse_int "1") in
                    FStar_Extraction_JavaScript_Ast.JSPM_Expression
                      uu____4221 in
                  (uu____4219, uu____4220) in
                FStar_Extraction_JavaScript_Ast.JSE_Member uu____4214 in
              (uu____4213, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____4225 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4225 = "FStar.Buffer.op_Array_Assignment") ||
                (let uu____4227 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4227 = "FStar.Buffer.upd")
              ->
              let uu____4228 =
                let uu____4229 =
                  let uu____4234 =
                    let uu____4235 =
                      let uu____4236 =
                        let uu____4241 =
                          FStar_List.nth args (Prims.parse_int "0") in
                        let uu____4242 =
                          let uu____4243 =
                            FStar_List.nth args (Prims.parse_int "1") in
                          FStar_Extraction_JavaScript_Ast.JSPM_Expression
                            uu____4243 in
                        (uu____4241, uu____4242) in
                      FStar_Extraction_JavaScript_Ast.JSE_Member uu____4236 in
                    FStar_Extraction_JavaScript_Ast.JGP_Expression uu____4235 in
                  let uu____4244 = FStar_List.nth args (Prims.parse_int "2") in
                  (uu____4234, uu____4244) in
                FStar_Extraction_JavaScript_Ast.JSE_Assignment uu____4229 in
              (uu____4228, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____4248 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4248 = "FStar.ST.op_Bang") ||
                (let uu____4250 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4250 = "FStar.ST.read")
              ->
              let uu____4251 =
                let uu____4252 =
                  let uu____4257 = FStar_List.nth args (Prims.parse_int "0") in
                  (uu____4257,
                    (FStar_Extraction_JavaScript_Ast.JSPM_Expression
                       (FStar_Extraction_JavaScript_Ast.JSE_Literal
                          ((FStar_Extraction_JavaScript_Ast.JSV_Number
                              (float_of_int (Prims.parse_int "0"))), "0")))) in
                FStar_Extraction_JavaScript_Ast.JSE_Member uu____4252 in
              (uu____4251, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____4261 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4261 = "FStar.ST.op_Colon_Equals") ||
                (let uu____4263 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4263 = "FStar.ST.write")
              ->
              let expr =
                let uu____4265 =
                  let uu____4270 = FStar_List.nth args (Prims.parse_int "0") in
                  (uu____4270,
                    (FStar_Extraction_JavaScript_Ast.JSPM_Expression
                       (FStar_Extraction_JavaScript_Ast.JSE_Literal
                          ((FStar_Extraction_JavaScript_Ast.JSV_Number
                              (float_of_int (Prims.parse_int "0"))), "0")))) in
                FStar_Extraction_JavaScript_Ast.JSE_Member uu____4265 in
              let uu____4271 =
                let uu____4272 =
                  let uu____4277 = FStar_List.nth args (Prims.parse_int "1") in
                  ((FStar_Extraction_JavaScript_Ast.JGP_Expression expr),
                    uu____4277) in
                FStar_Extraction_JavaScript_Ast.JSE_Assignment uu____4272 in
              (uu____4271, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              let uu____4279 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4279 = "FStar.ST.alloc" ->
              let uu____4280 =
                let uu____4281 =
                  let uu____4286 =
                    let uu____4289 =
                      FStar_List.nth args (Prims.parse_int "0") in
                    [uu____4289] in
                  FStar_Pervasives_Native.Some uu____4286 in
                FStar_Extraction_JavaScript_Ast.JSE_Array uu____4281 in
              (uu____4280, env)
          | FStar_Extraction_ML_Syntax.MLE_Name (path,function_name) ->
              let uu____4298 = addImportModule env (path, function_name) in
              (match uu____4298 with
               | (name,env1) ->
                   ((FStar_Extraction_JavaScript_Ast.JSE_Call
                       ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                           (name, FStar_Pervasives_Native.None)), args)),
                     env1))
          | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4316) ->
              ((FStar_Extraction_JavaScript_Ast.JSE_Call
                  ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                      (name, FStar_Pervasives_Native.None)), args)), env)
          | uu____4321 ->
              let uu____4322 = is_pure_expr e var in
              if uu____4322
              then
                let uu____4329 = translate_expr_pure e env in
                (match uu____4329 with
                 | (r,env1) ->
                     ((FStar_Extraction_JavaScript_Ast.JSE_Call (r, args)),
                       env1))
              else failwith "todo: translation [MLE_App]"
and map_expr_pure:
  FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
    env_t ->
      (FStar_Extraction_JavaScript_Ast.expression_t Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun exprs  ->
    fun env  ->
      FStar_List.fold_left
        (fun uu____4364  ->
           fun x  ->
             match uu____4364 with
             | (r,e) ->
                 let uu____4384 = translate_expr_pure x e in
                 (match uu____4384 with
                  | (r1,e1) -> ((FStar_List.append r [r1]), e1))) ([], env)
        exprs
and translate_expr_pure:
  FStar_Extraction_ML_Syntax.mlexpr ->
    env_t ->
      (FStar_Extraction_JavaScript_Ast.expression_t,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun env  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const c ->
          let uu____4408 = translate_constant c in (uu____4408, env)
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4410) ->
          ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
              (name, FStar_Pervasives_Native.None)), env)
      | FStar_Extraction_ML_Syntax.MLE_Name (path,name) ->
          let uu____4419 = addImportModule env (path, name) in
          (match uu____4419 with
           | (name1,env1) ->
               ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                   (name1, FStar_Pervasives_Native.None)), env1))
      | FStar_Extraction_ML_Syntax.MLE_Tuple lexp ->
          let uu____4437 = map_expr_pure lexp env in
          (match uu____4437 with
           | (r,env1) ->
               ((FStar_Extraction_JavaScript_Ast.JSE_Array
                   (FStar_Pervasives_Native.Some r)), env1))
      | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
          let uu____4474 =
            FStar_List.fold_left
              (fun uu____4500  ->
                 fun uu____4501  ->
                   match (uu____4500, uu____4501) with
                   | ((r,e1),(id,x)) ->
                       let uu____4546 = translate_expr_pure x e1 in
                       (match uu____4546 with
                        | (r1,e11) ->
                            ((FStar_List.append r
                                [FStar_Extraction_JavaScript_Ast.JSPO_Property
                                   ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                       ((Prims.strcat "_" id),
                                         FStar_Pervasives_Native.None)), r1,
                                     FStar_Extraction_JavaScript_Ast.JSO_Init)]),
                              e11))) ([], env) fields in
          (match uu____4474 with
           | (create_fields,env1) ->
               ((FStar_Extraction_JavaScript_Ast.JSE_Object
                   (FStar_List.append
                      [FStar_Extraction_JavaScript_Ast.JSPO_Property
                         ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                             ("_tag",
                               (FStar_Pervasives_Native.Some
                                  FStar_Extraction_JavaScript_Ast.JST_String))),
                           (FStar_Extraction_JavaScript_Ast.JSE_Literal
                              ((FStar_Extraction_JavaScript_Ast.JSV_String
                                  "Record"), "")),
                           FStar_Extraction_JavaScript_Ast.JSO_Init)]
                      create_fields)), env1))
      | FStar_Extraction_ML_Syntax.MLE_CTor ((path,c),lexpr) ->
          let uu____4594 = addImportModule env (path, c) in
          (match uu____4594 with
           | (name,env1) ->
               (match c with
                | x when (x = "Cons") || (x = "Nil") ->
                    (match lexpr with
                     | [] ->
                         ((FStar_Extraction_JavaScript_Ast.JSE_Array
                             FStar_Pervasives_Native.None), env1)
                     | hd1::tl1 ->
                         let uu____4622 = translate_expr_pure hd1 env1 in
                         (match uu____4622 with
                          | (r1,e1) ->
                              let uu____4633 = map_expr_pure tl1 e1 in
                              (match uu____4633 with
                               | (r2,e2) ->
                                   ((FStar_Extraction_JavaScript_Ast.JSE_Call
                                       ((FStar_Extraction_JavaScript_Ast.JSE_Member
                                           ((FStar_Extraction_JavaScript_Ast.JSE_Array
                                               (FStar_Pervasives_Native.Some
                                                  [r1])),
                                             (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                                ("concat",
                                                  FStar_Pervasives_Native.None)))),
                                         r2)), env1))))
                | x when (x = "Some") || (x = "None") ->
                    (match lexpr with
                     | [] ->
                         ((FStar_Extraction_JavaScript_Ast.JSE_Literal
                             (FStar_Extraction_JavaScript_Ast.JSV_Null, "")),
                           env1)
                     | hd1::tl1 ->
                         let uu____4665 = map_expr_pure lexpr env1 in
                         (match uu____4665 with
                          | (r1,e1) ->
                              let uu____4682 =
                                FStar_List.nth r1 (Prims.parse_int "0") in
                              (uu____4682, e1)))
                | uu____4683 ->
                    let uu____4684 =
                      FStar_List.fold_left
                        (fun uu____4710  ->
                           fun x  ->
                             match uu____4710 with
                             | (i,r,e1) ->
                                 let uu____4735 = translate_expr_pure x e1 in
                                 (match uu____4735 with
                                  | (r1,e11) ->
                                      let uu____4750 =
                                        let uu____4753 =
                                          let uu____4756 =
                                            let uu____4757 =
                                              let uu____4764 =
                                                let uu____4765 =
                                                  let uu____4772 =
                                                    let uu____4773 =
                                                      FStar_Util.string_of_int
                                                        i in
                                                    Prims.strcat "_"
                                                      uu____4773 in
                                                  (uu____4772,
                                                    FStar_Pervasives_Native.None) in
                                                FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                                  uu____4765 in
                                              (uu____4764, r1,
                                                FStar_Extraction_JavaScript_Ast.JSO_Init) in
                                            FStar_Extraction_JavaScript_Ast.JSPO_Property
                                              uu____4757 in
                                          [uu____4756] in
                                        FStar_List.append r uu____4753 in
                                      ((i + (Prims.parse_int "1")),
                                        uu____4750, e11)))
                        ((Prims.parse_int "0"), [], env1) lexpr in
                    (match uu____4684 with
                     | (uu____4784,r,env2) ->
                         ((FStar_Extraction_JavaScript_Ast.JSE_Object
                             (FStar_List.append
                                [FStar_Extraction_JavaScript_Ast.JSPO_Property
                                   ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                       ("_tag",
                                         (FStar_Pervasives_Native.Some
                                            FStar_Extraction_JavaScript_Ast.JST_String))),
                                     (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                        ((FStar_Extraction_JavaScript_Ast.JSV_String
                                            name), "")),
                                     FStar_Extraction_JavaScript_Ast.JSO_Init)]
                                r)), env2))))
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,uu____4794,uu____4795) ->
          translate_expr_pure e1 env
      | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
          let uu____4802 =
            FStar_List.fold_left
              (fun uu____4828  ->
                 fun x  ->
                   match uu____4828 with
                   | (r,e2) ->
                       (match x.FStar_Extraction_ML_Syntax.expr with
                        | FStar_Extraction_ML_Syntax.MLE_CTor
                            ((path,c),uu____4856) when
                            (c = "Nil") || (c = "None") ->
                            let uu____4871 = translate_expr_pure x e2 in
                            (match uu____4871 with
                             | (r1,e11) ->
                                 let uu____4884 =
                                   translate_type
                                     x.FStar_Extraction_ML_Syntax.mlty
                                     FStar_Pervasives_Native.None e11 in
                                 (match uu____4884 with
                                  | (r2,e21) ->
                                      ((FStar_List.append r
                                          [FStar_Extraction_JavaScript_Ast.JSE_TypeCast
                                             (r1, r2)]), e21)))
                        | uu____4901 ->
                            let uu____4902 = translate_expr_pure x e2 in
                            (match uu____4902 with
                             | (r1,e11) -> ((FStar_List.append r [r1]), e11))))
              ([], env) args in
          (match uu____4802 with
           | (args1,env1) ->
               translate_arg_app e1 args1 ("", FStar_Pervasives_Native.None)
                 env1)
      | FStar_Extraction_ML_Syntax.MLE_Proj (expr,(path,name)) ->
          let uu____4944 = translate_expr_pure expr env in
          (match uu____4944 with
           | (r,env1) ->
               let uu____4955 = addImportModule env1 (path, name) in
               (match uu____4955 with
                | (name1,env2) ->
                    ((FStar_Extraction_JavaScript_Ast.JSE_Member
                        (r,
                          (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                             ((Prims.strcat "_" name1),
                               FStar_Pervasives_Native.None)))), env2)))
      | uu____4970 -> failwith "todo: translation ml-expr-pure"
and translate_match:
  (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                          FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
    Prims.list ->
    FStar_Extraction_JavaScript_Ast.expression_t ->
      (FStar_Extraction_ML_Syntax.mlsymbol,FStar_Extraction_JavaScript_Ast.typ
                                             FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        env_t ->
          (FStar_Extraction_JavaScript_Ast.statement_t,env_t)
            FStar_Pervasives_Native.tuple2
  =
  fun lb  ->
    fun match_e  ->
      fun var  ->
        fun env  ->
          match lb with
          | [] ->
              ((FStar_Extraction_JavaScript_Ast.JSS_Throw
                  (FStar_Extraction_JavaScript_Ast.JSE_Literal
                     ((FStar_Extraction_JavaScript_Ast.JSV_String
                         "This value doesn't match!"), ""))), env)
          | (p,guard,expr_r)::tl1 ->
              let uu____5033 =
                let uu____5038 = is_pure_expr expr_r var in
                if uu____5038
                then
                  let uu____5045 = translate_expr_pure expr_r env in
                  match uu____5045 with
                  | (r1,e1) ->
                      ((FStar_Extraction_JavaScript_Ast.JSS_Expression
                          (FStar_Extraction_JavaScript_Ast.JSE_Assignment
                             ((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                 var), r1))), e1)
                else
                  (let uu____5057 = translate_expr expr_r var [] env true in
                   match uu____5057 with
                   | (r1,e1) ->
                       ((FStar_Extraction_JavaScript_Ast.JSS_Seq r1), e1)) in
              (match uu____5033 with
               | (expr_t,env1) ->
                   let uu____5080 = translate_match tl1 match_e var env in
                   translate_pat_guard (p, guard) match_e expr_t uu____5080
                     env1)
and translate_pat_guard:
  (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_JavaScript_Ast.expression_t ->
      FStar_Extraction_JavaScript_Ast.statement_t ->
        (FStar_Extraction_JavaScript_Ast.statement_t,env_t)
          FStar_Pervasives_Native.tuple2 ->
          env_t ->
            (FStar_Extraction_JavaScript_Ast.statement_t,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun uu____5087  ->
    fun match_e  ->
      fun s1  ->
        fun s2  ->
          fun env  ->
            match uu____5087 with
            | (p,guard) ->
                let uu____5116 = s2 in
                (match uu____5116 with
                 | (s21,env2) ->
                     let uu____5127 =
                       match guard with
                       | FStar_Pervasives_Native.None  ->
                           translate_pat p match_e s1 s21 env
                       | FStar_Pervasives_Native.Some v_guard ->
                           let uu____5137 = translate_expr_pure v_guard env in
                           (match uu____5137 with
                            | (r,env1) ->
                                let cond_stmt =
                                  FStar_Extraction_JavaScript_Ast.JSS_If
                                    (r, s1,
                                      (FStar_Pervasives_Native.Some s21)) in
                                translate_pat p match_e cond_stmt s21 env1) in
                     (match uu____5127 with
                      | (stmt,env1) ->
                          let env3 =
                            let uu___165_5158 = env1 in
                            {
                              names = (uu___165_5158.names);
                              module_name = (uu___165_5158.module_name);
                              import_module_names =
                                (FStar_List.append env1.import_module_names
                                   env2.import_module_names)
                            } in
                          (stmt, env3)))
and translate_pat:
  FStar_Extraction_ML_Syntax.mlpattern ->
    FStar_Extraction_JavaScript_Ast.expression_t ->
      FStar_Extraction_JavaScript_Ast.statement_t ->
        FStar_Extraction_JavaScript_Ast.statement_t ->
          env_t ->
            (FStar_Extraction_JavaScript_Ast.statement_t,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    fun match_e  ->
      fun s1  ->
        fun s2  ->
          fun env  ->
            match p with
            | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5169) ->
                ((FStar_Extraction_JavaScript_Ast.JSS_Seq
                    [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                       (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                            (name, FStar_Pervasives_Native.None)),
                          (FStar_Pervasives_Native.Some match_e)),
                         FStar_Extraction_JavaScript_Ast.JSV_Const);
                    s1]), env)
            | FStar_Extraction_ML_Syntax.MLP_Wild  -> (s1, env)
            | FStar_Extraction_ML_Syntax.MLP_Const c ->
                let uu____5181 =
                  let uu____5182 =
                    let uu____5191 =
                      let uu____5192 =
                        let uu____5199 = translate_constant c in
                        (FStar_Extraction_JavaScript_Ast.JSB_Equal, match_e,
                          uu____5199) in
                      FStar_Extraction_JavaScript_Ast.JSE_Binary uu____5192 in
                    (uu____5191, s1, (FStar_Pervasives_Native.Some s2)) in
                  FStar_Extraction_JavaScript_Ast.JSS_If uu____5182 in
                (uu____5181, env)
            | FStar_Extraction_ML_Syntax.MLP_CTor ((path,c),lp) ->
                let uu____5219 = addImportModule env (path, c) in
                (match uu____5219 with
                 | (name,env1) ->
                     let rec translate_p_ctor lp1 match_e1 s11 s21 i env2 =
                       let new_fv_x =
                         match c with
                         | x when x = "Some" -> match_e1
                         | x when (x = "Cons") && (i = (Prims.parse_int "0"))
                             ->
                             FStar_Extraction_JavaScript_Ast.JSE_Member
                               (match_e1,
                                 (FStar_Extraction_JavaScript_Ast.JSPM_Expression
                                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                       ((FStar_Extraction_JavaScript_Ast.JSV_Number
                                           (float_of_int
                                              (Prims.parse_int "0"))), "0"))))
                         | x when (x = "Cons") && (i = (Prims.parse_int "1"))
                             ->
                             FStar_Extraction_JavaScript_Ast.JSE_Member
                               (match_e1,
                                 (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                    ("slice(1)",
                                      FStar_Pervasives_Native.None)))
                         | uu____5265 ->
                             let uu____5266 =
                               let uu____5271 =
                                 let uu____5272 =
                                   let uu____5279 =
                                     let uu____5280 =
                                       FStar_Util.string_of_int i in
                                     Prims.strcat "_" uu____5280 in
                                   (uu____5279, FStar_Pervasives_Native.None) in
                                 FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                   uu____5272 in
                               (match_e1, uu____5271) in
                             FStar_Extraction_JavaScript_Ast.JSE_Member
                               uu____5266 in
                       match lp1 with
                       | [] -> (s11, env2)
                       | x::[] ->
                           let uu____5288 =
                             translate_pat x new_fv_x s11 s21 env2 in
                           (match uu____5288 with | (r,e1) -> (r, e1))
                       | hd1::tl1 ->
                           let uu____5303 =
                             translate_p_ctor tl1 match_e1 s11 s21
                               (i + (Prims.parse_int "1")) env2 in
                           (match uu____5303 with
                            | (r,e1) -> translate_pat hd1 new_fv_x r s21 e1) in
                     let if_stmt if_cond =
                       let uu____5322 =
                         translate_p_ctor lp match_e s1 s2
                           (Prims.parse_int "0") env1 in
                       match uu____5322 with
                       | (r,e1) ->
                           ((FStar_Extraction_JavaScript_Ast.JSS_If
                               (if_cond, r,
                                 (FStar_Pervasives_Native.Some s2))), e1) in
                     (match c with
                      | x when x = "Cons" ->
                          if_stmt
                            (FStar_Extraction_JavaScript_Ast.JSE_Binary
                               (FStar_Extraction_JavaScript_Ast.JSB_GreaterThan,
                                 (FStar_Extraction_JavaScript_Ast.JSE_Member
                                    (match_e,
                                      (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                         ("length",
                                           FStar_Pervasives_Native.None)))),
                                 (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                    ((FStar_Extraction_JavaScript_Ast.JSV_Number
                                        (float_of_int (Prims.parse_int "0"))),
                                      "0"))))
                      | x when x = "Nil" ->
                          if_stmt
                            (FStar_Extraction_JavaScript_Ast.JSE_Binary
                               (FStar_Extraction_JavaScript_Ast.JSB_Equal,
                                 (FStar_Extraction_JavaScript_Ast.JSE_Member
                                    (match_e,
                                      (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                         ("length",
                                           FStar_Pervasives_Native.None)))),
                                 (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                    ((FStar_Extraction_JavaScript_Ast.JSV_Number
                                        (float_of_int (Prims.parse_int "0"))),
                                      "0"))))
                      | x when x = "Some" ->
                          if_stmt
                            (FStar_Extraction_JavaScript_Ast.JSE_Binary
                               (FStar_Extraction_JavaScript_Ast.JSB_NotEqual,
                                 match_e,
                                 (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                    (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                      ""))))
                      | x when x = "None" ->
                          if_stmt
                            (FStar_Extraction_JavaScript_Ast.JSE_Binary
                               (FStar_Extraction_JavaScript_Ast.JSB_Equal,
                                 match_e,
                                 (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                    (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                      ""))))
                      | uu____5347 ->
                          let isSimple =
                            match match_e with
                            | FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                uu____5349 -> true
                            | uu____5356 -> false in
                          if isSimple
                          then
                            if_stmt
                              (FStar_Extraction_JavaScript_Ast.JSE_Binary
                                 (FStar_Extraction_JavaScript_Ast.JSB_StrictEqual,
                                   (FStar_Extraction_JavaScript_Ast.JSE_Member
                                      (match_e,
                                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                           ("_tag",
                                             (FStar_Pervasives_Native.Some
                                                FStar_Extraction_JavaScript_Ast.JST_String))))),
                                   (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                      ((FStar_Extraction_JavaScript_Ast.JSV_String
                                          c), ""))))
                          else
                            (let new_name =
                               let uu____5365 =
                                 FStar_Extraction_ML_Syntax.gensym () in
                               FStar_Pervasives_Native.fst uu____5365 in
                             let if_cond =
                               FStar_Extraction_JavaScript_Ast.JSE_Binary
                                 (FStar_Extraction_JavaScript_Ast.JSB_StrictEqual,
                                   (FStar_Extraction_JavaScript_Ast.JSE_Member
                                      ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                          (new_name,
                                            FStar_Pervasives_Native.None)),
                                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                           ("_tag",
                                             (FStar_Pervasives_Native.Some
                                                FStar_Extraction_JavaScript_Ast.JST_String))))),
                                   (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                      ((FStar_Extraction_JavaScript_Ast.JSV_String
                                          c), ""))) in
                             let uu____5375 =
                               translate_p_ctor lp
                                 (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                    (new_name, FStar_Pervasives_Native.None))
                                 s1 s2 (Prims.parse_int "0") env1 in
                             match uu____5375 with
                             | (r,env11) ->
                                 ((FStar_Extraction_JavaScript_Ast.JSS_Seq
                                     [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                        (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                             (new_name,
                                               FStar_Pervasives_Native.None)),
                                           (FStar_Pervasives_Native.Some
                                              match_e)),
                                          FStar_Extraction_JavaScript_Ast.JSV_Const);
                                     FStar_Extraction_JavaScript_Ast.JSS_If
                                       (if_cond, r,
                                         (FStar_Pervasives_Native.Some s2))]),
                                   env11))))
            | FStar_Extraction_ML_Syntax.MLP_Branch lp ->
                let rec translate_p_branch lp1 match_e1 s11 s21 env1 =
                  match lp1 with
                  | [] -> failwith "Empty list in translate_p_branch"
                  | x::[] -> translate_pat x match_e1 s11 s21 env1
                  | hd1::tl1 ->
                      let uu____5440 =
                        translate_p_branch tl1 match_e1 s11 s21 env1 in
                      (match uu____5440 with
                       | (r,e1) -> translate_pat hd1 match_e1 s11 r e1) in
                translate_p_branch lp match_e s1 s2 env
            | FStar_Extraction_ML_Syntax.MLP_Record (path,lp) ->
                let rec translate_p_record lp1 match_e1 s11 s21 env1 =
                  let new_fv_x n1 =
                    FStar_Extraction_JavaScript_Ast.JSE_Member
                      (match_e1,
                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                           ((Prims.strcat "_" n1),
                             FStar_Pervasives_Native.None))) in
                  match lp1 with
                  | [] -> failwith "Empty list in translate_p_record"
                  | x::[] ->
                      translate_pat (FStar_Pervasives_Native.snd x)
                        (new_fv_x (FStar_Pervasives_Native.fst x)) s11 s21
                        env1
                  | hd1::tl1 ->
                      let uu____5548 =
                        translate_p_record tl1 match_e1 s11 s21 env1 in
                      (match uu____5548 with
                       | (r,e1) ->
                           translate_pat (FStar_Pervasives_Native.snd hd1)
                             (new_fv_x (FStar_Pervasives_Native.fst hd1)) r
                             s21 e1) in
                translate_p_record lp match_e s1 s2 env
            | FStar_Extraction_ML_Syntax.MLP_Tuple lp ->
                let rec translate_p_tuple lp1 d match_e1 s11 s21 env1 =
                  let new_fv_x =
                    let uu____5590 =
                      let uu____5595 =
                        let uu____5596 =
                          let uu____5597 =
                            let uu____5602 = FStar_Util.string_of_int d in
                            ((FStar_Extraction_JavaScript_Ast.JSV_Number
                                (float_of_int d)), uu____5602) in
                          FStar_Extraction_JavaScript_Ast.JSE_Literal
                            uu____5597 in
                        FStar_Extraction_JavaScript_Ast.JSPM_Expression
                          uu____5596 in
                      (match_e1, uu____5595) in
                    FStar_Extraction_JavaScript_Ast.JSE_Member uu____5590 in
                  match lp1 with
                  | [] -> failwith "Empty list in translate_p_tuple"
                  | x::[] -> translate_pat x new_fv_x s11 s21 env1
                  | hd1::tl1 ->
                      let uu____5616 =
                        translate_p_tuple tl1 (d + (Prims.parse_int "1"))
                          match_e1 s11 s21 env1 in
                      (match uu____5616 with
                       | (r,e1) -> translate_pat hd1 new_fv_x r s21 e1) in
                translate_p_tuple lp (Prims.parse_int "0") match_e s1 s2 env
and translate_constant:
  FStar_Extraction_ML_Syntax.mlconstant ->
    FStar_Extraction_JavaScript_Ast.expression_t
  =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          (FStar_Extraction_JavaScript_Ast.JSV_Null, "")
    | FStar_Extraction_ML_Syntax.MLC_Bool b ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_Boolean b), "")
    | FStar_Extraction_ML_Syntax.MLC_Int (s,uu____5630) ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_Number
              (float_of_int (Prims.parse_int "0"))), s)
    | FStar_Extraction_ML_Syntax.MLC_Float f ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_Number f),
            (FStar_Util.string_of_float f))
    | FStar_Extraction_ML_Syntax.MLC_Char uu____5644 ->
        failwith "todo: translate_const [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_String s), s)
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____5646 ->
        failwith "todo: translate_const [MLC_Bytes]"
and map_type:
  env_t ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlsymbol Prims.list
        FStar_Pervasives_Native.option ->
        (FStar_Extraction_JavaScript_Ast.typ Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun args  ->
      fun lp_generic  ->
        FStar_List.fold_left
          (fun uu____5671  ->
             fun x  ->
               match uu____5671 with
               | (r,e) ->
                   let uu____5691 = translate_type x lp_generic e in
                   (match uu____5691 with
                    | (r1,e1) -> ((FStar_List.append r [r1]), e1))) ([], env)
          args
and translate_type:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlsymbol Prims.list
      FStar_Pervasives_Native.option ->
      env_t ->
        (FStar_Extraction_JavaScript_Ast.typ,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun lp_generic  ->
      fun env  ->
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Tuple [] ->
            (FStar_Extraction_JavaScript_Ast.JST_Any, env)
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            (FStar_Extraction_JavaScript_Ast.JST_Any, env)
        | FStar_Extraction_ML_Syntax.MLTY_Var (id,uu____5720) ->
            ((FStar_Extraction_JavaScript_Ast.JST_Generic
                (id, FStar_Pervasives_Native.None)), env)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple lt1 ->
            let uu____5730 = map_type env lt1 lp_generic in
            (match uu____5730 with
             | (r,env1) ->
                 ((FStar_Extraction_JavaScript_Ast.JST_Tuple r), env1))
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,e_tag,t2) ->
            let uu____5750 =
              translate_type t1 FStar_Pervasives_Native.None env in
            (match uu____5750 with
             | (t11,env1) ->
                 let uu____5763 =
                   if e_tag = FStar_Extraction_ML_Syntax.E_GHOST
                   then (FStar_Extraction_JavaScript_Ast.JST_Null, env1)
                   else translate_type t2 FStar_Pervasives_Native.None env1 in
                 (match uu____5763 with
                  | (t21,env2) ->
                      ((FStar_Extraction_JavaScript_Ast.JST_Function
                          ([(("_1", FStar_Pervasives_Native.None), t11)],
                            t21, lp_generic)), env2)))
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,p) when
            let uu____5831 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5831 = "FStar.ST.ref" ->
            let uu____5832 =
              let uu____5837 = FStar_List.nth args (Prims.parse_int "0") in
              translate_type uu____5837 lp_generic env in
            (match uu____5832 with
             | (r,env1) ->
                 ((FStar_Extraction_JavaScript_Ast.JST_Array r), env1))
        | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5844,p) when
            let uu____5850 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5850 = "FStar.Buffer.buffer" ->
            let uu____5851 = addImportModule env p in
            (match uu____5851 with
             | (name,env1) ->
                 ((FStar_Extraction_JavaScript_Ast.JST_Generic
                     (name, FStar_Pervasives_Native.None)), env1))
        | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5868,p) when
            let uu____5874 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5874 = "FStar.Ghost.erased" ->
            (FStar_Extraction_JavaScript_Ast.JST_Any, env)
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,(path,name)) ->
            if is_standart_type name
            then
              let uu____5896 = FStar_Util.must (mk_standart_type name) in
              (uu____5896, env)
            else
              (let uu____5898 =
                 let uu____5899 =
                   FStar_Extraction_ML_Util.is_xtuple_ty (path, name) in
                 FStar_Option.isSome uu____5899 in
               if uu____5898
               then
                 let uu____5908 = map_type env args lp_generic in
                 match uu____5908 with
                 | (r,env1) ->
                     ((FStar_Extraction_JavaScript_Ast.JST_Tuple r), env1)
               else
                 (let uu____5926 =
                    match args with
                    | [] -> (FStar_Pervasives_Native.None, env)
                    | uu____5949 ->
                        let uu____5952 = map_type env args lp_generic in
                        (match uu____5952 with
                         | (r,env1) ->
                             ((FStar_Pervasives_Native.Some r), env1)) in
                  match uu____5926 with
                  | (args_t,env1) ->
                      let uu____5993 = addImportModule env1 (path, name) in
                      (match uu____5993 with
                       | (name1,env2) ->
                           ((FStar_Extraction_JavaScript_Ast.JST_Generic
                               (name1, args_t)), env2))))