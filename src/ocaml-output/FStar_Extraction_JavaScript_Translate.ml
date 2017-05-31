open Prims
type file = (Prims.string* FStar_Extraction_JavaScript_Ast.t)
type env_t =
  {
  names: name Prims.list;
  module_name: Prims.string;
  import_module_names: Prims.string Prims.list;}
and name = {
  pretty: Prims.string;
  mut: Prims.bool;}
let empty: Prims.string -> env_t =
  fun module_name  -> { names = []; module_name; import_module_names = [] }
let mk_op_bin: Prims.string -> FStar_Extraction_JavaScript_Ast.op_bin option
  =
  fun uu___141_50  ->
    match uu___141_50 with
    | "op_Addition" -> Some FStar_Extraction_JavaScript_Ast.JSB_Plus
    | "op_Subtraction" -> Some FStar_Extraction_JavaScript_Ast.JSB_Minus
    | "op_Multiply" -> Some FStar_Extraction_JavaScript_Ast.JSB_Mult
    | "op_Division" -> Some FStar_Extraction_JavaScript_Ast.JSB_Div
    | "op_Equality" -> Some FStar_Extraction_JavaScript_Ast.JSB_Equal
    | "op_disEquality" -> Some FStar_Extraction_JavaScript_Ast.JSB_NotEqual
    | "op_LessThanOrEqual" ->
        Some FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual
    | "op_GreaterThanOrEqual" ->
        Some FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual
    | "op_LessThan" -> Some FStar_Extraction_JavaScript_Ast.JSB_LessThan
    | "op_GreaterThan" ->
        Some FStar_Extraction_JavaScript_Ast.JSB_GreaterThan
    | "op_Modulus" -> Some FStar_Extraction_JavaScript_Ast.JSB_Mod
    | uu____52 -> None
let is_op_bin: Prims.string -> Prims.bool = fun op  -> (mk_op_bin op) <> None
let mk_op_un: Prims.string -> FStar_Extraction_JavaScript_Ast.op_un option =
  fun uu___142_60  ->
    match uu___142_60 with
    | "op_Negation" -> Some FStar_Extraction_JavaScript_Ast.JSU_Not
    | "op_Minus" -> Some FStar_Extraction_JavaScript_Ast.JSU_Minus
    | uu____62 -> None
let is_op_un: Prims.string -> Prims.bool = fun op  -> (mk_op_un op) <> None
let mk_op_bool: Prims.string -> FStar_Extraction_JavaScript_Ast.op_log option
  =
  fun uu___143_70  ->
    match uu___143_70 with
    | "op_AmpAmp" -> Some FStar_Extraction_JavaScript_Ast.JSL_And
    | "op_BarBar" -> Some FStar_Extraction_JavaScript_Ast.JSL_Or
    | uu____72 -> None
let is_op_bool: Prims.string -> Prims.bool =
  fun op  -> (mk_op_bool op) <> None
let mk_standart_type:
  Prims.string -> FStar_Extraction_JavaScript_Ast.typ option =
  fun uu___144_80  ->
    match uu___144_80 with
    | "unit" -> Some FStar_Extraction_JavaScript_Ast.JST_Null
    | "bool" -> Some FStar_Extraction_JavaScript_Ast.JST_Boolean
    | "int" -> Some FStar_Extraction_JavaScript_Ast.JST_Number
    | "nat" -> Some FStar_Extraction_JavaScript_Ast.JST_Number
    | "string" -> Some FStar_Extraction_JavaScript_Ast.JST_String
    | uu____82 -> None
let is_standart_type: Prims.string -> Prims.bool =
  fun t  -> (mk_standart_type t) <> None
let float_of_int: Prims.int -> FStar_BaseTypes.float =
  fun i  -> FStar_Util.float_of_int32 (FStar_Util.int32_of_int i)
let isMutable typ =
  match typ with
  | None  -> false
  | Some (uu____105,ty) ->
      (match ty with
       | FStar_Extraction_ML_Syntax.MLTY_Named (uu____109,p) when
           let uu____113 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____113 = "FStar.ST.ref" -> true
       | uu____114 -> false)
let extendEnv env uu____136 typ =
  match uu____136 with
  | (path,n1) ->
      let path1 = FStar_String.concat "_" path in
      if (path1 = env.module_name) || (path1 = "")
      then
        let uu___145_149 = env in
        {
          names = ({ pretty = n1; mut = (isMutable typ) } :: (env.names));
          module_name = (uu___145_149.module_name);
          import_module_names = (uu___145_149.import_module_names)
        }
      else
        (let n2 = Prims.strcat path1 (Prims.strcat "." n1) in
         if
           Prims.op_Negation
             (FStar_List.existsb (fun x  -> x = path1)
                env.import_module_names)
         then
           let uu___146_153 = env in
           {
             names = ({ pretty = n2; mut = (isMutable typ) } :: (env.names));
             module_name = (uu___146_153.module_name);
             import_module_names = (path1 :: (env.import_module_names))
           }
         else
           (let uu___147_155 = env in
            {
              names = ({ pretty = n2; mut = (isMutable typ) } :: (env.names));
              module_name = (uu___147_155.module_name);
              import_module_names = (uu___147_155.import_module_names)
            }))
let addImportModule:
  env_t -> (Prims.string Prims.list* Prims.string) -> (Prims.string* env_t) =
  fun env  ->
    fun uu____166  ->
      match uu____166 with
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
                 (let uu___148_184 = env in
                  {
                    names = (uu___148_184.names);
                    module_name = (uu___148_184.module_name);
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
let rec is_pure_expr e var =
  match e.FStar_Extraction_ML_Syntax.expr with
  | FStar_Extraction_ML_Syntax.MLE_Const uu____216 -> true
  | FStar_Extraction_ML_Syntax.MLE_Name uu____217 -> true
  | FStar_Extraction_ML_Syntax.MLE_Var (n1,uu____219) -> n1 <> (fst var)
  | FStar_Extraction_ML_Syntax.MLE_Proj (expr,uu____221) ->
      is_pure_expr expr var
  | FStar_Extraction_ML_Syntax.MLE_CTor (p,le) ->
      let uu____226 =
        let uu____227 = FStar_List.map (fun x  -> is_pure_expr x var) le in
        FStar_List.contains false uu____227 in
      Prims.op_Negation uu____226
  | FStar_Extraction_ML_Syntax.MLE_Tuple le ->
      let uu____232 =
        let uu____233 = FStar_List.map (fun x  -> is_pure_expr x var) le in
        FStar_List.contains false uu____233 in
      Prims.op_Negation uu____232
  | FStar_Extraction_ML_Syntax.MLE_Record (uu____236,lne) ->
      let uu____246 =
        let uu____247 =
          FStar_List.map
            (fun uu____251  ->
               match uu____251 with | (n1,e1) -> is_pure_expr e1 var) lne in
        FStar_List.contains false uu____247 in
      Prims.op_Negation uu____246
  | FStar_Extraction_ML_Syntax.MLE_App (uu____256,args) ->
      let uu____260 =
        let uu____261 = FStar_List.map (fun x  -> is_pure_expr x var) args in
        FStar_List.contains false uu____261 in
      Prims.op_Negation uu____260
  | uu____264 -> false
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____419  ->
    match uu____419 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____450 = m in
               match uu____450 with
               | ((prefix1,final),uu____462,uu____463) ->
                   FStar_String.concat "_"
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____479 = translate_module (empty m_name) m in
                Some uu____479)
             with
             | e ->
                 ((let uu____484 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____484);
                  None)) modules1
and translate_module:
  env_t ->
    ((Prims.string Prims.list* Prims.string)*
      (FStar_Extraction_ML_Syntax.mlsig* FStar_Extraction_ML_Syntax.mlmodule)
      option* FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun env  ->
    fun uu____486  ->
      match uu____486 with
      | (module_name,modul,uu____498) ->
          let program =
            match modul with
            | Some (_signature,decls) ->
                let update_env uu____521 =
                  let uu___151_522 = env in
                  {
                    names = [];
                    module_name = (uu___151_522.module_name);
                    import_module_names = (uu___151_522.import_module_names)
                  } in
                let res =
                  FStar_List.filter_map
                    (fun d  -> translate_decl (update_env ()) d) decls in
                let td =
                  FStar_List.map
                    (fun uu____534  -> match uu____534 with | (x,e) -> x) res in
                let lmodules =
                  FStar_List.collect
                    (fun uu____543  ->
                       match uu____543 with | (x,e) -> e.import_module_names)
                    res in
                let lmodules1 =
                  FStar_List.fold_left
                    (fun acc  ->
                       fun m  ->
                         if FStar_List.existsb (fun x  -> x = m) acc
                         then acc
                         else m :: acc) [] lmodules in
                let create_module_imports =
                  let uu____559 =
                    let uu____560 =
                      FStar_List.map
                        (fun m  ->
                           FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration
                             (m, None)) lmodules1 in
                    FStar_All.pipe_right uu____560
                      (fun _0_31  ->
                         FStar_Extraction_JavaScript_Ast.JSS_Block _0_31) in
                  FStar_All.pipe_right uu____559
                    (fun _0_32  ->
                       FStar_Extraction_JavaScript_Ast.JS_Statement _0_32) in
                FStar_List.append [create_module_imports] td
            | uu____565 ->
                failwith "Unexpected standalone interface or nested modules" in
          ((env.module_name), program)
and translate_decl:
  env_t ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      (FStar_Extraction_JavaScript_Ast.source_t* env_t) option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (uu____579,c_flag,lfunc) ->
          let for1 uu____592 env1 =
            match uu____592 with
            | { FStar_Extraction_ML_Syntax.mllb_name = (name,uu____598);
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = unit_b;
                FStar_Extraction_ML_Syntax.mllb_def = expr;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let uu____604 =
                  if (Prims.op_Negation pt) || unit_b
                  then (None, env1)
                  else
                    (match tys with
                     | None  -> (None, env1)
                     | Some (lp,ty) ->
                         let lp_generic =
                           match lp with
                           | [] -> None
                           | uu____627 ->
                               let uu____628 =
                                 FStar_List.map
                                   (fun uu____632  ->
                                      match uu____632 with
                                      | (id,uu____636) -> id) lp in
                               Some uu____628 in
                         let uu____638 = translate_type ty lp_generic env1 in
                         (match uu____638 with | (t,env2) -> ((Some t), env2))) in
                (match uu____604 with
                 | (t,env2) ->
                     let is_private =
                       FStar_List.contains FStar_Extraction_ML_Syntax.Private
                         c_flag in
                     let uu____655 =
                       let uu____659 = is_pure_expr expr (name, None) in
                       if uu____659
                       then
                         let var_decl_q =
                           if isMutable tys
                           then FStar_Extraction_JavaScript_Ast.JSV_Let
                           else FStar_Extraction_JavaScript_Ast.JSV_Const in
                         let env3 = extendEnv env2 ([], name) tys in
                         let uu____669 = translate_expr_pure expr env3 in
                         match uu____669 with
                         | (r,env4) ->
                             ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                 (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                      (name, t)), (Some r)), var_decl_q)],
                               env4)
                       else translate_expr expr (name, t) [] env2 false in
                     (match uu____655 with
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
          let uu____698 =
            FStar_List.fold_left
              (fun uu____705  ->
                 fun x  ->
                   match uu____705 with
                   | (r,e) ->
                       let update_env uu____720 =
                         let uu___152_721 = e in
                         {
                           names = [];
                           module_name = (uu___152_721.module_name);
                           import_module_names =
                             (uu___152_721.import_module_names)
                         } in
                       let uu____722 = for1 x (update_env ()) in
                       (match uu____722 with
                        | (r1,e1) ->
                            ((FStar_List.append r
                                [FStar_Extraction_JavaScript_Ast.JSS_Seq r1]),
                              e1))) ([], env) lfunc in
          (match uu____698 with
           | (r,env1) ->
               Some
                 ((FStar_Extraction_JavaScript_Ast.JS_Statement
                     (FStar_Extraction_JavaScript_Ast.JSS_Block r)), env1))
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____744 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____747,name,uu____749,tparams,body)::[]) ->
          let tparams1 =
            match tparams with
            | [] -> None
            | uu____776 ->
                let uu____777 =
                  FStar_List.map
                    (fun uu____781  ->
                       match uu____781 with | (id,uu____785) -> id) tparams in
                Some uu____777 in
          let forbody body1 =
            let get_export stmt =
              FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration
                ((FStar_Extraction_JavaScript_Ast.JSE_Declaration stmt),
                  FStar_Extraction_JavaScript_Ast.ExportType) in
            match body1 with
            | FStar_Extraction_ML_Syntax.MLTD_Abbrev t ->
                let uu____800 = translate_type t tparams1 env in
                (match uu____800 with
                 | (t1,env1) ->
                     ((get_export
                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                            ((name, None), tparams1, t1))), env1))
            | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                let tag =
                  [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                       ("_tag", None)),
                     (FStar_Extraction_JavaScript_Ast.JST_StringLiteral
                        ("Record", "")))] in
                let uu____826 =
                  FStar_List.fold_left
                    (fun uu____839  ->
                       fun uu____840  ->
                         match (uu____839, uu____840) with
                         | ((r,e),(n1,t)) ->
                             let uu____877 = translate_type t tparams1 e in
                             (match uu____877 with
                              | (r1,e1) ->
                                  ((FStar_List.append r
                                      [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                           ((Prims.strcat "_" n1), None)),
                                         r1)]), e1))) ([], env) fields in
                (match uu____826 with
                 | (fields_t,env1) ->
                     ((get_export
                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                            ((name, None), tparams1,
                              (FStar_Extraction_JavaScript_Ast.JST_Object
                                 (FStar_List.append tag fields_t))))), env1))
            | FStar_Extraction_ML_Syntax.MLTD_DType lfields ->
                let tag n1 =
                  [((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                       ("_tag", None)),
                     (FStar_Extraction_JavaScript_Ast.JST_StringLiteral
                        (n1, "")))] in
                let fields_t fields env1 =
                  FStar_List.fold_left
                    (fun uu____958  ->
                       fun t  ->
                         match uu____958 with
                         | (i,r,e) ->
                             let uu____981 = translate_type t tparams1 e in
                             (match uu____981 with
                              | (r1,e1) ->
                                  let uu____992 =
                                    let uu____996 =
                                      let uu____1000 =
                                        let uu____1003 =
                                          let uu____1004 =
                                            let uu____1008 =
                                              let uu____1009 =
                                                FStar_Util.string_of_int i in
                                              Prims.strcat "_" uu____1009 in
                                            (uu____1008, None) in
                                          FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                            uu____1004 in
                                        (uu____1003, r1) in
                                      [uu____1000] in
                                    FStar_List.append r uu____996 in
                                  ((i + (Prims.parse_int "1")), uu____992,
                                    e1))) ((Prims.parse_int "0"), [], env1)
                    fields in
                let uu____1025 =
                  FStar_List.fold_left
                    (fun uu____1035  ->
                       fun uu____1036  ->
                         match (uu____1035, uu____1036) with
                         | ((r,e),(n1,l)) ->
                             let uu____1066 = fields_t l e in
                             (match uu____1066 with
                              | (uu____1076,r1,e1) ->
                                  ((FStar_List.append r
                                      [get_export
                                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                                            ((n1, None), tparams1,
                                              (FStar_Extraction_JavaScript_Ast.JST_Object
                                                 (FStar_List.append (
                                                    tag n1) r1))))]), e1)))
                    ([], env) lfields in
                (match uu____1025 with
                 | (lfields_t,env1) ->
                     let tparams_gen =
                       match tparams1 with
                       | Some t ->
                           let uu____1109 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_Extraction_JavaScript_Ast.JST_Generic
                                    (x, None)) t in
                           FStar_All.pipe_right uu____1109
                             (fun _0_33  -> Some _0_33)
                       | None  -> None in
                     let lnames =
                       FStar_List.map
                         (fun uu____1126  ->
                            match uu____1126 with
                            | (n1,l) ->
                                FStar_Extraction_JavaScript_Ast.JST_Generic
                                  (n1, tparams_gen)) lfields in
                     let union_t =
                       get_export
                         (FStar_Extraction_JavaScript_Ast.JSS_TypeAlias
                            ((name, None), tparams1,
                              (FStar_Extraction_JavaScript_Ast.JST_Union
                                 lnames))) in
                     ((FStar_Extraction_JavaScript_Ast.JSS_Block
                         (FStar_List.append lfields_t [union_t])), env1)) in
          let uu____1143 =
            match body with
            | None  ->
                failwith "todo: translate_decl [MLM_Ty] with empty body"
            | Some v1 -> forbody v1 in
          (match uu____1143 with
           | (body_t,env1) ->
               Some
                 ((FStar_Extraction_JavaScript_Ast.JS_Statement body_t),
                   env1))
      | FStar_Extraction_ML_Syntax.MLM_Ty uu____1158 ->
          failwith "todo: translate_decl [MLM_Ty]"
      | FStar_Extraction_ML_Syntax.MLM_Top uu____1162 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          Some
            ((FStar_Extraction_JavaScript_Ast.JS_Statement
                (FStar_Extraction_JavaScript_Ast.JSS_Block [])), env)
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____1170 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_expr:
  FStar_Extraction_ML_Syntax.mlexpr ->
    (FStar_Extraction_ML_Syntax.mlsymbol* FStar_Extraction_JavaScript_Ast.typ
      option) ->
      FStar_Extraction_JavaScript_Ast.statement_t Prims.list ->
        env_t ->
          Prims.bool ->
            (FStar_Extraction_JavaScript_Ast.statement_t Prims.list* env_t)
  =
  fun e  ->
    fun var  ->
      fun lstmt  ->
        fun env  ->
          fun isDecl  ->
            let get_res expr new_fv env1 =
              let is_inEnv = isInEnv env1 (fst var) in
              let uu____1206 =
                let res e1 =
                  let env2 = extendEnv env1 ([], (fst var)) None in
                  if is_inEnv
                  then ([FStar_Extraction_JavaScript_Ast.JSS_Block e1], env2)
                  else (e1, env2) in
                match expr with
                | FStar_Extraction_JavaScript_Ast.JSE_Assignment uu____1233
                    ->
                    if isDecl
                    then
                      (if (fst var) = "_"
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
                                (Some
                                   (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                      (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                        "")))),
                               FStar_Extraction_JavaScript_Ast.JSV_Let)]
                           lstmt)
                | uu____1251 ->
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
                                   var), (Some expr)),
                                FStar_Extraction_JavaScript_Ast.JSV_Let)]
                           lstmt) in
              match uu____1206 with
              | (expr1,env2) ->
                  (((match new_fv with
                     | [] -> expr1
                     | uu____1270 ->
                         if is_inEnv
                         then FStar_List.append new_fv expr1
                         else
                           FStar_List.append new_fv
                             [FStar_Extraction_JavaScript_Ast.JSS_Block expr1])),
                    env2) in
            match e.FStar_Extraction_ML_Syntax.expr with
            | x when is_pure_expr e var ->
                let uu____1279 = translate_expr_pure e env in
                (match uu____1279 with | (expr,env1) -> get_res expr [] env1)
            | FStar_Extraction_ML_Syntax.MLE_Let
                ((uu____1287,uu____1288,{
                                          FStar_Extraction_ML_Syntax.mllb_name
                                            = (name,uu____1290);
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
                let uu____1305 = is_pure_expr body (name, None) in
                if uu____1305
                then
                  let var_decl_q =
                    if isMutable tys
                    then FStar_Extraction_JavaScript_Ast.JSV_Let
                    else FStar_Extraction_JavaScript_Ast.JSV_Const in
                  let uu____1313 = translate_expr_pure body env1 in
                  (match uu____1313 with
                   | (r,env2) ->
                       let uu____1321 =
                         translate_expr continuation var lstmt env2 isDecl in
                       (match uu____1321 with
                        | (c,env11) ->
                            let c1 =
                              FStar_List.append
                                [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                   (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                        (name, None)), (Some r)), var_decl_q)]
                                c in
                            let env3 =
                              let uu___153_1340 = env2 in
                              {
                                names = (uu___153_1340.names);
                                module_name = (uu___153_1340.module_name);
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
                  (let uu____1348 =
                     translate_expr continuation var lstmt env1 isDecl in
                   match uu____1348 with
                   | (c,env11) ->
                       let uu____1359 =
                         translate_expr body (name, None) c env1 false in
                       (match uu____1359 with
                        | (r,env2) ->
                            let env3 =
                              let uu___154_1372 = env2 in
                              {
                                names = (uu___154_1372.names);
                                module_name = (uu___154_1372.module_name);
                                import_module_names =
                                  (FStar_List.append env2.import_module_names
                                     env11.import_module_names)
                              } in
                            (r, env3)))
            | FStar_Extraction_ML_Syntax.MLE_Let uu____1374 ->
                failwith "todo: translate_expr [MLE_Let]"
            | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
                let uu____1392 =
                  FStar_List.fold_left
                    (fun uu____1403  ->
                       fun uu____1404  ->
                         match (uu____1403, uu____1404) with
                         | ((r,e1),((n1,uu____1425),t)) ->
                             let uu____1438 = translate_type t None e1 in
                             (match uu____1438 with
                              | (r1,e11) ->
                                  ((FStar_List.append r
                                      [FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                         (n1, (Some r1))]), e11))) ([], env)
                    args in
                (match uu____1392 with
                 | (args1,env1) ->
                     let is_failwith =
                       match body.FStar_Extraction_ML_Syntax.expr with
                       | FStar_Extraction_ML_Syntax.MLE_App (expr,uu____1459)
                           ->
                           (match expr.FStar_Extraction_ML_Syntax.expr with
                            | FStar_Extraction_ML_Syntax.MLE_Name p when
                                let uu____1463 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    p in
                                uu____1463 = "failwith" -> true
                            | uu____1464 -> false)
                       | uu____1465 -> false in
                     let uu____1466 =
                       if is_failwith
                       then
                         ((FStar_Extraction_JavaScript_Ast.JS_BodyBlock
                             [FStar_Extraction_JavaScript_Ast.JSS_Throw
                                (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                   ((FStar_Extraction_JavaScript_Ast.JSV_String
                                       "Not yet implemented!"), ""))]), env1)
                       else
                         (let uu____1472 = is_pure_expr body var in
                          if uu____1472
                          then
                            let uu____1476 = translate_expr_pure body env1 in
                            match uu____1476 with
                            | (r,env11) ->
                                ((FStar_Extraction_JavaScript_Ast.JS_BodyExpression
                                    r), env11)
                          else
                            (let uu____1484 =
                               translate_expr body ("_res", None)
                                 [FStar_Extraction_JavaScript_Ast.JSS_Return
                                    (Some
                                       (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                          ("_res", None)))] env1 true in
                             match uu____1484 with
                             | (t1,env11) ->
                                 ((FStar_Extraction_JavaScript_Ast.JS_BodyBlock
                                     (FStar_List.append
                                        [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                           (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                                ("_res", None)), None),
                                             FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                        t1)), env11))) in
                     (match uu____1466 with
                      | (body_t,env11) ->
                          let uu____1506 =
                            match snd var with
                            | None  -> (None, None)
                            | Some v1 ->
                                (match v1 with
                                 | FStar_Extraction_JavaScript_Ast.JST_Function
                                     (uu____1528,t2,lp) -> ((Some t2), lp)
                                 | uu____1550 -> (None, None)) in
                          (match uu____1506 with
                           | (ret_t,lp_generic) ->
                               let expr =
                                 FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction
                                   (None, args1, body_t, ret_t, lp_generic) in
                               let uu____1578 =
                                 if isDecl
                                 then
                                   ([FStar_Extraction_JavaScript_Ast.JSS_Expression
                                       (FStar_Extraction_JavaScript_Ast.JSE_Assignment
                                          ((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                              ((fst var), None)), expr))],
                                     env1)
                                 else
                                   (let env2 =
                                      extendEnv env1 ([], (fst var)) None in
                                    ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                        (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                             ((fst var), None)), (Some expr)),
                                          FStar_Extraction_JavaScript_Ast.JSV_Const)],
                                      env2)) in
                               (match uu____1578 with
                                | (expr1,env2) ->
                                    let env3 =
                                      let uu___155_1609 = env2 in
                                      {
                                        names = (uu___155_1609.names);
                                        module_name =
                                          (uu___155_1609.module_name);
                                        import_module_names =
                                          (FStar_List.append
                                             env2.import_module_names
                                             env11.import_module_names)
                                      } in
                                    ((FStar_List.append expr1 lstmt), env3)))))
            | FStar_Extraction_ML_Syntax.MLE_If (cond,s1,s2) ->
                let uu____1616 = translate_expr s1 var [] env true in
                (match uu____1616 with
                 | (r1,env1) ->
                     let s11 = FStar_Extraction_JavaScript_Ast.JSS_Block r1 in
                     let uu____1628 =
                       match s2 with
                       | Some v1 ->
                           let uu____1636 = translate_expr v1 var [] env true in
                           (match uu____1636 with
                            | (r2,env2) ->
                                ((Some
                                    (FStar_Extraction_JavaScript_Ast.JSS_Block
                                       r2)), env2))
                       | None  -> (None, env) in
                     (match uu____1628 with
                      | (s21,env2) ->
                          let uu____1656 =
                            let uu____1660 = is_pure_expr cond var in
                            if uu____1660
                            then
                              let uu____1665 = translate_expr_pure cond env in
                              match uu____1665 with
                              | (c1,envc) ->
                                  ([FStar_Extraction_JavaScript_Ast.JSS_If
                                      (c1, s11, s21)], envc)
                            else
                              (let uu____1676 =
                                 translate_expr cond ("_cond", None)
                                   [FStar_Extraction_JavaScript_Ast.JSS_If
                                      ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                          ("_cond", None)), s11, s21)] env
                                   true in
                               match uu____1676 with
                               | (c1,envc) ->
                                   ((FStar_List.append
                                       [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                          (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                               ("_cond",
                                                 (Some
                                                    FStar_Extraction_JavaScript_Ast.JST_Boolean))),
                                             None),
                                            FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                       c1), envc)) in
                          (match uu____1656 with
                           | (c,env3) ->
                               let uu____1703 =
                                 if isDecl
                                 then (c, env3)
                                 else
                                   (let env4 =
                                      extendEnv env3 ([], (fst var)) None in
                                    ((FStar_List.append
                                        [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                           (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                                var), None),
                                             FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                        c), env4)) in
                               (match uu____1703 with
                                | (c1,env4) ->
                                    let env5 =
                                      let uu___156_1730 = env4 in
                                      {
                                        names = (uu___156_1730.names);
                                        module_name =
                                          (uu___156_1730.module_name);
                                        import_module_names =
                                          (FStar_List.append
                                             env4.import_module_names
                                             (FStar_List.append
                                                env1.import_module_names
                                                env2.import_module_names))
                                      } in
                                    ((FStar_List.append c1 lstmt), env5)))))
            | FStar_Extraction_ML_Syntax.MLE_Raise uu____1732 ->
                failwith "todo: translate_expr [MLE_Raise]"
            | FStar_Extraction_ML_Syntax.MLE_Try uu____1739 ->
                failwith "todo: translate_expr [MLE_Try]"
            | FStar_Extraction_ML_Syntax.MLE_Coerce (in_e,t,uu____1752) ->
                let lp_generic =
                  match snd var with
                  | None  -> None
                  | Some v1 ->
                      (match v1 with
                       | FStar_Extraction_JavaScript_Ast.JST_Function
                           (uu____1763,uu____1764,lp) -> lp
                       | uu____1782 -> None) in
                let uu____1784 = translate_type t lp_generic env in
                (match uu____1784 with
                 | (t1,env1) ->
                     let var1 = ((fst var), (Some t1)) in
                     translate_expr in_e var1 lstmt env1 isDecl)
            | FStar_Extraction_ML_Syntax.MLE_Match (e_in,lb) ->
                let match_e =
                  let uu____1814 =
                    let uu____1815 = FStar_Extraction_ML_Syntax.gensym () in
                    fst uu____1815 in
                  (uu____1814, None) in
                let uu____1819 =
                  let uu____1823 = is_pure_expr e_in var in
                  if uu____1823
                  then
                    let uu____1828 = translate_expr_pure e_in env in
                    match uu____1828 with
                    | (r1,env1) ->
                        let uu____1836 =
                          translate_match lb
                            (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                               match_e) var env1 in
                        (match uu____1836 with
                         | (r2,env2) ->
                             let env3 =
                               let uu___157_1845 = env1 in
                               {
                                 names = (uu___157_1845.names);
                                 module_name = (uu___157_1845.module_name);
                                 import_module_names =
                                   (FStar_List.append
                                      env1.import_module_names
                                      env2.import_module_names)
                               } in
                             ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                 (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                      match_e), (Some r1)),
                                   FStar_Extraction_JavaScript_Ast.JSV_Const);
                              r2], env3))
                  else
                    (let uu____1852 =
                       translate_match lb
                         (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                            match_e) var env in
                     match uu____1852 with
                     | (r2,env2) ->
                         let uu____1860 =
                           translate_expr e_in match_e [r2] env true in
                         (match uu____1860 with
                          | (r1,env1) ->
                              let env3 =
                                let uu___158_1872 = env1 in
                                {
                                  names = (uu___158_1872.names);
                                  module_name = (uu___158_1872.module_name);
                                  import_module_names =
                                    (FStar_List.append
                                       env1.import_module_names
                                       env2.import_module_names)
                                } in
                              ((FStar_List.append
                                  [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                     (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                          match_e), None),
                                       FStar_Extraction_JavaScript_Ast.JSV_Let)]
                                  r1), env3))) in
                (match uu____1819 with
                 | (c,env1) ->
                     let c1 = [FStar_Extraction_JavaScript_Ast.JSS_Block c] in
                     let uu____1887 =
                       if isDecl
                       then (c1, env1)
                       else
                         (let env2 = extendEnv env1 ([], (fst var)) None in
                          ((FStar_List.append
                              [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                 (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                      var), None),
                                   FStar_Extraction_JavaScript_Ast.JSV_Let)]
                              c1), env2)) in
                     (match uu____1887 with
                      | (c2,env2) -> ((FStar_List.append c2 lstmt), env2)))
            | FStar_Extraction_ML_Syntax.MLE_Seq ls ->
                let rec translate_seq l env1 acc =
                  match l with
                  | [] -> failwith "Empty list in [MLE_Seq]"
                  | x::[] ->
                      let uu____1940 = translate_expr x var [] env1 isDecl in
                      (match uu____1940 with
                       | (r,env2) -> ((FStar_List.append acc r), env2))
                  | hd1::tl1 ->
                      let uu____1955 =
                        translate_expr hd1 ("_", None) [] env1 true in
                      (match uu____1955 with
                       | (r,e1) ->
                           translate_seq tl1 e1 (FStar_List.append acc r)) in
                let uu____1967 = translate_seq ls env [] in
                (match uu____1967 with
                 | (r,env1) -> ((FStar_List.append r lstmt), env1))
            | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
                let uu____1983 = create_pure_args args var env in
                (match uu____1983 with
                 | (args1,new_fv,env1) ->
                     let uu____1999 = translate_arg_app e1 args1 var env1 in
                     (match uu____1999 with
                      | (expr,env2) -> get_res expr new_fv env2))
            | FStar_Extraction_ML_Syntax.MLE_CTor ((path,c),lexpr) ->
                let uu____2017 = create_pure_args lexpr var env in
                (match uu____2017 with
                 | (lexpr1,new_fv,env1) ->
                     let expr =
                       match c with
                       | x when (x = "Cons") || (x = "Nil") ->
                           (match lexpr1 with
                            | [] ->
                                FStar_Extraction_JavaScript_Ast.JSE_Array
                                  None
                            | hd1::tl1 ->
                                FStar_Extraction_JavaScript_Ast.JSE_Call
                                  ((FStar_Extraction_JavaScript_Ast.JSE_Member
                                      ((FStar_Extraction_JavaScript_Ast.JSE_Array
                                          (Some [hd1])),
                                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                           ("concat", None)))), tl1))
                       | x when (x = "Some") || (x = "None") ->
                           (match lexpr1 with
                            | [] ->
                                FStar_Extraction_JavaScript_Ast.JSE_Literal
                                  (FStar_Extraction_JavaScript_Ast.JSV_Null,
                                    "")
                            | hd1::tl1 ->
                                FStar_List.nth lexpr1 (Prims.parse_int "0"))
                       | uu____2046 ->
                           let uu____2047 =
                             let uu____2049 =
                               FStar_List.mapi
                                 (fun i  ->
                                    fun x  ->
                                      let uu____2053 =
                                        let uu____2057 =
                                          let uu____2058 =
                                            let uu____2062 =
                                              let uu____2063 =
                                                FStar_Util.string_of_int i in
                                              Prims.strcat "_" uu____2063 in
                                            (uu____2062, None) in
                                          FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                            uu____2058 in
                                        (uu____2057, x,
                                          FStar_Extraction_JavaScript_Ast.JSO_Init) in
                                      FStar_Extraction_JavaScript_Ast.JSPO_Property
                                        uu____2053) lexpr1 in
                             FStar_List.append
                               [FStar_Extraction_JavaScript_Ast.JSPO_Property
                                  ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                      ("_tag",
                                        (Some
                                           FStar_Extraction_JavaScript_Ast.JST_String))),
                                    (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                       ((FStar_Extraction_JavaScript_Ast.JSV_String
                                           c), "")),
                                    FStar_Extraction_JavaScript_Ast.JSO_Init)]
                               uu____2049 in
                           FStar_Extraction_JavaScript_Ast.JSE_Object
                             uu____2047 in
                     get_res expr new_fv env1)
            | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
                let uu____2076 =
                  FStar_List.fold_left
                    (fun uu____2089  ->
                       fun uu____2090  ->
                         match (uu____2089, uu____2090) with
                         | ((lexpr,lnew_fv,e1),(id,x)) ->
                             let uu____2126 = create_pure_args [x] var e1 in
                             (match uu____2126 with
                              | (expr,fv,e11) ->
                                  let uu____2144 =
                                    let uu____2146 =
                                      let uu____2148 =
                                        let uu____2149 =
                                          let uu____2153 =
                                            FStar_List.nth expr
                                              (Prims.parse_int "0") in
                                          ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                              ((Prims.strcat "_" id), None)),
                                            uu____2153,
                                            FStar_Extraction_JavaScript_Ast.JSO_Init) in
                                        FStar_Extraction_JavaScript_Ast.JSPO_Property
                                          uu____2149 in
                                      [uu____2148] in
                                    FStar_List.append lexpr uu____2146 in
                                  (uu____2144,
                                    (FStar_List.append fv lnew_fv), e11)))
                    ([], [], env) fields in
                (match uu____2076 with
                 | (create_fields,new_fv,env1) ->
                     let expr =
                       FStar_Extraction_JavaScript_Ast.JSE_Object
                         (FStar_List.append
                            [FStar_Extraction_JavaScript_Ast.JSPO_Property
                               ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                   ("_tag",
                                     (Some
                                        FStar_Extraction_JavaScript_Ast.JST_String))),
                                 (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                    ((FStar_Extraction_JavaScript_Ast.JSV_String
                                        "Record"), "")),
                                 FStar_Extraction_JavaScript_Ast.JSO_Init)]
                            create_fields) in
                     get_res expr new_fv env1)
            | FStar_Extraction_ML_Syntax.MLE_Tuple lexp ->
                let uu____2173 =
                  FStar_List.fold_left
                    (fun uu____2184  ->
                       fun x  ->
                         match uu____2184 with
                         | (lexpr,lnew_fv,e1) ->
                             let uu____2203 = create_pure_args [x] var e1 in
                             (match uu____2203 with
                              | (expr,fv,e11) ->
                                  ((FStar_List.append lexpr expr),
                                    (FStar_List.append fv lnew_fv), e11)))
                    ([], [], env) lexp in
                (match uu____2173 with
                 | (create_fields,new_fv,env1) ->
                     let expr =
                       FStar_Extraction_JavaScript_Ast.JSE_Array
                         (Some create_fields) in
                     get_res expr new_fv env1)
            | uu____2237 -> failwith "todo: translation ml-expr"
and create_pure_args:
  FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
    (FStar_Extraction_ML_Syntax.mlsymbol* FStar_Extraction_JavaScript_Ast.typ
      option) ->
      env_t ->
        (FStar_Extraction_JavaScript_Ast.expression_t Prims.list*
          FStar_Extraction_JavaScript_Ast.statement_t Prims.list* env_t)
  =
  fun args  ->
    fun var  ->
      fun env  ->
        FStar_List.fold_left
          (fun uu____2253  ->
             fun x  ->
               match uu____2253 with
               | (lexpr,lnew_fv,e) ->
                   (match x.FStar_Extraction_ML_Syntax.expr with
                    | FStar_Extraction_ML_Syntax.MLE_CTor
                        ((path,c),uu____2279) when
                        (c = "Nil") || (c = "None") ->
                        let uu____2287 = translate_expr_pure x e in
                        (match uu____2287 with
                         | (r1,e1) ->
                             let uu____2297 =
                               translate_type
                                 x.FStar_Extraction_ML_Syntax.mlty None e1 in
                             (match uu____2297 with
                              | (t1,e11) ->
                                  ((FStar_List.append lexpr
                                      [FStar_Extraction_JavaScript_Ast.JSE_TypeCast
                                         (r1, t1)]), lnew_fv, e11)))
                    | uu____2310 ->
                        let uu____2311 = is_pure_expr x var in
                        if uu____2311
                        then
                          let uu____2318 = translate_expr_pure x e in
                          (match uu____2318 with
                           | (r1,e1) ->
                               ((FStar_List.append lexpr [r1]), lnew_fv, e1))
                        else
                          (let fv_x =
                             let uu____2332 =
                               FStar_Extraction_ML_Syntax.gensym () in
                             fst uu____2332 in
                           let uu____2335 =
                             match x.FStar_Extraction_ML_Syntax.expr with
                             | FStar_Extraction_ML_Syntax.MLE_Var uu____2342
                                 ->
                                 let uu____2343 = translate_expr_pure x e in
                                 (match uu____2343 with
                                  | (r1,e1) ->
                                      ([FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                          (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                               (fv_x, None)), (Some r1)),
                                            FStar_Extraction_JavaScript_Ast.JSV_Const)],
                                        e1))
                             | uu____2357 ->
                                 translate_expr x (fv_x, None) [] env false in
                           match uu____2335 with
                           | (c,e1) ->
                               ((FStar_List.append lexpr
                                   [FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                      (fv_x, None)]),
                                 (FStar_List.append c lnew_fv), e1))))
          ([], [], env) args
and translate_arg_app:
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_JavaScript_Ast.expression_t Prims.list ->
      (FStar_Extraction_ML_Syntax.mlsymbol*
        FStar_Extraction_JavaScript_Ast.typ option) ->
        env_t -> (FStar_Extraction_JavaScript_Ast.expression_t* env_t)
  =
  fun e  ->
    fun args  ->
      fun var  ->
        fun env  ->
          match e.FStar_Extraction_ML_Syntax.expr with
          | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
              is_op_bin op ->
              let uu____2387 =
                let uu____2388 =
                  let uu____2392 = FStar_Util.must (mk_op_bin op) in
                  let uu____2393 = FStar_List.nth args (Prims.parse_int "0") in
                  let uu____2394 = FStar_List.nth args (Prims.parse_int "1") in
                  (uu____2392, uu____2393, uu____2394) in
                FStar_Extraction_JavaScript_Ast.JSE_Binary uu____2388 in
              (uu____2387, env)
          | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
              is_op_bool op ->
              let uu____2397 =
                let uu____2398 =
                  let uu____2402 = FStar_Util.must (mk_op_bool op) in
                  let uu____2403 = FStar_List.nth args (Prims.parse_int "0") in
                  let uu____2404 = FStar_List.nth args (Prims.parse_int "1") in
                  (uu____2402, uu____2403, uu____2404) in
                FStar_Extraction_JavaScript_Ast.JSE_Logical uu____2398 in
              (uu____2397, env)
          | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
              is_op_un op ->
              let uu____2407 =
                let uu____2408 =
                  let uu____2411 = FStar_Util.must (mk_op_un op) in
                  let uu____2412 = FStar_List.nth args (Prims.parse_int "0") in
                  (uu____2411, uu____2412) in
                FStar_Extraction_JavaScript_Ast.JSE_Unary uu____2408 in
              (uu____2407, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____2414 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____2414 = "FStar.Buffer.op_Array_Access") ||
                (let uu____2415 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____2415 = "FStar.Buffer.index")
              ->
              let uu____2416 =
                let uu____2417 =
                  let uu____2420 = FStar_List.nth args (Prims.parse_int "0") in
                  let uu____2421 =
                    let uu____2422 =
                      FStar_List.nth args (Prims.parse_int "1") in
                    FStar_Extraction_JavaScript_Ast.JSPM_Expression
                      uu____2422 in
                  (uu____2420, uu____2421) in
                FStar_Extraction_JavaScript_Ast.JSE_Member uu____2417 in
              (uu____2416, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____2424 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____2424 = "FStar.Buffer.op_Array_Assignment") ||
                (let uu____2425 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____2425 = "FStar.Buffer.upd")
              ->
              let uu____2426 =
                let uu____2427 =
                  let uu____2430 =
                    let uu____2431 =
                      let uu____2432 =
                        let uu____2435 =
                          FStar_List.nth args (Prims.parse_int "0") in
                        let uu____2436 =
                          let uu____2437 =
                            FStar_List.nth args (Prims.parse_int "1") in
                          FStar_Extraction_JavaScript_Ast.JSPM_Expression
                            uu____2437 in
                        (uu____2435, uu____2436) in
                      FStar_Extraction_JavaScript_Ast.JSE_Member uu____2432 in
                    FStar_Extraction_JavaScript_Ast.JGP_Expression uu____2431 in
                  let uu____2438 = FStar_List.nth args (Prims.parse_int "2") in
                  (uu____2430, uu____2438) in
                FStar_Extraction_JavaScript_Ast.JSE_Assignment uu____2427 in
              (uu____2426, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____2440 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____2440 = "FStar.ST.op_Bang") ||
                (let uu____2441 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____2441 = "FStar.ST.read")
              ->
              let uu____2442 =
                let uu____2443 =
                  let uu____2446 = FStar_List.nth args (Prims.parse_int "0") in
                  (uu____2446,
                    (FStar_Extraction_JavaScript_Ast.JSPM_Expression
                       (FStar_Extraction_JavaScript_Ast.JSE_Literal
                          ((FStar_Extraction_JavaScript_Ast.JSV_Number
                              (float_of_int (Prims.parse_int "0"))), "0")))) in
                FStar_Extraction_JavaScript_Ast.JSE_Member uu____2443 in
              (uu____2442, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              (let uu____2448 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____2448 = "FStar.ST.op_Colon_Equals") ||
                (let uu____2449 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____2449 = "FStar.ST.write")
              ->
              let expr =
                let uu____2451 =
                  let uu____2454 = FStar_List.nth args (Prims.parse_int "0") in
                  (uu____2454,
                    (FStar_Extraction_JavaScript_Ast.JSPM_Expression
                       (FStar_Extraction_JavaScript_Ast.JSE_Literal
                          ((FStar_Extraction_JavaScript_Ast.JSV_Number
                              (float_of_int (Prims.parse_int "0"))), "0")))) in
                FStar_Extraction_JavaScript_Ast.JSE_Member uu____2451 in
              let uu____2455 =
                let uu____2456 =
                  let uu____2459 = FStar_List.nth args (Prims.parse_int "1") in
                  ((FStar_Extraction_JavaScript_Ast.JGP_Expression expr),
                    uu____2459) in
                FStar_Extraction_JavaScript_Ast.JSE_Assignment uu____2456 in
              (uu____2455, env)
          | FStar_Extraction_ML_Syntax.MLE_Name p when
              let uu____2461 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____2461 = "FStar.ST.alloc" ->
              let uu____2462 =
                let uu____2463 =
                  let uu____2466 =
                    let uu____2468 =
                      FStar_List.nth args (Prims.parse_int "0") in
                    [uu____2468] in
                  Some uu____2466 in
                FStar_Extraction_JavaScript_Ast.JSE_Array uu____2463 in
              (uu____2462, env)
          | FStar_Extraction_ML_Syntax.MLE_Name (path,function_name) ->
              let uu____2474 = addImportModule env (path, function_name) in
              (match uu____2474 with
               | (name,env1) ->
                   ((FStar_Extraction_JavaScript_Ast.JSE_Call
                       ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                           (name, None)), args)), env1))
          | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2485) ->
              ((FStar_Extraction_JavaScript_Ast.JSE_Call
                  ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                      (name, None)), args)), env)
          | uu____2488 ->
              let uu____2489 = is_pure_expr e var in
              if uu____2489
              then
                let uu____2493 = translate_expr_pure e env in
                (match uu____2493 with
                 | (r,env1) ->
                     ((FStar_Extraction_JavaScript_Ast.JSE_Call (r, args)),
                       env1))
              else failwith "todo: translation [MLE_App]"
and map_expr_pure:
  FStar_Extraction_ML_Syntax.mlexpr Prims.list ->
    env_t -> (FStar_Extraction_JavaScript_Ast.expression_t Prims.list* env_t)
  =
  fun exprs  ->
    fun env  ->
      FStar_List.fold_left
        (fun uu____2510  ->
           fun x  ->
             match uu____2510 with
             | (r,e) ->
                 let uu____2522 = translate_expr_pure x e in
                 (match uu____2522 with
                  | (r1,e1) -> ((FStar_List.append r [r1]), e1))) ([], env)
        exprs
and translate_expr_pure:
  FStar_Extraction_ML_Syntax.mlexpr ->
    env_t -> (FStar_Extraction_JavaScript_Ast.expression_t* env_t)
  =
  fun e  ->
    fun env  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Const c ->
          let uu____2539 = translate_constant c in (uu____2539, env)
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2541) ->
          ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (name, None)),
            env)
      | FStar_Extraction_ML_Syntax.MLE_Name (path,name) ->
          let uu____2547 = addImportModule env (path, name) in
          (match uu____2547 with
           | (name1,env1) ->
               ((FStar_Extraction_JavaScript_Ast.JSE_Identifier (name1, None)),
                 env1))
      | FStar_Extraction_ML_Syntax.MLE_Tuple lexp ->
          let uu____2558 = map_expr_pure lexp env in
          (match uu____2558 with
           | (r,env1) ->
               ((FStar_Extraction_JavaScript_Ast.JSE_Array (Some r)), env1))
      | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
          let uu____2579 =
            FStar_List.fold_left
              (fun uu____2588  ->
                 fun uu____2589  ->
                   match (uu____2588, uu____2589) with
                   | ((r,e1),(id,x)) ->
                       let uu____2614 = translate_expr_pure x e1 in
                       (match uu____2614 with
                        | (r1,e11) ->
                            ((FStar_List.append r
                                [FStar_Extraction_JavaScript_Ast.JSPO_Property
                                   ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                       ((Prims.strcat "_" id), None)), r1,
                                     FStar_Extraction_JavaScript_Ast.JSO_Init)]),
                              e11))) ([], env) fields in
          (match uu____2579 with
           | (create_fields,env1) ->
               ((FStar_Extraction_JavaScript_Ast.JSE_Object
                   (FStar_List.append
                      [FStar_Extraction_JavaScript_Ast.JSPO_Property
                         ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                             ("_tag",
                               (Some
                                  FStar_Extraction_JavaScript_Ast.JST_String))),
                           (FStar_Extraction_JavaScript_Ast.JSE_Literal
                              ((FStar_Extraction_JavaScript_Ast.JSV_String
                                  "Record"), "")),
                           FStar_Extraction_JavaScript_Ast.JSO_Init)]
                      create_fields)), env1))
      | FStar_Extraction_ML_Syntax.MLE_CTor ((path,c),lexpr) ->
          let uu____2642 = addImportModule env (path, c) in
          (match uu____2642 with
           | (name,env1) ->
               (match c with
                | x when (x = "Cons") || (x = "Nil") ->
                    (match lexpr with
                     | [] ->
                         ((FStar_Extraction_JavaScript_Ast.JSE_Array None),
                           env1)
                     | hd1::tl1 ->
                         let uu____2659 = translate_expr_pure hd1 env1 in
                         (match uu____2659 with
                          | (r1,e1) ->
                              let uu____2666 = map_expr_pure tl1 e1 in
                              (match uu____2666 with
                               | (r2,e2) ->
                                   ((FStar_Extraction_JavaScript_Ast.JSE_Call
                                       ((FStar_Extraction_JavaScript_Ast.JSE_Member
                                           ((FStar_Extraction_JavaScript_Ast.JSE_Array
                                               (Some [r1])),
                                             (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                                ("concat", None)))), r2)),
                                     env1))))
                | x when (x = "Some") || (x = "None") ->
                    (match lexpr with
                     | [] ->
                         ((FStar_Extraction_JavaScript_Ast.JSE_Literal
                             (FStar_Extraction_JavaScript_Ast.JSV_Null, "")),
                           env1)
                     | hd1::tl1 ->
                         let uu____2685 = map_expr_pure lexpr env1 in
                         (match uu____2685 with
                          | (r1,e1) ->
                              let uu____2695 =
                                FStar_List.nth r1 (Prims.parse_int "0") in
                              (uu____2695, e1)))
                | uu____2696 ->
                    let uu____2697 =
                      FStar_List.fold_left
                        (fun uu____2706  ->
                           fun x  ->
                             match uu____2706 with
                             | (i,r,e1) ->
                                 let uu____2721 = translate_expr_pure x e1 in
                                 (match uu____2721 with
                                  | (r1,e11) ->
                                      let uu____2730 =
                                        let uu____2732 =
                                          let uu____2734 =
                                            let uu____2735 =
                                              let uu____2739 =
                                                let uu____2740 =
                                                  let uu____2744 =
                                                    let uu____2745 =
                                                      FStar_Util.string_of_int
                                                        i in
                                                    Prims.strcat "_"
                                                      uu____2745 in
                                                  (uu____2744, None) in
                                                FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                                  uu____2740 in
                                              (uu____2739, r1,
                                                FStar_Extraction_JavaScript_Ast.JSO_Init) in
                                            FStar_Extraction_JavaScript_Ast.JSPO_Property
                                              uu____2735 in
                                          [uu____2734] in
                                        FStar_List.append r uu____2732 in
                                      ((i + (Prims.parse_int "1")),
                                        uu____2730, e11)))
                        ((Prims.parse_int "0"), [], env1) lexpr in
                    (match uu____2697 with
                     | (uu____2751,r,env2) ->
                         ((FStar_Extraction_JavaScript_Ast.JSE_Object
                             (FStar_List.append
                                [FStar_Extraction_JavaScript_Ast.JSPO_Property
                                   ((FStar_Extraction_JavaScript_Ast.JSO_Identifier
                                       ("_tag",
                                         (Some
                                            FStar_Extraction_JavaScript_Ast.JST_String))),
                                     (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                        ((FStar_Extraction_JavaScript_Ast.JSV_String
                                            name), "")),
                                     FStar_Extraction_JavaScript_Ast.JSO_Init)]
                                r)), env2))))
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,uu____2758,uu____2759) ->
          translate_expr_pure e1 env
      | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
          let uu____2764 =
            FStar_List.fold_left
              (fun uu____2771  ->
                 fun x  ->
                   match uu____2771 with
                   | (r,e2) ->
                       (match x.FStar_Extraction_ML_Syntax.expr with
                        | FStar_Extraction_ML_Syntax.MLE_CTor
                            ((path,c),uu____2788) when
                            (c = "Nil") || (c = "None") ->
                            let uu____2796 = translate_expr_pure x e2 in
                            (match uu____2796 with
                             | (r1,e11) ->
                                 let uu____2804 =
                                   translate_type
                                     x.FStar_Extraction_ML_Syntax.mlty None
                                     e11 in
                                 (match uu____2804 with
                                  | (r2,e21) ->
                                      ((FStar_List.append r
                                          [FStar_Extraction_JavaScript_Ast.JSE_TypeCast
                                             (r1, r2)]), e21)))
                        | uu____2814 ->
                            let uu____2815 = translate_expr_pure x e2 in
                            (match uu____2815 with
                             | (r1,e11) -> ((FStar_List.append r [r1]), e11))))
              ([], env) args in
          (match uu____2764 with
           | (args1,env1) -> translate_arg_app e1 args1 ("", None) env1)
      | FStar_Extraction_ML_Syntax.MLE_Proj (expr,(path,name)) ->
          let uu____2840 = translate_expr_pure expr env in
          (match uu____2840 with
           | (r,env1) ->
               let uu____2847 = addImportModule env1 (path, name) in
               (match uu____2847 with
                | (name1,env2) ->
                    ((FStar_Extraction_JavaScript_Ast.JSE_Member
                        (r,
                          (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                             ((Prims.strcat "_" name1), None)))), env2)))
      | uu____2856 -> failwith "todo: translation ml-expr-pure"
and translate_match:
  (FStar_Extraction_ML_Syntax.mlpattern* FStar_Extraction_ML_Syntax.mlexpr
    option* FStar_Extraction_ML_Syntax.mlexpr) Prims.list ->
    FStar_Extraction_JavaScript_Ast.expression_t ->
      (FStar_Extraction_ML_Syntax.mlsymbol*
        FStar_Extraction_JavaScript_Ast.typ option) ->
        env_t -> (FStar_Extraction_JavaScript_Ast.statement_t* env_t)
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
              let uu____2894 =
                let uu____2897 = is_pure_expr expr_r var in
                if uu____2897
                then
                  let uu____2901 = translate_expr_pure expr_r env in
                  match uu____2901 with
                  | (r1,e1) ->
                      ((FStar_Extraction_JavaScript_Ast.JSS_Expression
                          (FStar_Extraction_JavaScript_Ast.JSE_Assignment
                             ((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                 var), r1))), e1)
                else
                  (let uu____2909 = translate_expr expr_r var [] env true in
                   match uu____2909 with
                   | (r1,e1) ->
                       ((FStar_Extraction_JavaScript_Ast.JSS_Seq r1), e1)) in
              (match uu____2894 with
               | (expr_t,env1) ->
                   let uu____2923 = translate_match tl1 match_e var env in
                   translate_pat_guard (p, guard) match_e expr_t uu____2923
                     env1)
and translate_pat_guard:
  (FStar_Extraction_ML_Syntax.mlpattern* FStar_Extraction_ML_Syntax.mlexpr
    option) ->
    FStar_Extraction_JavaScript_Ast.expression_t ->
      FStar_Extraction_JavaScript_Ast.statement_t ->
        (FStar_Extraction_JavaScript_Ast.statement_t* env_t) ->
          env_t -> (FStar_Extraction_JavaScript_Ast.statement_t* env_t)
  =
  fun uu____2927  ->
    fun match_e  ->
      fun s1  ->
        fun s2  ->
          fun env  ->
            match uu____2927 with
            | (p,guard) ->
                let uu____2945 = s2 in
                (match uu____2945 with
                 | (s21,env2) ->
                     let uu____2952 =
                       match guard with
                       | None  -> translate_pat p match_e s1 s21 env
                       | Some v_guard ->
                           let uu____2958 = translate_expr_pure v_guard env in
                           (match uu____2958 with
                            | (r,env1) ->
                                let cond_stmt =
                                  FStar_Extraction_JavaScript_Ast.JSS_If
                                    (r, s1, (Some s21)) in
                                translate_pat p match_e cond_stmt s21 env1) in
                     (match uu____2952 with
                      | (stmt,env1) ->
                          let env3 =
                            let uu___159_2972 = env1 in
                            {
                              names = (uu___159_2972.names);
                              module_name = (uu___159_2972.module_name);
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
          env_t -> (FStar_Extraction_JavaScript_Ast.statement_t* env_t)
  =
  fun p  ->
    fun match_e  ->
      fun s1  ->
        fun s2  ->
          fun env  ->
            match p with
            | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____2983) ->
                ((FStar_Extraction_JavaScript_Ast.JSS_Seq
                    [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                       (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                            (name, None)), (Some match_e)),
                         FStar_Extraction_JavaScript_Ast.JSV_Const);
                    s1]), env)
            | FStar_Extraction_ML_Syntax.MLP_Wild  -> (s1, env)
            | FStar_Extraction_ML_Syntax.MLP_Const c ->
                let uu____2990 =
                  let uu____2991 =
                    let uu____2996 =
                      let uu____2997 =
                        let uu____3001 = translate_constant c in
                        (FStar_Extraction_JavaScript_Ast.JSB_Equal, match_e,
                          uu____3001) in
                      FStar_Extraction_JavaScript_Ast.JSE_Binary uu____2997 in
                    (uu____2996, s1, (Some s2)) in
                  FStar_Extraction_JavaScript_Ast.JSS_If uu____2991 in
                (uu____2990, env)
            | FStar_Extraction_ML_Syntax.MLP_CTor ((path,c),lp) ->
                let uu____3013 = addImportModule env (path, c) in
                (match uu____3013 with
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
                                    ("slice(1)", None)))
                         | uu____3049 ->
                             let uu____3050 =
                               let uu____3053 =
                                 let uu____3054 =
                                   let uu____3058 =
                                     let uu____3059 =
                                       FStar_Util.string_of_int i in
                                     Prims.strcat "_" uu____3059 in
                                   (uu____3058, None) in
                                 FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                   uu____3054 in
                               (match_e1, uu____3053) in
                             FStar_Extraction_JavaScript_Ast.JSE_Member
                               uu____3050 in
                       match lp1 with
                       | [] -> (s11, env2)
                       | x::[] ->
                           let uu____3064 =
                             translate_pat x new_fv_x s11 s21 env2 in
                           (match uu____3064 with | (r,e1) -> (r, e1))
                       | hd1::tl1 ->
                           let uu____3074 =
                             translate_p_ctor tl1 match_e1 s11 s21
                               (i + (Prims.parse_int "1")) env2 in
                           (match uu____3074 with
                            | (r,e1) -> translate_pat hd1 new_fv_x r s21 e1) in
                     let if_stmt if_cond =
                       let uu____3087 =
                         translate_p_ctor lp match_e s1 s2
                           (Prims.parse_int "0") env1 in
                       match uu____3087 with
                       | (r,e1) ->
                           ((FStar_Extraction_JavaScript_Ast.JSS_If
                               (if_cond, r, (Some s2))), e1) in
                     (match c with
                      | x when x = "Cons" ->
                          if_stmt
                            (FStar_Extraction_JavaScript_Ast.JSE_Binary
                               (FStar_Extraction_JavaScript_Ast.JSB_GreaterThan,
                                 (FStar_Extraction_JavaScript_Ast.JSE_Member
                                    (match_e,
                                      (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                         ("length", None)))),
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
                                         ("length", None)))),
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
                      | uu____3103 ->
                          let isSimple =
                            match match_e with
                            | FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                uu____3105 -> true
                            | uu____3109 -> false in
                          if isSimple
                          then
                            if_stmt
                              (FStar_Extraction_JavaScript_Ast.JSE_Binary
                                 (FStar_Extraction_JavaScript_Ast.JSB_StrictEqual,
                                   (FStar_Extraction_JavaScript_Ast.JSE_Member
                                      (match_e,
                                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                           ("_tag",
                                             (Some
                                                FStar_Extraction_JavaScript_Ast.JST_String))))),
                                   (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                      ((FStar_Extraction_JavaScript_Ast.JSV_String
                                          c), ""))))
                          else
                            (let new_name =
                               let uu____3115 =
                                 FStar_Extraction_ML_Syntax.gensym () in
                               fst uu____3115 in
                             let if_cond =
                               FStar_Extraction_JavaScript_Ast.JSE_Binary
                                 (FStar_Extraction_JavaScript_Ast.JSB_StrictEqual,
                                   (FStar_Extraction_JavaScript_Ast.JSE_Member
                                      ((FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                          (new_name, None)),
                                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                                           ("_tag",
                                             (Some
                                                FStar_Extraction_JavaScript_Ast.JST_String))))),
                                   (FStar_Extraction_JavaScript_Ast.JSE_Literal
                                      ((FStar_Extraction_JavaScript_Ast.JSV_String
                                          c), ""))) in
                             let uu____3121 =
                               translate_p_ctor lp
                                 (FStar_Extraction_JavaScript_Ast.JSE_Identifier
                                    (new_name, None)) s1 s2
                                 (Prims.parse_int "0") env1 in
                             match uu____3121 with
                             | (r,env11) ->
                                 ((FStar_Extraction_JavaScript_Ast.JSS_Seq
                                     [FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration
                                        (((FStar_Extraction_JavaScript_Ast.JGP_Identifier
                                             (new_name, None)),
                                           (Some match_e)),
                                          FStar_Extraction_JavaScript_Ast.JSV_Const);
                                     FStar_Extraction_JavaScript_Ast.JSS_If
                                       (if_cond, r, (Some s2))]), env11))))
            | FStar_Extraction_ML_Syntax.MLP_Branch lp ->
                let rec translate_p_branch lp1 match_e1 s11 s21 env1 =
                  match lp1 with
                  | [] -> failwith "Empty list in translate_p_branch"
                  | x::[] -> translate_pat x match_e1 s11 s21 env1
                  | hd1::tl1 ->
                      let uu____3165 =
                        translate_p_branch tl1 match_e1 s11 s21 env1 in
                      (match uu____3165 with
                       | (r,e1) -> translate_pat hd1 match_e1 s11 r e1) in
                translate_p_branch lp match_e s1 s2 env
            | FStar_Extraction_ML_Syntax.MLP_Record (path,lp) ->
                let rec translate_p_record lp1 match_e1 s11 s21 env1 =
                  let new_fv_x n1 =
                    FStar_Extraction_JavaScript_Ast.JSE_Member
                      (match_e1,
                        (FStar_Extraction_JavaScript_Ast.JSPM_Identifier
                           ((Prims.strcat "_" n1), None))) in
                  match lp1 with
                  | [] -> failwith "Empty list in translate_p_record"
                  | x::[] ->
                      translate_pat (snd x) (new_fv_x (fst x)) s11 s21 env1
                  | hd1::tl1 ->
                      let uu____3233 =
                        translate_p_record tl1 match_e1 s11 s21 env1 in
                      (match uu____3233 with
                       | (r,e1) ->
                           translate_pat (snd hd1) (new_fv_x (fst hd1)) r s21
                             e1) in
                translate_p_record lp match_e s1 s2 env
            | FStar_Extraction_ML_Syntax.MLP_Tuple lp ->
                let rec translate_p_tuple lp1 d match_e1 s11 s21 env1 =
                  let new_fv_x =
                    let uu____3266 =
                      let uu____3269 =
                        let uu____3270 =
                          let uu____3271 =
                            let uu____3274 = FStar_Util.string_of_int d in
                            ((FStar_Extraction_JavaScript_Ast.JSV_Number
                                (float_of_int d)), uu____3274) in
                          FStar_Extraction_JavaScript_Ast.JSE_Literal
                            uu____3271 in
                        FStar_Extraction_JavaScript_Ast.JSPM_Expression
                          uu____3270 in
                      (match_e1, uu____3269) in
                    FStar_Extraction_JavaScript_Ast.JSE_Member uu____3266 in
                  match lp1 with
                  | [] -> failwith "Empty list in translate_p_tuple"
                  | x::[] -> translate_pat x new_fv_x s11 s21 env1
                  | hd1::tl1 ->
                      let uu____3283 =
                        translate_p_tuple tl1 (d + (Prims.parse_int "1"))
                          match_e1 s11 s21 env1 in
                      (match uu____3283 with
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
    | FStar_Extraction_ML_Syntax.MLC_Int (s,uu____3293) ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_Number
              (float_of_int (Prims.parse_int "0"))), s)
    | FStar_Extraction_ML_Syntax.MLC_Float f ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_Number f),
            (FStar_Util.string_of_float f))
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3301 ->
        failwith "todo: translate_const [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        FStar_Extraction_JavaScript_Ast.JSE_Literal
          ((FStar_Extraction_JavaScript_Ast.JSV_String s), s)
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3303 ->
        failwith "todo: translate_const [MLC_Bytes]"
and map_type:
  env_t ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlsymbol Prims.list option ->
        (FStar_Extraction_JavaScript_Ast.typ Prims.list* env_t)
  =
  fun env  ->
    fun args  ->
      fun lp_generic  ->
        FStar_List.fold_left
          (fun uu____3314  ->
             fun x  ->
               match uu____3314 with
               | (r,e) ->
                   let uu____3326 = translate_type x lp_generic e in
                   (match uu____3326 with
                    | (r1,e1) -> ((FStar_List.append r [r1]), e1))) ([], env)
          args
and translate_type:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlsymbol Prims.list option ->
      env_t -> (FStar_Extraction_JavaScript_Ast.typ* env_t)
  =
  fun t  ->
    fun lp_generic  ->
      fun env  ->
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Tuple [] ->
            (FStar_Extraction_JavaScript_Ast.JST_Any, env)
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            (FStar_Extraction_JavaScript_Ast.JST_Any, env)
        | FStar_Extraction_ML_Syntax.MLTY_Var (id,uu____3346) ->
            ((FStar_Extraction_JavaScript_Ast.JST_Generic (id, None)), env)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple lt1 ->
            let uu____3352 = map_type env lt1 lp_generic in
            (match uu____3352 with
             | (r,env1) ->
                 ((FStar_Extraction_JavaScript_Ast.JST_Tuple r), env1))
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,e_tag,t2) ->
            let uu____3365 = translate_type t1 None env in
            (match uu____3365 with
             | (t11,env1) ->
                 let uu____3373 =
                   if e_tag = FStar_Extraction_ML_Syntax.E_GHOST
                   then (FStar_Extraction_JavaScript_Ast.JST_Null, env1)
                   else translate_type t2 None env1 in
                 (match uu____3373 with
                  | (t21,env2) ->
                      ((FStar_Extraction_JavaScript_Ast.JST_Function
                          ([(("_1", None), t11)], t21, lp_generic)), env2)))
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,p) when
            let uu____3410 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____3410 = "FStar.ST.ref" ->
            let uu____3411 =
              let uu____3414 = FStar_List.nth args (Prims.parse_int "0") in
              translate_type uu____3414 lp_generic env in
            (match uu____3411 with
             | (r,env1) ->
                 ((FStar_Extraction_JavaScript_Ast.JST_Array r), env1))
        | FStar_Extraction_ML_Syntax.MLTY_Named (uu____3419,p) when
            let uu____3423 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____3423 = "FStar.Buffer.buffer" ->
            let uu____3424 = addImportModule env p in
            (match uu____3424 with
             | (name,env1) ->
                 ((FStar_Extraction_JavaScript_Ast.JST_Generic (name, None)),
                   env1))
        | FStar_Extraction_ML_Syntax.MLTY_Named (uu____3434,p) when
            let uu____3438 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____3438 = "FStar.Ghost.erased" ->
            (FStar_Extraction_JavaScript_Ast.JST_Any, env)
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,(path,name)) ->
            if is_standart_type name
            then
              let uu____3451 = FStar_Util.must (mk_standart_type name) in
              (uu____3451, env)
            else
              if
                FStar_Option.isSome
                  (FStar_Extraction_ML_Util.is_xtuple_ty (path, name))
              then
                (let uu____3456 = map_type env args lp_generic in
                 match uu____3456 with
                 | (r,env1) ->
                     ((FStar_Extraction_JavaScript_Ast.JST_Tuple r), env1))
              else
                (let uu____3467 =
                   match args with
                   | [] -> (None, env)
                   | uu____3479 ->
                       let uu____3481 = map_type env args lp_generic in
                       (match uu____3481 with | (r,env1) -> ((Some r), env1)) in
                 match uu____3467 with
                 | (args_t,env1) ->
                     let uu____3504 = addImportModule env1 (path, name) in
                     (match uu____3504 with
                      | (name1,env2) ->
                          ((FStar_Extraction_JavaScript_Ast.JST_Generic
                              (name1, args_t)), env2)))