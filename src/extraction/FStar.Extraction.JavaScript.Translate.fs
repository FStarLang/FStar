#light "off"

module FStar.Extraction.JavaScript.Translate

open FStar.All
open FStar
open FStar.Util
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format
open FStar.Const
open FStar.BaseTypes
open FStar.Extraction.JavaScript.Ast

type file = string * t

type env_t = {
  names: list<name>;
  module_name: string;
  import_module_names: list<string>;
}

and name = {
  pretty: string;
  mut: bool;
}

let empty module_name = {
  names = [];
  module_name = module_name;
  import_module_names = [];
}

let mk_op_bin = function
  | "op_Addition" ->
      Some JSB_Plus
  | "op_Subtraction" ->
      Some JSB_Minus
  | "op_Multiply" ->
      Some JSB_Mult
  | "op_Division" ->
      Some JSB_Div
  | "op_Equality" ->
      Some JSB_Equal
  | "op_disEquality" ->
      Some JSB_NotEqual
  | "op_LessThanOrEqual" ->
      Some JSB_LessThanEqual
  | "op_GreaterThanOrEqual" ->
      Some JSB_GreaterThanEqual
  | "op_LessThan" ->
      Some JSB_LessThan
  | "op_GreaterThan" ->
      Some JSB_GreaterThan
  | "op_Modulus" ->
      Some JSB_Mod
  | _ ->
      None

let is_op_bin op =
  mk_op_bin op <> None

let mk_op_un = function
  | "op_Negation" ->
      Some JSU_Not
  | "op_Minus" ->
      Some JSU_Minus
  | _ ->
      None

let is_op_un op =
  mk_op_un op <> None

let mk_op_bool = function 
  | "op_AmpAmp" ->
      Some JSL_And
  | "op_BarBar" ->
      Some JSL_Or  
  | _ ->
      None
 
let is_op_bool op =
  mk_op_bool op <> None

let mk_standart_type = function 
  | "unit" ->
      Some JST_Null
  | "bool" ->
      Some JST_Boolean
  | "int" | "nat" ->
      Some JST_Number
  | "string" ->
      Some JST_String
  | _ ->
      None

let is_standart_type t =
  mk_standart_type t <> None

let float_of_int i = float_of_int32 (int32_of_int i)

let isMutable typ =
  match typ with
  | None -> false
  | Some (_, ty) ->
      (match ty with
      | MLTY_Named (_, p) when string_of_mlpath p = "FStar.ST.ref" -> true
      | _ -> false)
 
let extendEnv env (path, n) typ =
  let path = String.concat "_" path in
  if (path = env.module_name || path = "")
  then {env with names = {pretty = n; mut = isMutable typ} :: env.names}
  else
      let n = path ^ "." ^ n in
      if not (List.existsb (fun x -> x = path) env.import_module_names)
      then {env with names = {pretty = n; mut = isMutable typ} :: env.names;
                     import_module_names = path :: env.import_module_names}
      else {env with names = {pretty = n; mut = isMutable typ} :: env.names}

let addImportModule env (path, name) =
  let path = String.concat "_" path in
  if (path = env.module_name || path = "")
  then (name, env)
  else
      let name = path ^ "." ^ name in
      if not (List.existsb (fun x -> x = path) env.import_module_names)
      then (name, {env with import_module_names = path :: env.import_module_names})
      else (name, env)

let findEnv env name =
  List.index (fun x -> x.pretty = name) env.names

let isInEnv env name =
  List.existsb (fun x -> x.pretty = name) env.names

let rec is_pure_expr e var =
  match e.expr with
  | MLE_Const _ | MLE_Name _ -> true
  | MLE_Var (n, _) -> n <> fst var
  | MLE_Proj (expr, _) -> is_pure_expr expr var
  | MLE_CTor (p, le) ->
      not (List.contains false (List.map (fun x -> is_pure_expr x var) le))
  | MLE_Tuple le ->
      not (List.contains false (List.map (fun x -> is_pure_expr x var) le))
  | MLE_Record (_, lne) ->
      not (List.contains false (List.map (fun (n, e) -> is_pure_expr e var) lne))
  | MLE_App (_, args) ->
      not (List.contains false (List.map (fun x -> is_pure_expr x var) args))
  | _ -> false
          
let rec translate (MLLib modules): list<file> =
  List.filter_map (fun m ->
    let m_name =
      let (prefix, final), _, _ = m in
      String.concat "_" (prefix @ [final])
    in
    try
      print1 "Attempting to translate module %s\n" m_name;
      Some (translate_module (empty m_name) m)
    with
    | e ->
        print2 "Unable to translate module: %s because:\n  %s\n" m_name (print_exn e);
        None
  ) modules

and translate_module env (module_name, modul, _): file =
  let program = match modul with
    | Some (_signature, decls) ->
        let update_env () = {env with names = []} in
        let res = List.filter_map (fun d -> translate_decl (update_env ()) d) decls in
        let td = List.map (fun (x, e) -> x) res in
        let lmodules = List.collect (fun (x, e) -> e.import_module_names) res in
        let lmodules = List.fold_left (fun acc m -> 
            if (List.existsb (fun x -> x = m) acc) then acc else m :: acc) [] lmodules in
        let create_module_imports = List.map (fun m ->
            JSS_ImportDeclaration (m, None)) lmodules |> JSS_Block |> JS_Statement
        in [create_module_imports] @ td
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
    env.module_name, program

and translate_decl env d: option<(source_t * env_t)> =
  match d with
  | MLM_Let (_, c_flag,  lfunc) ->
      let for1 { mllb_name = name, _; mllb_tysc = tys; mllb_def = expr; print_typ = pt; mllb_add_unit = unit_b} env =
        let (t, env) =
            if (not pt) || unit_b then (None, env)
            else match tys with
                 | None -> (None, env)
                 | Some (lp, ty) ->
                     let lp_generic = match lp with | [] -> None | _ -> Some (List.map (fun (id, _) -> id) lp) in
                     let (t, env) = translate_type ty lp_generic env in
                     (Some t, env) in
        let is_private = List.contains Private c_flag in
        let (c, env) =
            if is_pure_expr expr (name, t)
            then
                let var_decl_q = if isMutable tys then JSV_Let else JSV_Const in
                let env = extendEnv env ([], name) tys in
                let (r, env) = translate_expr_pure expr env in
                ([JSS_VariableDeclaration ((JGP_Identifier (name, t), Some r), var_decl_q)], env)
            else translate_expr expr (name, t) [] env false in
        if is_private then (c, env) else ([JSS_ExportDefaultDeclaration (JSE_Declaration (JSS_Block c), ExportValue)], env)
     in
        let (r, env) =
            List.fold_left (fun (r, e) x ->
                let update_env () = {e with names = []} in
                let (r1, e1) = for1 x (update_env ()) in (r @ [JSS_Seq r1], e1)) ([], env) lfunc in
        Some (JS_Statement (JSS_Block r), env)

  | MLM_Loc _ -> None (* only for OCaml backend *)

  | MLM_Ty [(_, name, _, tparams, _, body)] ->
      let tparams =
        match tparams with
        | [] -> None
        | _ -> Some (List.map (fun (id, _) -> id) tparams) in
      let forbody body =
        let get_export stmt =
            JSS_ExportDefaultDeclaration (JSE_Declaration stmt, ExportType) in
        match body with
        | MLTD_Abbrev t ->
            let (t, env) = translate_type t tparams env in
            (get_export (JSS_TypeAlias ((name, None), tparams, t)), env)
        | MLTD_Record fields ->
            let tag = [(JSO_Identifier ("_tag", None), JST_StringLiteral ("Record", ""))] in
            let (fields_t, env) =
                List.fold_left (fun (r, e) (n, t) ->
                    let (r1, e1) = translate_type t tparams e in
                    (r @ [JSO_Identifier ("_" ^ n, None), r1], e1)) ([], env) fields in
            (get_export (JSS_TypeAlias ((name, None), tparams, JST_Object (tag @ fields_t))), env)
        | MLTD_DType lfields ->
            let tag n = [(JSO_Identifier ("_tag", None), JST_StringLiteral (n, ""))] in
            let fields_t fields env =
                List.fold_left (fun (r, e) (n, t) ->
                    let (r1, e1) = translate_type t tparams e in
                    (r @ [JSO_Identifier ("_" ^ n, None), r1], e1)) ([], env) fields in
            let (lfields_t, env) = 
                List.fold_left (fun (r, e) (n, l) ->
                    let (r1, e1) = fields_t l e in
                    (r @ [get_export (JSS_TypeAlias ((n, None), tparams, JST_Object ((tag n) @ r1)))], e1)) ([], env) lfields in
            let tparams_gen =
                match tparams with
                | Some t -> List.map (fun x -> JST_Generic (x, None)) t |> Some
                | None -> None in
            let lnames = List.map (fun (n, _) -> JST_Generic (n, tparams_gen)) lfields in
            let union_t = get_export (JSS_TypeAlias ((name, None), tparams, JST_Union lnames)) in
            (JSS_Block (lfields_t @ [union_t]), env) in
      let (body_t, env) =
        match body with
           | None -> failwith "todo: translate_decl [MLM_Ty] with empty body"
           | Some v -> forbody v in
        Some (JS_Statement body_t, env)

  | MLM_Ty _ ->
      failwith "todo: translate_decl [MLM_Ty]"

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn (x, []) -> (* exception Name in JS would be nothing? *)
      Some (JS_Statement (JSS_Block []), env)

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

and translate_expr e var lstmt env isDecl: (list<statement_t> * env_t) =
  let get_res expr new_fv env =
    let is_inEnv = isInEnv env (fst var) in
    let (expr, env) = (* todo: JSV_Let and JSV_Const *)
      let res e =
        //let env = extendEnv env ([], fst var) None in
        if is_inEnv then ([JSS_Block e], env) else (e, env) in
      match expr with
       | JSE_Assignment _ ->
            if isDecl (* in JS assign_op returns the expr type *)
            then
                if (fst var = "_") then ([JSS_Expression expr] @ lstmt, env) 
                else ([JSS_Expression expr; JSS_Expression (JSE_Assignment (JGP_Identifier var, JSE_Literal (JSV_Null, "")))] @ lstmt, env)
            else res ([JSS_Expression expr; JSS_VariableDeclaration ((JGP_Identifier var, Some (JSE_Literal (JSV_Null, ""))), JSV_Let)] @ lstmt)
       | _ ->
            if isDecl then ([JSS_Expression (JSE_Assignment (JGP_Identifier var, expr))] @ lstmt, env)
            else res ([JSS_VariableDeclaration ((JGP_Identifier var, Some expr), JSV_Let)] @ lstmt) in
    ((match new_fv with | [] -> expr | _ -> if is_inEnv then new_fv @ expr else new_fv @ [JSS_Block expr]), env) in
  
  match e.expr with
  | x when is_pure_expr e var ->
      let (expr, env) = translate_expr_pure e env in
      get_res expr [] env

  | MLE_Let ((_, _,  [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_add_unit = add_unit;
      mllb_def = body;
      print_typ = pt
      }]), continuation) ->
     let isEqName = isInEnv env name in
     let env = extendEnv env ([], name) tys in
     if is_pure_expr body (name, tys)
     then
        let var_decl_q = if isMutable tys then JSV_Let else JSV_Const in
        let (r, env) = translate_expr_pure body env in
        let (c, env1) = translate_expr continuation var lstmt env isDecl in
        let c = [JSS_VariableDeclaration ((JGP_Identifier (name, None), Some r), var_decl_q)] @ c in
        let env = {env with import_module_names = env.import_module_names @ env1.import_module_names} in
        if isEqName then ([JSS_Block c], env) else (c, env)
     else
        let (c, env1) = translate_expr continuation var lstmt env isDecl in
        let (r, env) = translate_expr body (name, None) c env false in
        let env = {env with import_module_names = env.import_module_names @ env1.import_module_names} in
        (r, env)

  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"

  | MLE_Fun (args, body) ->
      let (args, env) =
        List.fold_left (fun (r, e) ((n,_), t) ->
            let (r1, e1) = translate_type t None e in
            (r @ [JGP_Identifier (n, Some r1)], e1)) ([], env) args in
      let is_failwith =
       (match body.expr with
        | MLE_App (expr, _) ->
           (match expr.expr with
            | MLE_Name p when string_of_mlpath p = "failwith" -> true
            | _ -> false)
        | _ -> false) in
      let (body_t, env1) =
        if is_failwith
        then (JS_BodyBlock [JSS_Throw (JSE_Literal (JSV_String "Not yet implemented!", ""))], env)
        else
            if is_pure_expr body var
            then
                let (r, env1) = translate_expr_pure body env in  
                (JS_BodyExpression r, env1)
            else
                let (t1, env1) = translate_expr body ("_res", None) [JSS_Return (Some (JSE_Identifier("_res", None)))] env true in 
                (JS_BodyBlock ([JSS_VariableDeclaration ((JGP_Identifier ("_res", None), None), JSV_Let)] @ t1), env1) in
      let (ret_t, lp_generic) =
        (match (snd var) with
         | None -> (None, None)
         | Some v -> match v with | JST_Function (_, t2, lp) -> (Some t2, lp) | _ -> (None, None)) in
      let expr = JSE_ArrowFunction (None, args, body_t, ret_t, lp_generic) in
      let (expr, env) =
        if isDecl then ([JSS_Expression (JSE_Assignment (JGP_Identifier (fst var, None), expr))], env)
        else
            //let env = extendEnv env ([], fst var) None in 
            ([JSS_VariableDeclaration ((JGP_Identifier (fst var, None), Some expr), JSV_Const)], env) in
      let env = {env with import_module_names = env.import_module_names @ env1.import_module_names} in
      (expr @ lstmt, env)

  | MLE_If (cond, s1, s2) ->
      let (r1, env1) = translate_expr s1 var [] env true in
      let s1 = JSS_Block r1 in
      let (s2, env2) =
        (match s2 with
        | Some v ->
            let (r2, env2) = translate_expr v var [] env true in
            (Some (JSS_Block r2), env2)
        | None -> (None, env)) in
      let (c, env) =
        if is_pure_expr cond var
        then
            let (c1, envc) = translate_expr_pure cond env in
            ([JSS_If (c1, s1, s2)], envc)
        else  (* maybe generate fv instead of _cond *)
            let (c1, envc) = translate_expr cond ("_cond", None) [JSS_If (JSE_Identifier ("_cond", None), s1, s2)] env true in 
            ([JSS_VariableDeclaration ((JGP_Identifier ("_cond", Some JST_Boolean), None), JSV_Let)] @ c1, envc) in
      let (c, env) =
        if isDecl then (c, env) 
        else 
            //let env = extendEnv env ([], fst var) None in
            ([JSS_VariableDeclaration ((JGP_Identifier var, None), JSV_Let)] @ c, env) in
      let env = {env with import_module_names = env.import_module_names @
                          env1.import_module_names @ env2.import_module_names} in
      (c @ lstmt, env)

  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"

  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

  | MLE_Coerce (in_e, t, _) ->
      let lp_generic = 
        (match (snd var) with
         | None -> None
         | Some v -> match v with | JST_Function (_, _, lp) -> lp | _ -> None) in
      let (t, env) = translate_type t lp_generic env in
      let var = (fst var, Some t) in
      translate_expr in_e var lstmt env isDecl

  | MLE_Match (e_in, lb) ->
      let match_e = (fst (gensym()), None) in
      let (c, env) =
        if is_pure_expr e_in var
        then
            let (r1, env) = translate_expr_pure e_in env in
            let (r2, env2) = translate_match lb (JSE_Identifier match_e) var env in
            let env = {env with import_module_names = env.import_module_names @ env2.import_module_names} in
            ([JSS_VariableDeclaration ((JGP_Identifier match_e, Some r1), JSV_Const); r2], env)
        else
            let (r2, env2) = translate_match lb (JSE_Identifier match_e) var env in
            let (r1, env) = translate_expr e_in match_e [r2] env true in
            let env = {env with import_module_names = env.import_module_names @ env2.import_module_names} in
            ([JSS_VariableDeclaration ((JGP_Identifier match_e, None), JSV_Let)] @ r1, env) in
      let c = [JSS_Block c] in  (* match can be inner *)
      let (c, env) =
        if isDecl then (c, env)
        else
            //let env = extendEnv env ([], fst var) None in 
            ([JSS_VariableDeclaration ((JGP_Identifier var, None), JSV_Let)] @ c, env) in
      (c @ lstmt, env)

  | MLE_Seq ls ->
      let rec translate_seq l env acc =
        match l with
        | [] -> failwith "Empty list in [MLE_Seq]"
        | [x] -> 
            let (r, env) = translate_expr x var [] env isDecl
            in (acc @ r, env)
        | hd :: tl ->
            let (r, e1) = translate_expr hd ("_", None) [] env true in
            translate_seq tl e1 (acc @ r) in
      let (r, env) = translate_seq ls env [] in
      (r @ lstmt, env)

  | MLE_App (e, args) ->
      let (args, new_fv, env) = create_pure_args args var env in
      let (expr, env) = translate_arg_app e args var env in
      get_res expr new_fv env
     
  | MLE_CTor ((path, c), lexpr) ->
      let (lexpr, new_fv, env) = create_pure_args lexpr var env in
      let expr =
        (match c with
        | x when x = "Cons" || x = "Nil" ->
            (match lexpr with
            | [] -> JSE_Array None
            | hd :: tl -> JSE_Call (JSE_Member (JSE_Array (Some [hd]), JSPM_Identifier ("concat", None)), tl))
        | x when x = "Some" || x = "None" ->
            (match lexpr with
            | [] -> JSE_Literal (JSV_Null, "")
            | hd :: tl -> List.nth lexpr 0)
        | _ -> JSE_Object ([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String c, ""), JSO_Init)] @
                           List.mapi (fun i x -> JSPO_Property (JSO_Identifier ("_" ^ string_of_int i, None), x, JSO_Init)) lexpr)) in
      get_res expr new_fv env

  | MLE_Record (path, fields) ->
      let (create_fields, new_fv, env) =
        List.fold_left (fun (lexpr, lnew_fv, e) (id, x) ->
            let (expr, fv, e1) = create_pure_args [x] var e in
            (lexpr @ [JSPO_Property (JSO_Identifier ("_" ^ id, None), List.nth expr 0, JSO_Init)], fv @ lnew_fv, e1)) ([], [], env) fields in
      let expr = JSE_Object ([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String "Record", ""), JSO_Init)] @
                             create_fields) in
      get_res expr new_fv env

  | MLE_Tuple lexp ->
      let (create_fields, new_fv, env) =
        List.fold_left (fun (lexpr, lnew_fv, e) x ->
            let (expr, fv, e1) = create_pure_args [x] var e in
            (lexpr @ expr, fv @ lnew_fv, e1)) ([], [], env) lexp in
      let expr = JSE_Array (Some create_fields) in
      get_res expr new_fv env

  | _ -> failwith "todo: translation ml-expr"

and create_pure_args args var env =
    List.fold_left (fun (lexpr, lnew_fv, e) x ->
        match x.expr with
        | MLE_CTor ((path, c), _) when c = "Nil" || c = "None" ->
            let (r1, e1) = translate_expr_pure x e in
            let (t1, e1) = translate_type x.mlty None e1 in
            (lexpr @ [JSE_TypeCast (r1, t1)], lnew_fv, e1)
        | _ ->
            if is_pure_expr x var
            then
                let (r1, e1) = translate_expr_pure x e in 
                (lexpr @ [r1], lnew_fv, e1)
            else
                let fv_x = fst (gensym()) in
                let (c, e1) =
                    (match x.expr with
                     | MLE_Var _ ->
                        let (r1, e1) = translate_expr_pure x e in  
                        ([JSS_VariableDeclaration ((JGP_Identifier (fv_x, None), Some r1), JSV_Const)], e1)
                     | _ -> translate_expr x (fv_x, None) [] env false) in
                (lexpr @ [JSE_Identifier (fv_x, None)], c @ lnew_fv, e1)) ([], [], env) args

and translate_arg_app e args var env: (expression_t * env_t) =
  match e.expr with
  | MLE_Name(["Prims"], op) when is_op_bin op ->
      (JSE_Binary (must (mk_op_bin op), List.nth args 0, List.nth args 1), env)
  | MLE_Name(["Prims"], op) when is_op_bool op ->
      (JSE_Logical (must (mk_op_bool op), List.nth args 0, List.nth args 1), env)
  | MLE_Name(["Prims"], op) when is_op_un op ->
      (JSE_Unary (must (mk_op_un op), List.nth args 0), env)
  | MLE_Name p when string_of_mlpath p = "FStar.Buffer.op_Array_Access"
                 || string_of_mlpath p = "FStar.Buffer.index" ->
      (JSE_Member (List.nth args 0, JSPM_Expression (List.nth args 1)), env)
  | MLE_Name p when string_of_mlpath p = "FStar.Buffer.op_Array_Assignment"
                 || string_of_mlpath p = "FStar.Buffer.upd" ->
      (JSE_Assignment (JGP_Expression (JSE_Member (List.nth args 0, JSPM_Expression (List.nth args 1))), List.nth args 2), env)
  | MLE_Name p when string_of_mlpath p = "FStar.ST.op_Bang"
                 || string_of_mlpath p = "FStar.ST.read" ->
      (JSE_Member (List.nth args 0, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int 0), "0"))), env)
  | MLE_Name p when string_of_mlpath p = "FStar.ST.op_Colon_Equals"
                 || string_of_mlpath p = "FStar.ST.write" ->
      let expr = JSE_Member (List.nth args 0, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int 0), "0"))) in
      (JSE_Assignment (JGP_Expression expr, List.nth args 1), env)
  | MLE_Name p when string_of_mlpath p = "FStar.ST.alloc" ->
      (JSE_Array (Some [List.nth args 0]), env)
  | MLE_Name (path, function_name) ->
      let (name, env) = addImportModule env (path, function_name) in
      (JSE_Call (JSE_Identifier (name, None), args), env)
  | MLE_Var (name, _) ->
      (JSE_Call (JSE_Identifier (name, None), args), env)
  | _ ->
      if is_pure_expr e var
      then
        let (r, env) = translate_expr_pure e env in 
        (JSE_Call (r, args), env)
      else failwith "todo: translation [MLE_App]"

and map_expr_pure exprs env =
    List.fold_left (fun (r, e) x ->
        let (r1, e1) = translate_expr_pure x e in
        (r @ [r1], e1)) ([], env) exprs
         
and translate_expr_pure e env: (expression_t * env_t) =
  match e.expr with
  | MLE_Const c -> (translate_constant c, env)
  | MLE_Var (name, _) -> (JSE_Identifier (name, None), env)
  | MLE_Name (path, name) ->
      let (name, env) = addImportModule env (path, name) in
      (JSE_Identifier (name, None), env)
  | MLE_Tuple lexp ->
      let (r, env) = map_expr_pure lexp env in
      (JSE_Array (Some r), env)
  | MLE_Record (path, fields) ->
      let (create_fields, env) =
        List.fold_left (fun (r, e) (id, x) ->
            let (r1, e1) = translate_expr_pure x e in
            (r @ [JSPO_Property (JSO_Identifier ("_" ^ id, None), r1, JSO_Init)], e1)) ([], env) fields in
      (JSE_Object([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String "Record", ""), JSO_Init)] @ create_fields), env)
  | MLE_CTor ((path, c), lexpr) ->
     let (name, env) = addImportModule env (path, c) in
     (match c with
      | x when x = "Cons" || x = "Nil" ->
           (match lexpr with
           | [] -> (JSE_Array None, env)
           | hd :: tl ->
                let (r1, e1) = translate_expr_pure hd env in
                let (r2, e2) = map_expr_pure tl e1 in
                (JSE_Call (JSE_Member (JSE_Array (Some [r1]), JSPM_Identifier ("concat", None)), r2), env))
      | x when x = "Some" || x = "None" ->
           (match lexpr with
           | [] -> (JSE_Literal (JSV_Null, ""), env)
           | hd :: tl ->
                let (r1, e1) = map_expr_pure lexpr env in ((List.nth r1 0), e1))
      | _ -> 
           (let (_, r, env) = List.fold_left (fun (i, r, e) x ->
               let (r1, e1) = translate_expr_pure x e in
               (i + 1), r @ [(JSPO_Property (JSO_Identifier ("_" ^ string_of_int i, None), r1, JSO_Init))], e1) (0, [], env) lexpr in
           (JSE_Object ([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String name, ""), JSO_Init)] @ r), env)))
  | MLE_Coerce (e, _, _) -> translate_expr_pure e env
  | MLE_App (e, args) ->
      let (args, env) = 
        List.fold_left (fun (r, e) x ->
            match x.expr with
            | MLE_CTor ((path, c), _) when c = "Nil" || c = "None" ->
                let (r1, e1) = translate_expr_pure x e in
                let (r2, e2) = translate_type x.mlty None e1 in 
                (r @ [JSE_TypeCast (r1, r2)], e2)
            | _ -> let (r1, e1) = translate_expr_pure x e in
                (r @ [r1], e1)) ([], env) args in
      translate_arg_app e args ("", None) env
  | MLE_Proj (expr, (path, name)) ->
      let (r, env) = translate_expr_pure expr env in
      let (name, env) = addImportModule env (path, name) in
      (JSE_Member (r, JSPM_Identifier ("_" ^ name, None)), env)
  | _ -> failwith "todo: translation ml-expr-pure"

and translate_match lb match_e var env: (statement_t * env_t) =
  match lb with
  | [] -> (JSS_Throw (JSE_Literal (JSV_String ("This value doesn't match!"), "")), env)
  | (p, guard, expr_r) :: tl ->
    let (expr_t, env1) =
        if is_pure_expr expr_r var
        then
            let (r1, e1) = translate_expr_pure expr_r env in
            (JSS_Expression (JSE_Assignment (JGP_Identifier var, r1)), e1)
        else 
            let (r1, e1) = translate_expr expr_r var [] env true in
            (JSS_Seq r1, e1) in
    translate_pat_guard (p, guard) match_e expr_t (translate_match tl match_e var env) env1

and translate_pat_guard (p, guard) match_e s1 s2 env: (statement_t * env_t) =
  let (s2, env2) = s2 in
  let (stmt, env) = 
    match guard with
    | None -> translate_pat p match_e s1 s2 env
    | Some v_guard -> (* maybe add translation for case when v_guard isn't pure *)
        let (r, env1) = translate_expr_pure v_guard env in
        let cond_stmt = JSS_If (r, s1, Some s2) in
        translate_pat p match_e cond_stmt s2 env1 in
  let env = {env with import_module_names = env.import_module_names @ env2.import_module_names} in
  (stmt, env)

and translate_pat p match_e s1 s2 env: (statement_t * env_t) =
  match p with
  | MLP_Var (name, _) ->
      (JSS_Seq [JSS_VariableDeclaration ((JGP_Identifier (name, None), Some match_e), JSV_Const); s1], env)
  | MLP_Wild -> (s1, env)
  | MLP_Const c ->
      (JSS_If (JSE_Binary (JSB_Equal, match_e, translate_constant c), s1, Some s2), env)
  | MLP_CTor ((path, c), lp) ->
      let (name, env) = addImportModule env (path, c) in
      let rec translate_p_ctor lp match_e s1 s2 i env =
        let new_fv_x =
            match c with
            | x when x = "Some" -> match_e
            | x when x = "Cons" && i = 0 -> JSE_Member (match_e, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int 0), "0")))
            | x when x = "Cons" && i = 1 -> JSE_Member (match_e, JSPM_Identifier ("slice(1)", None))
            | _ -> JSE_Member (match_e, JSPM_Identifier ("_" ^ string_of_int i, None)) in
       (match lp with
        | [] -> (s1, env)
        | [x] -> let (r, e1) = translate_pat x new_fv_x s1 s2 env in (r, e1)
        | hd::tl ->
            let (r, e1) = translate_p_ctor tl match_e s1 s2 (i + 1) env in 
            translate_pat hd new_fv_x r s2 e1)
      in
        begin
        let if_stmt if_cond =
            let (r, e1) = translate_p_ctor lp match_e s1 s2 0 env in
            (JSS_If (if_cond, r, Some s2), e1) in
        match c with
        | x when x = "Cons" ->
            if_stmt (JSE_Binary (JSB_GreaterThan, JSE_Member (match_e, JSPM_Identifier("length", None)), JSE_Literal (JSV_Number (float_of_int 0), "0")))
        | x when x = "Nil" ->
            if_stmt (JSE_Binary (JSB_Equal, JSE_Member (match_e, JSPM_Identifier ("length", None)), JSE_Literal (JSV_Number (float_of_int 0), "0")))
        | x when x = "Some" ->
            if_stmt (JSE_Binary (JSB_NotEqual, match_e, JSE_Literal (JSV_Null, "")))
        | x when x = "None" ->
            if_stmt (JSE_Binary (JSB_Equal, match_e, JSE_Literal (JSV_Null, "")))
        | _ ->
            let isSimple = match match_e with | JSE_Identifier _ -> true | _ -> false in
            if isSimple
            then if_stmt (JSE_Binary (JSB_StrictEqual, JSE_Member (match_e, JSPM_Identifier ("_tag", Some JST_String)), JSE_Literal (JSV_String c, "")))
            else
                let new_name = fst (gensym()) in
                let if_cond = JSE_Binary (JSB_StrictEqual, JSE_Member (JSE_Identifier (new_name, None), 
                                                           JSPM_Identifier ("_tag", Some JST_String)), JSE_Literal (JSV_String c, "")) in
                let (r, env1) = translate_p_ctor lp (JSE_Identifier (new_name, None)) s1 s2 0 env in
                (JSS_Seq [JSS_VariableDeclaration ((JGP_Identifier (new_name, None), Some match_e), JSV_Const); JSS_If (if_cond, r, Some s2)], env1)
        end
  | MLP_Branch lp ->
      let rec translate_p_branch lp match_e s1 s2 env =
        match lp with
        | [] -> failwith "Empty list in translate_p_branch"
        | [x] -> translate_pat x match_e s1 s2 env
        | hd :: tl ->
            let (r, e1) = translate_p_branch tl match_e s1 s2 env in 
            translate_pat hd match_e s1 r e1
      in translate_p_branch lp match_e s1 s2 env
  | MLP_Record (path, lp) ->
      let rec translate_p_record lp match_e s1 s2 env =
        let new_fv_x n = JSE_Member (match_e, JSPM_Identifier ("_" ^ n, None)) in
            (match lp with
            | [] -> failwith "Empty list in translate_p_record"
            | [x] -> translate_pat (snd x) (new_fv_x (fst x)) s1 s2 env
            | hd :: tl ->
                let (r, e1) = translate_p_record tl match_e s1 s2 env in 
                translate_pat (snd hd) (new_fv_x (fst hd)) r s2 e1)
      in translate_p_record lp match_e s1 s2 env
  | MLP_Tuple lp ->
      let rec translate_p_tuple lp d match_e s1 s2 env =
        let new_fv_x = JSE_Member (match_e, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int d), string_of_int d))) in
            (match lp with
            | [] -> failwith "Empty list in translate_p_tuple"
            | [x] -> translate_pat x new_fv_x s1 s2 env
            | hd :: tl ->
                let (r, e1) = translate_p_tuple tl (d + 1) match_e s1 s2 env in
                translate_pat hd new_fv_x r s2 e1)
      in translate_p_tuple lp 0 match_e s1 s2 env
      
and translate_constant c: expression_t =
  match c with
  | MLC_Unit ->
      JSE_Literal (JSV_Null, "")
  | MLC_Bool b ->
      JSE_Literal (JSV_Boolean b, "")
  | MLC_Int (s, _) ->
      //JSE_Literal(JSV_Number (float_of_int (int_of_string s)), s)
      JSE_Literal (JSV_Number (float_of_int 0), s) (* print only s *)
  | MLC_Float f ->
      JSE_Literal (JSV_Number f, string_of_float f)
  | MLC_Char _ ->
      failwith "todo: translate_const [MLC_Char]"
  | MLC_String s ->
      JSE_Literal (JSV_String s, s)
  | MLC_Bytes _ ->
      failwith "todo: translate_const [MLC_Bytes]"

and map_type env args lp_generic =
    List.fold_left (fun (r, e) x ->
        let (r1, e1) = translate_type x lp_generic e in
        (r @ [r1], e1)) ([], env) args

and translate_type t lp_generic env: (typ * env_t) =  
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      (JST_Any, env)
  | MLTY_Var (id, _) ->
      (JST_Generic (id, None), env)
  | MLTY_Tuple lt ->
      let (r, env) = map_type env lt lp_generic in
      (JST_Tuple r, env)
  | MLTY_Fun (t1, e_tag, t2) ->
      let (t1, env) = translate_type t1 None env in
      let (t2, env) = 
        if e_tag = E_GHOST then (JST_Null, env) 
        else translate_type t2 None env in
      (JST_Function ([(("_1", None), t1)], t2, lp_generic), env)
  | MLTY_Named (args, p) when string_of_mlpath p = "FStar.ST.ref" ->
      let (r, env) = translate_type (List.nth args 0) lp_generic env in
      (JST_Array r, env)
  | MLTY_Named (_, p) when string_of_mlpath p = "FStar.Buffer.buffer" ->
      let (name, env) = addImportModule env p in
      (JST_Generic (name, None), env) (* no polymorphism *)
  | MLTY_Named (_, p) when string_of_mlpath p = "FStar.Ghost.erased" ->
      (JST_Any, env)
  | MLTY_Named (args, (path, name)) ->
      if is_standart_type name
      then (must (mk_standart_type name), env)
      else (if Option.isSome (Util.is_xtuple_ty (path, name))
           then 
              let (r, env) = map_type env args lp_generic in
              (JST_Tuple r, env)
           else
              let (args_t, env) =
                 match args with
                 | [] -> (None, env)
                 | _ -> let (r, env) = map_type env args lp_generic in (Some r, env) in
              let (name, env) = addImportModule env (path, name) in
              (JST_Generic (name, args_t), env))