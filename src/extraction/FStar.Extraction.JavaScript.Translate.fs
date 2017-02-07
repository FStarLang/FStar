#light "off"

module FStar.Extraction.JavaScript.Translate

open FStar
open FStar.Util
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format
open FStar.Const
open FStar.BaseTypes
open FStar.Extraction.JavaScript.Ast

type file = string * t

type env = {
  names: list<name>;
  module_name: string;
  export_module_names: list<string>;
}

and name = {
  pretty: string;
  mut: bool;
}

let empty module_name = {
  names = [];
  module_name = module_name;
  export_module_names = [];
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
      if not (List.existsb (fun x -> x = path) env.export_module_names)
      then {env with names = {pretty = n; mut = isMutable typ} :: env.names;
                     export_module_names = path :: env.export_module_names}
      else {env with names = {pretty = n; mut = isMutable typ} :: env.names}

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
        let res = List.filter_map (translate_decl (update_env())) decls in
        let create_module_imports =
            List.map (fun m -> JSS_ImportDeclaration (m, None)) env.export_module_names
                |> JSS_Block |> JS_Statement
        in [create_module_imports] @ res
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
    env.module_name, program

and translate_decl env d: option<source_t> =
  match d with
  | MLM_Let (_, c_flag,  lfunc) ->
      let for1 { mllb_name = name, _; mllb_tysc = tys; mllb_def = expr; print_typ = pt; mllb_add_unit = unit_b} =
        let t =
            if (not pt) || unit_b then None
            else match tys with
                 | None -> None
                 | Some (lp, ty) ->
                     let lp_generic = match lp with | [] -> None | _ -> Some (List.map (fun (id, _) -> id) lp) in
                     translate_type ty lp_generic env |> Some in
        let is_private = List.contains Private c_flag in
        let env = extendEnv env ([], name) tys in
        let c =
            if is_pure_expr expr (name, None)
            then
                let var_decl_q = if isMutable tys then JSV_Let else JSV_Const in
                [JSS_VariableDeclaration ((JGP_Identifier (name, t), Some (translate_expr_pure expr env)), var_decl_q)]
            else translate_expr expr (name, t) [] env false in
        if is_private then c else [JSS_ExportDefaultDeclaration (JSE_Declaration (JSS_Block c), ExportValue)]
     in (* refresh env? *)
        List.collect for1 lfunc |> JSS_Block |> JS_Statement |> Some

  | MLM_Loc _ -> None (* only for OCaml backend *)

  | MLM_Ty [(_, name, _, tparams, body)] ->
      let tparams =
        match tparams with
        | [] -> None
        | _ -> Some (List.map (fun (id, _) -> id) tparams) in
      let forbody body =
        let get_export stmt =
            JSS_ExportDefaultDeclaration (JSE_Declaration stmt, ExportType) in
        match body with
        | MLTD_Abbrev t ->
            get_export (JSS_TypeAlias ((name, None), tparams, translate_type t tparams env))
        | MLTD_Record fields ->
            let tag = [(JSO_Identifier ("_tag", None), JST_StringLiteral ("Record", ""))] in
            let fields_t = List.map (fun (n, t) -> (JSO_Identifier ("_" ^ n, None), translate_type t tparams env)) fields in
            get_export (JSS_TypeAlias ((name, None), tparams, JST_Object (tag @ fields_t)))
        | MLTD_DType lfields ->
            let tag n = [(JSO_Identifier ("_tag", None), JST_StringLiteral (n, ""))] in
            let fields_t fields = List.mapi (fun i t -> (JSO_Identifier ("_" ^ string_of_int i, None), translate_type t tparams env)) fields in
            let lfields_t = List.map (fun (n, l) -> get_export (JSS_TypeAlias ((n, None), tparams, JST_Object ((tag n) @ fields_t l)))) lfields in
            let tparams_gen =
                match tparams with
                | Some t -> List.map (fun x -> JST_Generic (x, None)) t |> Some
                | None -> None in
            let lnames = List.map (fun (n, l) -> JST_Generic (n, tparams_gen)) lfields in
            let union_t = get_export (JSS_TypeAlias ((name, None), tparams, JST_Union lnames)) in
            JSS_Block (lfields_t @ [union_t]) in
      let body_t =
        match body with
           | None -> failwith "todo: translate_decl [MLM_Ty] with empty body"
           | Some v -> forbody v in
        body_t |> JS_Statement |> Some

  | MLM_Ty _ ->
      failwith "todo: translate_decl [MLM_Ty]"

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn (x, []) -> (* exception Name in JS would be nothing? *)
      JSS_Block([]) |> JS_Statement |> Some

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

and translate_expr e var lstmt env isDecl: list<statement_t> =
  let get_res expr new_fv =
    let expr = (* todo: JSV_Let and JSV_Const *)
      match expr with
       | JSE_Assignment _ -> 
            if isDecl (* in JS assign_op returns the expr type *)
            then [JSS_Expression expr; JSS_Expression (JSE_Assignment (JGP_Identifier var, JSE_Literal (JSV_Null, "")))] @ lstmt
            else [JSS_Expression expr; JSS_VariableDeclaration ((JGP_Identifier var, Some (JSE_Literal (JSV_Null, ""))), JSV_Let)] @ lstmt
       | _ ->
            if isDecl then [JSS_Expression (JSE_Assignment (JGP_Identifier var, expr))] @ lstmt
            else [JSS_VariableDeclaration ((JGP_Identifier var, Some expr), JSV_Let)] @ lstmt in 
    (match new_fv with | [] -> expr | _ -> new_fv @ [JSS_Block expr]) in
    
  match e.expr with
  | x when is_pure_expr e var ->
      let expr = translate_expr_pure e env in
      get_res expr []

  | MLE_Let ((_, _,  [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_add_unit = add_unit;
      mllb_def = body;
      print_typ = pt
      }]), continuation) ->
     let isEqName = isInEnv env name in
     let env = if isEqName then env else extendEnv env ([], name) tys in
     let c = translate_expr continuation var lstmt env isDecl in
     if is_pure_expr body (name, None)
     then
        let var_decl_q = if isMutable tys then JSV_Let else JSV_Const in       
        let c = [JSS_VariableDeclaration ((JGP_Identifier (name, None), Some (translate_expr_pure body env)), var_decl_q)] @ c in
        if isEqName then [JSS_Block c] else c
     else
        translate_expr body (name, None) c env false

  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"

  | MLE_Fun (args, body) ->
      let args = List.map (fun ((n,_), t) -> JGP_Identifier (n, Some (translate_type t None env))) args in
      let is_failwith =
       (match body.expr with
        | MLE_App (expr, _) ->
           (match expr.expr with
            | MLE_Name p when string_of_mlpath p = "failwith" -> true
            | _ -> false)
        | _ -> false) in
      let body_t =
        if is_failwith
        then JS_BodyBlock [JSS_Throw (JSE_Literal (JSV_String "Not yet implemented!", ""))]
        else
            if is_pure_expr body var
            then JS_BodyExpression (translate_expr_pure body env)
            else JS_BodyBlock ([JSS_VariableDeclaration ((JGP_Identifier ("_res", None), None), JSV_Let)] @
                               translate_expr body ("_res", None) [JSS_Return (Some (JSE_Identifier("_res", None)))] env true) in
      let (ret_t, lp_generic) =
        (match (snd var) with
         | None -> (None, None)
         | Some v -> match v with | JST_Function (_, t2, lp) -> (Some t2, lp) | _ -> (None, None)) in
      let expr = JSE_ArrowFunction (None, args, body_t, ret_t, lp_generic) in
      let expr =
        if isDecl then [JSS_Expression (JSE_Assignment (JGP_Identifier (fst var, None), expr))]
        else [JSS_VariableDeclaration ((JGP_Identifier (fst var, None), Some expr), JSV_Const)] in
      expr @ lstmt

  | MLE_If (cond, s1, s2) ->
      let s1 = JSS_Block (translate_expr s1 var [] env true) in
      let s2 = (match s2 with | Some v -> Some (JSS_Block (translate_expr v var [] env true)) | None -> None) in
      let c =
        if is_pure_expr cond var
        then [JSS_If (translate_expr_pure cond env, s1, s2)]
        else [JSS_VariableDeclaration ((JGP_Identifier ("_cond", Some JST_Boolean), None), JSV_Let)] @
             translate_expr cond ("_cond", None) [JSS_If (JSE_Identifier ("_cond", None), s1, s2)] env true in
      let c = if isDecl then c else [JSS_VariableDeclaration ((JGP_Identifier var, None), JSV_Let)] @ c in
      c @ lstmt

  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"

  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

  | MLE_Coerce (in_e, t_from, t_to) ->
      let var = (fst var, Some JST_Any) in
      translate_expr in_e var lstmt env isDecl

  | MLE_Match (e_in, lb) ->
      let match_e = (fst (gensym()), None) in
      let c =
        if is_pure_expr e_in var
        then [JSS_VariableDeclaration ((JGP_Identifier match_e, Some (translate_expr_pure e_in env)), JSV_Const);
              translate_match lb (JSE_Identifier match_e) var env]
        else [JSS_VariableDeclaration ((JGP_Identifier match_e, None), JSV_Let)] @
              translate_expr e_in match_e [translate_match lb (JSE_Identifier match_e) var env] env true in
      let c = if isDecl then c else [JSS_VariableDeclaration ((JGP_Identifier var, None), JSV_Let)] @ c in
      c @ lstmt

  | MLE_Seq ls ->
      let rec translate_seq l =
        match l with
        | [] -> failwith "Empty list in [MLE_Seq]"
        | [x] -> translate_expr x var [] env isDecl
        | hd :: tl -> translate_expr hd ("_", None) (translate_seq tl) env false in
      (translate_seq ls) @ lstmt

  | MLE_App (e, args) ->
      let (args, new_fv) = create_pure_args args var env in
      let expr = translate_arg_app e args var env in
      get_res expr new_fv
     
  | MLE_CTor ((path, c), lexpr) ->
      let (lexpr, new_fv) = create_pure_args lexpr var env in
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
      get_res expr new_fv

  | MLE_Record (path, fields) ->
      let (create_fields, new_fv) =
        List.fold_left (fun (lexpr, lnew_fv) (id, x) ->
            let (expr, fv) = create_pure_args [x] var env in
            ([JSPO_Property (JSO_Identifier ("_" ^ id, None), List.nth expr 0, JSO_Init)] @ lexpr, fv @ lnew_fv)) ([], []) fields in
      let expr = JSE_Object ([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String "Record", ""), JSO_Init)] @
                             create_fields) in
      get_res expr new_fv

  | MLE_Tuple lexp ->
      let (create_fields, new_fv) =
        List.fold_left (fun (lexpr, lnew_fv) x ->
            let (expr, fv) = create_pure_args [x] var env in
            (expr @ lexpr, fv @ lnew_fv)) ([], []) lexp in
      let expr = JSE_Array (Some create_fields) in
      get_res expr new_fv

  | _ -> failwith "todo: translation ml-expr"

and create_pure_args args var env =
    List.fold_left (fun (lexpr, lnew_fv) x ->
        match x.expr with
        | MLE_CTor ((path, c), _) when c = "Nil" || c = "None" ->
            ([JSE_TypeCast (translate_expr_pure x env, translate_type x.mlty None env)] @ lexpr, lnew_fv)
        | _ ->
            if is_pure_expr x var
            then ([translate_expr_pure x env] @ lexpr, lnew_fv)
            else
                let fv_x = fst (gensym()) in
                let c =
                    (match x.expr with
                     | MLE_Var _ -> [JSS_VariableDeclaration ((JGP_Identifier (fv_x, None), Some (translate_expr_pure x env)), JSV_Const)]
                     | _ -> translate_expr x (fv_x, None) [] env false) in
                ([JSE_Identifier (fv_x, None)] @ lexpr, c @ lnew_fv)) ([], []) args

and translate_arg_app e args var env: expression_t =
  match e.expr with
  | MLE_Name(["Prims"], op) when is_op_bin op ->
      JSE_Binary (must (mk_op_bin op), List.nth args 0, List.nth args 1)
  | MLE_Name(["Prims"], op) when is_op_bool op ->
      JSE_Logical (must (mk_op_bool op), List.nth args 0, List.nth args 1)
  | MLE_Name(["Prims"], op) when is_op_un op ->
      JSE_Unary (must (mk_op_un op), List.nth args 0)
  | MLE_Name p when string_of_mlpath p = "FStar.Buffer.op_Array_Access"
                 || string_of_mlpath p = "FStar.Buffer.index" ->
      JSE_Member (List.nth args 0, JSPM_Expression (List.nth args 1))
  | MLE_Name p when string_of_mlpath p = "FStar.Buffer.op_Array_Assignment"
                 || string_of_mlpath p = "FStar.Buffer.upd" ->
      JSE_Assignment (JGP_Expression (JSE_Member (List.nth args 0, JSPM_Expression (List.nth args 1))), List.nth args 2)
  | MLE_Name p when string_of_mlpath p = "FStar.ST.op_Bang"
                 || string_of_mlpath p = "FStar.ST.read" ->
      JSE_Member (List.nth args 0, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int 0), "0")))
  | MLE_Name p when string_of_mlpath p = "FStar.ST.op_Colon_Equals"
                 || string_of_mlpath p = "FStar.ST.write" ->
      let expr = JSE_Member (List.nth args 0, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int 0), "0"))) in
      JSE_Assignment (JGP_Expression expr, List.nth args 1)
  | MLE_Name p when string_of_mlpath p = "FStar.ST.alloc" ->
      JSE_Array (Some [List.nth args 0])
  | MLE_Name (path, function_name) ->
      let path = String.concat "_" path in
      let name = if (path = env.module_name || path = "") then function_name else path ^ "." ^ function_name in
      JSE_Call (JSE_Identifier (name, None), args)
  | MLE_Var (name, _) ->
      JSE_Call (JSE_Identifier (name, None), args)
  | _ ->
      if is_pure_expr e var
      then JSE_Call (translate_expr_pure e env, args)
      else failwith "todo: translation [MLE_App]"

and translate_expr_pure e env: expression_t =
  match e.expr with
  | MLE_Const c -> translate_constant c
  | MLE_Var (name, _) -> JSE_Identifier (name, None)
  | MLE_Name (path, name) ->
      let path = String.concat "_" path in
      let name = if (path = env.module_name || path = "") then name else path ^ "." ^ name in
      JSE_Identifier (name, None)
  | MLE_Tuple lexp ->
      JSE_Array (Some (List.map (fun x -> translate_expr_pure x env) lexp))
  | MLE_Record (path, fields) ->
      let create_fields = List.map (fun (id, x) -> JSPO_Property (JSO_Identifier ("_" ^ id, None), translate_expr_pure x env, JSO_Init)) fields in
      JSE_Object([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String "Record", ""), JSO_Init)] @ create_fields)
  | MLE_CTor ((path, c), lexpr) ->
     (match c with
      | x when x = "Cons" || x = "Nil" ->
           (match lexpr with
           | [] -> JSE_Array None
           | hd :: tl -> JSE_Call (JSE_Member (JSE_Array (Some [translate_expr_pure hd env]), JSPM_Identifier ("concat", None)), 
                                   List.map ( fun x -> translate_expr_pure x env) tl))
      | x when x = "Some" || x = "None" ->
           (match lexpr with
           | [] -> JSE_Literal (JSV_Null, "")
           | hd :: tl -> List.nth (List.map (fun x -> translate_expr_pure x env) lexpr) 0)
      | _ -> JSE_Object ([JSPO_Property (JSO_Identifier ("_tag", Some JST_String), JSE_Literal (JSV_String c, ""), JSO_Init)] @
                         List.mapi (fun i x -> JSPO_Property (JSO_Identifier ("_" ^ string_of_int i, None), translate_expr_pure x env, JSO_Init)) lexpr))
  | MLE_Coerce (e, _, _) -> translate_expr_pure e env (*!!*)
  | MLE_App (e, args) ->
      let args = List.map (fun x ->
        match x.expr with
        | MLE_CTor ((path, c), _) when c = "Nil" || c = "None" ->
            JSE_TypeCast (translate_expr_pure x env, translate_type x.mlty None env)
        | _ -> translate_expr_pure x env) args
      in translate_arg_app e args ("", None) env
  | MLE_Proj (expr, (path, name)) ->
      JSE_Member (translate_expr_pure expr env, JSPM_Identifier ("_" ^ name, None))
  | _ -> failwith "todo: translation ml-expr-pure"

and translate_match lb match_e var env: statement_t =
  match lb with
  | [] -> JSS_Throw (JSE_Literal (JSV_String ("This value doesn't match!"), ""))
  | (p, guard, expr_r) :: tl ->
    let expr_t =
        if is_pure_expr expr_r var
        then JSE_Assignment (JGP_Identifier var, translate_expr_pure expr_r env) |> JSS_Expression
        else translate_expr expr_r var [] env true |> JSS_Seq in
    translate_pat_guard (p, guard) match_e expr_t (translate_match tl match_e var env) env

and translate_pat_guard (p, guard) match_e s1 s2 env: statement_t =
  match guard with
  | None -> translate_pat p match_e s1 s2
  | Some v_guard -> (* maybe add translation for case when v_guard isn't pure *)
      let cond_stmt = JSS_If (translate_expr_pure v_guard env, s1, Some s2) in
      translate_pat p match_e cond_stmt s2

and translate_pat p match_e s1 s2: statement_t =
  match p with
  | MLP_Var (name, _) ->
      JSS_Seq [JSS_VariableDeclaration ((JGP_Identifier (name, None), Some match_e), JSV_Const); s1]
  | MLP_Wild -> s1
  | MLP_Const c ->
      JSS_If (JSE_Binary (JSB_Equal, match_e, translate_constant c), s1, Some s2)
  | MLP_CTor ((path, c), lp) ->
      let rec translate_p_ctor lp match_e s1 s2 i =
        let new_fv_x =
            match c with
            | x when x = "Some" -> match_e
            | x when x = "Cons" && i = 0 -> JSE_Member (match_e, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int 0), "0")))
            | x when x = "Cons" && i = 1 -> JSE_Member (match_e, JSPM_Identifier ("slice(1)", None))
            | _ -> JSE_Member (match_e, JSPM_Identifier ("_" ^ string_of_int i, None)) in
       (match lp with
        | [] -> s1
        | [x] -> translate_pat x new_fv_x s1 s2
        | hd::tl -> translate_pat hd new_fv_x (translate_p_ctor tl match_e s1 s2 (i + 1)) s2)
      in
        begin
        let if_stmt if_cond = JSS_If (if_cond, translate_p_ctor lp match_e s1 s2 0, Some s2) in
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
                let if_cond =
                    JSE_Binary (JSB_StrictEqual, JSE_Member (JSE_Identifier (new_name, None), JSPM_Identifier ("_tag", Some JST_String)), JSE_Literal (JSV_String c, "")) in
                JSS_Seq [JSS_VariableDeclaration ((JGP_Identifier (new_name, None), Some match_e), JSV_Const);
                         JSS_If (if_cond, translate_p_ctor lp (JSE_Identifier (new_name, None)) s1 s2 0, Some s2)]
        end
  | MLP_Branch lp ->
      let rec translate_p_branch lp match_e s1 s2 =
        match lp with
        | [] -> failwith "Empty list in translate_p_branch"
        | [x] -> translate_pat x match_e s1 s2
        | hd :: tl -> translate_pat hd match_e s1 (translate_p_branch tl match_e s1 s2)
      in translate_p_branch lp match_e s1 s2
  | MLP_Record (path, lp) ->
      let rec translate_p_record lp match_e s1 s2 =
        let new_fv_x n = JSE_Member (match_e, JSPM_Identifier ("_" ^ n, None)) in
            (match lp with
            | [] -> failwith "Empty list in translate_p_record"
            | [x] -> translate_pat (snd x) (new_fv_x (fst x)) s1 s2
            | hd :: tl -> translate_pat (snd hd) (new_fv_x (fst hd)) (translate_p_record tl match_e s1 s2) s2)
      in translate_p_record lp match_e s1 s2
  | MLP_Tuple lp ->
      let rec translate_p_tuple lp d match_e s1 s2 =
        let new_fv_x = JSE_Member (match_e, JSPM_Expression (JSE_Literal (JSV_Number (float_of_int d), string_of_int d))) in
            (match lp with
            | [] -> failwith "Empty list in translate_p_tuple"
            | [x] -> translate_pat x new_fv_x s1 s2
            | hd :: tl -> translate_pat hd new_fv_x (translate_p_tuple tl (d + 1) match_e s1 s2) s2)
      in translate_p_tuple lp 0 match_e s1 s2
      
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

and translate_type t lp_generic env: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      JST_Any
  | MLTY_Var (id, _) ->
      JST_Generic (id, None)
  | MLTY_Tuple lt ->
      JST_Tuple (List.map (fun x -> translate_type x lp_generic env) lt)
  | MLTY_Fun (t1, e_tag, t2) ->
      let t2 = if e_tag = E_GHOST then JST_Null else translate_type t2 None env in
      JST_Function ([(("_1", None), translate_type t1 None env)], t2, lp_generic)
  | MLTY_Named (args, p) when string_of_mlpath p = "FStar.ST.ref" ->
      JST_Array (translate_type (List.nth args 0) lp_generic env)
  | MLTY_Named (_, p) when string_of_mlpath p = "FStar.Buffer.buffer" ->
      JST_Generic ("FStar_Buffer.buffer", None) (* no polymorphism *)
  | MLTY_Named (_, p) when string_of_mlpath p = "FStar.Ghost.erased" ->
      JST_Any
  | MLTY_Named (args, (path, name)) ->
      if is_standart_type name
      then must (mk_standart_type name)
      else (if Option.isSome (Util.is_xtuple_ty (path, name))
           then JST_Tuple (List.map (fun x -> translate_type x lp_generic env) args)
           else
              let args_t =
                 match args with
                 | [] -> None
                 | _ -> List.map (fun x -> translate_type x lp_generic env) args |> Some in
              let path = String.concat "_" path in
              let name = if (path = env.module_name || path = "") then name else path ^ "." ^ name in
              JST_Generic (name, args_t))