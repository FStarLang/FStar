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
  module_name: list<string>;
}

and name = {
  pretty: string;
  mut: bool;
}

let empty module_name = {
  names = [];
  module_name = module_name
}

(**************************)
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
      Some JST_Void
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

let float_of_int i = Util.float_of_int32 (Util.int32_of_int i)

(* Actual translation ********************************************************)
let rec translate (MLLib modules): list<file> =
  List.filter_map (fun m ->
    let m_name =
      let (prefix, final), _, _ = m in
      String.concat "." (prefix @ [ final ])
    in
    try
      Util.print1 "Attempting to translate module %s\n" m_name;
      Some (translate_module m)
    with
    | e ->
        Util.print2 "Unable to translate module: %s because:\n  %s\n"
          m_name (Util.print_exn e);
        None
  ) modules

and translate_module (module_name, modul, _): file =
  let module_name = fst module_name @ [ snd module_name ] in
  let program = match modul with
    | Some (_signature, decls) ->
        List.filter_map (translate_decl (empty module_name)) decls
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  (String.concat "_" module_name), program

and translate_decl env d: option<source_t> =
  match d with
  | MLM_Let (_, [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_def = expr;
      print_typ=pt}]) ->
      let t = if (not pt) then None 
              else match tys with 
                   | None -> None
                   | Some ([], ty) -> translate_type ty |> Some
                   | Some (_ ::_, ty) -> None
              in
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier(name, t), None)], JSV_Var) in 
      JSS_Block([decl_v; translate_expr expr (name, None) None]) |> JS_Statement |> Some

  | MLM_Let _ -> None

  | MLM_Loc _ -> None (*only for OCaml backend*)

  | MLM_Ty [(_, name, tparams, body)] ->
      let tparams = 
        match tparams with
        | [] -> None
        | _ -> List.map (fun (id, _) -> id) tparams |> Some
        in
      let forbody body =
        match body with
        | MLTD_Abbrev t -> JSS_TypeAlias((name, None), tparams, translate_type t)
        | MLTD_Record fields ->
            let tag = [(JSO_Identifier("_tag", None), JST_StringLiteral("Record", ""))] in
            let fields_t = List.map (fun (n, t) -> (JSO_Identifier("_" ^ n, None), translate_type t)) fields in
            JSS_TypeAlias((name, None), tparams, JST_Object(tag @ fields_t, [], []))
        | MLTD_DType lfields ->
            let tag n = [(JSO_Identifier("_tag", None), JST_StringLiteral(n, ""))] in
            let fields_t fields = List.map (fun t -> (JSO_Identifier("_value", None), JST_Tuple [translate_type t])) fields in
            let lfields_t = List.map (fun (n, l) -> JSS_TypeAlias((n, None), tparams, JST_Object((tag n) @ fields_t l, [], []))) lfields in
            let tparams_gen = 
                match tparams with 
                | Some t -> List.map (fun x -> JST_Generic(Unqualified(x, None), None)) t |> Some
                | None -> None in
            let lnames = List.map (fun (n,l) -> JST_Generic(Unqualified(n, None), tparams_gen)) lfields in
            let union_t = JSS_TypeAlias((name, None), tparams, JST_Union(lnames)) in
            JSS_Block(lfields_t @ [union_t]) in
      let body_t =
        match body with
           | None -> failwith "todo: translate_decl [MLM_Ty] with empty body"
           | Some v -> forbody v in
        body_t |> JS_Statement |> Some

  | MLM_Ty _ ->
      failwith "todo: translate_decl [MLM_Ty]"

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

 and translate_expr e var stmt : statement_t =
  match e.expr with
  | MLE_Const c ->
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_constant c)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Var (name, _) ->        
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Identifier(name, None))) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Name(path, n) ->      
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Identifier(n, None))) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Let ((_, [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_add_unit = add_unit;
      mllb_def = body;
      print_typ = pt
      }]), continuation) ->
      let t = if (not pt) then None 
              else match tys with 
                   | None -> None
                   | Some ([], ty) -> translate_type ty |> Some
                   | Some (_ ::_, ty) -> None
              in
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier(name, t), None)], JSV_Let) in
      let body_t = translate_expr body (name, None)  (Some (translate_expr continuation var stmt)) in
      JSS_Block([decl_v; body_t])

  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"

  | MLE_App (e, args) ->
      let args_t = List.map translate_expr_app args in
      let c = 
         match e.expr with
         | MLE_Name (["Prims"], op) when is_op_bin op ->
              JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Binary((must (mk_op_bin op)), List.nth args_t 0, List.nth args_t 1)))
         | MLE_Name (["Prims"], op) when is_op_bool op ->
              JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Logical((must (mk_op_bool op)), List.nth args_t 0, List.nth args_t 1)))
         | MLE_Name (["Prims"], op) when is_op_un op ->
              JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Unary((must (mk_op_un op)), List.nth args_t 0)))
         | MLE_Name (_, "failwith") ->
              JSS_Throw(JSE_Literal(JSV_String("Not yet implemented in ML extraction!"), ""))
         | MLE_Name (path, function_name) ->
              JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Call(JSE_Identifier(function_name, None), args_t)))          
         | MLE_Var (name, _) ->
              JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Call (JSE_Identifier(name, None), args_t)))
         | _ -> failwith "todo: translate_expr [MLE_App]"
        in
        (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Record (_, fields) ->
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_app e)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Proj (_, path) ->
      failwith "todo: translate_expr [MLE_Proj]"

  | MLE_Fun (args, body) ->
      let args_t = List.map (fun ((n,_), t) -> JGP_Identifier(n, None)) args in
      let fv = Absyn.Util.gensym() in
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier(fv, None), None)], JSV_Let) in
      let body_t = translate_expr body (fv, None) (Some(JSS_Return(Some(JSE_Identifier(fv, None))))) in
      let fun_t = (JSE_Function(None, args_t, JS_BodyBlock([decl_v; body_t]), None, None)) in
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), fun_t)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_CTor _  ->
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_app e)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Tuple _ ->
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_app e)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Seq ls ->
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_app e)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_If(cond, s1, s2) ->
      let fv_t = Absyn.Util.gensym() in
      let s2_t = (match s2 with | Some v -> Some (translate_expr v var None) | None -> None) in
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier(fv_t, Some (JST_Boolean)), None)], JSV_Let) in 
      let c = translate_expr cond (fv_t, None) (Some (JSS_If(JSE_Identifier(fv_t, Some JST_Boolean), translate_expr s1 var None, s2_t))) in
      (match stmt with | Some v -> JSS_Block([decl_v; c; v]) | None -> JSS_Block([decl_v; c]))

  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"

  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

  | MLE_Coerce(in_e, t_from, t_to) -> (*consider the type*)
      translate_expr in_e var stmt

  | MLE_Match(e_in, lb) ->
      let fv_x = "_x" in//Absyn.Util.gensym() in
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier(fv_x, None), None)], JSV_Let) in
      let c = translate_expr e_in (fv_x, None) (Some (translate_match lb (JSE_Identifier(fv_x, None)) (List.length lb) var)) in
      (match stmt with | Some v -> JSS_Block([decl_v; c; v]) | None -> JSS_Block([decl_v; c]))

and translate_expr_app e: expression_t = 
  match e.expr with 
  | MLE_Const c  -> 
      translate_constant c
  | MLE_Var (name, _) -> 
      JSE_Identifier(name, None)
  | MLE_Name (_, name) -> 
      JSE_Identifier(name, None)
  | MLE_App (e, args) ->
      let args_t = List.map translate_expr_app args in
      (match e.expr with
       | MLE_Name(["Prims"], op) when is_op_bin op ->
            JSE_Binary((must (mk_op_bin op)), List.nth args_t 0, List.nth args_t 1)
       | MLE_Name(["Prims"], op) when is_op_bool op ->
            JSE_Logical((must (mk_op_bool op)), List.nth args_t 0, List.nth args_t 1)
       | MLE_Name(["Prims"], op) when is_op_un op ->
            JSE_Unary((must (mk_op_un op)), List.nth args_t 0)
       | MLE_Name (path, function_name) ->
            JSE_Call (JSE_Identifier(function_name, None), args_t)          
       | MLE_Var (name, _) ->
            JSE_Call (JSE_Identifier(name, None), args_t)
       | _ -> failwith "todo: translate_expr [MLE_App]")
  | MLE_Tuple lexp ->
      let create_fields = List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_f" ^ Util.string_of_int i, None), translate_expr_app x, JSO_Init)) lexp in
          JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Tuple", ""), JSO_Init);
                      JSPO_Property(JSO_Identifier("_arity", Some JST_Number), JSE_Literal(JSV_Number (float_of_int (List.length lexp)), ""), JSO_Init)] @
                      create_fields)
  | MLE_Record (path, fields) ->
      let create_fields = List.map (fun (id, x) -> JSPO_Property(JSO_Identifier("_" ^ id, None), translate_expr_app x, JSO_Init)) fields in
          JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Record", ""), JSO_Init)] @
                      create_fields)
  | MLE_CTor ((p, c), lexpr) ->      
      JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String c, ""), JSO_Init);
                  JSPO_Property(JSO_Identifier("_value", None), JSE_Array(Some (List.map (translate_expr_app) lexpr)), JSO_Init)])
  | MLE_Seq ls ->
      JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Seq", ""), JSO_Init);
                  JSPO_Property(JSO_Identifier("_value", None), JSE_Array(Some (List.map (translate_expr_app) ls)), JSO_Init)])
  | _ -> JSE_Literal(JSV_String "TODO!!!", "")//failwith "todo: translation of expressions"

and translate_match lb fv_x d var : statement_t =
    if d = 0 then JSS_Throw (JSE_Literal(JSV_String("This value doesn't match!"), ""))
    else
        let (p, guard, expr_r) = List.nth lb (List.length lb - d) in
            translate_pat_guard (p, guard) fv_x (translate_expr expr_r var None) (translate_match lb fv_x (d-1) var)

and translate_pat_guard (p, guard) fv_x s1 s2: statement_t =
  match guard with   
  | None -> translate_pat p fv_x s1 s2
  | Some v_guard ->
      let cond_stmt = JSS_If(translate_expr_app v_guard, s1, Some s2) in
          translate_pat p fv_x cond_stmt s2

and translate_pat p fv_x s1 s2: statement_t =
  match p with
  | MLP_Var (name, _) ->
      JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(name, None), Some fv_x)], JSV_Let); s1])
  | MLP_Wild -> 
      s1
  | MLP_Const c ->
      JSS_If(JSE_Binary(JSB_Equal, fv_x, translate_constant c), s1, Some s2)
  | MLP_CTor((p, c), lp) ->      
      let if_true =
        match (List.length lp) with
        | 0 -> s1
        | 1 -> translate_pat (List.nth lp 0) (JSE_Member(JSE_Member(fv_x, JSPM_Identifier("_value", None)), 
                                                         JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 0), "")))) s1 s2
        | _ -> translate_p_ctor lp (JSE_Member(fv_x, JSPM_Identifier("_value", None))) s1 s2 in
      JSS_If(JSE_Binary(JSB_StrictEqual,
                        JSE_Member(fv_x, JSPM_Identifier("_tag", Some JST_String)),
                        JSE_Literal(JSV_String c, "")), if_true, Some s2)
  | MLP_Branch _ ->
      failwith "todo: translate_pat [MLP_Branch]"
  | MLP_Record (_, lp) -> 
      translate_p_record lp (List.length lp) fv_x s1 s2
  | MLP_Tuple lp -> 
      translate_p_tuple lp (List.length lp) fv_x s1 s2

and translate_p_ctor lp fv_x s1 s2 : statement_t =
  match lp with
  | [x] -> translate_pat x fv_x s1 s2
  | hd::tl -> translate_pat hd (JSE_Member(fv_x, JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 0), ""))))
                               (translate_p_ctor tl (JSE_Member(fv_x, JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 1), "")))) s1 s2) s2
  | [] -> failwith "Empty list in pattern matching"

and translate_p_tuple lp d fv_x s1 s2 : statement_t =
  let n = List.length lp in
  if d = 1 then translate_pat (List.nth lp (n-d)) (JSE_Member(fv_x, JSPM_Identifier("_f" ^ string_of_int (n-d), None))) s1 s2
  else
        translate_pat (List.nth lp (n-d)) (JSE_Member(fv_x, JSPM_Identifier("_f" ^ string_of_int (n-d), None))) (translate_p_tuple lp (d-1) fv_x s1 s2) s2

and translate_p_record lp d fv_x s1 s2 : statement_t =
  let n = List.length lp in
  if d = 1 then translate_pat (snd (List.nth lp (n-d))) (JSE_Member(fv_x, JSPM_Identifier("_" ^ (fst (List.nth lp (n-d))), None))) s1 s2
  else
      translate_pat (snd (List.nth lp (n-d))) (JSE_Member(fv_x, JSPM_Identifier("_" ^ (fst (List.nth lp (n-d))), None))) (translate_p_record lp (d-1) fv_x s1 s2) s2

and translate_constant c: expression_t =
  match c with
  | MLC_Unit ->
      JSE_Literal(JSV_Null, "")
  | MLC_Bool b ->
      JSE_Literal(JSV_Boolean b, "")
  | MLC_Int (s, _) ->
      JSE_Literal(JSV_Number (float_of_int (Util.int_of_string s)), s)
  | MLC_Float f ->
      JSE_Literal(JSV_Number f, Util.string_of_float f)
  | MLC_Char _ ->
      failwith "todo: translate_const [MLC_Char]"
  | MLC_String s ->
      JSE_Literal(JSV_String s, s)
  | MLC_Bytes _ ->
      failwith "todo: translate_const [MLC_Bytes]"  

and translate_type t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      JST_Any
  | MLTY_Var (id, _) ->
      JST_Generic (Unqualified(id, None), None)
  | MLTY_Tuple lt ->
      JST_Tuple (List.map translate_type lt)
  | MLTY_Fun (t1, _, t2) ->
      let t1_t = translate_type t1 in
      let t2_t = translate_type t2 in      
      //JST_Function([(("_1", None), t1_t)], t2_t, None)  (*!!!*)
      //JST_Function([(("_1", None), JST_Any)], JST_Any, None) 
      JST_Any
  | MLTY_Named (args, (path, name)) ->      
      if is_standart_type name
      then must (mk_standart_type name)
      else (if Option.isSome (Util.is_xtuple_ty (path, name))
           then 
                let args = List.mapi (fun i x -> (JSO_Identifier("_" ^ string_of_int i, None), translate_type x)) args in     
                let tag = [(JSO_Identifier("_tag", None), JST_StringLiteral("Tuple", ""))] in
                let arity = [(JSO_Identifier("_arity", None), JST_NumberLiteral(float_of_int (List.length args), ""))] in
                JST_Object(tag @ arity @ args, [], [])
           else 
                let args = match args with 
                           | [] -> None 
                           | _ -> List.map translate_type args |> Some in 
                let name = match name with 
                           | "list" | "option" -> Syntax.string_of_mlpath (path, name)
                           | _ -> name 
                in JST_Generic (Unqualified(name, None), args))