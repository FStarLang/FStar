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

let mk_op_bool = function 
  | "op_AmpAmp" ->
      Some JSL_And
  | "op_BarBar" ->
      Some JSL_Or  
  | _ ->
      None
 
 let is_op_bool op =
    mk_op_bool op <> None

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
  | MLM_Let (flavor, [ {
      mllb_name = name, _;
      mllb_tysc = Some (_); //Some ([], _);
      mllb_def = expr
    } ]) ->
      let var = (name, None) in 
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier(var), None)], JSV_Let) in 
      JSS_Block([decl_v; translate_expr expr var None]) |> JS_Statement |> Some
     //JSS_VariableDeclaration([(JGP_Identifier(name, None), Some (translate_expr expr var None))], JSV_Let) |> JS_Statement  |> Some    
  | MLM_Let _ -> None

  | MLM_Loc _ -> None (*only for OCaml backend*)

  | MLM_Ty [ (_, name, [], Some (MLTD_Abbrev t)) ] ->
      JSS_TypeAlias((name, None), None, translate_type t) |> JS_Statement  |> Some

  | MLM_Ty [ (_, name, [], Some (MLTD_Record fields)) ] ->       
      let fields_t = List.map (fun (n, t) -> (JSO_Identifier(n, None), translate_type t)) fields in      
        JSS_TypeAlias((name, None), None, JST_Object(fields_t, [], [])) |> JS_Statement  |> Some

  | MLM_Ty [ (_, name, [], Some (MLTD_DType lfields)) ] -> (*TODO!*)
      let fields_t fields = List.map (fun t -> (JSO_Identifier("_value", None), translate_type t)) fields in
      let lfields_t = List.map (fun (n, l) -> JSS_TypeAlias((n, None), None, JST_Object(fields_t l, [], []))) lfields in
      let lnames = List.map (fun (n,l) -> JST_StringLiteral(n, "")) lfields in
      let union_t = JSS_TypeAlias((name, None), None, JST_Union(lnames)) in
        JSS_Block(lfields_t) |> JS_Statement  |> Some

  | MLM_Ty _ ->
      failwith "todo: translate_decl [MLM_Ty]"

  | MLM_Top _ ->
      failwith "todo: translate_decl [MLM_Top]"

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

 and translate_expr e var stmt : statement_t =   
   match e.expr with  
   | MLE_Const c ->        
        let com = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_constant c)) in
        (match stmt with | Some v -> JSS_Block([com; v]) | None -> com)
   | MLE_Var (name, _) ->        
        let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Identifier(name, None))) in
        (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_Name(path, n) ->        
        let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Identifier(n, None))) in
        (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_Let ((flavor, [{
       mllb_name = name, _;
       mllb_tysc = Some ([], _);
       mllb_add_unit = add_unit; 
       mllb_def = body;
       print_typ = print 
       }]), continuation) ->
        let decl_v = JSS_VariableDeclaration([(JGP_Identifier(name, None), None)], JSV_Let) in 
        let tr_e = translate_expr body (name, None)  (Some(translate_expr continuation var stmt)) in
        JSS_Block([decl_v; tr_e])
   | MLE_Let _ ->
        failwith "todo: translate_expr [MLE_Let]"
   | MLE_App ({ expr = MLE_Name ([ "Prims"], op) }, args) when is_op_bin op ->
        let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Binary((must (mk_op_bin op)), 
                                                                     translate_expr_app (List.nth args 0), 
                                                                     translate_expr_app (List.nth args 1)))) in 
        (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_App ({ expr = MLE_Name ([ "Prims"], op) }, args) when is_op_bool op ->
       let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Logical((must (mk_op_bool op)), 
                                                                     translate_expr_app (List.nth args 0), 
                                                                     translate_expr_app (List.nth args 1)))) in 
       (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_App ({ expr = MLE_Name (path, function_name) }, args) ->
       let args_t = List.map translate_expr_app args in              
       let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_Call(JSE_Identifier(function_name, None), args_t))) in
       (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_App _ -> failwith "todo: translate_expr [MLE_App]"
   | MLE_Record (_, fields) ->
       failwith "todo: translate_expr [MLE_Record]"
   | MLE_Proj (_, path) ->
       failwith "todo: translate_expr [MLE_Proj]"
   | MLE_Fun (args, body) ->
       let args_t = List.map (fun ((n,_), t) -> JGP_Identifier(n, None)) args in
       let fv = Absyn.Util.gensym() in
       let decl_v = JSS_VariableDeclaration([(JGP_Identifier(fv, None), None)], JSV_Let) in 
       let body_t = translate_expr body (fv, None) (Some(JSS_Return(Some(JSE_Identifier(fv, None))))) in
       let newFun = (JSE_Function(None, args_t, JS_BodyBlock([decl_v; body_t]), None, None)) in       
       let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), newFun)) in
       (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_CTor _  ->        
       let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_app e)) in
       (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_Tuple _ ->       
       let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_app e)) in
       (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
   | MLE_Seq _ ->
       failwith "todo: translate_expr [MLE_Seq]"   
   | MLE_If(cond, s1, s2) ->
       let fv_t = Absyn.Util.gensym() in
       let s2_tr = (match s2 with | Some v -> Some (translate_expr v var None) | None -> None) in
       let decl_v = JSS_VariableDeclaration([(JGP_Identifier(fv_t, None), None)], JSV_Let) in 
       let c = translate_expr cond (fv_t, None) (Some (JSS_If(JSE_Identifier(fv_t, None), translate_expr s1 var None, s2_tr))) in
       (match stmt with | Some v -> JSS_Block([decl_v; c; v]) | None -> JSS_Block([decl_v; c]))
   | MLE_Raise _ ->
       failwith "todo: translate_expr [MLE_Raise]"
   | MLE_Try _ ->
       failwith "todo: translate_expr [MLE_Try]"
   | MLE_Coerce(in_e, t_from, t_to) -> 
       failwith "todo: translate_expr [MLE_Coerce]"
   | MLE_Match(e_in, lb) ->      
       let depth = List.length lb in
       let fv_x = "_x" in//Absyn.Util.gensym() in
       let decl_v = JSS_VariableDeclaration([(JGP_Identifier(fv_x, None), None)], JSV_Let) in        
       let c = translate_expr e_in (fv_x, None) (Some (translate_match lb (JSE_Identifier(fv_x, None)) depth var)) in
       (match stmt with | Some v -> JSS_Block([decl_v; c; v]) | None -> JSS_Block([decl_v; c]))

and translate_expr_app e: expression_t = 
    match e.expr with 
    | MLE_Const c  -> translate_constant c
    | MLE_Var (name, _) -> JSE_Identifier(name, None)
    | MLE_Name (_, name) -> JSE_Identifier(name, None)
    | MLE_App ({ expr = MLE_Name ([ "Prims"], op) }, args) when is_op_bin op ->
         JSE_Binary((must (mk_op_bin op)), translate_expr_app  (List.nth args 0), translate_expr_app  (List.nth args 1))
    | MLE_App ({ expr = MLE_Name (path, function_name) }, args) ->
         JSE_Call (JSE_Identifier(function_name, None), List.map (translate_expr_app) args) (*Full name for function?*)
    | MLE_Tuple lexp -> 
        let arity = List.length lexp in
        let create_field (i:int) v = JSPO_Property(JSO_Identifier("_f" ^ Util.string_of_int i, None), translate_expr_app v, JSO_Init) in
        let create_fields = List.mapi (fun i x -> create_field i x) lexp in
         JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Tuple", ""), JSO_Init); 
                     JSPO_Property(JSO_Identifier("_arity", Some JST_Number), JSE_Literal(JSV_Number (Util.float_of_int32 (Util.int32_of_int arity)), ""), JSO_Init)] @
                     create_fields)
    | MLE_CTor (c, lexpr) ->
         JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String (Syntax.string_of_mlpath c), ""), JSO_Init);
                     JSPO_Property(JSO_Identifier("_value", None), JSE_Array(Some (List.map (translate_expr_app) lexpr)), JSO_Init)])
    | _ -> failwith "todo: translation of expressions"

and translate_match lb fv_x d var : statement_t =
    if d = 0 then JSS_Throw (JSE_Literal(JSV_String("This value doesn't match!"), "")) (*Or assume that we don't have incomplete pattern matching?*)
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
      failwith "todo: translate_pat [MLP_Wild]"
  | MLP_Const c ->
      JSS_If(JSE_Binary(JSB_Equal, fv_x, translate_constant c), s1, Some s2)
  | MLP_CTor(c, lp) ->
        let if_true =
        match (List.length lp) with
        | 0 -> s1
        | 1 -> translate_pat (List.nth lp 0) (JSE_Member(JSE_Member(fv_x, JSPM_Identifier("_value", None)), JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 0), "")))) s1 s2
        | _ -> translate_p_ctor lp (JSE_Member(fv_x, JSPM_Identifier("_value", None))) s1 s2 in
      JSS_If(JSE_Binary(JSB_Equal,
                        JSE_Member(fv_x, JSPM_Identifier("_tag", Some JST_String)),
                        JSE_Literal(JSV_String (Syntax.string_of_mlpath c), "")), if_true, Some s2)
  | MLP_Branch _ ->
      failwith "todo: translate_pat [MLP_Branch]"
  | MLP_Record _ ->
      failwith "todo: translate_pat [MLP_Record]"
  | MLP_Tuple lp -> translate_p_tuple lp (List.length lp) fv_x s1 s2

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

and translate_constant c: expression_t =
  match c with
  | MLC_Unit ->
      JSE_Literal(JSV_Null, "")
  | MLC_Bool b ->
      JSE_Literal(JSV_Boolean b, "")
  | MLC_Int (s, Some _) ->
      failwith "impossible: machine integer not desugared to a function call"
  | MLC_Float f ->
      JSE_Literal(JSV_Number f, Util.string_of_float f)
  | MLC_Char _ ->
      failwith "todo: translate_const [MLC_Char]"
  | MLC_String s ->
      JSE_Literal(JSV_String s, s)
  | MLC_Bytes _ ->
      failwith "todo: translate_const [MLC_Bytes]"
  | MLC_Int (s, None) ->
      JSE_Literal(JSV_Number (float_of_int (Util.int_of_string s)), s)

and translate_type t: typ =
  match t with
  | MLTY_Tuple []
  | MLTY_Top ->
      failwith "todo: translate_type [MLTY_Top]"
  | MLTY_Var _ ->
      failwith "todo: translate_type [MLTY_Var]"
  | MLTY_Fun (t1, _, t2) ->
      failwith "todo: translate_type [MLTY_Fun]"
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.unit") ->
      JST_Void
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.bool") ->
      JST_Boolean
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.int")
                         || (Syntax.string_of_mlpath p = "Prims.nat") ->
      JST_Number
  | MLTY_Named ([], p) when (Syntax.string_of_mlpath p = "Prims.string") ->
      JST_String
  | MLTY_Named (_, (path, type_name)) ->      
      failwith "todo: translate_type [MLTY_Named]"
  | MLTY_Tuple _ ->
      failwith "todo: translate_type [MLTY_Tuple]"