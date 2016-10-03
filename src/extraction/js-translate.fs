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
      mllb_tysc = Some ([], MLTY_Fun (_, _, t));
      mllb_def = expr
    } ]) -> 
    let rec find_return_type = function
        | MLTY_Fun (_, _, t) ->
            find_return_type t
        | t ->
            t in
    let t = translate_type (find_return_type t) in
        translate_expr expr (name, Some t) None |> JS_Statement |> Some

  | MLM_Let (flavor, [ {
      mllb_name = name, _;
      mllb_tysc = Some ([], t);
      mllb_def = expr
    } ]) ->
      let t = translate_type t in
        translate_expr expr (name, Some t) None |> JS_Statement |> Some

 | MLM_Let (flavor, [ {
      mllb_name = name, _;
      mllb_tysc = Some (_); //Some ([], _);
      mllb_def = expr
    } ]) ->
      translate_expr expr (name, None) None |> JS_Statement |> Some

  | MLM_Let _ -> None

  | MLM_Loc _ -> None (*only for OCaml backend*)

  | MLM_Ty [ (_, name, [], Some (MLTD_Abbrev t)) ] ->
      JSS_TypeAlias((name, None), None, translate_type t) |> JS_Statement  |> Some

  | MLM_Ty [ (_, name, [], Some (MLTD_Record fields)) ] ->       
      let fields_t = List.map (fun (n, t) -> (JSO_Identifier(n, None), translate_type t)) fields in      
        JSS_TypeAlias((name, None), None, JST_Object(fields_t, [], [])) |> JS_Statement  |> Some

  | MLM_Ty [ (_, name, [], Some (MLTD_DType lfields)) ] ->
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
       (match stmt with 
       | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var), Some (translate_constant c))], JSV_Const); v])
       | None -> JSS_VariableDeclaration([(JGP_Identifier(var), Some (translate_constant c))], JSV_Const))
   | MLE_Var (name, _) -> 
       (match stmt with 
       | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var),  Some (JSE_Identifier(name, None)))], JSV_Var); v])
       | None -> JSS_VariableDeclaration([(JGP_Identifier(var),  Some (JSE_Identifier(name, None)))], JSV_Var))       
   | MLE_Name(path, n) ->
       JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Identifier(n, None)))], JSV_Var)
   | MLE_Let ((flavor, [{
       mllb_name = name, _;
       mllb_tysc = Some ([], _); 
       mllb_add_unit = add_unit; 
       mllb_def = body;
       print_typ = print 
       }]), continuation) ->
       translate_expr body (name, None)  (Some(translate_expr continuation var stmt)) 
   | MLE_Let _ ->
       failwith "todo: translate_expr [MLE_Let]"
   | MLE_App ({ expr = MLE_Name ([ "Prims"], op) }, args) when is_op_bin op ->
       (match stmt with
       | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Binary((must (mk_op_bin op)), translate_expr_app (List.nth args 0), translate_expr_app (List.nth args 1))))], JSV_Var); v])
       | None -> JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Binary((must (mk_op_bin op)), translate_expr_app (List.nth args 0), translate_expr_app (List.nth args 0))))], JSV_Var))
   | MLE_App ({ expr = MLE_Name ([ "Prims"], op) }, args) when is_op_bool op ->
       (match stmt with
       | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Logical((must (mk_op_bool op)), translate_expr_app (List.nth args 0), translate_expr_app (List.nth args 1))))], JSV_Var); v])
       | None -> JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Logical((must (mk_op_bool op)), translate_expr_app (List.nth args 0), translate_expr_app (List.nth args 1))))], JSV_Var))
   | MLE_App ({ expr = MLE_Name (path, function_name) }, args) ->      
       let args_t = List.map translate_expr_app args in
       (match stmt with 
       | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Call(JSE_Identifier(function_name, None), args_t)))], JSV_Var); v])
       | None -> JSS_VariableDeclaration([(JGP_Identifier(var), Some (JSE_Call(JSE_Identifier(function_name, None), args_t)))], JSV_Var))
   | MLE_App _ -> failwith "todo: translate_expr [MLE_App]"
   | MLE_Record (_, fields) ->
       failwith "todo: translate_expr [MLE_Record]"
   | MLE_Proj (_, path) ->
       failwith "todo: translate_expr [MLE_Proj]"
   | MLE_Fun (args, body) ->
       let args_t = List.map (fun ((n,_), t) -> JGP_Identifier(n, None)) args in
       let fv = Absyn.Util.gensym() in
       let body_t = translate_expr body (fv, None) (Some(JSS_Return(Some(JSE_Identifier(fv, None))))) in
       let newFun = (JSE_Function(None, args_t, JS_BodyBlock([body_t]), None, None)) in
          (match stmt with 
          | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var), Some (newFun))], JSV_Var); v])
          | None -> JSS_VariableDeclaration([(JGP_Identifier(var), Some (newFun))], JSV_Var))
   | MLE_CTor _  -> failwith "todo: translate_expr [MLE_CTor]"
   | MLE_Tuple _ ->
       (match stmt with 
       | Some v -> JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(var), Some (translate_expr_app e))], JSV_Var); v])
       | None -> JSS_VariableDeclaration([(JGP_Identifier(var), Some (translate_expr_app e))], JSV_Var))      
   | MLE_Seq _ ->
       failwith "todo: translate_expr [MLE_Seq]"   
   | MLE_If(_, e1, e2) ->
       failwith "todo: translate_expr [MLE_If]"
   | MLE_Raise _ ->
       failwith "todo: translate_expr [MLE_Raise]"
   | MLE_Try _ ->
       failwith "todo: translate_expr [MLE_Try]"
   | MLE_Coerce(in_e, t_from, t_to) -> (*todo: consider type!*)
       translate_expr in_e var stmt
   | MLE_Match(e_in, lb) ->
       let depth = List.length lb in 
       let r = Absyn.Util.gensym() in
           translate_expr e_in (r, None) (Some (translate_match (JSE_Identifier(r, None)) lb var depth))

and translate_expr_app e: expression_t = 
    match e.expr with 
    | MLE_Const c  -> translate_constant c
    | MLE_Var (name, _) -> JSE_Identifier(name, None)
    | MLE_Name (_, name) -> JSE_Identifier(name, None)
    | MLE_App ({ expr = MLE_Name ([ "Prims"], op) }, args) when is_op_bin op ->
         JSE_Binary((must (mk_op_bin op)), translate_expr_app  (List.nth args 0), translate_expr_app  (List.nth args 1))
    | MLE_App ({ expr = MLE_Name (path, function_name) }, args) ->
         JSE_Call (JSE_Identifier(function_name, None), List.map (translate_expr_app) args)
    | MLE_Tuple lexp -> 
        let arnity = List.length lexp in
        let create_field (i:int) v = JSPO_Property(JSO_Identifier("_f" ^ Util.string_of_int i, None), translate_expr_app v, JSO_Init) in
        let create_fields = List.mapi (fun i x -> create_field i x) lexp in
         JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Tuple", ""), JSO_Init); 
                     JSPO_Property(JSO_Identifier("_arity", Some JST_Number), JSE_Literal(JSV_Number (Util.float_of_int32 (Util.int32_of_int arnity)), ""), JSO_Init)] @
                     create_fields)
    | MLE_CTor (c, lexpr) -> 
         JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String (Syntax.string_of_mlpath c), ""), JSO_Init);
                     JSPO_Property(JSO_Identifier("_value", None), JSE_Array(Some (List.map (translate_expr_app) lexpr)), JSO_Init);])
    | _ -> failwith "todo: translation of expressions"

//r -- JSE_Identifier; v1:JST_Object; d = depth of if-s
and translate_match r lb x d : statement_t = 
    let v1 = Absyn.Util.gensym() in    
    let (p, guard, expr_r) = List.nth lb (List.length lb - d) in 
    let (pattern_tran, pattern_fv) = (JSE_This, None) in//translate_pat p v1 in 
    match guard with 
    | Some v ->
        let f1 = Absyn.Util.gensym() in
        let stmt_true = (match pattern_fv with 
                | Some fv -> JSS_Block([fv; translate_expr v (f1, None) None])
                | None -> translate_expr v (f1, None) None) in 
        let if_stmt = JSS_Block([
                       stmt_true;
                       JSS_If(JSE_Identifier(f1, None), translate_expr expr_r x (Some(JSS_Return(Some(JSE_Identifier x)))),
                                                       (if d = 1 then None (*or Exn*) else Some (translate_match r lb x (d-1))))
                       ]) in 
        JSS_Block([
        JSS_VariableDeclaration([(JGP_Identifier(v1, None), Some (JSE_Call(pattern_tran, [r])))], JSV_Var);
        JSS_If(JSE_Member(JSE_Identifier(v1, None), JSPM_Identifier("_valid", Some JST_Boolean)), 
            if_stmt, None);        
        ])
    | None -> 
        let stmt_true = (match pattern_fv with 
                | Some fv -> JSS_Block([fv; translate_expr expr_r x (Some(JSS_Return(Some(JSE_Identifier x))))])
                | None -> translate_expr expr_r x (Some(JSS_Return(Some(JSE_Identifier x))))) in 
        JSS_Block([
        JSS_VariableDeclaration([(JGP_Identifier(v1, None), Some (JSE_Call(pattern_tran, [r])))], JSV_Var);
        JSS_If(JSE_Member(JSE_Identifier(v1, None), JSPM_Identifier("_valid", Some JST_Boolean)),
              stmt_true, (if d = 1 then None (*or Exn*) else Some (translate_match r lb x (d-1))))
        ])
(*
and translate_pat p v1: (expression_t * option<statement_t>) =
  match p with  
  | MLP_Var (name, _) ->        
        let body = JSE_Object([JSPO_Property(JSO_Identifier("_valid", Some JST_Boolean), JSE_Literal(JSV_Boolean(true), ""), JSO_Init);
                               JSPO_Property(JSO_Identifier("_x", Some JST_Boolean), JSE_Identifier(name, None), JSO_Init)]) |> Some |> JSS_Return in
        (* let createfv =  *)
        (*     if (v1.[0..1] = "_r") //ident doesn't support dot notation *)
        (*     then JSS_VariableDeclaration([(JGP_Identifier(name, None), Some (JSE_Identifier(v1 ^ "_x", None)))], JSV_Var) *)
        (*     else JSS_VariableDeclaration([(JGP_Identifier(name, None), Some (JSE_Member(JSE_Identifier(v1, None), JSPM_Identifier("_x", None))))], JSV_Var) in *)
        //let createfv = JSS_VariableDeclaration([(JGP_Identifier(name, None), Some (JSE_Member(JSE_Identifier(v1, None), JSPM_Identifier("_x", None))))], JSV_Var) in
        (JSE_Function(None, [JGP_Identifier(name, None)], JS_BodyBlock([body]), None, None), None (* Some createfv *))
  | MLP_Wild ->
      failwith "todo: translate_pat [MLP_Wild]"
  | MLP_Const c ->         
        let ob1 = JSE_Object([JSPO_Property(JSO_Identifier("_valid", Some JST_Boolean), JSE_Literal(JSV_Boolean(true), ""), JSO_Init)]) |> Some |> JSS_Return in
        let ob2 = JSE_Object([JSPO_Property(JSO_Identifier("_valid", Some JST_Boolean), JSE_Literal(JSV_Boolean(false), ""), JSO_Init)]) |> Some |> JSS_Return in
        (JSE_Function(None, [JGP_Identifier("_x", None)],
             JS_BodyBlock([JSS_If(JSE_Binary(JSB_Equal, JSE_Identifier("_x", None), translate_constant c), ob1, Some ob2)]), None, None), None)
  | MLP_CTor(c, lp) -> 
        let (pattern_tr,fv) = translate_constr lp v1 in
        let ob1 = JSE_Call(pattern_tr, [JSE_Member(JSE_Identifier("e", None), JSPM_Identifier("_value", None))])  |> Some |> JSS_Return in
        let ob2 = JSE_Object([JSPO_Property(JSO_Identifier("_valid", Some JST_Boolean), JSE_Literal(JSV_Boolean(false), ""), JSO_Init)]) |> Some |> JSS_Return in
        (JSE_Function(None, [JGP_Identifier("e", None)],
                JS_BodyBlock([JSS_If(JSE_Binary(JSB_Equal, JSE_Member(JSE_Identifier("e", None), JSPM_Identifier("_tag", None)), JSE_Literal(JSV_String((* c.ToString() *) "todo"), "")),
                                    ob1, Some ob2)]), None, None), None)      
  | MLP_Branch _ ->
      failwith "todo: translate_pat [MLP_Branch]"
  | MLP_Record _ ->
      failwith "todo: translate_pat [MLP_Record]"
  | MLP_Tuple lp ->
        let arnity = List.length lp in
        let create_decl p1 i = 
            let (pattern_tr,fv) = translate_pat p1 ("_r" ^ Util.string_of_int i) in
            (JSS_VariableDeclaration([(JGP_Identifier("_r" ^ Util.string_of_int i, None), Some (JSE_Call(pattern_tr, [JSE_Member(JSE_Identifier("e", None), JSPM_Identifier("_f" ^ Util.string_of_int i, None))])))], JSV_Var), fv) in
        let create_decls_fv = List.mapi (fun i x -> create_decl x i) lp in
        let create_decls = List.map (fst) create_decls_fv in
        let create_tmp_fv i = 
            JSS_VariableDeclaration([(JGP_Identifier("_r" ^ Util.string_of_int i ^ "_x", None),  Some (JSE_Member(JSE_Identifier(v1, None), JSPM_Identifier("_f" ^ Util.string_of_int i, None))))], JSV_Var) in           
        let create_tmp_fvs = List.map (create_tmp_fv) [0; 1] (* todo [0..(arnity-1)]*) in
        (*let create_fvs = create_tmp_fvs @ List.map (fun el -> match (snd el) with | Some v -> v |None -> ()) create_decls_fv |> JSS_Block in *)
        let create_field_ob1 i = JSPO_Property(JSO_Identifier("_f" ^ Util.string_of_int i, None), JSE_Member(JSE_Identifier("_r" ^ Util.string_of_int i, None), JSPM_Identifier("_x", None)), JSO_Init) in 
        let create_fields_ob1 = List.map (create_field_ob1) [0; 1] (* todo [0..(arnity-1)]*) in        
        let ob1 = JSE_Object([JSPO_Property(JSO_Identifier("_valid", Some JST_Boolean), JSE_Literal(JSV_Boolean(true), ""), JSO_Init)] @ create_fields_ob1) |> Some |> JSS_Return in
        let ob2 = JSE_Object([JSPO_Property(JSO_Identifier("_valid", Some JST_Boolean), JSE_Literal(JSV_Boolean(false), ""), JSO_Init)]) |> Some |> JSS_Return in
        let rec if_cond i = JSE_Logical(JSL_And, JSE_Member(JSE_Identifier("e", None), JSPM_Identifier("_f" ^ Util.string_of_int i, None)), 
                        (if (i = arnity - 2) then JSE_Member(JSE_Identifier("e", None), JSPM_Identifier("_f" ^ Util.string_of_int (i+1), None)) else if_cond (i+1))) in
        (JSE_Function(None, [JGP_Identifier("e", None)],
                    JS_BodyBlock(create_decls @ [JSS_If(if_cond 0, ob1, Some ob2)]), None, None), None(*Some create_fvs*))

and translate_constr lp v1 = 
        failwith "todo: translation CTor"  
*)
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
      JSE_Literal(JSV_Number ( Util.float_of_int32 (Util.int32_of_int (Util.int_of_string s))), s)

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
