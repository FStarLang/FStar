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
  | "op_Colon_Equals" -> 
      failwith "todo: translation [:=] for mutable variables"
  | _ ->
      None

let is_op_bin op =
  mk_op_bin op <> None

let mk_op_un = function
  | "op_Negation" ->
      Some JSU_Not
  | "op_Minus" ->
      Some JSU_Minus
  | "op_Bang" ->
      failwith "todo: translation [!] for mutable variables"
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

let float_of_int i = Util.float_of_int32 (Util.int32_of_int i)

let export_modules = ref []

let current_module_name = ref ""

let getName (path, n) =
    let path = String.concat "_" path in
    if (path = !current_module_name || path = "")
    then 
        JSE_Identifier(n, None)
    else
        ((if not (List.existsb (fun x -> x = path) !export_modules) 
          then export_modules := List.append [path] !export_modules);
        JSE_Identifier(path ^ "." ^ n, None))

let rec is_pure_expr e = 
    match e.expr with
    | MLE_Const _ | MLE_Var _ | MLE_Name _ -> true
    | MLE_CTor (p, le) ->
        not (List.contains false (List.map is_pure_expr le))
    | MLE_Tuple le ->
        not (List.contains false (List.map is_pure_expr le))
    | MLE_Record (_, lne) ->
        not (List.contains false (List.map ( fun (n, e) -> is_pure_expr e) lne))
    | MLE_App (e, le) ->
        not (List.contains false (List.map is_pure_expr le))
    | MLE_Fun (largs, e) -> is_pure_expr e
    | _ -> false

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
        current_module_name := String.concat "_" module_name;
        let res = List.filter_map translate_decl decls in
        let create_module_exports =
            let require_f m = JSE_Call (JSE_Identifier("require", None), [JSE_Literal(JSV_String( "./" ^ m), "")]) in
            List.map (fun m -> JSS_VariableDeclaration([(JGP_Identifier(m, None), Some (require_f m))], JSV_Var)) (!export_modules)
            |> JSS_Block |> JS_Statement
        in [create_module_exports] @ res
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in 
  (String.concat "_" module_name), program

and translate_decl d: option<source_t> =
  match d with
  | MLM_Let (_, lfunc) ->
      let for1 { mllb_name = name, _; mllb_tysc = tys; mllb_def = expr; print_typ=pt} = 
          let t = if (not pt) then None 
                  else match tys with 
                       | None -> None
                       | Some ([], ty) -> translate_type ty |> Some
                       | Some (_, ty) -> None  in
          if is_pure_expr expr
          then
            [JSS_VariableDeclaration([(JGP_Identifier(name, t), Some (translate_expr_pure expr))], JSV_Var)]
          else
            let decl_v = JSS_VariableDeclaration([(JGP_Identifier(name, t), None)], JSV_Var) in
            [decl_v; translate_expr expr (name, None) None]
     in
        List.collect for1 lfunc |> JSS_Block |> JS_Statement |> Some

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
            let fields_t fields = List.mapi (fun i t -> (JSO_Identifier("_" ^ string_of_int i, None), JST_Tuple [translate_type t])) fields in
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

  | MLM_Exn (x, []) -> (*exception Name => in JS?*)
      JSS_Block([]) |> JS_Statement |> Some

  | MLM_Exn _ ->
      failwith "todo: translate_decl [MLM_Exn]"

 and translate_expr e var stmt : statement_t =
  match e.expr with
  | x when is_pure_expr e ->
       let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_pure e)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)
          
  | MLE_Let ((_, [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_add_unit = add_unit;
      mllb_def = body;
      print_typ = pt
      }]), continuation) ->
      let c = 
        if is_pure_expr body 
        then 
           [JSS_VariableDeclaration([(JGP_Identifier(name, None), Some (translate_expr_pure body))], JSV_Let);
            translate_expr continuation var stmt]
        else 
           [JSS_VariableDeclaration([(JGP_Identifier(name, None), None)], JSV_Let);
            translate_expr body (name, None)  (Some (translate_expr continuation var stmt))] in
      JSS_Block(c)

  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"

  | MLE_Fun (args, body) ->
      let args = List.map (fun ((n,_), _) -> JGP_Identifier(n, None)) args in
      let decl_v = JSS_VariableDeclaration([(JGP_Identifier("_res", None), None)], JSV_Let) in
      let body_t = translate_expr body ("_res", None) (Some(JSS_Return(Some(JSE_Identifier("_res", None))))) in
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_ArrowFunction(None, args, JS_BodyBlock([decl_v; body_t]), None, None))) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Proj (_, path) ->
      failwith "todo: translate_expr [MLE_Proj]"
    
  | MLE_If(cond, s1, s2) ->
      let s2 = (match s2 with | Some v -> Some (translate_expr v var None) | None -> None) in
      let c =
        if is_pure_expr cond
        then
           [JSS_If(translate_expr_pure cond, translate_expr s1 var None, s2)]
        else
           [JSS_VariableDeclaration([(JGP_Identifier("_cond", Some (JST_Boolean)), None)], JSV_Let);
           translate_expr cond ("_cond", None) (Some (JSS_If(JSE_Identifier("_cond", Some JST_Boolean), translate_expr s1 var None, s2)))] in
      (match stmt with | Some v -> JSS_Block(c @ [v]) | None -> JSS_Block(c))

  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"

  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

  | MLE_Coerce(in_e, t_from, t_to) ->
      //let var = (fst var, Some (translate_type in_e.mlty)) in
      translate_expr in_e var stmt

  | MLE_Match(e_in, lb) ->
    let c =
      if is_pure_expr e_in 
      then 
        let expr = translate_expr_pure e_in in
        [translate_match lb expr var]
      else        
        let decl_v = JSS_VariableDeclaration([(JGP_Identifier("_match_e", None), None)], JSV_Let) in
        [decl_v; translate_expr e_in ("_match_e", None) (Some (translate_match lb (JSE_Identifier("_match_e", None)) var))] in
      (match stmt with | Some v -> JSS_Block(c @ [v]) | None -> JSS_Block(c))

  | MLE_Seq ls -> (*last element in Seq is result*)
      List.map (fun x -> translate_expr x var None) ls |> JSS_Block

  | MLE_App (e, args) ->
      let new_fv = ref [] in
      let is_If e = match e.expr with | MLE_If _ | MLE_Match _ -> true | _ -> false in
      let args = List.map (fun x -> if is_If x 
                                    then 
                                        let fv_x = Absyn.Util.gensym() in
                                        new_fv := List.append !new_fv 
                                                    [JSS_VariableDeclaration([(JGP_Identifier(fv_x, None), None)], JSV_Let); 
                                                     translate_expr x (fv_x, None) None];
                                        JSE_Identifier(fv_x, None)
                                     else
                                        translate_expr_pure x) args in
      let expr = 
      (match e.expr with
       | MLE_Name(["Prims"], op) when is_op_bin op ->
            JSE_Binary((must (mk_op_bin op)), List.nth args 0, List.nth args 1)
       | MLE_Name(["Prims"], op) when is_op_bool op ->
            JSE_Logical((must (mk_op_bool op)), List.nth args 0, List.nth args 1)
       | MLE_Name(["Prims"], op) when is_op_un op ->
            JSE_Unary((must (mk_op_un op)), List.nth args 0)
       | MLE_Name (path, function_name) ->      
            JSE_Call (getName(path, function_name), args)          
       | MLE_Var (name, _) ->
            JSE_Call (JSE_Identifier(name, None), args)       
       | _ -> failwith "todo: translation [MLE_App]") |> JSS_Expression in
       JSS_Block(!new_fv @ [expr])

  | _ -> failwith "todo: translation ml-expr"

and translate_expr_pure e: expression_t = 
  match e.expr with
  | MLE_Const c  ->
      translate_constant c

  | MLE_Var (name, _) ->
      JSE_Identifier(name, None)

  | MLE_Name(path, n) ->
      getName(path, n)

  | MLE_App (e, args) ->
      let args_t = List.map translate_expr_pure args in
      (match e.expr with
       | MLE_Name(["Prims"], op) when is_op_bin op ->
            JSE_Binary((must (mk_op_bin op)), List.nth args_t 0, List.nth args_t 1)
       | MLE_Name(["Prims"], op) when is_op_bool op ->
            JSE_Logical((must (mk_op_bool op)), List.nth args_t 0, List.nth args_t 1)
       | MLE_Name(["Prims"], op) when is_op_un op ->
            JSE_Unary((must (mk_op_un op)), List.nth args_t 0)
       | MLE_Name (path, function_name) ->      
            JSE_Call (getName(path, function_name), args_t)          
       | MLE_Var (name, _) ->
            JSE_Call (JSE_Identifier(name, None), args_t)       
       | _ -> failwith "todo: translation [MLE_App]")

  | MLE_Tuple lexp ->
      let create_fields = List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_" ^ Util.string_of_int i, None), translate_expr_pure x, JSO_Init)) lexp in
          JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Tuple", ""), JSO_Init);
                      JSPO_Property(JSO_Identifier("_arity", Some JST_Number), JSE_Literal(JSV_Number (float_of_int (List.length lexp)), ""), JSO_Init)] @
                      create_fields)

  | MLE_Record (path, fields) ->
      let create_fields = List.map (fun (id, x) -> JSPO_Property(JSO_Identifier("_" ^ id, None), translate_expr_pure x, JSO_Init)) fields in
          JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Record", ""), JSO_Init)] @
                      create_fields)

  | MLE_CTor ((path, c), lexpr) ->
      JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String c, ""), JSO_Init);
                  JSPO_Property(JSO_Identifier("_0", None), JSE_Array(Some (List.map (translate_expr_pure) lexpr)), JSO_Init)])

  | MLE_Fun (args, body) ->
      let args = List.map (fun ((n,_), _) -> JGP_Identifier(n, None)) args in
      JSE_ArrowFunction(None, args, JS_BodyExpression(translate_expr_pure body), None, None)

  | _ -> failwith "todo: translation ml-expr-pure"

and translate_match lb fv_x var : statement_t =
    match lb with 
    | [] -> JSS_Throw (JSE_Literal(JSV_String("This value doesn't match!"), ""))
    | (p, guard, expr_r) :: tl -> translate_pat_guard (p, guard) fv_x (translate_expr expr_r var None) (translate_match tl fv_x var)

and translate_pat_guard (p, guard) fv_x s1 s2: statement_t =
  match guard with   
  | None -> translate_pat p fv_x s1 s2
  | Some v_guard -> (*maybe add translation for case when v_guard isn't pure*)
      let cond_stmt = JSS_If(translate_expr_pure v_guard, s1, Some s2) in
          translate_pat p fv_x cond_stmt s2

and translate_pat p fv_x s1 s2: statement_t =
  match p with
  | MLP_Var (name, _) ->
      JSS_Block([JSS_VariableDeclaration([(JGP_Identifier(name, None), Some fv_x)], JSV_Let); s1])
  | MLP_Wild -> 
      s1
  | MLP_Const c ->
      JSS_If(JSE_Binary(JSB_Equal, fv_x, translate_constant c), s1, Some s2)
  | MLP_CTor((path, c), lp) ->
      let if_true =
        match lp with
        | [] -> s1
        | [x] -> translate_pat x (JSE_Member(JSE_Member(fv_x, JSPM_Identifier("_0", None)), 
                                                         JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 0), "")))) s1 s2
        | _ -> translate_p_ctor lp (JSE_Member(fv_x, JSPM_Identifier("_0", None))) s1 s2 in
      JSS_If(JSE_Binary(JSB_StrictEqual,
                        JSE_Member(fv_x, JSPM_Identifier("_tag", Some JST_String)),
                        JSE_Literal(JSV_String c, "")), if_true, Some s2)
  | MLP_Branch (lp) ->
      translate_p_branch lp fv_x s1 s2
  | MLP_Record (path, lp) ->
      translate_p_record lp fv_x s1 s2
  | MLP_Tuple lp ->
      translate_p_tuple lp 0 fv_x s1 s2

and translate_p_ctor lp fv_x s1 s2 : statement_t =
  match lp with
  | [x] -> translate_pat x fv_x s1 s2
  | hd::tl -> translate_pat hd (JSE_Member(fv_x, JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 0), ""))))
                               (translate_p_ctor tl (JSE_Member(fv_x, JSPM_Expression(JSE_Literal(JSV_Number(float_of_int 1), "")))) s1 s2) s2
  | [] -> failwith "Empty list in pattern matching"

and translate_p_tuple lp d fv_x s1 s2 : statement_t =
    match lp with
    | [x] -> translate_pat x (JSE_Member(fv_x, JSPM_Identifier("_" ^ string_of_int d, None))) s1 s2
    | hd :: tl -> translate_pat hd (JSE_Member(fv_x, JSPM_Identifier("_" ^ string_of_int d, None))) (translate_p_tuple tl (d+1) fv_x s1 s2) s2
    | [] -> failwith "Empty list in translate_p_tuple"
  
and translate_p_record lp fv_x s1 s2 : statement_t =
    match lp with
    | [x] -> translate_pat (snd x) (JSE_Member(fv_x, JSPM_Identifier("_" ^ (fst x), None))) s1 s2
    | hd :: tl -> translate_pat (snd hd) (JSE_Member(fv_x, JSPM_Identifier("_" ^ (fst hd), None))) (translate_p_record tl fv_x s1 s2) s2
    | [] -> failwith "Empty list in translate_p_record"

and translate_p_branch lp fv_x s1 s2 : statement_t =
    match lp with
    | [x] -> translate_pat x fv_x s1 s2
    | hd :: tl -> translate_pat hd fv_x s1 (translate_p_branch tl fv_x s1 s2)
    | [] -> failwith "Empty list in translate_p_branch"

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
      JST_Function([(("_1", None), t1_t)], t2_t, None)  (*we want to save the source names of function parameters*)
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
                           | _ -> List.map translate_type args |> Some 
                in JST_Generic (Unqualified(name, None), args))