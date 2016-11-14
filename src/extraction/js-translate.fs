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
  | "op_Bang" ->
      failwith "todo: translation [!]"
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

let is_prim_constructors s =
    List.existsb (fun x -> x = s) ["Cons" ; "Nil"; "Some"; "None"]
    
let float_of_int i = float_of_int32 (int32_of_int i)

let export_modules = ref []

let current_module_name = ref ""

let lp_generic = ref []

let isEqVar = ref false

let getName (path, n) =
  let path = String.concat "_" path in
  if (path = !current_module_name || path = "")
  then (n, None)
  else ((if not (List.existsb (fun x -> x = path) !export_modules)
         then export_modules := List.append [path] !export_modules);
         (path ^ "." ^ n, None))

let rec is_pure_expr e var =
  match e.expr with
  | MLE_Const _ | MLE_Name _ -> true
  | MLE_Var (n, _) -> n <> fst var
  | MLE_Proj(expr, _) -> is_pure_expr expr var
  | MLE_CTor (p, le) ->
      not (List.contains false (List.map (fun x -> is_pure_expr x var) le))
  | MLE_Tuple le ->
      not (List.contains false (List.map (fun x -> is_pure_expr x var) le))
  | MLE_Record (_, lne) ->
      not (List.contains false (List.map (fun (n, e) -> is_pure_expr e var) lne))
  | MLE_App (_, args) ->
      not (List.contains false (List.map (fun x -> is_pure_expr x var) args))
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
      export_modules := [];
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
        let create_module_imports =
            List.map (fun m -> JSS_ImportDeclaration (m, None)) (!export_modules)
                |> JSS_Block |> JS_Statement
        in [create_module_imports] @ res
    | _ ->
        failwith "Unexpected standalone interface or nested modules"
  in
  (String.concat "_" module_name), program

and translate_decl d: option<source_t> =
  match d with
  | MLM_Let (_, c_flag,  lfunc) ->
      let for1 { mllb_name = name, _; mllb_tysc = tys; mllb_def = expr; print_typ=pt; mllb_add_unit = unit_b} =
        let t =
            lp_generic:= [];
            if (not pt) || unit_b then None
            else match tys with
                 | None -> None
                 | Some (lp, ty) -> lp_generic:= List.map (fun (id, _) -> id) lp; translate_type ty |> Some in
        let is_private = List.contains Private c_flag in
        let c =
            if is_pure_expr expr (name, None)
            then [JSS_VariableDeclaration((JGP_Identifier(name, t), Some(translate_expr_pure expr)), JSV_Let)]
            else translate_expr expr (name, t) None false in
        if is_private then c else [JSS_ExportDefaultDeclaration(JSE_Declaration(JSS_Block(c)), ExportValue)]
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
        let get_export stmt = 
            (JSE_Declaration(stmt), ExportType) |> JSS_ExportDefaultDeclaration in
        match body with
        | MLTD_Abbrev t ->
            get_export (JSS_TypeAlias((name, None), tparams, translate_type t))
        | MLTD_Record fields ->
            let tag = [(JSO_Identifier("_tag", None), JST_StringLiteral("Record", ""))] in
            let fields_t = List.map (fun (n, t) -> (JSO_Identifier("_" ^ n, None), translate_type t)) fields in
            get_export (JSS_TypeAlias((name, None), tparams, JST_Object(tag @ fields_t, [], [])))
        | MLTD_DType lfields ->
            let tag n = [(JSO_Identifier("_tag", None), JST_StringLiteral(n, ""))] in
            let fields_t fields = List.mapi (fun i t -> (JSO_Identifier("_" ^ string_of_int i, None), translate_type t)) fields in
            let lfields_t = List.map (fun (n, l) -> get_export(JSS_TypeAlias((n, None), tparams, JST_Object((tag n) @ fields_t l, [], [])))) lfields in
            let tparams_gen =
                match tparams with
                | Some t -> List.map (fun x -> JST_Generic(Unqualified(x, None), None)) t |> Some
                | None -> None in
            let lnames = List.map (fun (n,l) -> JST_Generic(Unqualified(n, None), tparams_gen)) lfields in
            let union_t = get_export(JSS_TypeAlias((name, None), tparams, JST_Union(lnames))) in
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

and translate_expr e var lstmt isDecl: list<statement_t> =
  let get_res expr new_fv =
    let lstmt = (match lstmt with | Some v -> v | None -> []) in
    let expr =
        if isDecl
        then JSS_Expression(JSE_Assignment(JGP_Identifier(var), expr))
        else JSS_VariableDeclaration((JGP_Identifier(var), Some(expr)), JSV_Let)
    in (match new_fv with
        | Some v -> if !isEqVar
                    then (isEqVar := false;
                         !v @ [JSS_Block([expr] @ lstmt)])
                    else !v @ [expr] @ lstmt
        | None -> [expr] @ lstmt) in
    
  match e.expr with
  | x when is_pure_expr e var ->
      let expr = translate_expr_pure e in
      get_res expr None

  | MLE_Let ((_, _,  [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_add_unit = add_unit;
      mllb_def = body;
      print_typ = pt
      }]), continuation) ->
      let c = translate_expr continuation var lstmt isDecl in
      if is_pure_expr body (name, None)
      then
        [JSS_VariableDeclaration((JGP_Identifier(name, None), Some (translate_expr_pure body)), JSV_Let);
        JSS_Block(c)]
      else
        translate_expr body (name, None) (Some c) false

  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"

  | MLE_Fun (args, body) ->
      let args = List.map (fun ((n,_), t) -> JGP_Identifier(n, Some (translate_type t))) args in
      let generic_t = (match !lp_generic with | [] -> None | _ -> Some !lp_generic) in
      let body_t =
        if is_pure_expr body var
        then JS_BodyExpression(translate_expr_pure body)
        else JS_BodyBlock([JSS_VariableDeclaration((JGP_Identifier("_res", None), None), JSV_Let)] @
                           translate_expr body ("_res", None) (Some([JSS_Return(Some(JSE_Identifier("_res", None)))])) true) in
      let ret_t =
        (match (snd var) with
         | None -> None
         | Some v -> match v with | JST_Function (_, t2, _) -> Some t2 | _ -> None) in
      let expr = JSE_ArrowFunction(None, args, body_t, ret_t, generic_t) in
      let lstmt = (match lstmt with | Some v -> v | None -> []) in
      let expr =
        if isDecl
        then [JSS_Expression(JSE_Assignment(JGP_Identifier(fst var, None), expr))]
        else [JSS_VariableDeclaration((JGP_Identifier(fst var, None), Some(expr)), JSV_Let)] in
      expr @ lstmt

  | MLE_If(cond, s1, s2) ->
      let s1 = JSS_Block(translate_expr s1 var None true) in
      let s2 = (match s2 with | Some v -> Some (JSS_Block(translate_expr v var None true)) | None -> None) in
      let c =
        if is_pure_expr cond var
        then
            [JSS_If(translate_expr_pure cond, s1, s2)]
        else
            [JSS_VariableDeclaration((JGP_Identifier("_cond", Some (JST_Boolean)), None), JSV_Let)] @
             translate_expr cond ("_cond", None) (Some [JSS_If(JSE_Identifier("_cond", Some JST_Boolean), s1, s2)]) true in
      let c =
        if isDecl then c
        else [JSS_VariableDeclaration((JGP_Identifier(var), None), JSV_Let)] @ c in
      (match lstmt with | Some v -> c @ v | None -> c)

  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"

  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

  | MLE_Coerce(in_e, t_from, t_to) ->
      let var = (fst var, Some (translate_type in_e.mlty)) in
      translate_expr in_e var lstmt false

  | MLE_Match(e_in, lb) ->
      let c =
        if is_pure_expr e_in var
        then
            [JSS_VariableDeclaration((JGP_Identifier("_match_e", None), Some(translate_expr_pure e_in)), JSV_Let);
             translate_match lb (JSE_Identifier("_match_e", None)) var]
        else
            [JSS_VariableDeclaration((JGP_Identifier("_match_e", None), None), JSV_Let)] @
             translate_expr e_in ("_match_e", None) (Some [translate_match lb (JSE_Identifier("_match_e", None)) var]) true in
      let c =
        if isDecl then c
        else [JSS_VariableDeclaration((JGP_Identifier(var), None), JSV_Let)] @ c in
      (match lstmt with | Some v -> c @ v | None -> c)

  | MLE_Seq ls ->
      let rec translate_seq l =
        match l with
        | [] -> failwith "Empty list in [MLE_Seq]"
        | [x] -> translate_expr x var None isDecl
        | hd :: tl -> translate_expr hd ("_", None) (Some(translate_seq tl)) false in
      let c = translate_seq ls in
      (match lstmt with | Some v -> c @ v | None -> c)

  | MLE_App (e, args) ->
      let new_fv = ref [] in
      let args = create_pure_args new_fv args var in
      let expr = translate_arg_app e args var in
      get_res expr (Some new_fv)
     
  | MLE_CTor ((path, c), lexpr) ->
      let new_fv = ref [] in
      let lexpr = create_pure_args new_fv lexpr var in
      let expr =
        (match c with
        | x when x = "Cons" || x = "Nil" ->
            (match lexpr with
            | [] -> JSE_Array(None)
            | hd :: tl -> JSE_Call (JSE_Member(JSE_Array(Some [hd]), JSPM_Identifier("concat", None)), tl))
        | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims.mk_" ^ c, None), lexpr)
        | _ -> JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String c, ""), JSO_Init)] @
                           List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_" ^ string_of_int i, None), x, JSO_Init)) lexpr)) in
      get_res expr (Some new_fv)

  | MLE_Record (path, fields) ->
      let new_fv = ref [] in
      let create_fields =
        List.map (fun (id, x) -> JSPO_Property(JSO_Identifier("_" ^ id, None), List.nth (create_pure_args new_fv [x] var) 0, JSO_Init)) fields in
      let expr = JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Record", ""), JSO_Init)] @
                            create_fields) in
      get_res expr (Some new_fv)

  | MLE_Tuple lexp ->
      let new_fv = ref [] in
      let create_fields = List.map (fun x -> List.nth (create_pure_args new_fv [x] var) 0) lexp in
      let expr = JSE_Array(Some (create_fields)) in
      get_res expr (Some new_fv)

  | _ -> failwith "todo: translation ml-expr"

and create_pure_args new_fv args var =
  List.map (fun x ->
    match x.expr with
    | MLE_CTor ((path, c), _) when c = "Nil" || c = "None" ->
        JSE_TypeCast(translate_expr_pure x, translate_type x.mlty)
    | _ ->
        if is_pure_expr x var
        then translate_expr_pure x
        else
            let fv_x = Absyn.Util.gensym() in
            let c =
                (match x.expr with
                | MLE_Var _ -> ( isEqVar:= true; [JSS_VariableDeclaration((JGP_Identifier(fv_x, None), Some (translate_expr_pure x)), JSV_Let)])
                | _ -> translate_expr x (fv_x, None) None false) in
            new_fv := List.append !new_fv c;
            JSE_Identifier(fv_x, None)) args

and translate_arg_app e args var: expression_t =
  match e.expr with
  | MLE_Name(["Prims"], op) when is_op_bin op ->
      JSE_Binary((must (mk_op_bin op)), List.nth args 0, List.nth args 1)
  | MLE_Name(["Prims"], op) when is_op_bool op ->
      JSE_Logical((must (mk_op_bool op)), List.nth args 0, List.nth args 1)
  | MLE_Name(["Prims"], op) when is_op_un op ->
      JSE_Unary((must (mk_op_un op)), List.nth args 0)
  | MLE_Name (path, function_name) ->
      JSE_Call (JSE_Identifier(getName(path, function_name)), args)
  | MLE_Var (name, _) ->
      JSE_Call (JSE_Identifier(name, None), args)
  | _ ->
      if is_pure_expr e var
      then JSE_Call (translate_expr_pure e, args)
      else failwith "todo: translation [MLE_App]"

and translate_expr_pure e: expression_t =
  match e.expr with
  | MLE_Const c  ->
      translate_constant c

  | MLE_Var (name, _) ->
      JSE_Identifier(name, None)

  | MLE_Name(path, n) ->
      JSE_Identifier(getName(path, n))

  | MLE_Tuple lexp ->
      JSE_Array(Some (List.map translate_expr_pure lexp))

  | MLE_Record (path, fields) ->
      let create_fields = List.map (fun (id, x) -> JSPO_Property(JSO_Identifier("_" ^ id, None), translate_expr_pure x, JSO_Init)) fields in
        JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Record", ""), JSO_Init)] @
                    create_fields)

  | MLE_CTor ((path, c), lexpr) ->
      (match c with
      | x when x = "Cons" || x = "Nil" ->
            (match lexpr with
            | [] -> JSE_Array(None)
            | hd :: tl -> JSE_Call (JSE_Member(JSE_Array(Some [translate_expr_pure hd]), JSPM_Identifier("concat", None)), List.map translate_expr_pure tl))
      | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims.mk_" ^ c, None), List.map translate_expr_pure lexpr)
      | _ ->  JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String c, ""), JSO_Init)] @
                   List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_" ^ string_of_int i, None), translate_expr_pure x, JSO_Init)) lexpr))

  | MLE_Coerce (e, _, _) -> translate_expr_pure e  (*!!*)

  | MLE_App (e, args) ->
      let args = List.map ( fun x ->
        match x.expr with
        | MLE_CTor ((path, c), _) when c = "Nil" || c = "None" ->
            JSE_TypeCast(translate_expr_pure x, translate_type x.mlty)
        | _ -> translate_expr_pure x) args
      in translate_arg_app e args ("", None)

  | MLE_Proj (expr, (path, name)) ->
      JSE_Member(translate_expr_pure expr, JSPM_Identifier("_" ^ name, None))
   
  | _ -> failwith "todo: translation ml-expr-pure"

and translate_match lb fv_x var : statement_t =
  match lb with
  | [] -> JSS_Throw (JSE_Literal(JSV_String("This value doesn't match!"), ""))
  | (p, guard, expr_r) :: tl -> translate_pat_guard (p, guard) fv_x (JSS_Block(translate_expr expr_r var None true)) (translate_match tl fv_x var)

and translate_pat_guard (p, guard) fv_x s1 s2: statement_t =
  match guard with
  | None -> translate_pat p fv_x s1 s2
  | Some v_guard -> (*maybe add translation for case when v_guard isn't pure*)
      let cond_stmt = JSS_If(translate_expr_pure v_guard, s1, Some s2) in
          translate_pat p fv_x cond_stmt s2

and translate_pat p fv_x s1 s2: statement_t =
  match p with
  | MLP_Var (name, _) ->
      JSS_Block([JSS_VariableDeclaration((JGP_Identifier(name, None), Some fv_x), JSV_Let); s1])

  | MLP_Wild ->
      s1

  | MLP_Const c ->
      JSS_If(JSE_Binary(JSB_Equal, fv_x, translate_constant c), s1, Some s2)

  | MLP_CTor((path, c), lp) ->
      let rec translate_p_ctor lp fv_x s1 s2 i =
        let new_fv_x =
            match c with
            | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims.get_" ^ c ^ "_" ^ string_of_int i, None), [fv_x])
            | _ -> JSE_Member(fv_x, JSPM_Identifier("_" ^ string_of_int i, None)) in
       (match lp with
        | [] -> s1
        | [x] -> translate_pat x new_fv_x s1 s2
        | hd::tl -> translate_pat hd new_fv_x (translate_p_ctor tl fv_x s1 s2 (i+1)) s2)
      in
        begin
        match c with
        | x when is_prim_constructors x ->
            let if_cond = JSE_Call (JSE_Identifier("Prims.is_" ^ c, None), [fv_x]) in
            JSS_If(if_cond, translate_p_ctor lp fv_x s1 s2 0, Some s2)
        | _ ->
            let isSimple = (match fv_x with |JSE_Identifier _ -> true | _ -> false) in
            if isSimple
            then
                let if_cond = JSE_Binary(JSB_StrictEqual, JSE_Member(fv_x, JSPM_Identifier("_tag", Some JST_String)), JSE_Literal(JSV_String c, "")) in
                JSS_If(if_cond, translate_p_ctor lp fv_x s1 s2 0, Some s2)
            else
                let new_name = Absyn.Util.gensym() in
                let if_cond = 
                    JSE_Binary(JSB_StrictEqual, JSE_Member(JSE_Identifier(new_name, None), JSPM_Identifier("_tag", Some JST_String)), JSE_Literal(JSV_String c, "")) in
                JSS_Block[JSS_VariableDeclaration((JGP_Identifier(new_name, None), Some fv_x), JSV_Let);
                          JSS_If(if_cond, translate_p_ctor lp (JSE_Identifier(new_name, None)) s1 s2 0, Some s2)]
        end
  | MLP_Branch (lp) ->
      let rec translate_p_branch lp fv_x s1 s2 =
        (match lp with
        | [] -> failwith "Empty list in translate_p_branch"
        | [x] -> translate_pat x fv_x s1 s2
        | hd :: tl -> translate_pat hd fv_x s1 (translate_p_branch tl fv_x s1 s2))
      in translate_p_branch lp fv_x s1 s2

  | MLP_Record (path, lp) ->
      let rec translate_p_record lp fv_x s1 s2 =
        let new_fv_x n = JSE_Member(fv_x, JSPM_Identifier("_" ^ n, None)) in
            (match lp with
            | [] -> failwith "Empty list in translate_p_record"
            | [x] -> translate_pat (snd x) (new_fv_x (fst x)) s1 s2
            | hd :: tl -> translate_pat (snd hd) (new_fv_x (fst hd)) (translate_p_record tl fv_x s1 s2) s2)
      in translate_p_record lp fv_x s1 s2

  | MLP_Tuple lp ->
      let rec translate_p_tuple lp d fv_x s1 s2 =
        let new_fv_x = JSE_Member(fv_x, JSPM_Expression(JSE_Literal(JSV_Number(float_of_int d), ""))) in
            (match lp with
            | [] -> failwith "Empty list in translate_p_tuple"
            | [x] -> translate_pat x new_fv_x s1 s2
            | hd :: tl -> translate_pat hd new_fv_x (translate_p_tuple tl (d+1) fv_x s1 s2) s2)
      in translate_p_tuple lp 0 fv_x s1 s2
      
and translate_constant c: expression_t =
  match c with
  | MLC_Unit ->
      JSE_Literal(JSV_Null, "")
  | MLC_Bool b ->
      JSE_Literal(JSV_Boolean b, "")
  | MLC_Int (s, _) ->
      JSE_Literal(JSV_Number (float_of_int (int_of_string s)), s)
  | MLC_Float f ->
      JSE_Literal(JSV_Number f, string_of_float f)
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
      (*we want to save the source names of function parameters*)
      JST_Function([(("_1", None), translate_type t1)], translate_type t2, None)
  | MLTY_Named (args, (path, name)) ->
      if is_standart_type name
      then must (mk_standart_type name)
      else (if Option.isSome (Util.is_xtuple_ty (path, name))
           then
                JST_Tuple(List.map translate_type args)
           else
                let args_t =
                    match args with
                    | [] -> None
                    | _ -> List.map translate_type args |> Some
                in
                   JST_Generic (Unqualified(getName (path, name)), args_t))