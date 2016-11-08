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

let rec get_Generic t =
  begin
    match t with
    | JST_Generic (g, v) ->
        (match v with
        | Some v1 -> List.collect get_Generic v1
        | None ->
            (match g with
            | Unqualified (id, _) -> if String.get id 0 = '\'' then [id] else []
            | _ -> []))
    | JST_Function (_, _, gen_d) ->
        (match gen_d with
        | Some v -> v
        | None -> [])
    | JST_Tuple lt -> List.collect get_Generic lt
    | JST_Object (l, _, _) -> List.collect (fun (_, t) -> get_Generic t) l
    | _ -> []
  end

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
            begin
            if (not pt) then None
            else match tys with
                 | None -> None
                 | Some ([], ty) -> translate_type ty |> Some
                 | Some (lp, ty) ->
                    (match ty with
                     | MLTY_Fun (t1, _, t2) ->
                        let lp = match lp with
                                 | [] -> None
                                 | _ -> List.map (fun (id, _) -> id) lp |> Some in
                        if unit_b then None
                        else JST_Function([(("_1", None), translate_type t1)], translate_type t2, lp) |> Some
                     | _ -> None)
            end in        
        let is_private = List.contains Private c_flag in        
        if is_pure_expr expr (name, None)
        then
            let c = JSS_VariableDeclaration((JGP_Identifier(name, t), Some (translate_expr_pure expr)), JSV_Let) in
            if is_private then [c] else [JSS_ExportDefaultDeclaration(JSE_Declaration(c), ExportValue)]
        else
            let c = JSS_VariableDeclaration((JGP_Identifier(name, t), None), JSV_Let) in
            let c1 = translate_expr expr (name, t) None in
            if is_private then [c; c1] else [JSS_ExportDefaultDeclaration(JSE_Declaration(c), ExportValue); c1]
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
        | MLTD_Abbrev t -> 
            JSS_TypeAlias((name, None), tparams, translate_type t)
        | MLTD_Record fields ->
            let tag = [(JSO_Identifier("_tag", None), JST_StringLiteral("Record", ""))] in
            let fields_t = List.map (fun (n, t) -> (JSO_Identifier("_" ^ n, None), translate_type t)) fields in
            JSS_TypeAlias((name, None), tparams, JST_Object(tag @ fields_t, [], []))
        | MLTD_DType lfields ->
            let tag n = [(JSO_Identifier("_tag", None), JST_StringLiteral(n, ""))] in
            let fields_t fields = List.mapi (fun i t -> (JSO_Identifier("_" ^ string_of_int i, None), translate_type t)) fields in
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
  | x when is_pure_expr e var ->
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_expr_pure e)) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Let ((_, _,  [{
      mllb_name = name, _;
      mllb_tysc = tys;
      mllb_add_unit = add_unit;
      mllb_def = body;
      print_typ = pt
      }]), continuation) ->
      if is_pure_expr body (name, None)
      then
        [JSS_VariableDeclaration((JGP_Identifier(name, None), Some (translate_expr_pure body)), JSV_Let);
         translate_expr continuation var stmt] |> JSS_Block
      else
        translate_expr body (name, None) (Some (translate_expr continuation var stmt))

  | MLE_Let _ ->
      failwith "todo: translate_expr [MLE_Let]"

  | MLE_Fun (args, body) ->
      let generic_t = ref [] in
      let addUnique lst =
        List.map (fun el ->
            if not (List.existsb (fun x -> x = el) !generic_t)
            then generic_t := List.append [el] !generic_t) lst in
      let args =
        List.map (fun ((n,_), t) ->
            let t = translate_type t in
            addUnique (get_Generic t) |> ignore;
            JGP_Identifier(n, Some t)) args in
      let generic_r = (match !generic_t with | [] -> None | _ -> Some !generic_t) in
      let body_t =
        begin
        if is_pure_expr body var
        then JS_BodyExpression(translate_expr_pure body)
        else JS_BodyBlock([JSS_VariableDeclaration((JGP_Identifier("_res", None), None), JSV_Let);
                          translate_expr body ("_res", None) (Some(JSS_Return(Some(JSE_Identifier("_res", None)))))])
        end in
      let ret_t =
        (match (snd var) with
         | None -> None
         | Some v -> match v with | JST_Function (_, t2, _) -> Some t2 | _ -> None) in
      let c = JSS_Expression(JSE_Assignment(JGP_Identifier(var), JSE_ArrowFunction(None, args, body_t, ret_t, generic_r))) in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_If(cond, s1, s2) ->
      let s2 = (match s2 with | Some v -> Some (translate_expr v var None) | None -> None) in
      let c =
        if is_pure_expr cond var
        then 
            JSS_If(translate_expr_pure cond, translate_expr s1 var None, s2)
        else
            [JSS_VariableDeclaration((JGP_Identifier("_cond", Some (JST_Boolean)), None), JSV_Let);
             translate_expr cond ("_cond", None) (Some (JSS_If(JSE_Identifier("_cond", Some JST_Boolean), translate_expr s1 var None, s2)))] |> JSS_Block in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Raise _ ->
      failwith "todo: translate_expr [MLE_Raise]"

  | MLE_Try _ ->
      failwith "todo: translate_expr [MLE_Try]"

  | MLE_Coerce(in_e, t_from, t_to) ->
      let var = (fst var, Some (translate_type in_e.mlty)) in
      translate_expr in_e var stmt

  | MLE_Match(e_in, lb) ->
      let c =
        if is_pure_expr e_in var
        then 
            translate_match lb (translate_expr_pure e_in) var
        else
            [JSS_VariableDeclaration((JGP_Identifier("_match_e", None), None), JSV_Let);
             translate_expr e_in ("_match_e", None) (Some (translate_match lb (JSE_Identifier("_match_e", None)) var))] |> JSS_Block in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_Seq ls ->
      let rec translate_seq l =
        match l with
        | [] -> failwith "Empty list in [MLE_Seq]"
        | [x] -> translate_expr x var None
        | hd :: tl -> translate_expr hd ("_", None) (Some(translate_seq tl)) in
      let c = translate_seq ls in
      (match stmt with | Some v -> JSS_Block([c; v]) | None -> c)

  | MLE_App (e, args) ->
      let new_fv = ref [] in
      let args = create_pure_args new_fv args var in
      let stmt = match stmt with | Some v -> [v] | None -> [] in
      let expr =
        if (fst var = "_res")
        then [JSS_Expression(JSE_Assignment(JGP_Identifier(var), translate_arg_app e args var))] @ stmt
        else [JSS_Block([JSS_VariableDeclaration((JGP_Identifier(var), Some(translate_arg_app e args var)), JSV_Let)] @ stmt)] in
      JSS_Block(!new_fv @ expr)

  | MLE_CTor ((path, c), lexpr) ->
      let new_fv = ref [] in
      let lexpr = create_pure_args new_fv lexpr var in
      let expr = 
        (match c with
        | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims._mk_" ^ c, None), lexpr)
        | _ -> JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String c, ""), JSO_Init)] @
                           List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_" ^ string_of_int i, None), x, JSO_Init)) lexpr)) in
      let expr = JSS_Expression(JSE_Assignment(JGP_Identifier(var), expr)) in
      let stmt = match stmt with | Some v -> [v] | None -> [] in
      JSS_Block(!new_fv @ [JSS_Block([expr] @ stmt)])

  | MLE_Record (path, fields) ->
      let new_fv = ref [] in
      let create_fields =
        List.map (fun (id, x) -> JSPO_Property(JSO_Identifier("_" ^ id, None), List.nth (create_pure_args new_fv [x] var) 0, JSO_Init)) fields in
      let expr = JSS_Expression(JSE_Assignment(JGP_Identifier(var),
                    JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Record", ""), JSO_Init)] @
                                create_fields))) in
      let stmt = match stmt with | Some v -> [v] | None -> [] in
      JSS_Block(!new_fv @ [JSS_Block([expr] @ stmt)])

  | MLE_Tuple lexp ->
      let new_fv = ref [] in
      let create_fields =
        List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_" ^ string_of_int i, None), List.nth (create_pure_args new_fv [x] var) 0, JSO_Init)) lexp in
      let expr = JSS_Expression(JSE_Assignment(JGP_Identifier(var),     
                    JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Tuple", ""), JSO_Init);
                                JSPO_Property(JSO_Identifier("_arity", Some JST_Number), JSE_Literal(JSV_Number (float_of_int (List.length lexp)), ""), JSO_Init)] @
                                create_fields))) in
      let stmt = match stmt with | Some v -> [v] | None -> [] in
      JSS_Block(!new_fv @ [JSS_Block([expr] @ stmt)])

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
                | MLE_Var _ -> [JSS_VariableDeclaration((JGP_Identifier(fv_x, None), Some (translate_expr_pure x)), JSV_Let)]
                | _ -> [JSS_VariableDeclaration((JGP_Identifier(fv_x, None), None), JSV_Let); translate_expr x (fv_x, None) None]) in
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
      let create_fields = List.mapi (fun i x -> JSPO_Property(JSO_Identifier("_" ^ string_of_int i, None), translate_expr_pure x, JSO_Init)) lexp in
        JSE_Object([JSPO_Property(JSO_Identifier("_tag", Some JST_String), JSE_Literal(JSV_String "Tuple", ""), JSO_Init);
                    JSPO_Property(JSO_Identifier("_arity", Some JST_Number), JSE_Literal(JSV_Number (float_of_int (List.length lexp)), ""), JSO_Init)] @
                    create_fields)

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
      | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims._mk_" ^ c, None), List.map translate_expr_pure lexpr)
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
      JSS_Block([JSS_VariableDeclaration((JGP_Identifier(name, None), Some fv_x), JSV_Let); s1])

  | MLP_Wild ->
      s1

  | MLP_Const c ->
      JSS_If(JSE_Binary(JSB_Equal, fv_x, translate_constant c), s1, Some s2)

  | MLP_CTor((path, c), lp) ->
      let rec translate_p_ctor lp fv_x s1 s2 i =
        let new_fv_x =
            match c with
            | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims._get_" ^ c ^ "_" ^ string_of_int i, None), [fv_x])
            | _ -> JSE_Member(fv_x, JSPM_Identifier("_" ^ string_of_int i, None)) in
       (match lp with
        | [] -> s1
        | [x] -> translate_pat x new_fv_x s1 s2
        | hd::tl -> translate_pat hd new_fv_x (translate_p_ctor tl fv_x s1 s2 (i+1)) s2)
      in
        let if_cond =
            match c with
            | x when is_prim_constructors x -> JSE_Call (JSE_Identifier("Prims._is_" ^ c, None), [fv_x])
            | _ -> JSE_Binary(JSB_StrictEqual, JSE_Member(fv_x, JSPM_Identifier("_tag", Some JST_String)), JSE_Literal(JSV_String c, ""))
        in JSS_If(if_cond, translate_p_ctor lp fv_x s1 s2 0, Some s2)

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
        let new_fv_x = JSE_Member(fv_x, JSPM_Identifier("_" ^ string_of_int d, None)) in
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
      let t1_t = translate_type t1 in
      let t2_t = translate_type t2 in
      let generic_t = ref [] in
      let addUnique lst =
        List.map (fun el -> 
            if not (List.existsb (fun x -> x = el) !generic_t)
            then generic_t := List.append [el] !generic_t) lst in
      addUnique (get_Generic t1_t) |> ignore;
      addUnique (get_Generic t2_t) |> ignore;
      let generic_r = (match !generic_t with | [] -> None | _ -> Some !generic_t) in
      JST_Function([(("_1", None), t1_t)], t2_t, generic_r)  (*we want to save the source names of function parameters*)
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
                let args_t = 
                    match args with
                    | [] -> None
                    | _ -> List.map translate_type args |> Some
                in
                   JST_Generic (Unqualified(getName (path, name)), args_t))