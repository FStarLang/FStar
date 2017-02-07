#light "off"

module FStar.Extraction.JavaScript.PrintAst

open FStar.Extraction.JavaScript.Ast
open FStar.Format
open FStar.Util
open FStar

let semi = text ";"
let comma = text ","
let dot = text "."
let colon = text ":"
let ws = break1

let escape_or fallback = function
  | c when (c = '\\')            -> "\\\\"
  | c when (c = ' ' )            -> " "
  | c when (c = '\b')            -> "\\b"
  | c when (c = '\t')            -> "\\t"
  | c when (c = '\r')            -> "\\r"
  | c when (c = '\n')            -> "\\n"
  | c when (c = '\'')            -> "\\'"
  | c when (c = '\"')            -> "\\\""
  | c when (is_letter_or_digit c)-> string_of_char c
  | c when (is_punctuation c)    -> string_of_char c
  | c when (is_symbol c)         -> string_of_char c
  | c                            -> fallback c

let jstr_escape s = String.collect (escape_or string_of_char) s

(* don't use a prime for ident *)
let escape_char fallback = function
  | c when (c = '\'')            -> "_"
  | c when (is_letter_or_digit c)-> string_of_char c
  | c when (is_punctuation c)    -> string_of_char c
  | c when (is_symbol c)         -> string_of_char c
  | c                            -> fallback c

let remove_chars_t s = String.collect (escape_char string_of_char) s

let print_op_un = function
    | JSU_Minus -> text "-"
    | JSU_Not -> text "!"

let print_op_bin = function
    | JSB_Equal -> text "=="
    | JSB_NotEqual -> text "!="
    | JSB_LessThan -> text "<"
    | JSB_LessThanEqual -> text "<="
    | JSB_GreaterThan -> text ">"
    | JSB_GreaterThanEqual -> text ">="
    | JSB_Plus -> text "+"
    | JSB_Minus -> text "-"
    | JSB_Mult -> text "*"
    | JSB_Div -> text "/"
    | JSB_Mod -> text "%"
    | JSB_StrictEqual -> text "==="

let print_op_log = function
    | JSL_Or -> text "||"
    | JSL_And -> text "&&"

let keywords_js = [
    "abstract"; "arguments"; "boolean";	"break"; "byte";
    "case";	"catch"; "char"; "class"; "const"; "continue";
    "debugger"; "default"; "delete"; "do"; "double"; "else";
    "enum";	"eval";	"export"; "extends"; "false"; "final";
    "finally"; "float"; "for"; "function"; "goto"; "if";
    "implements"; "import"; "in"; "instanceof"; "int";
    "interface"; "let"; "long";	"native"; "new"; "null";
    "package"; "private"; "protected"; "public"; "return";
    "short"; "static"; "super"; "switch"; "synchronized";
    "this";	"throw"; "throws"; "transient";	"true"; "try";
    "typeof"; "var"; "void"; "volatile"; "while"; "with"; "yield" ]

let remove_chars s =
    if List.existsb (fun x -> s = x) keywords_js
    then
        let v = List.tryFind (fun x -> s = x) keywords_js in
        print1 "Warning: this name is a keyword in JavaScript: %s \n" (must v);
        reduce [text "_"; text (remove_chars_t s)]
    else text (remove_chars_t s)

let rec pretty_print (program:Ast.t) : doc =
    reduce ([text "/* @flow */"; hardline] @
        List.map (function | JS_Statement s ->
            (match s with
            | JSS_Block l -> pretty_print_statements l
            | _ -> pretty_print_statement s)) program)

and pretty_print_statement (p:statement_t) : doc =
  let optws (s:statement_t) =
    match s with
    | JSS_Block b -> pretty_print_statements b
    | _ -> pretty_print_statement s in
  match p with
    | JSS_Empty -> semi
    | JSS_Block l -> reduce [ws; text "{"; pretty_print_statements l; text "}"; hardline]
    | JSS_Expression e -> reduce [ws; pretty_print_exp e; semi; hardline]
    | JSS_If (c, t, f) ->
        reduce [ws; text "if"; parens (pretty_print_exp c); text "{"; hardline; optws t; text "}";
        (match f with | None -> empty | Some s -> reduce [ws; text "else"; text "{"; optws s; text "}"]); hardline]
    | JSS_TypeAlias ((id, _), lt, t) ->
        reduce [ws; text "type "; remove_chars id; print_decl_t lt; text "="; print_typ t; semi; hardline]
    | JSS_Return e ->
        reduce [ws; text "return"; (match e with | None -> empty | Some v -> reduce [ws; pretty_print_exp v]); semi; hardline]
    | JSS_Throw e -> reduce [ws; text "throw "; pretty_print_exp e; semi]
    | JSS_VariableDeclaration ((p, e), k) ->
        (match p with
        | JGP_Identifier (n, _) when n = "_" ->
            (match e with | Some v -> reduce [pretty_print_exp v; semi; hardline] | None -> empty)
        | _ -> reduce [print_kind_var k; print_pattern p true;
            (match e with | None -> empty | Some v -> reduce [text "="; pretty_print_exp v]); semi; hardline])
    | JSS_ExportDefaultDeclaration (d, k) ->
         (match d with
         | JSE_Declaration s ->
              (match s with
               | JSS_Block l -> reduce (List.map (fun x -> print_export_stmt x) l)
               | _ -> reduce [ text "export "; optws s; hardline])
         | JSE_Expression e -> reduce [ text "export "; pretty_print_exp e; hardline])
    | JSS_ImportDeclaration d ->
        reduce [text "import * as "; text (jstr_escape (fst d));
                text " from "; text "\"./"; text (jstr_escape (fst d)); text "\""; semi; hardline]
    | JSS_Seq l -> pretty_print_statements l

and pretty_print_statements l = reduce (List.map pretty_print_statement l)

and print_export_stmt s =
    (match s with
    | JSS_VariableDeclaration ((p, e), k) ->
       (match p with
        | JGP_Identifier (n, _) when n = "_" ->
            (match e with | Some v -> reduce [pretty_print_exp v; semi; hardline] | None -> empty)
        | _ -> reduce [text "export "; pretty_print_statement s; hardline])
    | _ -> reduce [text "export "; pretty_print_statement s; hardline])

and pretty_print_exp = function
    | JSE_Array l ->
        (match l with
        | Some v -> reduce [text "["; List.map pretty_print_exp v |> combine comma ; text "]"]
        | None -> reduce [text "["; text "]"])
    | JSE_Object l -> reduce [text "{"; List.map pretty_print_obj l |> combine comma; text "}"]
    | JSE_ArrowFunction (_, args, body, ret_t, decl_vars) ->
        reduce [print_decl_t decl_vars; print_arrow_fun args (print_body body) ret_t]
    | JSE_Unary (o, e) -> reduce [print_op_un o; pretty_print_exp e]
    | JSE_Binary (o, e1, e2) -> reduce [text "("; pretty_print_exp e1; print_op_bin o; pretty_print_exp e2; text ")"]
    | JSE_Assignment (p, e) ->
        (match p with
        | JGP_Identifier (n, _) when n = "_" -> pretty_print_exp e
        | _ -> reduce [print_pattern p false; text "="; pretty_print_exp e])
    | JSE_Logical (o, e1, e2) ->  reduce [pretty_print_exp e1; print_op_log o; pretty_print_exp e2]
    | JSE_Call (e, l) ->
        let le = List.map (fun x -> parens (pretty_print_exp x)) l |> combine empty in
        reduce [pretty_print_exp e; (match l with | [] -> text "()" | _ -> le)]
    | JSE_Member (o, p) ->  reduce [pretty_print_exp o; pretty_print_propmem p]
    | JSE_Identifier (id, t) -> remove_chars id
    | JSE_Literal l -> print_literal l
    | JSE_TypeCast (e, t) -> reduce [ text "("; pretty_print_exp e; colon; print_typ t; text ")"]

and print_decl_t lt =
    match lt with
    | Some l -> reduce [text "<"; List.map (fun s -> remove_chars s) l |> combine comma; text ">"]
    | None -> empty

and print_arrow_fun args body ret_t =
    let ret_t = (match ret_t with | None -> empty | Some v -> reduce [colon; parens (print_typ v)]) in
    print_arrow_fun_p args body ret_t true

(* print a return type once *)
and print_arrow_fun_p args body ret_t print_ret_t =
    let ret_t = (if print_ret_t then ret_t else empty) in
    match args with
    | [] -> reduce [text "()"; text "=>"; body]
    | [x] -> reduce [parens (print_pattern x true); ret_t; text "=>";  body]
    | hd :: tl -> reduce [parens (print_pattern hd true); ret_t; text "=>"; parens (print_arrow_fun_p tl body ret_t false)]
       
and pretty_print_obj el =
    match el with
    | JSPO_Property(k, e, _) -> reduce [ pretty_print_prop_key k; text ":"; pretty_print_exp e]
    | JSPO_SpreadProperty e -> pretty_print_exp e

and pretty_print_prop_key k =
    match k with 
    | JSO_Literal l -> print_literal l
    | JSO_Identifier (id, t) -> text (jstr_escape id)
    | JSO_Computed e -> pretty_print_exp e

and pretty_print_propmem p = 
    match p with
    | JSPM_Identifier (i, t) -> reduce [ text "."; text (jstr_escape i)]
    | JSPM_Expression e -> reduce [ text "["; pretty_print_exp e; text "]"] 

and print_typ = function
    | JST_Any -> text "any"
    | JST_Void -> text "void"
    | JST_Null -> text "null"
    | JST_Number -> text "number"
    | JST_String -> text "string"
    | JST_Boolean -> text "boolean"
    | JST_Function (args, ret_t, decl_vars) -> reduce [print_decl_t decl_vars; print_fun_typ args ret_t]
    | JST_Object lp ->
        reduce [text "{"; List.map (fun (k, t) ->
            reduce [pretty_print_prop_key k; text ":"; print_typ t]) lp |> combine comma; text "}"]
    | JST_Array t -> reduce [text "Array"; text "<"; print_typ t; text ">"]
    | JST_Union l ->  reduce [List.map print_typ l |> combine (text "|")]
    | JST_Intersection l -> reduce [List.map print_typ l |> combine (text "&")]
    | JST_Tuple lt -> reduce [text "["; List.map (print_typ) lt |> combine comma; text "]"]
    | JST_StringLiteral (s,_) -> text ("\"" ^ (jstr_escape s) ^ "\"")
    | JST_Generic(n, lt) ->
        let print_lt = 
            match lt with
            | None -> empty 
            | Some v -> reduce [text "<"; List.map print_typ v |> combine comma; text ">"]
        in reduce [remove_chars n; print_lt]

and print_fun_typ args ret_t  =
    let print_arg ((id,_), t) = reduce [text (jstr_escape id); colon; print_typ t] in
    (match args with
    | [] -> reduce [text "()"; text "=>"; print_typ ret_t]
    | [x] -> reduce [parens (print_arg x); text "=>"; parens (print_typ ret_t)]
    | hd :: tl -> reduce [parens (print_arg hd); text "=>"; parens (print_fun_typ tl ret_t)])

and print_literal (v, s) =
    match (v, s) with
    | (JSV_String s, _) -> text ("\"" ^ (jstr_escape s) ^ "\"")
    | (JSV_Boolean b, _) -> text (string_of_bool b)
    | (JSV_Null, _) -> text "null"
    | (JSV_Number f, s) -> text s

and print_kind_var = function
    | JSV_Var -> text "var "
    | JSV_Let -> text "let "
    | JSV_Const -> text "const "

and print_pattern p print_t =
    match p with
    | JGP_Expression e -> pretty_print_exp e
    | JGP_Identifier (id, t) ->
        let r = match t with | Some v -> reduce [colon; print_typ v] | None -> empty
        in reduce [remove_chars id; (if print_t then r else empty)]

and print_body = function 
    | JS_BodyBlock l -> reduce [text "{"; hardline; pretty_print_statements l; text "}"]
    | JS_BodyExpression e -> parens (pretty_print_exp e)