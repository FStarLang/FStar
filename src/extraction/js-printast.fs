#light "off"

module FStar.Extraction.JavaScript.PrintAst

open FStar.Extraction.JavaScript.Ast
open System
open System.Text
open FStar.Format
open FStar.Util

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

let escape_char fallback = function 
  | c when (c = '\'')            -> "_"
  | c when (is_letter_or_digit c)-> string_of_char c
  | c when (is_punctuation c)    -> string_of_char c
  | c when (is_symbol c)         -> string_of_char c
  | c                            -> fallback c

let remove_chars_t s = String.collect (escape_char string_of_char) s

let print_op_un = function
    | JSU_Minus -> text "-"
    | JSU_Plus -> text "+"
    | JSU_Not -> text "!"
    | JSU_BitNot -> text "~"
    | JSU_Typeof -> text "typeof"
    | JSU_Void -> text "void"
    | JSU_Delete -> text "delete"
    | JSU_Await -> text "await"

let print_op_bin = function
    | JSB_Equal -> text "==" 
    | JSB_NotEqual -> text "!=" 
    | JSB_StrictEqual -> text "===" 
    | JSB_StrictNotEqual -> text "!=="
    | JSB_LessThan -> text "<" 
    | JSB_LessThanEqual -> text "<=" 
    | JSB_GreaterThan -> text ">" 
    | JSB_GreaterThanEqual -> text ">="
    | JSB_LShift -> text "<<"
    | JSB_RShift -> text ">>" 
    | JSB_RShift3 -> text ">>>" 
    | JSB_Plus -> text "+" 
    | JSB_Minus -> text "-" 
    | JSB_Mult -> text "*" 
    | JSB_Exp -> text "**"
    | JSB_Div -> text "/" 
    | JSB_Mod -> text "%" 
    | JSB_BitOr -> text "|" 
    | JSB_Xor -> text "^" 
    | JSB_BitAnd -> text "&" 
    | JSB_In -> text "in"  
    | JSB_Instanceof -> text "instanceof"

let print_op_log = function
    | JSL_Or -> text "||"
    | JSL_And -> text "&&"

let f_print_arrow_fun_t = ref true

let f_print_arrow_fun = ref true

let rec pretty_print (program:Ast.t) : doc = 
    reduce ([text "/* @flow */"; hardline] @           
            List.map (function 
                | JS_Statement(s) ->
                    f_print_arrow_fun_t := true;
                    f_print_arrow_fun := true;
                    (match s with 
                    | JSS_Block l ->  pretty_print_statements l
                    | _ -> pretty_print_statement s)) program)

and pretty_print_statement (p:statement_t) : doc =
  let optws (s:statement_t) =
    match s with
    | JSS_Block(b) -> pretty_print_statements b
    | _ -> reduce [ws; nest 1 (pretty_print_statement s)] in
  let f = function
    | JSS_Empty -> semi
    | JSS_Block(l) -> reduce [text "{"; pretty_print_statements l; text "}"]
    | JSS_Expression(e) -> reduce [ws; pretty_print_exp e; semi]
    | JSS_If(c,t,f) ->
        reduce [ws; text "if"; parens (pretty_print_exp c); text "{"; hardline; optws t; text "}";
        (match f with
         | None -> empty
         | Some s -> reduce [ws; text "else"; text "{"; optws s; text "}"])]
    | JSS_Labeled((l, t), s) -> reduce [ws; text (jstr_escape l); colon; hardline; optws s]
    | JSS_Break(i) -> reduce [ws; text "break";
        (match i with | None -> empty | Some (v, t) -> reduce [ws; text (jstr_escape v)]); semi]
    | JSS_Continue(i) -> reduce [ws; text "continue";
        (match i with | None -> empty | Some (v, t) -> reduce [ws; text (jstr_escape v)]); semi]
    | JSS_With(e,s) -> reduce [ws; text "with"; parens (pretty_print_exp e); hardline; optws s]
    | JSS_TypeAlias((id,_),lt,t) -> reduce [text "type "; text (jstr_escape id); print_decl_t lt; text "="; print_typ t; semi]
    | JSS_Switch(e,lcase) ->
        reduce [ws; text "switch"; parens (pretty_print_exp e); hardline;
                ws; text "{"; hardline;
                (List.map (fun (e,l) ->
                    reduce [ws; text "case "; (match e with | Some v -> pretty_print_exp v | None -> text "default"); colon; hardline;
                           nest 1 (pretty_print_statements l)]) lcase) |> combine hardline;
                    text "}"]
    | JSS_Return(e) -> reduce [ws; text "return"; (match e with | None -> empty | Some v -> reduce [ws; pretty_print_exp v]); semi]
    | JSS_Throw(e) -> reduce [ws; text "throw "; pretty_print_exp e; semi]
    | JSS_Try(b,h)  ->  reduce [text "try"; text "{"; pretty_print_statements b; text "}"; text "TODO:catch"]
    | JSS_While(e, s) -> reduce [ws; text "while"; parens (pretty_print_exp e); hardline; optws s]
    | JSS_DoWhile(s, e) -> reduce [ws; text "do"; hardline; optws s; pretty_print_statement s;
                                   ws; text "while"; parens (pretty_print_exp e); semi]
    | JSS_For(i,c,l,s) -> failwith "todo: pretty-print [JSS_For]"
    | JSS_Forin(i,e,s) -> failwith "todo: pretty-print [JSS_Forin]"
    | JSS_ForOf(i,e,s) -> failwith "todo: pretty-print [JSS_ForOf]"
    | JSS_Let(l,s) -> failwith "todo: pretty-print [JSS_Let]"
    | JSS_Debugger -> reduce [ws; text "debugger;"]
    | JSS_FunctionDeclaration(f) -> pretty_print_fun f
    | JSS_VariableDeclaration((p, e), k) ->
        (match p with
        | JGP_Identifier (n, _) when n = "_" -> (match e with | Some v -> pretty_print_exp v | None -> empty)
        | _ -> reduce [print_kind_var k; print_pattern p true;
                      (match e with | None -> empty | Some v -> reduce [text "="; pretty_print_exp v]); semi])
    | JSS_DeclareVariable _ -> failwith "todo: pretty-print [JSS_DeclareVariable]"
    | JSS_DeclareFunction _ -> failwith "todo: pretty-print [JSS_DeclareFunction]"
    | JSS_ExportDefaultDeclaration (d, k) ->
        let print_declaration =
            (match d with
            | JSE_Declaration s -> optws s
            | JSE_Expression e -> pretty_print_exp e) in
        reduce [print_exp_kind k; print_declaration]
    | JSS_ImportDeclaration d ->
        reduce [text "import * as "; text (jstr_escape (fst d));
                text " from "; text "\"./"; text (jstr_escape (fst d)); text "\""; text ";"]

  in reduce [(f p); hardline]

and print_exp_kind = function
    | ExportType -> text "declare "
    | ExportValue -> text "export "

and pretty_print_statements l = reduce (List.map pretty_print_statement l)

and print_decl_t lt =
    match lt with
    | Some l -> reduce [text "<"; List.map (fun s -> text (remove_chars_t s)) l |> combine comma; text ">"]
    | None -> empty

and pretty_print_exp = function
    | JSE_This -> text "this"
    | JSE_Array(l) ->
        (match l with 
        | Some v ->  reduce [text "["; List.map pretty_print_exp v |> combine comma ; text "]"]
        | None -> reduce [text "["; text "]"])
    | JSE_Object(l) ->  reduce [text "{"; List.map pretty_print_obj l |> combine comma; text "}"]
    | JSE_Function(f) ->  pretty_print_fun f    
    | JSE_ArrowFunction(_, args, body, ret_t, decl_vars) ->
        let decl_t = (if !f_print_arrow_fun then print_decl_t decl_vars else empty) in
            f_print_arrow_fun := false;
            reduce [decl_t; print_arrow_fun args (print_body body) ret_t]
    | JSE_Sequence(e) -> reduce [ List.map pretty_print_exp e |> combine semi]
    | JSE_Unary(o,e) -> reduce [print_op_un o; pretty_print_exp e]
    | JSE_Binary(o,e1,e2) -> reduce [text "("; pretty_print_exp e1; print_op_bin o; pretty_print_exp e2; text ")"]
    | JSE_Assignment(p,e) ->
        (match p with
        | JGP_Identifier (n, _) when n = "_" -> pretty_print_exp e
        | _ -> reduce [print_pattern p false; text "="; pretty_print_exp e])    
    | JSE_Logical(o,e1,e2) ->  reduce [pretty_print_exp e1; print_op_log o; pretty_print_exp e2]
    | JSE_Conditional(c,e,f) -> failwith "todo: pretty-print [JSE_Conditional]"
    | JSE_New(e,l) -> failwith "todo: pretty-print [JSE_New]"
    | JSE_Call(e,l) -> 
        let le = List.map (fun x -> parens (pretty_print_exp x)) l |> combine empty in
        reduce [pretty_print_exp e;  (match l with | [] -> text "()" | _ -> le)]
    | JSE_Member(o, p) ->  reduce [pretty_print_exp o; pretty_print_propmem p]
    | JSE_Yield(e,b) -> failwith "todo: pretty-print [JSE_Yield]"
    | JSE_Comprehension(l,e) -> failwith "todo: pretty-print [JSE_Comprehension]"
    | JSE_Generator(l,e) -> failwith "todo: pretty-print [JSE_Generator]"
    | JSE_Let(l,e) -> failwith "todo: pretty-print [JSE_Let]"
    | JSE_Identifier(id,t) -> text (remove_chars_t id)
    | JSE_Literal(l) -> print_literal (fst l)
    | JSE_TypeCast(e,t) -> reduce [ text "("; pretty_print_exp e; colon; print_typ t; text ")"]

and print_arrow_fun args body ret_t =
    let ret_t = (match ret_t with | None -> empty | Some v -> reduce [colon; parens (print_typ v)]) in
    print_arrow_fun_p args body ret_t true

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
    | JSO_Literal l -> print_literal (fst l)
    | JSO_Identifier(id, t) -> text (jstr_escape id)
    | JSO_Computed e -> pretty_print_exp e

and pretty_print_propmem p = 
    match p with
    | JSPM_Identifier(i, t) -> reduce [ text "."; text (jstr_escape i)]
    | JSPM_Expression e -> reduce [ text "["; pretty_print_exp e; text "]"] 

and print_typ = function
    | JST_Any -> text "any"
    | JST_Mixed -> text "mixed"
    | JST_Empty -> failwith "todo: pretty-print [JST_Empty]"
    | JST_Void -> text "void"
    | JST_Null -> text "null"
    | JST_Number -> text "number"
    | JST_String -> text "string"
    | JST_Boolean -> text "boolean"
    | JST_Nullable _ -> failwith "todo: pretty-print [JST_Nullable]"
    | JST_Function (args, ret_t, decl_vars) -> 
        let decl_vars = (if !f_print_arrow_fun_t then decl_vars else None) in
            f_print_arrow_fun_t := false;
            print_fun_typ args ret_t decl_vars
    | JST_Object (lp, _, _) -> reduce [text "{" ;
                                       List.map (fun (k, t) ->
                                            reduce [pretty_print_prop_key k; text ":"; print_typ t]) lp |> combine comma;
                                       text "}" ]
    | JST_Array t -> reduce [text "Array"; text "<"; print_typ t; text ">"]
    | JST_Union l ->  reduce [List.map print_typ l |> combine (text "|")]
    | JST_Intersection l -> reduce [List.map print_typ l |> combine (text "&")]
    | JST_Typeof t -> reduce [text "typeof"; print_typ t]
    | JST_Tuple lt -> reduce [text "["; List.map (print_typ) lt |> combine comma; text "]"]
    | JST_StringLiteral (s,_) -> text ("\"" ^ (jstr_escape s) ^ "\"")
    | JST_NumberLiteral (n, _)-> text (string_of_float n)
    | JST_BooleanLiteral (b, _) -> text (string_of_bool b)
    | JST_Exists -> failwith "todo: pretty-print [JST_Exists]"
    | JST_Generic(n, lt) ->
        let print_lt = match lt with 
                      | None -> empty 
                      | Some v -> reduce [text "<"; List.map print_typ v |> combine comma; text ">"] 
        in reduce [print_gen_t n; print_lt]

and print_fun_typ args ret_t decl_vars =    
    let print_arg ((id,_), t) = reduce[text (jstr_escape id); colon; print_typ t] in
    let args_t =
    (match args with
    | [] -> reduce [text "()"; text "=>"; print_typ ret_t]
    | [x] -> reduce [parens (print_arg x); text "=>"; parens (print_typ ret_t)]
    | hd :: tl -> reduce [parens (print_arg hd); text "=>"; parens (print_fun_typ tl ret_t None)])
    in reduce [print_decl_t decl_vars; args_t]

and print_gen_t = function 
    | Unqualified (id, _) -> text (remove_chars_t id)
    | Qualified (g, (id, _)) -> reduce [print_gen_t g; comma; text (remove_chars_t id)]

and print_literal = function
    | JSV_String s -> text ("\"" ^ (jstr_escape s) ^ "\"")
    | JSV_Boolean b -> text (string_of_bool b)
    | JSV_Null -> text "null"
    | JSV_Number f -> text (string_of_float f)
    | JSV_RegExp _ -> text "!!"

and print_kind_var = function
    | JSV_Var -> text "var "
    | JSV_Let -> text "let "
    | JSV_Const -> text "const "

and print_pattern p print_t =
    match p with
    | JGP_Object _ -> failwith "todo: pretty-print [JGP_Object]"
    | JGP_Array _ -> failwith "todo: pretty-print [JGP_Array]"
    | JGP_Assignment _ -> failwith "todo: pretty-print [JGP_Assignment]"
    | JGP_Expression e  -> pretty_print_exp e
    | JGP_Identifier(id, t) ->
        let r = match t with
                | Some v -> reduce [colon; print_typ v]
                | None -> empty
        in reduce [text (remove_chars_t id); (if print_t then r else empty)]

and print_body = function 
    | JS_BodyBlock l -> reduce [text "{"; pretty_print_statements l; text "}"]
    | JS_BodyExpression e -> parens(pretty_print_exp e)

and pretty_print_fun (n, pars, body, t, typePars) =
    let name = match n with | Some v -> text (fst v) | None -> empty in
    let returnT = match t with | Some v -> reduce [text ":"; ws; print_typ v] | None -> empty in
    reduce [text "function"; ws; name; print_decl_t typePars; parens (List.map (fun p -> print_pattern p true) pars |> combine comma); returnT;
            text "{";  hardline; print_body body; text "}"]    