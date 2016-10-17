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
  | c when (c = '\'')            -> ""
  | c when (is_letter_or_digit c)-> string_of_char c
  | c when (is_punctuation c)    -> string_of_char c
  | c when (is_symbol c)         -> string_of_char c
  | c                            -> fallback c

let remove_chars_t s = String.collect (escape_char string_of_char) s
//let remove_chars_t s =  String.filter ((<>) '\'') s |> jstr_escape

let print_op_un:op_un -> doc = function
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

let rec pretty_print (program:Ast.t) : doc = 
    reduce ([text "/* @flow */"; hardline] @           
            List.map (function | JS_Statement(s) -> 
                                    match s with 
                                    | JSS_Block l ->  pretty_print_statements l
                                    | _ -> pretty_print_statement s) program)

and pretty_print_statement (p:statement_t) : doc =
  let optws (s:statement_t) = 
    match s with 
    | JSS_Block(b) -> pretty_print_statements b
    | _ -> reduce [ws; nest 1 (pretty_print_statement s)] in
  let f = function
    | JSS_Empty -> semi
    | JSS_Block(l) -> reduce [ text "{"; pretty_print_statements l; text "}" ]
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
    | JSS_For(i,c,l,s) -> semi (*!!!*)
    | JSS_Forin(i,e,s) -> semi (*!!!*)
    | JSS_ForOf(i,e,s) -> semi (*!!!*)
    | JSS_Let(l,s) -> semi (*!!!*)
    | JSS_Debugger -> reduce [ws; text "debugger;"]
    | JSS_FunctionDeclaration(f) -> pretty_print_fun f
    | JSS_VariableDeclaration(l, k) ->
        reduce [ws; print_kind_var k; ws;  
               (List.map (fun (p,e) -> 
                    reduce [print_pattern p; 
                           (match e with | None -> empty | Some v -> reduce [ws; text "="; ws; pretty_print_exp v])]) l) |> combine comma;
               semi]
    | JSS_DeclareVariable _ -> semi (*!!!*)
    | JSS_DeclareFunction _ -> semi (*!!!*)

  in reduce [(f p); hardline]

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
    | JSE_ArrowFunction(_, args, body, ret_t, decl_vars) -> print_arrow_fun args (print_body body)
    | JSE_Sequence(e) -> reduce [ List.map pretty_print_exp e |> combine semi]
    | JSE_Unary(o,e) -> reduce [print_op_un o; pretty_print_exp e]
    | JSE_Binary(o,e1,e2) -> reduce [text "("; pretty_print_exp e1; print_op_bin o; pretty_print_exp e2; text ")"]
    | JSE_Assignment(p,e) -> reduce [print_pattern p; text "="; pretty_print_exp e]
    | JSE_Update(o,e,b) -> semi (*!!!*)
    | JSE_Logical(o,e1,e2) ->  reduce [pretty_print_exp e1; print_op_log o; pretty_print_exp e2]
    | JSE_Conditional(c,e,f) -> semi (*!!!*)
    | JSE_New(e,l) -> semi (*!!!*)
    | JSE_Call(e,l) -> //reduce [pretty_print_exp e; parens (List.map pretty_print_exp l |> combine comma)]
        reduce [pretty_print_exp e;  List.map (fun x -> parens (pretty_print_exp x)) l |> combine empty]
    | JSE_Member(o, p) ->  reduce [pretty_print_exp o; pretty_print_propmem p]
    | JSE_Yield(e,b) -> semi (*!!!*)
    | JSE_Comprehension(l,e) -> semi (*!!!*)
    | JSE_Generator(l,e) -> semi (*!!!*)
    | JSE_Let(l,e) -> semi (*!!!*)
    | JSE_Identifier(id,t) -> text (jstr_escape id)// reduce [text (jstr_escape id); (match t with | Some v -> reduce [text ":"; print_typ v] | None -> text "")] 
    | JSE_Literal(l) -> print_literal (fst l)
    | JSE_TypeCast(e,t) -> semi (*!!!*)

and print_arrow_fun args body = 
    match args with
    | [] -> reduce [text "()"; text "=>"; body]
    | [x] -> reduce [parens (print_pattern x); text "=>";  body]
    | hd :: tl -> reduce [parens (print_pattern hd); text "=>"; parens (print_arrow_fun tl body)]
       
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
    | JST_Empty -> text "!!!"
    | JST_Void -> text "void"
    | JST_Null -> text "null"
    | JST_Number -> text "number"
    | JST_String -> text "string"
    | JST_Boolean -> text "boolean"
    | JST_Nullable _ -> text "!!!"
    | JST_Function (args, ret_t, decl_vars) -> reduce [print_decl_t decl_vars; print_fun_typ args ret_t]        
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
    | JST_Exists -> text "!!!"
    | JST_Generic(n, lt) ->
        let print_lt = match lt with 
                      | None -> empty 
                      | Some v -> reduce [text "<"; List.map print_typ v |> combine comma; text ">"] 
        in reduce [print_gen_t n; print_lt]

and print_fun_typ args ret_t = 
    let print_arg ((id,_), t) = reduce[text (jstr_escape id); colon; print_typ t] in
    match args with
    | [] -> reduce [text "()"; text "=>"; print_typ ret_t]
    | [x] -> reduce [parens (print_arg x); text "=>"; parens (print_typ ret_t)]
    | hd :: tl -> reduce [parens (print_arg hd); text "=>"; parens (print_fun_typ tl ret_t)]

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
    | JSV_Var -> text "var"
    | JSV_Let -> text "let"
    | JSV_Const -> text "const"

and print_pattern = function
    | JGP_Object _ -> text "!!"
    | JGP_Array _ -> text "!!"
    | JGP_Assignment _ -> text "!!"
    | JGP_Expression _ -> text "!!"
    | JGP_Identifier(id, t) ->
        let r = match t with
                | Some v -> reduce [colon; print_typ v]
                | None -> empty
        in reduce [text (jstr_escape id); r]

and print_body = function 
    | JS_BodyBlock l -> reduce [text "{"; pretty_print_statements l; text "}"]
    | JS_BodyExpression e -> pretty_print_exp e

and pretty_print_fun (n, pars, body, t, typePars) =
    let name = match n with | Some v -> text (fst v) | None -> empty in
    let returnT = match t with | Some v -> reduce [text ":"; ws; print_typ v] | None -> empty in
    reduce [text "function"; ws; name; print_decl_t typePars; parens (List.map print_pattern pars |> combine comma); returnT;
            text "{";  hardline; print_body body; text "}"]