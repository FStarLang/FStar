#light "off"

module FStar.Extraction.JavaScript.Ast

open FStar
open FStar.Util
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format
open FStar.Const
open FStar.BaseTypes

(* Type of Flow program *)
type t = list<source_t>

and source_t =
    | JS_Statement of statement_t  

and statement_t =
    | JSS_Empty
    | JSS_Block of list<statement_t>
    | JSS_Expression of expression_t
    | JSS_If of expression_t * statement_t * option<statement_t>
    | JSS_Labeled of identifier_t * statement_t  
    | JSS_Break of option<identifier_t>
    | JSS_Continue of option<identifier_t>
    | JSS_With of expression_t * statement_t
    | JSS_TypeAlias of identifier_t * option<param_decl_t> * typ
    | JSS_Switch of expression_t * list<(option<expression_t> * list<statement_t>)>
    | JSS_Return of option<expression_t>
    | JSS_Throw of expression_t
    | JSS_Try of list<statement_t> * option<(pattern_t * list<statement_t>)>
    | JSS_While of expression_t * statement_t
    | JSS_DoWhile of statement_t * expression_t
    | JSS_For of option<forinit_t> * option<expression_t> * option<expression_t> * statement_t
    | JSS_Forin of forinit_t * expression_t * statement_t
    | JSS_ForOf of forinit_t * expression_t * statement_t
    | JSS_Let of list<(pattern_t * option<expression_t>)> * statement_t
    | JSS_Debugger
    | JSS_FunctionDeclaration of function_t
    | JSS_VariableDeclaration of list<(pattern_t * option<expression_t>)> * kind_var_t
    | JSS_DeclareVariable of identifier_t
    | JSS_DeclareFunction of identifier_t * option<predicate_t>
    | JSS_ExportDefaultDeclaration of export_default_declaration_t
    | JSS_ImportDeclaration of import_declaration_t
    
and expression_t =
    | JSE_This
    | JSE_Array of option<(list<expression_t>)>
    | JSE_Object of list<property_obj_t>
    | JSE_Function of function_t
    | JSE_ArrowFunction of function_t
    | JSE_Sequence of list<expression_t>
    | JSE_Unary of op_un * expression_t
    | JSE_Binary of op_bin * expression_t * expression_t   
    | JSE_Assignment of pattern_t * expression_t
    | JSE_Update of op_update * expression_t * bool
    | JSE_Logical of op_log * expression_t * expression_t
    | JSE_Conditional of expression_t * expression_t * expression_t
    | JSE_New of expression_t * list<expression_t>    
    | JSE_Call of expression_t * list<expression_t>    
    | JSE_Member of expression_t * propmem_t
    | JSE_Yield of option<expression_t> * bool
    | JSE_Comprehension of list<t> * option<expression_t>
    | JSE_Generator of list<t> * option<expression_t>
    | JSE_Let of list<(pattern_t * option<expression_t>)> * expression_t
    | JSE_Identifier of identifier_t
    | JSE_Literal of literal_t
    | JSE_TypeCast of expression_t * typ

and op_un =       
    | JSU_Minus | JSU_Plus | JSU_Not | JSU_BitNot
    | JSU_Typeof | JSU_Void | JSU_Delete | JSU_Await

and op_bin =
    | JSB_Equal | JSB_NotEqual | JSB_StrictEqual | JSB_StrictNotEqual
    | JSB_LessThan | JSB_LessThanEqual | JSB_GreaterThan | JSB_GreaterThanEqual
    | JSB_LShift | JSB_RShift | JSB_RShift3 | JSB_Plus | JSB_Minus | JSB_Mult | JSB_Exp
    | JSB_Div | JSB_Mod | JSB_BitOr | JSB_Xor | JSB_BitAnd | JSB_In | JSB_Instanceof

and op_update = | JSUP_Increment | JSUP_Decrement

and op_log = | JSL_Or | JSL_And

and forinit_t = 
    | JSF_Declaration of list<(pattern_t * option<expression_t>)> * kind_var_t
    | JSF_Expression of expression_t

and kind_var_t = | JSV_Var | JSV_Let | JSV_Const

and kind_obj_t = | JSO_Init | JSO_Get | JSO_Set

and property_obj_t = 
    | JSPO_Property of object_prop_key_t * expression_t * kind_obj_t
    | JSPO_SpreadProperty of expression_t

and propmem_t =   
    | JSPM_Identifier of identifier_t
    | JSPM_Expression of expression_t

and typ = 
    | JST_Any
    | JST_Mixed
    | JST_Empty 
    | JST_Void
    | JST_Null
    | JST_Number
    | JST_String
    | JST_Boolean
    | JST_Nullable of typ
    | JST_Function of list<(identifier_t * typ)> * typ * option<param_decl_t> (*!!!*)
    | JST_Object of list<(object_prop_key_t * typ)> * list<(identifier_t * typ * typ)> * list<function_t>
    | JST_Array of typ
    | JST_Generic of generic_t * option<(list<typ>)>
    | JST_Union of list<typ>
    | JST_Intersection of list<typ>
    | JST_Typeof of typ
    | JST_Tuple of list<typ>
    | JST_StringLiteral of string * string 
    | JST_NumberLiteral of float * string
    | JST_BooleanLiteral of bool * string
    | JST_Exists

and generic_t = 
    | Unqualified of identifier_t
    | Qualified of generic_t * identifier_t

and identifier_t = string * option<typ>

and function_t = (*option<identifier_t> * list<pattern_t> * option<list<expression_t>> * option<identifier_t> 
                    * body_t * option<predicate_t> * option<typ> * option<param_decl_t> *)
                 option<identifier_t> * list<pattern_t> * body_t * option<typ> * option<param_decl_t>

and body_t = | JS_BodyBlock of list<statement_t> | JS_BodyExpression of expression_t

and literal_t = value_t * string

and value_t = 
    | JSV_String of string
    | JSV_Boolean of bool
    | JSV_Null
    | JSV_Number of float
    | JSV_RegExp of string * string

and param_decl_t = list<string> (*Use only for generic types*)

and predicate_t = | JSP_Declared of expression_t | JSP_Inferred

and pattern_t = 
    | JGP_Object of list<property_t> * option<typ>
    | JGP_Array of option<(list<pattern_t>)> * option<typ>
    | JGP_Assignment of pattern_t * expression_t
    | JGP_Identifier of identifier_t
    | JGP_Expression of expression_t

and property_t = 
    | JSP_SpreadProperty of pattern_t
    | JSP_Property of object_prop_key_t * pattern_t

and object_prop_key_t = 
    | JSO_Literal of literal_t
    | JSO_Identifier of identifier_t
    | JSO_Computed of expression_t

and export_default_declaration_t = declaration * export_kind

and declaration = 
    | JSE_Declaration of statement_t
    | JSE_Expression of expression_t

and export_kind = 
    | ExportType
    | ExportValue

(* add support only for import * as ".." from ".." *)
and import_declaration_t = identifier_t