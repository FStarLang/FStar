#light "off"

module FStar.Extraction.JavaScript.Ast
open FStar.All
open FStar
open FStar.Ident
open FStar.Util
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
    | JSS_TypeAlias of identifier_t * option<param_decl_t> * typ
    | JSS_Return of option<expression_t>
    | JSS_Throw of expression_t
    | JSS_VariableDeclaration of (pattern_t * option<expression_t>) * kind_var_t
    | JSS_ExportDefaultDeclaration of declaration * export_kind
      (* add support only for import * as ".." from ".." *)
    | JSS_ImportDeclaration of identifier_t
    | JSS_Seq of list<statement_t>
    
and expression_t =
    | JSE_Array of option<(list<expression_t>)>
    | JSE_Object of list<property_obj_t>
    | JSE_ArrowFunction of function_t
    | JSE_Unary of op_un * expression_t
    | JSE_Binary of op_bin * expression_t * expression_t
    | JSE_Assignment of pattern_t * expression_t
    | JSE_Logical of op_log * expression_t * expression_t
    | JSE_Call of expression_t * list<expression_t>
    | JSE_Member of expression_t * propmem_t
    | JSE_Identifier of identifier_t
    | JSE_Literal of literal_t
    | JSE_TypeCast of expression_t * typ

and op_un =
    | JSU_Minus | JSU_Not

and op_bin =
    | JSB_Equal | JSB_NotEqual | JSB_LessThan | JSB_LessThanEqual | JSB_GreaterThan
    | JSB_GreaterThanEqual | JSB_Plus | JSB_Minus | JSB_Mult | JSB_Div | JSB_Mod
    | JSB_StrictEqual

and op_log = | JSL_Or | JSL_And

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
    | JST_Void
    | JST_Null
    | JST_Number
    | JST_String
    | JST_Boolean
    | JST_Function of list<(identifier_t * typ)> * typ * option<param_decl_t>
    | JST_Object of list<(object_prop_key_t * typ)>
    | JST_Array of typ
    | JST_Generic of string * option<(list<typ>)>
    | JST_Union of list<typ>
    | JST_Intersection of list<typ>
    | JST_Tuple of list<typ>
    | JST_StringLiteral of string * string 

and identifier_t = string * option<typ>

and function_t = option<identifier_t> * list<pattern_t> * body_t * option<typ> * option<param_decl_t>

and body_t = 
    | JS_BodyBlock of list<statement_t> 
    | JS_BodyExpression of expression_t

and literal_t = value_t * string

and value_t = 
    | JSV_String of string
    | JSV_Boolean of bool
    | JSV_Null
    | JSV_Number of float

and param_decl_t = list<string> (*Use only for generic types*)

and pattern_t =
    | JGP_Identifier of identifier_t
    | JGP_Expression of expression_t

and property_t =
    | JSP_SpreadProperty of pattern_t
    | JSP_Property of object_prop_key_t * pattern_t

and object_prop_key_t =
    | JSO_Literal of literal_t
    | JSO_Identifier of identifier_t
    | JSO_Computed of expression_t

and declaration =
    | JSE_Declaration of statement_t
    | JSE_Expression of expression_t

and export_kind =
    | ExportType
    | ExportValue