open Prims
type source_t =
  | JS_Statement of statement_t
and statement_t =
  | JSS_Empty
  | JSS_Block of statement_t Prims.list
  | JSS_Expression of expression_t
  | JSS_If of (expression_t* statement_t* statement_t option)
  | JSS_TypeAlias of ((Prims.string* typ option)* Prims.string Prims.list
  option* typ)
  | JSS_Return of expression_t option
  | JSS_Throw of expression_t
  | JSS_VariableDeclaration of ((pattern_t* expression_t option)*
  kind_var_t)
  | JSS_ExportDefaultDeclaration of (declaration* export_kind)
  | JSS_ImportDeclaration of (Prims.string* typ option)
  | JSS_Seq of statement_t Prims.list
and expression_t =
  | JSE_Array of expression_t Prims.list option
  | JSE_Object of property_obj_t Prims.list
  | JSE_ArrowFunction of ((Prims.string* typ option) option* pattern_t
  Prims.list* body_t* typ option* Prims.string Prims.list option)
  | JSE_Unary of (op_un* expression_t)
  | JSE_Binary of (op_bin* expression_t* expression_t)
  | JSE_Assignment of (pattern_t* expression_t)
  | JSE_Logical of (op_log* expression_t* expression_t)
  | JSE_Call of (expression_t* expression_t Prims.list)
  | JSE_Member of (expression_t* propmem_t)
  | JSE_Identifier of (Prims.string* typ option)
  | JSE_Literal of (value_t* Prims.string)
  | JSE_TypeCast of (expression_t* typ)
and op_un =
  | JSU_Minus
  | JSU_Not
and op_bin =
  | JSB_Equal
  | JSB_NotEqual
  | JSB_LessThan
  | JSB_LessThanEqual
  | JSB_GreaterThan
  | JSB_GreaterThanEqual
  | JSB_Plus
  | JSB_Minus
  | JSB_Mult
  | JSB_Div
  | JSB_Mod
  | JSB_StrictEqual
and op_log =
  | JSL_Or
  | JSL_And
and kind_var_t =
  | JSV_Var
  | JSV_Let
  | JSV_Const
and kind_obj_t =
  | JSO_Init
  | JSO_Get
  | JSO_Set
and property_obj_t =
  | JSPO_Property of (object_prop_key_t* expression_t* kind_obj_t)
  | JSPO_SpreadProperty of expression_t
and propmem_t =
  | JSPM_Identifier of (Prims.string* typ option)
  | JSPM_Expression of expression_t
and typ =
  | JST_Any
  | JST_Void
  | JST_Null
  | JST_Number
  | JST_String
  | JST_Boolean
  | JST_Function of (((Prims.string* typ option)* typ) Prims.list* typ*
  Prims.string Prims.list option)
  | JST_Object of (object_prop_key_t* typ) Prims.list
  | JST_Array of typ
  | JST_Generic of (Prims.string* typ Prims.list option)
  | JST_Union of typ Prims.list
  | JST_Intersection of typ Prims.list
  | JST_Tuple of typ Prims.list
  | JST_StringLiteral of (Prims.string* Prims.string)
and body_t =
  | JS_BodyBlock of statement_t Prims.list
  | JS_BodyExpression of expression_t
and value_t =
  | JSV_String of Prims.string
  | JSV_Boolean of Prims.bool
  | JSV_Null
  | JSV_Number of FStar_BaseTypes.float
and pattern_t =
  | JGP_Identifier of (Prims.string* typ option)
  | JGP_Expression of expression_t
and property_t =
  | JSP_SpreadProperty of pattern_t
  | JSP_Property of (object_prop_key_t* pattern_t)
and object_prop_key_t =
  | JSO_Literal of (value_t* Prims.string)
  | JSO_Identifier of (Prims.string* typ option)
  | JSO_Computed of expression_t
and declaration =
  | JSE_Declaration of statement_t
  | JSE_Expression of expression_t
and export_kind =
  | ExportType
  | ExportValue
let uu___is_JS_Statement: source_t -> Prims.bool = fun projectee  -> true
let __proj__JS_Statement__item___0: source_t -> statement_t =
  fun projectee  -> match projectee with | JS_Statement _0 -> _0
let uu___is_JSS_Empty: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_Empty  -> true | uu____261 -> false
let uu___is_JSS_Block: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_Block _0 -> true | uu____267 -> false
let __proj__JSS_Block__item___0: statement_t -> statement_t Prims.list =
  fun projectee  -> match projectee with | JSS_Block _0 -> _0
let uu___is_JSS_Expression: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_Expression _0 -> true | uu____282 -> false
let __proj__JSS_Expression__item___0: statement_t -> expression_t =
  fun projectee  -> match projectee with | JSS_Expression _0 -> _0
let uu___is_JSS_If: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_If _0 -> true | uu____298 -> false
let __proj__JSS_If__item___0:
  statement_t -> (expression_t* statement_t* statement_t option) =
  fun projectee  -> match projectee with | JSS_If _0 -> _0
let uu___is_JSS_TypeAlias: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_TypeAlias _0 -> true | uu____330 -> false
let __proj__JSS_TypeAlias__item___0:
  statement_t ->
    ((Prims.string* typ option)* Prims.string Prims.list option* typ)
  = fun projectee  -> match projectee with | JSS_TypeAlias _0 -> _0
let uu___is_JSS_Return: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_Return _0 -> true | uu____367 -> false
let __proj__JSS_Return__item___0: statement_t -> expression_t option =
  fun projectee  -> match projectee with | JSS_Return _0 -> _0
let uu___is_JSS_Throw: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_Throw _0 -> true | uu____382 -> false
let __proj__JSS_Throw__item___0: statement_t -> expression_t =
  fun projectee  -> match projectee with | JSS_Throw _0 -> _0
let uu___is_JSS_VariableDeclaration: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | JSS_VariableDeclaration _0 -> true
    | uu____399 -> false
let __proj__JSS_VariableDeclaration__item___0:
  statement_t -> ((pattern_t* expression_t option)* kind_var_t) =
  fun projectee  -> match projectee with | JSS_VariableDeclaration _0 -> _0
let uu___is_JSS_ExportDefaultDeclaration: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | JSS_ExportDefaultDeclaration _0 -> true
    | uu____428 -> false
let __proj__JSS_ExportDefaultDeclaration__item___0:
  statement_t -> (declaration* export_kind) =
  fun projectee  ->
    match projectee with | JSS_ExportDefaultDeclaration _0 -> _0
let uu___is_JSS_ImportDeclaration: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | JSS_ImportDeclaration _0 -> true
    | uu____449 -> false
let __proj__JSS_ImportDeclaration__item___0:
  statement_t -> (Prims.string* typ option) =
  fun projectee  -> match projectee with | JSS_ImportDeclaration _0 -> _0
let uu___is_JSS_Seq: statement_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSS_Seq _0 -> true | uu____471 -> false
let __proj__JSS_Seq__item___0: statement_t -> statement_t Prims.list =
  fun projectee  -> match projectee with | JSS_Seq _0 -> _0
let uu___is_JSE_Array: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Array _0 -> true | uu____488 -> false
let __proj__JSE_Array__item___0:
  expression_t -> expression_t Prims.list option =
  fun projectee  -> match projectee with | JSE_Array _0 -> _0
let uu___is_JSE_Object: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Object _0 -> true | uu____507 -> false
let __proj__JSE_Object__item___0: expression_t -> property_obj_t Prims.list =
  fun projectee  -> match projectee with | JSE_Object _0 -> _0
let uu___is_JSE_ArrowFunction: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_ArrowFunction _0 -> true | uu____535 -> false
let __proj__JSE_ArrowFunction__item___0:
  expression_t ->
    ((Prims.string* typ option) option* pattern_t Prims.list* body_t* typ
      option* Prims.string Prims.list option)
  = fun projectee  -> match projectee with | JSE_ArrowFunction _0 -> _0
let uu___is_JSE_Unary: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Unary _0 -> true | uu____588 -> false
let __proj__JSE_Unary__item___0: expression_t -> (op_un* expression_t) =
  fun projectee  -> match projectee with | JSE_Unary _0 -> _0
let uu___is_JSE_Binary: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Binary _0 -> true | uu____609 -> false
let __proj__JSE_Binary__item___0:
  expression_t -> (op_bin* expression_t* expression_t) =
  fun projectee  -> match projectee with | JSE_Binary _0 -> _0
let uu___is_JSE_Assignment: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Assignment _0 -> true | uu____632 -> false
let __proj__JSE_Assignment__item___0:
  expression_t -> (pattern_t* expression_t) =
  fun projectee  -> match projectee with | JSE_Assignment _0 -> _0
let uu___is_JSE_Logical: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Logical _0 -> true | uu____653 -> false
let __proj__JSE_Logical__item___0:
  expression_t -> (op_log* expression_t* expression_t) =
  fun projectee  -> match projectee with | JSE_Logical _0 -> _0
let uu___is_JSE_Call: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Call _0 -> true | uu____677 -> false
let __proj__JSE_Call__item___0:
  expression_t -> (expression_t* expression_t Prims.list) =
  fun projectee  -> match projectee with | JSE_Call _0 -> _0
let uu___is_JSE_Member: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Member _0 -> true | uu____700 -> false
let __proj__JSE_Member__item___0: expression_t -> (expression_t* propmem_t) =
  fun projectee  -> match projectee with | JSE_Member _0 -> _0
let uu___is_JSE_Identifier: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Identifier _0 -> true | uu____721 -> false
let __proj__JSE_Identifier__item___0:
  expression_t -> (Prims.string* typ option) =
  fun projectee  -> match projectee with | JSE_Identifier _0 -> _0
let uu___is_JSE_Literal: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Literal _0 -> true | uu____744 -> false
let __proj__JSE_Literal__item___0: expression_t -> (value_t* Prims.string) =
  fun projectee  -> match projectee with | JSE_Literal _0 -> _0
let uu___is_JSE_TypeCast: expression_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_TypeCast _0 -> true | uu____764 -> false
let __proj__JSE_TypeCast__item___0: expression_t -> (expression_t* typ) =
  fun projectee  -> match projectee with | JSE_TypeCast _0 -> _0
let uu___is_JSU_Minus: op_un -> Prims.bool =
  fun projectee  ->
    match projectee with | JSU_Minus  -> true | uu____781 -> false
let uu___is_JSU_Not: op_un -> Prims.bool =
  fun projectee  ->
    match projectee with | JSU_Not  -> true | uu____785 -> false
let uu___is_JSB_Equal: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_Equal  -> true | uu____789 -> false
let uu___is_JSB_NotEqual: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_NotEqual  -> true | uu____793 -> false
let uu___is_JSB_LessThan: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_LessThan  -> true | uu____797 -> false
let uu___is_JSB_LessThanEqual: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_LessThanEqual  -> true | uu____801 -> false
let uu___is_JSB_GreaterThan: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_GreaterThan  -> true | uu____805 -> false
let uu___is_JSB_GreaterThanEqual: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_GreaterThanEqual  -> true | uu____809 -> false
let uu___is_JSB_Plus: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_Plus  -> true | uu____813 -> false
let uu___is_JSB_Minus: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_Minus  -> true | uu____817 -> false
let uu___is_JSB_Mult: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_Mult  -> true | uu____821 -> false
let uu___is_JSB_Div: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_Div  -> true | uu____825 -> false
let uu___is_JSB_Mod: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_Mod  -> true | uu____829 -> false
let uu___is_JSB_StrictEqual: op_bin -> Prims.bool =
  fun projectee  ->
    match projectee with | JSB_StrictEqual  -> true | uu____833 -> false
let uu___is_JSL_Or: op_log -> Prims.bool =
  fun projectee  ->
    match projectee with | JSL_Or  -> true | uu____837 -> false
let uu___is_JSL_And: op_log -> Prims.bool =
  fun projectee  ->
    match projectee with | JSL_And  -> true | uu____841 -> false
let uu___is_JSV_Var: kind_var_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_Var  -> true | uu____845 -> false
let uu___is_JSV_Let: kind_var_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_Let  -> true | uu____849 -> false
let uu___is_JSV_Const: kind_var_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_Const  -> true | uu____853 -> false
let uu___is_JSO_Init: kind_obj_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSO_Init  -> true | uu____857 -> false
let uu___is_JSO_Get: kind_obj_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSO_Get  -> true | uu____861 -> false
let uu___is_JSO_Set: kind_obj_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSO_Set  -> true | uu____865 -> false
let uu___is_JSPO_Property: property_obj_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSPO_Property _0 -> true | uu____873 -> false
let __proj__JSPO_Property__item___0:
  property_obj_t -> (object_prop_key_t* expression_t* kind_obj_t) =
  fun projectee  -> match projectee with | JSPO_Property _0 -> _0
let uu___is_JSPO_SpreadProperty: property_obj_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | JSPO_SpreadProperty _0 -> true
    | uu____894 -> false
let __proj__JSPO_SpreadProperty__item___0: property_obj_t -> expression_t =
  fun projectee  -> match projectee with | JSPO_SpreadProperty _0 -> _0
let uu___is_JSPM_Identifier: propmem_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSPM_Identifier _0 -> true | uu____909 -> false
let __proj__JSPM_Identifier__item___0:
  propmem_t -> (Prims.string* typ option) =
  fun projectee  -> match projectee with | JSPM_Identifier _0 -> _0
let uu___is_JSPM_Expression: propmem_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSPM_Expression _0 -> true | uu____930 -> false
let __proj__JSPM_Expression__item___0: propmem_t -> expression_t =
  fun projectee  -> match projectee with | JSPM_Expression _0 -> _0
let uu___is_JST_Any: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Any  -> true | uu____941 -> false
let uu___is_JST_Void: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Void  -> true | uu____945 -> false
let uu___is_JST_Null: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Null  -> true | uu____949 -> false
let uu___is_JST_Number: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Number  -> true | uu____953 -> false
let uu___is_JST_String: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_String  -> true | uu____957 -> false
let uu___is_JST_Boolean: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Boolean  -> true | uu____961 -> false
let uu___is_JST_Function: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Function _0 -> true | uu____977 -> false
let __proj__JST_Function__item___0:
  typ ->
    (((Prims.string* typ option)* typ) Prims.list* typ* Prims.string
      Prims.list option)
  = fun projectee  -> match projectee with | JST_Function _0 -> _0
let uu___is_JST_Object: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Object _0 -> true | uu____1025 -> false
let __proj__JST_Object__item___0: typ -> (object_prop_key_t* typ) Prims.list
  = fun projectee  -> match projectee with | JST_Object _0 -> _0
let uu___is_JST_Array: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Array _0 -> true | uu____1046 -> false
let __proj__JST_Array__item___0: typ -> typ =
  fun projectee  -> match projectee with | JST_Array _0 -> _0
let uu___is_JST_Generic: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Generic _0 -> true | uu____1062 -> false
let __proj__JST_Generic__item___0:
  typ -> (Prims.string* typ Prims.list option) =
  fun projectee  -> match projectee with | JST_Generic _0 -> _0
let uu___is_JST_Union: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Union _0 -> true | uu____1087 -> false
let __proj__JST_Union__item___0: typ -> typ Prims.list =
  fun projectee  -> match projectee with | JST_Union _0 -> _0
let uu___is_JST_Intersection: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Intersection _0 -> true | uu____1103 -> false
let __proj__JST_Intersection__item___0: typ -> typ Prims.list =
  fun projectee  -> match projectee with | JST_Intersection _0 -> _0
let uu___is_JST_Tuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_Tuple _0 -> true | uu____1119 -> false
let __proj__JST_Tuple__item___0: typ -> typ Prims.list =
  fun projectee  -> match projectee with | JST_Tuple _0 -> _0
let uu___is_JST_StringLiteral: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | JST_StringLiteral _0 -> true | uu____1136 -> false
let __proj__JST_StringLiteral__item___0: typ -> (Prims.string* Prims.string)
  = fun projectee  -> match projectee with | JST_StringLiteral _0 -> _0
let uu___is_JS_BodyBlock: body_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JS_BodyBlock _0 -> true | uu____1155 -> false
let __proj__JS_BodyBlock__item___0: body_t -> statement_t Prims.list =
  fun projectee  -> match projectee with | JS_BodyBlock _0 -> _0
let uu___is_JS_BodyExpression: body_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JS_BodyExpression _0 -> true | uu____1170 -> false
let __proj__JS_BodyExpression__item___0: body_t -> expression_t =
  fun projectee  -> match projectee with | JS_BodyExpression _0 -> _0
let uu___is_JSV_String: value_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_String _0 -> true | uu____1182 -> false
let __proj__JSV_String__item___0: value_t -> Prims.string =
  fun projectee  -> match projectee with | JSV_String _0 -> _0
let uu___is_JSV_Boolean: value_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_Boolean _0 -> true | uu____1194 -> false
let __proj__JSV_Boolean__item___0: value_t -> Prims.bool =
  fun projectee  -> match projectee with | JSV_Boolean _0 -> _0
let uu___is_JSV_Null: value_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_Null  -> true | uu____1205 -> false
let uu___is_JSV_Number: value_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSV_Number _0 -> true | uu____1210 -> false
let __proj__JSV_Number__item___0: value_t -> FStar_BaseTypes.float =
  fun projectee  -> match projectee with | JSV_Number _0 -> _0
let uu___is_JGP_Identifier: pattern_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JGP_Identifier _0 -> true | uu____1225 -> false
let __proj__JGP_Identifier__item___0: pattern_t -> (Prims.string* typ option)
  = fun projectee  -> match projectee with | JGP_Identifier _0 -> _0
let uu___is_JGP_Expression: pattern_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JGP_Expression _0 -> true | uu____1246 -> false
let __proj__JGP_Expression__item___0: pattern_t -> expression_t =
  fun projectee  -> match projectee with | JGP_Expression _0 -> _0
let uu___is_JSP_SpreadProperty: property_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | JSP_SpreadProperty _0 -> true
    | uu____1258 -> false
let __proj__JSP_SpreadProperty__item___0: property_t -> pattern_t =
  fun projectee  -> match projectee with | JSP_SpreadProperty _0 -> _0
let uu___is_JSP_Property: property_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSP_Property _0 -> true | uu____1272 -> false
let __proj__JSP_Property__item___0:
  property_t -> (object_prop_key_t* pattern_t) =
  fun projectee  -> match projectee with | JSP_Property _0 -> _0
let uu___is_JSO_Literal: object_prop_key_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSO_Literal _0 -> true | uu____1292 -> false
let __proj__JSO_Literal__item___0:
  object_prop_key_t -> (value_t* Prims.string) =
  fun projectee  -> match projectee with | JSO_Literal _0 -> _0
let uu___is_JSO_Identifier: object_prop_key_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSO_Identifier _0 -> true | uu____1313 -> false
let __proj__JSO_Identifier__item___0:
  object_prop_key_t -> (Prims.string* typ option) =
  fun projectee  -> match projectee with | JSO_Identifier _0 -> _0
let uu___is_JSO_Computed: object_prop_key_t -> Prims.bool =
  fun projectee  ->
    match projectee with | JSO_Computed _0 -> true | uu____1334 -> false
let __proj__JSO_Computed__item___0: object_prop_key_t -> expression_t =
  fun projectee  -> match projectee with | JSO_Computed _0 -> _0
let uu___is_JSE_Declaration: declaration -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Declaration _0 -> true | uu____1346 -> false
let __proj__JSE_Declaration__item___0: declaration -> statement_t =
  fun projectee  -> match projectee with | JSE_Declaration _0 -> _0
let uu___is_JSE_Expression: declaration -> Prims.bool =
  fun projectee  ->
    match projectee with | JSE_Expression _0 -> true | uu____1358 -> false
let __proj__JSE_Expression__item___0: declaration -> expression_t =
  fun projectee  -> match projectee with | JSE_Expression _0 -> _0
let uu___is_ExportType: export_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | ExportType  -> true | uu____1369 -> false
let uu___is_ExportValue: export_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | ExportValue  -> true | uu____1373 -> false
type t = source_t Prims.list
type identifier_t = (Prims.string* typ option)
type param_decl_t = Prims.string Prims.list
type function_t =
  ((Prims.string* typ option) option* pattern_t Prims.list* body_t* typ
    option* Prims.string Prims.list option)
type literal_t = (value_t* Prims.string)