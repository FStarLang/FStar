
open Prims

type source_t =
| JS_Statement of statement_t 
 and statement_t =
| JSS_Empty
| JSS_Block of statement_t Prims.list
| JSS_Expression of expression_t
| JSS_If of (expression_t * statement_t * statement_t Prims.option)
| JSS_Labeled of (identifier_t * statement_t)
| JSS_Break of identifier_t Prims.option
| JSS_Continue of identifier_t Prims.option
| JSS_With of (expression_t * statement_t)
| JSS_TypeAlias of (identifier_t * param_decl_t Prims.option * typ)
| JSS_Switch of (expression_t * (expression_t Prims.option * statement_t Prims.list) Prims.list)
| JSS_Return of expression_t Prims.option
| JSS_Throw of expression_t
| JSS_Try of (statement_t Prims.list * (pattern_t * statement_t Prims.list) Prims.option)
| JSS_While of (expression_t * statement_t)
| JSS_DoWhile of (statement_t * expression_t)
| JSS_For of (forinit_t Prims.option * expression_t Prims.option * expression_t Prims.option * statement_t)
| JSS_Forin of (forinit_t * expression_t * statement_t)
| JSS_ForOf of (forinit_t * expression_t * statement_t)
| JSS_Let of ((pattern_t * expression_t Prims.option) Prims.list * statement_t)
| JSS_Debugger
| JSS_FunctionDeclaration of function_t
| JSS_VariableDeclaration of ((pattern_t * expression_t Prims.option) Prims.list * kind_var_t)
| JSS_DeclareVariable of identifier_t
| JSS_DeclareFunction of (identifier_t * predicate_t Prims.option) 
 and expression_t =
| JSE_This
| JSE_Array of expression_t Prims.list Prims.option
| JSE_Object of property_obj_t Prims.list
| JSE_Function of function_t
| JSE_ArrowFunction of function_t
| JSE_Sequence of expression_t Prims.list
| JSE_Unary of (op_un * expression_t)
| JSE_Binary of (op_bin * expression_t * expression_t)
| JSE_Assignment of (pattern_t * expression_t)
| JSE_Update of (op_update * expression_t * Prims.bool)
| JSE_Logical of (op_log * expression_t * expression_t)
| JSE_Conditional of (expression_t * expression_t * expression_t)
| JSE_New of (expression_t * expression_t Prims.list)
| JSE_Call of (expression_t * expression_t Prims.list)
| JSE_Member of (expression_t * propmem_t)
| JSE_Yield of (expression_t Prims.option * Prims.bool)
| JSE_Comprehension of (t Prims.list * expression_t Prims.option)
| JSE_Generator of (t Prims.list * expression_t Prims.option)
| JSE_Let of ((pattern_t * expression_t Prims.option) Prims.list * expression_t)
| JSE_Identifier of identifier_t
| JSE_Literal of literal_t
| JSE_TypeCast of (expression_t * typ) 
 and op_un =
| JSU_Minus
| JSU_Plus
| JSU_Not
| JSU_BitNot
| JSU_Typeof
| JSU_Void
| JSU_Delete
| JSU_Await 
 and op_bin =
| JSB_Equal
| JSB_NotEqual
| JSB_StrictEqual
| JSB_StrictNotEqual
| JSB_LessThan
| JSB_LessThanEqual
| JSB_GreaterThan
| JSB_GreaterThanEqual
| JSB_LShift
| JSB_RShift
| JSB_RShift3
| JSB_Plus
| JSB_Minus
| JSB_Mult
| JSB_Exp
| JSB_Div
| JSB_Mod
| JSB_BitOr
| JSB_Xor
| JSB_BitAnd
| JSB_In
| JSB_Instanceof 
 and op_update =
| JSUP_Increment
| JSUP_Decrement 
 and op_log =
| JSL_Or
| JSL_And 
 and forinit_t =
| JSF_Declaration of ((pattern_t * expression_t Prims.option) Prims.list * kind_var_t)
| JSF_Expression of expression_t 
 and kind_var_t =
| JSV_Var
| JSV_Let
| JSV_Const 
 and kind_obj_t =
| JSO_Init
| JSO_Get
| JSO_Set 
 and property_obj_t =
| JSPO_Property of (object_prop_key_t * expression_t * kind_obj_t)
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
| JST_Function of ((identifier_t * typ) Prims.list * typ * param_decl_t Prims.option)
| JST_Object of ((object_prop_key_t * typ) Prims.list * (identifier_t * typ * typ) Prims.list * function_t Prims.list)
| JST_Array of typ
| JST_Generic of (generic_t * typ Prims.list Prims.option)
| JST_Union of typ Prims.list
| JST_Intersection of typ Prims.list
| JST_Typeof of typ
| JST_Tuple of typ Prims.list
| JST_StringLiteral of (Prims.string * Prims.string)
| JST_NumberLiteral of (FStar_BaseTypes.float * Prims.string)
| JST_BooleanLiteral of (Prims.bool * Prims.string)
| JST_Exists 
 and generic_t =
| Unqualified of identifier_t
| Qualified of (generic_t * identifier_t) 
 and body_t =
| JS_BodyBlock of statement_t Prims.list
| JS_BodyExpression of expression_t 
 and value_t =
| JSV_String of Prims.string
| JSV_Boolean of Prims.bool
| JSV_Null
| JSV_Number of FStar_BaseTypes.float
| JSV_RegExp of (Prims.string * Prims.string) 
 and predicate_t =
| JSP_Declared of expression_t
| JSP_Inferred 
 and pattern_t =
| JGP_Object of (property_t Prims.list * typ Prims.option)
| JGP_Array of (pattern_t Prims.list Prims.option * typ Prims.option)
| JGP_Assignment of (pattern_t * expression_t)
| JGP_Identifier of identifier_t
| JGP_Expression of expression_t 
 and property_t =
| JSP_SpreadProperty of pattern_t
| JSP_Property of (object_prop_key_t * pattern_t) 
 and object_prop_key_t =
| JSO_Literal of literal_t
| JSO_Identifier of identifier_t
| JSO_Computed of expression_t 
 and t =
source_t Prims.list 
 and identifier_t =
(Prims.string * typ Prims.option) 
 and function_t =
(identifier_t Prims.option * pattern_t Prims.list * body_t * typ Prims.option * param_decl_t Prims.option) 
 and literal_t =
(value_t * Prims.string) 
 and param_decl_t =
Prims.string Prims.list


let is_JS_Statement = (fun _discr_ -> (match (_discr_) with
| JS_Statement (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Empty = (fun _discr_ -> (match (_discr_) with
| JSS_Empty (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Block = (fun _discr_ -> (match (_discr_) with
| JSS_Block (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Expression = (fun _discr_ -> (match (_discr_) with
| JSS_Expression (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_If = (fun _discr_ -> (match (_discr_) with
| JSS_If (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Labeled = (fun _discr_ -> (match (_discr_) with
| JSS_Labeled (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Break = (fun _discr_ -> (match (_discr_) with
| JSS_Break (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Continue = (fun _discr_ -> (match (_discr_) with
| JSS_Continue (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_With = (fun _discr_ -> (match (_discr_) with
| JSS_With (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_TypeAlias = (fun _discr_ -> (match (_discr_) with
| JSS_TypeAlias (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Switch = (fun _discr_ -> (match (_discr_) with
| JSS_Switch (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Return = (fun _discr_ -> (match (_discr_) with
| JSS_Return (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Throw = (fun _discr_ -> (match (_discr_) with
| JSS_Throw (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Try = (fun _discr_ -> (match (_discr_) with
| JSS_Try (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_While = (fun _discr_ -> (match (_discr_) with
| JSS_While (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_DoWhile = (fun _discr_ -> (match (_discr_) with
| JSS_DoWhile (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_For = (fun _discr_ -> (match (_discr_) with
| JSS_For (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Forin = (fun _discr_ -> (match (_discr_) with
| JSS_Forin (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_ForOf = (fun _discr_ -> (match (_discr_) with
| JSS_ForOf (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Let = (fun _discr_ -> (match (_discr_) with
| JSS_Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_Debugger = (fun _discr_ -> (match (_discr_) with
| JSS_Debugger (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_FunctionDeclaration = (fun _discr_ -> (match (_discr_) with
| JSS_FunctionDeclaration (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_VariableDeclaration = (fun _discr_ -> (match (_discr_) with
| JSS_VariableDeclaration (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_DeclareVariable = (fun _discr_ -> (match (_discr_) with
| JSS_DeclareVariable (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSS_DeclareFunction = (fun _discr_ -> (match (_discr_) with
| JSS_DeclareFunction (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_This = (fun _discr_ -> (match (_discr_) with
| JSE_This (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Array = (fun _discr_ -> (match (_discr_) with
| JSE_Array (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Object = (fun _discr_ -> (match (_discr_) with
| JSE_Object (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Function = (fun _discr_ -> (match (_discr_) with
| JSE_Function (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_ArrowFunction = (fun _discr_ -> (match (_discr_) with
| JSE_ArrowFunction (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Sequence = (fun _discr_ -> (match (_discr_) with
| JSE_Sequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Unary = (fun _discr_ -> (match (_discr_) with
| JSE_Unary (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Binary = (fun _discr_ -> (match (_discr_) with
| JSE_Binary (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Assignment = (fun _discr_ -> (match (_discr_) with
| JSE_Assignment (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Update = (fun _discr_ -> (match (_discr_) with
| JSE_Update (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Logical = (fun _discr_ -> (match (_discr_) with
| JSE_Logical (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Conditional = (fun _discr_ -> (match (_discr_) with
| JSE_Conditional (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_New = (fun _discr_ -> (match (_discr_) with
| JSE_New (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Call = (fun _discr_ -> (match (_discr_) with
| JSE_Call (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Member = (fun _discr_ -> (match (_discr_) with
| JSE_Member (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Yield = (fun _discr_ -> (match (_discr_) with
| JSE_Yield (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Comprehension = (fun _discr_ -> (match (_discr_) with
| JSE_Comprehension (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Generator = (fun _discr_ -> (match (_discr_) with
| JSE_Generator (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Let = (fun _discr_ -> (match (_discr_) with
| JSE_Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Identifier = (fun _discr_ -> (match (_discr_) with
| JSE_Identifier (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_Literal = (fun _discr_ -> (match (_discr_) with
| JSE_Literal (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSE_TypeCast = (fun _discr_ -> (match (_discr_) with
| JSE_TypeCast (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Minus = (fun _discr_ -> (match (_discr_) with
| JSU_Minus (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Plus = (fun _discr_ -> (match (_discr_) with
| JSU_Plus (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Not = (fun _discr_ -> (match (_discr_) with
| JSU_Not (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_BitNot = (fun _discr_ -> (match (_discr_) with
| JSU_BitNot (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Typeof = (fun _discr_ -> (match (_discr_) with
| JSU_Typeof (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Void = (fun _discr_ -> (match (_discr_) with
| JSU_Void (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Delete = (fun _discr_ -> (match (_discr_) with
| JSU_Delete (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSU_Await = (fun _discr_ -> (match (_discr_) with
| JSU_Await (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Equal = (fun _discr_ -> (match (_discr_) with
| JSB_Equal (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_NotEqual = (fun _discr_ -> (match (_discr_) with
| JSB_NotEqual (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_StrictEqual = (fun _discr_ -> (match (_discr_) with
| JSB_StrictEqual (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_StrictNotEqual = (fun _discr_ -> (match (_discr_) with
| JSB_StrictNotEqual (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_LessThan = (fun _discr_ -> (match (_discr_) with
| JSB_LessThan (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_LessThanEqual = (fun _discr_ -> (match (_discr_) with
| JSB_LessThanEqual (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_GreaterThan = (fun _discr_ -> (match (_discr_) with
| JSB_GreaterThan (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_GreaterThanEqual = (fun _discr_ -> (match (_discr_) with
| JSB_GreaterThanEqual (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_LShift = (fun _discr_ -> (match (_discr_) with
| JSB_LShift (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_RShift = (fun _discr_ -> (match (_discr_) with
| JSB_RShift (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_RShift3 = (fun _discr_ -> (match (_discr_) with
| JSB_RShift3 (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Plus = (fun _discr_ -> (match (_discr_) with
| JSB_Plus (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Minus = (fun _discr_ -> (match (_discr_) with
| JSB_Minus (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Mult = (fun _discr_ -> (match (_discr_) with
| JSB_Mult (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Exp = (fun _discr_ -> (match (_discr_) with
| JSB_Exp (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Div = (fun _discr_ -> (match (_discr_) with
| JSB_Div (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Mod = (fun _discr_ -> (match (_discr_) with
| JSB_Mod (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_BitOr = (fun _discr_ -> (match (_discr_) with
| JSB_BitOr (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Xor = (fun _discr_ -> (match (_discr_) with
| JSB_Xor (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_BitAnd = (fun _discr_ -> (match (_discr_) with
| JSB_BitAnd (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_In = (fun _discr_ -> (match (_discr_) with
| JSB_In (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSB_Instanceof = (fun _discr_ -> (match (_discr_) with
| JSB_Instanceof (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSUP_Increment = (fun _discr_ -> (match (_discr_) with
| JSUP_Increment (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSUP_Decrement = (fun _discr_ -> (match (_discr_) with
| JSUP_Decrement (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSL_Or = (fun _discr_ -> (match (_discr_) with
| JSL_Or (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSL_And = (fun _discr_ -> (match (_discr_) with
| JSL_And (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSF_Declaration = (fun _discr_ -> (match (_discr_) with
| JSF_Declaration (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSF_Expression = (fun _discr_ -> (match (_discr_) with
| JSF_Expression (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_Var = (fun _discr_ -> (match (_discr_) with
| JSV_Var (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_Let = (fun _discr_ -> (match (_discr_) with
| JSV_Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_Const = (fun _discr_ -> (match (_discr_) with
| JSV_Const (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSO_Init = (fun _discr_ -> (match (_discr_) with
| JSO_Init (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSO_Get = (fun _discr_ -> (match (_discr_) with
| JSO_Get (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSO_Set = (fun _discr_ -> (match (_discr_) with
| JSO_Set (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSPO_Property = (fun _discr_ -> (match (_discr_) with
| JSPO_Property (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSPO_SpreadProperty = (fun _discr_ -> (match (_discr_) with
| JSPO_SpreadProperty (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSPM_Identifier = (fun _discr_ -> (match (_discr_) with
| JSPM_Identifier (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSPM_Expression = (fun _discr_ -> (match (_discr_) with
| JSPM_Expression (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Any = (fun _discr_ -> (match (_discr_) with
| JST_Any (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Mixed = (fun _discr_ -> (match (_discr_) with
| JST_Mixed (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Empty = (fun _discr_ -> (match (_discr_) with
| JST_Empty (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Void = (fun _discr_ -> (match (_discr_) with
| JST_Void (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Null = (fun _discr_ -> (match (_discr_) with
| JST_Null (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Number = (fun _discr_ -> (match (_discr_) with
| JST_Number (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_String = (fun _discr_ -> (match (_discr_) with
| JST_String (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Boolean = (fun _discr_ -> (match (_discr_) with
| JST_Boolean (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Nullable = (fun _discr_ -> (match (_discr_) with
| JST_Nullable (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Function = (fun _discr_ -> (match (_discr_) with
| JST_Function (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Object = (fun _discr_ -> (match (_discr_) with
| JST_Object (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Array = (fun _discr_ -> (match (_discr_) with
| JST_Array (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Generic = (fun _discr_ -> (match (_discr_) with
| JST_Generic (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Union = (fun _discr_ -> (match (_discr_) with
| JST_Union (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Intersection = (fun _discr_ -> (match (_discr_) with
| JST_Intersection (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Typeof = (fun _discr_ -> (match (_discr_) with
| JST_Typeof (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Tuple = (fun _discr_ -> (match (_discr_) with
| JST_Tuple (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_StringLiteral = (fun _discr_ -> (match (_discr_) with
| JST_StringLiteral (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_NumberLiteral = (fun _discr_ -> (match (_discr_) with
| JST_NumberLiteral (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_BooleanLiteral = (fun _discr_ -> (match (_discr_) with
| JST_BooleanLiteral (_) -> begin
true
end
| _ -> begin
false
end))


let is_JST_Exists = (fun _discr_ -> (match (_discr_) with
| JST_Exists (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unqualified = (fun _discr_ -> (match (_discr_) with
| Unqualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_Qualified = (fun _discr_ -> (match (_discr_) with
| Qualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_JS_BodyBlock = (fun _discr_ -> (match (_discr_) with
| JS_BodyBlock (_) -> begin
true
end
| _ -> begin
false
end))


let is_JS_BodyExpression = (fun _discr_ -> (match (_discr_) with
| JS_BodyExpression (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_String = (fun _discr_ -> (match (_discr_) with
| JSV_String (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_Boolean = (fun _discr_ -> (match (_discr_) with
| JSV_Boolean (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_Null = (fun _discr_ -> (match (_discr_) with
| JSV_Null (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_Number = (fun _discr_ -> (match (_discr_) with
| JSV_Number (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSV_RegExp = (fun _discr_ -> (match (_discr_) with
| JSV_RegExp (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSP_Declared = (fun _discr_ -> (match (_discr_) with
| JSP_Declared (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSP_Inferred = (fun _discr_ -> (match (_discr_) with
| JSP_Inferred (_) -> begin
true
end
| _ -> begin
false
end))


let is_JGP_Object = (fun _discr_ -> (match (_discr_) with
| JGP_Object (_) -> begin
true
end
| _ -> begin
false
end))


let is_JGP_Array = (fun _discr_ -> (match (_discr_) with
| JGP_Array (_) -> begin
true
end
| _ -> begin
false
end))


let is_JGP_Assignment = (fun _discr_ -> (match (_discr_) with
| JGP_Assignment (_) -> begin
true
end
| _ -> begin
false
end))


let is_JGP_Identifier = (fun _discr_ -> (match (_discr_) with
| JGP_Identifier (_) -> begin
true
end
| _ -> begin
false
end))


let is_JGP_Expression = (fun _discr_ -> (match (_discr_) with
| JGP_Expression (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSP_SpreadProperty = (fun _discr_ -> (match (_discr_) with
| JSP_SpreadProperty (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSP_Property = (fun _discr_ -> (match (_discr_) with
| JSP_Property (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSO_Literal = (fun _discr_ -> (match (_discr_) with
| JSO_Literal (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSO_Identifier = (fun _discr_ -> (match (_discr_) with
| JSO_Identifier (_) -> begin
true
end
| _ -> begin
false
end))


let is_JSO_Computed = (fun _discr_ -> (match (_discr_) with
| JSO_Computed (_) -> begin
true
end
| _ -> begin
false
end))


let ___JS_Statement____0 = (fun projectee -> (match (projectee) with
| JS_Statement (_81_2) -> begin
_81_2
end))


let ___JSS_Block____0 = (fun projectee -> (match (projectee) with
| JSS_Block (_81_5) -> begin
_81_5
end))


let ___JSS_Expression____0 = (fun projectee -> (match (projectee) with
| JSS_Expression (_81_8) -> begin
_81_8
end))


let ___JSS_If____0 = (fun projectee -> (match (projectee) with
| JSS_If (_81_11) -> begin
_81_11
end))


let ___JSS_Labeled____0 = (fun projectee -> (match (projectee) with
| JSS_Labeled (_81_14) -> begin
_81_14
end))


let ___JSS_Break____0 = (fun projectee -> (match (projectee) with
| JSS_Break (_81_17) -> begin
_81_17
end))


let ___JSS_Continue____0 = (fun projectee -> (match (projectee) with
| JSS_Continue (_81_20) -> begin
_81_20
end))


let ___JSS_With____0 = (fun projectee -> (match (projectee) with
| JSS_With (_81_23) -> begin
_81_23
end))


let ___JSS_TypeAlias____0 = (fun projectee -> (match (projectee) with
| JSS_TypeAlias (_81_26) -> begin
_81_26
end))


let ___JSS_Switch____0 = (fun projectee -> (match (projectee) with
| JSS_Switch (_81_29) -> begin
_81_29
end))


let ___JSS_Return____0 = (fun projectee -> (match (projectee) with
| JSS_Return (_81_32) -> begin
_81_32
end))


let ___JSS_Throw____0 = (fun projectee -> (match (projectee) with
| JSS_Throw (_81_35) -> begin
_81_35
end))


let ___JSS_Try____0 = (fun projectee -> (match (projectee) with
| JSS_Try (_81_38) -> begin
_81_38
end))


let ___JSS_While____0 = (fun projectee -> (match (projectee) with
| JSS_While (_81_41) -> begin
_81_41
end))


let ___JSS_DoWhile____0 = (fun projectee -> (match (projectee) with
| JSS_DoWhile (_81_44) -> begin
_81_44
end))


let ___JSS_For____0 = (fun projectee -> (match (projectee) with
| JSS_For (_81_47) -> begin
_81_47
end))


let ___JSS_Forin____0 = (fun projectee -> (match (projectee) with
| JSS_Forin (_81_50) -> begin
_81_50
end))


let ___JSS_ForOf____0 = (fun projectee -> (match (projectee) with
| JSS_ForOf (_81_53) -> begin
_81_53
end))


let ___JSS_Let____0 = (fun projectee -> (match (projectee) with
| JSS_Let (_81_56) -> begin
_81_56
end))


let ___JSS_FunctionDeclaration____0 = (fun projectee -> (match (projectee) with
| JSS_FunctionDeclaration (_81_59) -> begin
_81_59
end))


let ___JSS_VariableDeclaration____0 = (fun projectee -> (match (projectee) with
| JSS_VariableDeclaration (_81_62) -> begin
_81_62
end))


let ___JSS_DeclareVariable____0 = (fun projectee -> (match (projectee) with
| JSS_DeclareVariable (_81_65) -> begin
_81_65
end))


let ___JSS_DeclareFunction____0 = (fun projectee -> (match (projectee) with
| JSS_DeclareFunction (_81_68) -> begin
_81_68
end))


let ___JSE_Array____0 = (fun projectee -> (match (projectee) with
| JSE_Array (_81_71) -> begin
_81_71
end))


let ___JSE_Object____0 = (fun projectee -> (match (projectee) with
| JSE_Object (_81_74) -> begin
_81_74
end))


let ___JSE_Function____0 = (fun projectee -> (match (projectee) with
| JSE_Function (_81_77) -> begin
_81_77
end))


let ___JSE_ArrowFunction____0 = (fun projectee -> (match (projectee) with
| JSE_ArrowFunction (_81_80) -> begin
_81_80
end))


let ___JSE_Sequence____0 = (fun projectee -> (match (projectee) with
| JSE_Sequence (_81_83) -> begin
_81_83
end))


let ___JSE_Unary____0 = (fun projectee -> (match (projectee) with
| JSE_Unary (_81_86) -> begin
_81_86
end))


let ___JSE_Binary____0 = (fun projectee -> (match (projectee) with
| JSE_Binary (_81_89) -> begin
_81_89
end))


let ___JSE_Assignment____0 = (fun projectee -> (match (projectee) with
| JSE_Assignment (_81_92) -> begin
_81_92
end))


let ___JSE_Update____0 = (fun projectee -> (match (projectee) with
| JSE_Update (_81_95) -> begin
_81_95
end))


let ___JSE_Logical____0 = (fun projectee -> (match (projectee) with
| JSE_Logical (_81_98) -> begin
_81_98
end))


let ___JSE_Conditional____0 = (fun projectee -> (match (projectee) with
| JSE_Conditional (_81_101) -> begin
_81_101
end))


let ___JSE_New____0 = (fun projectee -> (match (projectee) with
| JSE_New (_81_104) -> begin
_81_104
end))


let ___JSE_Call____0 = (fun projectee -> (match (projectee) with
| JSE_Call (_81_107) -> begin
_81_107
end))


let ___JSE_Member____0 = (fun projectee -> (match (projectee) with
| JSE_Member (_81_110) -> begin
_81_110
end))


let ___JSE_Yield____0 = (fun projectee -> (match (projectee) with
| JSE_Yield (_81_113) -> begin
_81_113
end))


let ___JSE_Comprehension____0 = (fun projectee -> (match (projectee) with
| JSE_Comprehension (_81_116) -> begin
_81_116
end))


let ___JSE_Generator____0 = (fun projectee -> (match (projectee) with
| JSE_Generator (_81_119) -> begin
_81_119
end))


let ___JSE_Let____0 = (fun projectee -> (match (projectee) with
| JSE_Let (_81_122) -> begin
_81_122
end))


let ___JSE_Identifier____0 = (fun projectee -> (match (projectee) with
| JSE_Identifier (_81_125) -> begin
_81_125
end))


let ___JSE_Literal____0 = (fun projectee -> (match (projectee) with
| JSE_Literal (_81_128) -> begin
_81_128
end))


let ___JSE_TypeCast____0 = (fun projectee -> (match (projectee) with
| JSE_TypeCast (_81_131) -> begin
_81_131
end))


let ___JSF_Declaration____0 = (fun projectee -> (match (projectee) with
| JSF_Declaration (_81_134) -> begin
_81_134
end))


let ___JSF_Expression____0 = (fun projectee -> (match (projectee) with
| JSF_Expression (_81_137) -> begin
_81_137
end))


let ___JSPO_Property____0 = (fun projectee -> (match (projectee) with
| JSPO_Property (_81_140) -> begin
_81_140
end))


let ___JSPO_SpreadProperty____0 = (fun projectee -> (match (projectee) with
| JSPO_SpreadProperty (_81_143) -> begin
_81_143
end))


let ___JSPM_Identifier____0 = (fun projectee -> (match (projectee) with
| JSPM_Identifier (_81_146) -> begin
_81_146
end))


let ___JSPM_Expression____0 = (fun projectee -> (match (projectee) with
| JSPM_Expression (_81_149) -> begin
_81_149
end))


let ___JST_Nullable____0 = (fun projectee -> (match (projectee) with
| JST_Nullable (_81_152) -> begin
_81_152
end))


let ___JST_Function____0 = (fun projectee -> (match (projectee) with
| JST_Function (_81_155) -> begin
_81_155
end))


let ___JST_Object____0 = (fun projectee -> (match (projectee) with
| JST_Object (_81_158) -> begin
_81_158
end))


let ___JST_Array____0 = (fun projectee -> (match (projectee) with
| JST_Array (_81_161) -> begin
_81_161
end))


let ___JST_Generic____0 = (fun projectee -> (match (projectee) with
| JST_Generic (_81_164) -> begin
_81_164
end))


let ___JST_Union____0 = (fun projectee -> (match (projectee) with
| JST_Union (_81_167) -> begin
_81_167
end))


let ___JST_Intersection____0 = (fun projectee -> (match (projectee) with
| JST_Intersection (_81_170) -> begin
_81_170
end))


let ___JST_Typeof____0 = (fun projectee -> (match (projectee) with
| JST_Typeof (_81_173) -> begin
_81_173
end))


let ___JST_Tuple____0 = (fun projectee -> (match (projectee) with
| JST_Tuple (_81_176) -> begin
_81_176
end))


let ___JST_StringLiteral____0 = (fun projectee -> (match (projectee) with
| JST_StringLiteral (_81_179) -> begin
_81_179
end))


let ___JST_NumberLiteral____0 = (fun projectee -> (match (projectee) with
| JST_NumberLiteral (_81_182) -> begin
_81_182
end))


let ___JST_BooleanLiteral____0 = (fun projectee -> (match (projectee) with
| JST_BooleanLiteral (_81_185) -> begin
_81_185
end))


let ___Unqualified____0 = (fun projectee -> (match (projectee) with
| Unqualified (_81_188) -> begin
_81_188
end))


let ___Qualified____0 = (fun projectee -> (match (projectee) with
| Qualified (_81_191) -> begin
_81_191
end))


let ___JS_BodyBlock____0 = (fun projectee -> (match (projectee) with
| JS_BodyBlock (_81_194) -> begin
_81_194
end))


let ___JS_BodyExpression____0 = (fun projectee -> (match (projectee) with
| JS_BodyExpression (_81_197) -> begin
_81_197
end))


let ___JSV_String____0 = (fun projectee -> (match (projectee) with
| JSV_String (_81_200) -> begin
_81_200
end))


let ___JSV_Boolean____0 = (fun projectee -> (match (projectee) with
| JSV_Boolean (_81_203) -> begin
_81_203
end))


let ___JSV_Number____0 = (fun projectee -> (match (projectee) with
| JSV_Number (_81_206) -> begin
_81_206
end))


let ___JSV_RegExp____0 = (fun projectee -> (match (projectee) with
| JSV_RegExp (_81_209) -> begin
_81_209
end))


let ___JSP_Declared____0 = (fun projectee -> (match (projectee) with
| JSP_Declared (_81_212) -> begin
_81_212
end))


let ___JGP_Object____0 = (fun projectee -> (match (projectee) with
| JGP_Object (_81_215) -> begin
_81_215
end))


let ___JGP_Array____0 = (fun projectee -> (match (projectee) with
| JGP_Array (_81_218) -> begin
_81_218
end))


let ___JGP_Assignment____0 = (fun projectee -> (match (projectee) with
| JGP_Assignment (_81_221) -> begin
_81_221
end))


let ___JGP_Identifier____0 = (fun projectee -> (match (projectee) with
| JGP_Identifier (_81_224) -> begin
_81_224
end))


let ___JGP_Expression____0 = (fun projectee -> (match (projectee) with
| JGP_Expression (_81_227) -> begin
_81_227
end))


let ___JSP_SpreadProperty____0 = (fun projectee -> (match (projectee) with
| JSP_SpreadProperty (_81_230) -> begin
_81_230
end))


let ___JSP_Property____0 = (fun projectee -> (match (projectee) with
| JSP_Property (_81_233) -> begin
_81_233
end))


let ___JSO_Literal____0 = (fun projectee -> (match (projectee) with
| JSO_Literal (_81_236) -> begin
_81_236
end))


let ___JSO_Identifier____0 = (fun projectee -> (match (projectee) with
| JSO_Identifier (_81_239) -> begin
_81_239
end))


let ___JSO_Computed____0 = (fun projectee -> (match (projectee) with
| JSO_Computed (_81_242) -> begin
_81_242
end))




