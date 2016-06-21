
open Prims

type level =
| Un
| Expr
| Type
| Kind
| Formula


let is_Un = (fun _discr_ -> (match (_discr_) with
| Un (_) -> begin
true
end
| _ -> begin
false
end))


let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr (_) -> begin
true
end
| _ -> begin
false
end))


let is_Type = (fun _discr_ -> (match (_discr_) with
| Type (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind (_) -> begin
true
end
| _ -> begin
false
end))


let is_Formula = (fun _discr_ -> (match (_discr_) with
| Formula (_) -> begin
true
end
| _ -> begin
false
end))


type imp =
| FsTypApp
| Hash
| Nothing


let is_FsTypApp = (fun _discr_ -> (match (_discr_) with
| FsTypApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Hash = (fun _discr_ -> (match (_discr_) with
| Hash (_) -> begin
true
end
| _ -> begin
false
end))


let is_Nothing = (fun _discr_ -> (match (_discr_) with
| Nothing (_) -> begin
true
end
| _ -> begin
false
end))


type arg_qualifier =
| Implicit
| Equality


let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))


let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))


type aqual =
arg_qualifier Prims.option


type let_qualifier =
| NoLetQualifier
| Rec
| Mutable


let is_NoLetQualifier = (fun _discr_ -> (match (_discr_) with
| NoLetQualifier (_) -> begin
true
end
| _ -> begin
false
end))


let is_Rec = (fun _discr_ -> (match (_discr_) with
| Rec (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mutable = (fun _discr_ -> (match (_discr_) with
| Mutable (_) -> begin
true
end
| _ -> begin
false
end))


type term' =
| Wild
| Const of FStar_Const.sconst
| Op of (Prims.string * term Prims.list)
| Tvar of FStar_Ident.ident
| Var of FStar_Ident.lid
| Name of FStar_Ident.lid
| Construct of (FStar_Ident.lid * (term * imp) Prims.list)
| Abs of (pattern Prims.list * term)
| App of (term * term * imp)
| Let of (let_qualifier * (pattern * term) Prims.list * term)
| Seq of (term * term)
| If of (term * term * term)
| Match of (term * branch Prims.list)
| TryWith of (term * branch Prims.list)
| Ascribed of (term * term)
| Record of (term Prims.option * (FStar_Ident.lid * term) Prims.list)
| Project of (term * FStar_Ident.lid)
| Product of (binder Prims.list * term)
| Sum of (binder Prims.list * term)
| QForall of (binder Prims.list * term Prims.list Prims.list * term)
| QExists of (binder Prims.list * term Prims.list Prims.list * term)
| Refine of (binder * term)
| NamedTyp of (FStar_Ident.ident * term)
| Paren of term
| Requires of (term * Prims.string Prims.option)
| Ensures of (term * Prims.string Prims.option)
| Labeled of (term * Prims.string * Prims.bool)
| Assign of (FStar_Ident.ident * term) 
 and term =
{tm : term'; range : FStar_Range.range; level : level} 
 and binder' =
| Variable of FStar_Ident.ident
| TVariable of FStar_Ident.ident
| Annotated of (FStar_Ident.ident * term)
| TAnnotated of (FStar_Ident.ident * term)
| NoName of term 
 and binder =
{b : binder'; brange : FStar_Range.range; blevel : level; aqual : aqual} 
 and pattern' =
| PatWild
| PatConst of FStar_Const.sconst
| PatApp of (pattern * pattern Prims.list)
| PatVar of (FStar_Ident.ident * arg_qualifier Prims.option)
| PatName of FStar_Ident.lid
| PatTvar of (FStar_Ident.ident * arg_qualifier Prims.option)
| PatList of pattern Prims.list
| PatTuple of (pattern Prims.list * Prims.bool)
| PatRecord of (FStar_Ident.lid * pattern) Prims.list
| PatAscribed of (pattern * term)
| PatOr of pattern Prims.list 
 and pattern =
{pat : pattern'; prange : FStar_Range.range} 
 and branch =
(pattern * term Prims.option * term)


let is_Wild = (fun _discr_ -> (match (_discr_) with
| Wild (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const = (fun _discr_ -> (match (_discr_) with
| Const (_) -> begin
true
end
| _ -> begin
false
end))


let is_Op = (fun _discr_ -> (match (_discr_) with
| Op (_) -> begin
true
end
| _ -> begin
false
end))


let is_Tvar = (fun _discr_ -> (match (_discr_) with
| Tvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))


let is_Name = (fun _discr_ -> (match (_discr_) with
| Name (_) -> begin
true
end
| _ -> begin
false
end))


let is_Construct = (fun _discr_ -> (match (_discr_) with
| Construct (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))


let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))


let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Seq = (fun _discr_ -> (match (_discr_) with
| Seq (_) -> begin
true
end
| _ -> begin
false
end))


let is_If = (fun _discr_ -> (match (_discr_) with
| If (_) -> begin
true
end
| _ -> begin
false
end))


let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))


let is_TryWith = (fun _discr_ -> (match (_discr_) with
| TryWith (_) -> begin
true
end
| _ -> begin
false
end))


let is_Ascribed = (fun _discr_ -> (match (_discr_) with
| Ascribed (_) -> begin
true
end
| _ -> begin
false
end))


let is_Record = (fun _discr_ -> (match (_discr_) with
| Record (_) -> begin
true
end
| _ -> begin
false
end))


let is_Project = (fun _discr_ -> (match (_discr_) with
| Project (_) -> begin
true
end
| _ -> begin
false
end))


let is_Product = (fun _discr_ -> (match (_discr_) with
| Product (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sum = (fun _discr_ -> (match (_discr_) with
| Sum (_) -> begin
true
end
| _ -> begin
false
end))


let is_QForall = (fun _discr_ -> (match (_discr_) with
| QForall (_) -> begin
true
end
| _ -> begin
false
end))


let is_QExists = (fun _discr_ -> (match (_discr_) with
| QExists (_) -> begin
true
end
| _ -> begin
false
end))


let is_Refine = (fun _discr_ -> (match (_discr_) with
| Refine (_) -> begin
true
end
| _ -> begin
false
end))


let is_NamedTyp = (fun _discr_ -> (match (_discr_) with
| NamedTyp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Paren = (fun _discr_ -> (match (_discr_) with
| Paren (_) -> begin
true
end
| _ -> begin
false
end))


let is_Requires = (fun _discr_ -> (match (_discr_) with
| Requires (_) -> begin
true
end
| _ -> begin
false
end))


let is_Ensures = (fun _discr_ -> (match (_discr_) with
| Ensures (_) -> begin
true
end
| _ -> begin
false
end))


let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assign = (fun _discr_ -> (match (_discr_) with
| Assign (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))


let is_Variable = (fun _discr_ -> (match (_discr_) with
| Variable (_) -> begin
true
end
| _ -> begin
false
end))


let is_TVariable = (fun _discr_ -> (match (_discr_) with
| TVariable (_) -> begin
true
end
| _ -> begin
false
end))


let is_Annotated = (fun _discr_ -> (match (_discr_) with
| Annotated (_) -> begin
true
end
| _ -> begin
false
end))


let is_TAnnotated = (fun _discr_ -> (match (_discr_) with
| TAnnotated (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoName = (fun _discr_ -> (match (_discr_) with
| NoName (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_PatWild = (fun _discr_ -> (match (_discr_) with
| PatWild (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatConst = (fun _discr_ -> (match (_discr_) with
| PatConst (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatApp = (fun _discr_ -> (match (_discr_) with
| PatApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatVar = (fun _discr_ -> (match (_discr_) with
| PatVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatName = (fun _discr_ -> (match (_discr_) with
| PatName (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatTvar = (fun _discr_ -> (match (_discr_) with
| PatTvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatList = (fun _discr_ -> (match (_discr_) with
| PatList (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatTuple = (fun _discr_ -> (match (_discr_) with
| PatTuple (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatRecord = (fun _discr_ -> (match (_discr_) with
| PatRecord (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatAscribed = (fun _discr_ -> (match (_discr_) with
| PatAscribed (_) -> begin
true
end
| _ -> begin
false
end))


let is_PatOr = (fun _discr_ -> (match (_discr_) with
| PatOr (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))


let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_58_16) -> begin
_58_16
end))


let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_58_19) -> begin
_58_19
end))


let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_58_22) -> begin
_58_22
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_58_25) -> begin
_58_25
end))


let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_58_28) -> begin
_58_28
end))


let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_58_31) -> begin
_58_31
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_58_34) -> begin
_58_34
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_58_37) -> begin
_58_37
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_58_40) -> begin
_58_40
end))


let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_58_43) -> begin
_58_43
end))


let ___If____0 = (fun projectee -> (match (projectee) with
| If (_58_46) -> begin
_58_46
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_58_49) -> begin
_58_49
end))


let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_58_52) -> begin
_58_52
end))


let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_58_55) -> begin
_58_55
end))


let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_58_58) -> begin
_58_58
end))


let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_58_61) -> begin
_58_61
end))


let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_58_64) -> begin
_58_64
end))


let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_58_67) -> begin
_58_67
end))


let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_58_70) -> begin
_58_70
end))


let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_58_73) -> begin
_58_73
end))


let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_58_76) -> begin
_58_76
end))


let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_58_79) -> begin
_58_79
end))


let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_58_82) -> begin
_58_82
end))


let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_58_85) -> begin
_58_85
end))


let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_58_88) -> begin
_58_88
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_58_91) -> begin
_58_91
end))


let ___Assign____0 = (fun projectee -> (match (projectee) with
| Assign (_58_94) -> begin
_58_94
end))


let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_58_98) -> begin
_58_98
end))


let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_58_101) -> begin
_58_101
end))


let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_58_104) -> begin
_58_104
end))


let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_58_107) -> begin
_58_107
end))


let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_58_110) -> begin
_58_110
end))


let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_58_114) -> begin
_58_114
end))


let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_58_117) -> begin
_58_117
end))


let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_58_120) -> begin
_58_120
end))


let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_58_123) -> begin
_58_123
end))


let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_58_126) -> begin
_58_126
end))


let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_58_129) -> begin
_58_129
end))


let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_58_132) -> begin
_58_132
end))


let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_58_135) -> begin
_58_135
end))


let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_58_138) -> begin
_58_138
end))


let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_58_141) -> begin
_58_141
end))


type knd =
term


type typ =
term


type expr =
term


type tycon =
| TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd Prims.option)
| TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd Prims.option * term)
| TyconRecord of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term) Prims.list)
| TyconVariant of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term Prims.option * Prims.bool) Prims.list)


let is_TyconAbstract = (fun _discr_ -> (match (_discr_) with
| TyconAbstract (_) -> begin
true
end
| _ -> begin
false
end))


let is_TyconAbbrev = (fun _discr_ -> (match (_discr_) with
| TyconAbbrev (_) -> begin
true
end
| _ -> begin
false
end))


let is_TyconRecord = (fun _discr_ -> (match (_discr_) with
| TyconRecord (_) -> begin
true
end
| _ -> begin
false
end))


let is_TyconVariant = (fun _discr_ -> (match (_discr_) with
| TyconVariant (_) -> begin
true
end
| _ -> begin
false
end))


let ___TyconAbstract____0 = (fun projectee -> (match (projectee) with
| TyconAbstract (_58_145) -> begin
_58_145
end))


let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_58_148) -> begin
_58_148
end))


let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_58_151) -> begin
_58_151
end))


let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_58_154) -> begin
_58_154
end))


type qualifier =
| Private
| Abstract
| Noeq
| Assumption
| DefaultEffect
| TotalEffect
| Effect
| New
| Inline
| Unfoldable
| Irreducible
| Opaque
| Logic


let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))


let is_Noeq = (fun _discr_ -> (match (_discr_) with
| Noeq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))


let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))


let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable (_) -> begin
true
end
| _ -> begin
false
end))


let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))


let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque (_) -> begin
true
end
| _ -> begin
false
end))


let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))


type qualifiers =
qualifier Prims.list


type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : term}


let is_Mklift : lift  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklift"))))


type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string Prims.option


let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))


let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))


let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_58_161) -> begin
_58_161
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_58_164) -> begin
_58_164
end))


type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| KindAbbrev of (FStar_Ident.ident * binder Prims.list * knd)
| ToplevelLet of (qualifiers * let_qualifier * (pattern * term) Prims.list)
| Main of term
| Assume of (qualifiers * FStar_Ident.ident * term)
| Tycon of (qualifiers * tycon Prims.list)
| Val of (qualifiers * FStar_Ident.ident * term)
| Exception of (FStar_Ident.ident * term Prims.option)
| NewEffect of (qualifiers * effect_decl)
| NewEffectForFree of effect_decl
| SubEffect of lift
| Pragma of pragma 
 and decl =
{d : decl'; drange : FStar_Range.range} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)


let is_TopLevelModule = (fun _discr_ -> (match (_discr_) with
| TopLevelModule (_) -> begin
true
end
| _ -> begin
false
end))


let is_Open = (fun _discr_ -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))


let is_ModuleAbbrev = (fun _discr_ -> (match (_discr_) with
| ModuleAbbrev (_) -> begin
true
end
| _ -> begin
false
end))


let is_KindAbbrev = (fun _discr_ -> (match (_discr_) with
| KindAbbrev (_) -> begin
true
end
| _ -> begin
false
end))


let is_ToplevelLet = (fun _discr_ -> (match (_discr_) with
| ToplevelLet (_) -> begin
true
end
| _ -> begin
false
end))


let is_Main = (fun _discr_ -> (match (_discr_) with
| Main (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))


let is_Tycon = (fun _discr_ -> (match (_discr_) with
| Tycon (_) -> begin
true
end
| _ -> begin
false
end))


let is_Val = (fun _discr_ -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exception = (fun _discr_ -> (match (_discr_) with
| Exception (_) -> begin
true
end
| _ -> begin
false
end))


let is_NewEffect = (fun _discr_ -> (match (_discr_) with
| NewEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_NewEffectForFree = (fun _discr_ -> (match (_discr_) with
| NewEffectForFree (_) -> begin
true
end
| _ -> begin
false
end))


let is_SubEffect = (fun _discr_ -> (match (_discr_) with
| SubEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Pragma = (fun _discr_ -> (match (_discr_) with
| Pragma (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkdecl : decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdecl"))))


let is_DefineEffect = (fun _discr_ -> (match (_discr_) with
| DefineEffect (_) -> begin
true
end
| _ -> begin
false
end))


let is_RedefineEffect = (fun _discr_ -> (match (_discr_) with
| RedefineEffect (_) -> begin
true
end
| _ -> begin
false
end))


let ___TopLevelModule____0 = (fun projectee -> (match (projectee) with
| TopLevelModule (_58_169) -> begin
_58_169
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_58_172) -> begin
_58_172
end))


let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_58_175) -> begin
_58_175
end))


let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_58_178) -> begin
_58_178
end))


let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_58_181) -> begin
_58_181
end))


let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_58_184) -> begin
_58_184
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_58_187) -> begin
_58_187
end))


let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_58_190) -> begin
_58_190
end))


let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_58_193) -> begin
_58_193
end))


let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_58_196) -> begin
_58_196
end))


let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_58_199) -> begin
_58_199
end))


let ___NewEffectForFree____0 = (fun projectee -> (match (projectee) with
| NewEffectForFree (_58_202) -> begin
_58_202
end))


let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_58_205) -> begin
_58_205
end))


let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_58_208) -> begin
_58_208
end))


let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_58_212) -> begin
_58_212
end))


let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_58_215) -> begin
_58_215
end))


type modul =
| Module of (FStar_Ident.lid * decl Prims.list)
| Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool)


let is_Module = (fun _discr_ -> (match (_discr_) with
| Module (_) -> begin
true
end
| _ -> begin
false
end))


let is_Interface = (fun _discr_ -> (match (_discr_) with
| Interface (_) -> begin
true
end
| _ -> begin
false
end))


let ___Module____0 = (fun projectee -> (match (projectee) with
| Module (_58_218) -> begin
_58_218
end))


let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_58_221) -> begin
_58_221
end))


type file =
modul Prims.list


type inputFragment =
(file, decl Prims.list) FStar_Util.either


let check_id : FStar_Ident.ident  ->  Prims.unit = (fun id -> if (FStar_Options.universes ()) then begin
(

let first_char = (FStar_String.substring id.FStar_Ident.idText 0 1)
in if ((FStar_String.lowercase first_char) = first_char) then begin
()
end else begin
<<<<<<< HEAD
(let _148_987 = (let _148_986 = (let _148_985 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in (_148_985, id.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_148_986))
in (Prims.raise _148_987))
=======
(let _149_1003 = (let _149_1002 = (let _149_1001 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in (_149_1001, id.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_149_1002))
in (Prims.raise _149_1003))
>>>>>>> master
end)
end else begin
()
end)


let mk_decl : decl'  ->  FStar_Range.range  ->  decl = (fun d r -> {d = d; drange = r})


let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})


let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((FStar_List.append ps p'), body'))
end
| _58_242 -> begin
Abs ((ps, body))
end))


let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = if (FStar_Options.universes ()) then begin
(

let i = (FStar_Syntax_Syntax.next_id ())
in (FStar_Ident.gen r1))
end else begin
(FStar_Absyn_Util.genident (Some (r1)))
end
<<<<<<< HEAD
in (let _148_1027 = (let _148_1026 = (let _148_1025 = (let _148_1024 = (let _148_1023 = (let _148_1022 = (let _148_1021 = (let _148_1020 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_148_1020))
in (mk_term _148_1021 r1 Expr))
in (_148_1022, branches))
in Match (_148_1023))
in (mk_term _148_1024 r2 Expr))
in (((mk_pattern (PatVar ((x, None))) r1))::[], _148_1025))
in Abs (_148_1026))
in (mk_term _148_1027 r2 Expr))))
=======
in (let _149_1043 = (let _149_1042 = (let _149_1041 = (let _149_1040 = (let _149_1039 = (let _149_1038 = (let _149_1037 = (let _149_1036 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_149_1036))
in (mk_term _149_1037 r1 Expr))
in (_149_1038, branches))
in Match (_149_1039))
in (mk_term _149_1040 r2 Expr))
in (((mk_pattern (PatVar ((x, None))) r1))::[], _149_1041))
in Abs (_149_1042))
in (mk_term _149_1043 r2 Expr))))
>>>>>>> master


let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_58_251), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _58_259 -> begin
None
end))


<<<<<<< HEAD
let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _148_1036 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _148_1036 r)))
=======
let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _149_1052 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _149_1052 r)))
>>>>>>> master


let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd tl -> PatApp (((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))


let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))


let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))


let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct ((FStar_Absyn_Const.nil_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))


let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct ((FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))


let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _58_286 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _58_290 -> begin
(FStar_List.fold_left (fun t _58_294 -> (match (_58_294) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

<<<<<<< HEAD
<<<<<<< HEAD
let empty = (let _148_1080 = (let _148_1079 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
=======
let empty = (let _148_1080 = (let _148_1079 = (FStar_Ident.set_lid_range FStar_Absyn_Const.tset_empty r)
>>>>>>> aa37889a5d27fe5e89f0f746f1cb47144c601d0a
in Var (_148_1079))
in (mk_term _148_1080 r Expr))
in (

let ref_constr = (let _148_1082 = (let _148_1081 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_148_1081))
in (mk_term _148_1082 r Expr))
in (

let singleton = (let _148_1084 = (let _148_1083 = (FStar_Ident.set_lid_range FStar_Absyn_Const.tset_singleton r)
in Var (_148_1083))
in (mk_term _148_1084 r Expr))
in (

let union = (let _148_1086 = (let _148_1085 = (FStar_Ident.set_lid_range FStar_Absyn_Const.tset_union r)
in Var (_148_1085))
in (mk_term _148_1086 r Expr))
=======
let empty = (let _149_1096 = (let _149_1095 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_149_1095))
in (mk_term _149_1096 r Expr))
in (

let ref_constr = (let _149_1098 = (let _149_1097 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_149_1097))
in (mk_term _149_1098 r Expr))
in (

let singleton = (let _149_1100 = (let _149_1099 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_149_1099))
in (mk_term _149_1100 r Expr))
in (

let union = (let _149_1102 = (let _149_1101 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_149_1101))
in (mk_term _149_1102 r Expr))
>>>>>>> master
in (FStar_List.fold_right (fun e tl -> (

let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (

let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))


let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _58_310 -> begin
(match (t.tm) with
| Name (s) -> begin
<<<<<<< HEAD
(let _148_1098 = (let _148_1097 = (let _148_1096 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _148_1096))
in Construct (_148_1097))
in (mk_term _148_1098 r Un))
=======
(let _149_1114 = (let _149_1113 = (let _149_1112 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _149_1112))
in Construct (_149_1113))
in (mk_term _149_1114 r Un))
>>>>>>> master
end
| _58_315 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (

let admit = (

<<<<<<< HEAD
let admit_name = (let _148_1104 = (let _148_1103 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_148_1103))
in (mk_term _148_1104 r Expr))
=======
let admit_name = (let _149_1120 = (let _149_1119 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_149_1119))
in (mk_term _149_1120 r Expr))
>>>>>>> master
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (

let magic = (

<<<<<<< HEAD
let magic_name = (let _148_1106 = (let _148_1105 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_148_1105))
in (mk_term _148_1106 r Expr))
=======
let magic_name = (let _149_1122 = (let _149_1121 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_149_1121))
in (mk_term _149_1122 r Expr))
>>>>>>> master
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (

let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))


<<<<<<< HEAD
let mkWildAdmitMagic = (fun r -> (let _148_1108 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _148_1108)))
=======
let mkWildAdmitMagic = (fun r -> (let _149_1124 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _149_1124)))
>>>>>>> master


let focusBranches = (fun branches r -> (

let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(

let _58_329 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (

<<<<<<< HEAD
let focussed = (let _148_1111 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _148_1111 (FStar_List.map Prims.snd)))
in (let _148_1113 = (let _148_1112 = (mkWildAdmitMagic r)
in (_148_1112)::[])
in (FStar_List.append focussed _148_1113))))
=======
let focussed = (let _149_1127 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _149_1127 (FStar_List.map Prims.snd)))
in (let _149_1129 = (let _149_1128 = (mkWildAdmitMagic r)
in (_149_1128)::[])
in (FStar_List.append focussed _149_1129))))
>>>>>>> master
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))


let focusLetBindings = (fun lbs r -> (

let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(

let _58_335 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _58_339 -> (match (_58_339) with
| (f, lb) -> begin
if f then begin
lb
end else begin
<<<<<<< HEAD
(let _148_1117 = (mkAdmitMagic r)
in ((Prims.fst lb), _148_1117))
=======
(let _149_1133 = (mkAdmitMagic r)
in ((Prims.fst lb), _149_1133))
>>>>>>> master
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))


<<<<<<< HEAD
let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _148_1125 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _148_1125 r)))
=======
let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _149_1141 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _149_1141 r)))
>>>>>>> master


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
<<<<<<< HEAD
in (let _148_1131 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _148_1131 r))))
=======
in (let _149_1147 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _149_1147 r))))
>>>>>>> master


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
<<<<<<< HEAD
in (let _148_1137 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _148_1137 r))))
=======
in (let _149_1153 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _149_1153 r))))
>>>>>>> master


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t refopt m implicit -> (

let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))


let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term Prims.option) Prims.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some ((x, t, None))
end
| Refine ({b = Annotated (x, t); brange = _58_371; blevel = _58_369; aqual = _58_367}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _58_383 -> begin
None
end))


<<<<<<< HEAD
let to_string_l = (fun sep f l -> (let _148_1156 = (FStar_List.map f l)
in (FStar_String.concat sep _148_1156)))
=======
let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun _58_1 -> (match (_58_1) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end
| Mutable -> begin
"mutable"
end))


let to_string_l = (fun sep f l -> (let _149_1174 = (FStar_List.map f l)
in (FStar_String.concat sep _149_1174)))
>>>>>>> master


let imp_to_string : imp  ->  Prims.string = (fun _58_2 -> (match (_58_2) with
| Hash -> begin
"#"
end
| _58_394 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
<<<<<<< HEAD
| Requires (t, _58_391) -> begin
(let _148_1164 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _148_1164))
end
| Ensures (t, _58_396) -> begin
(let _148_1165 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _148_1165))
end
| Labeled (t, l, _58_402) -> begin
(let _148_1166 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _148_1166))
=======
| Requires (t, _58_399) -> begin
(let _149_1182 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _149_1182))
end
| Ensures (t, _58_404) -> begin
(let _149_1183 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _149_1183))
end
| Labeled (t, l, _58_410) -> begin
(let _149_1184 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _149_1184))
>>>>>>> master
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
<<<<<<< HEAD
(let _148_1169 = (let _148_1168 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _148_1168))
in (FStar_Util.format2 "%s(%s)" s _148_1169))
=======
(let _149_1187 = (let _149_1186 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _149_1186))
in (FStar_Util.format2 "%s(%s)" s _149_1187))
>>>>>>> master
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
<<<<<<< HEAD
(let _148_1172 = (to_string_l " " (fun _58_423 -> (match (_58_423) with
| (a, imp) -> begin
(let _148_1171 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _148_1171))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _148_1172))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _148_1174 = (to_string_l " " pat_to_string pats)
in (let _148_1173 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _148_1174 _148_1173)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _148_1176 = (to_string_l " " pat_to_string pats)
in (let _148_1175 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _148_1176 _148_1175)))
end
| App (t1, t2, imp) -> begin
(let _148_1178 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1177 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _148_1178 (imp_to_string imp) _148_1177)))
end
| Let (false, ((pat, tm))::[], body) -> begin
(let _148_1181 = (FStar_All.pipe_right pat pat_to_string)
in (let _148_1180 = (FStar_All.pipe_right tm term_to_string)
in (let _148_1179 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _148_1181 _148_1180 _148_1179))))
end
| Let (_58_446, lbs, body) -> begin
(let _148_1186 = (to_string_l " and " (fun _58_453 -> (match (_58_453) with
| (p, b) -> begin
(let _148_1184 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1183 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _148_1184 _148_1183)))
end)) lbs)
in (let _148_1185 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _148_1186 _148_1185)))
end
| Seq (t1, t2) -> begin
(let _148_1188 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1187 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _148_1188 _148_1187)))
end
| If (t1, t2, t3) -> begin
(let _148_1191 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1190 = (FStar_All.pipe_right t2 term_to_string)
in (let _148_1189 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _148_1191 _148_1190 _148_1189))))
end
| Match (t, branches) -> begin
(let _148_1198 = (FStar_All.pipe_right t term_to_string)
in (let _148_1197 = (to_string_l " | " (fun _58_470 -> (match (_58_470) with
| (p, w, e) -> begin
(let _148_1196 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1195 = (match (w) with
=======
(let _149_1190 = (to_string_l " " (fun _58_431 -> (match (_58_431) with
| (a, imp) -> begin
(let _149_1189 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _149_1189))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _149_1190))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _149_1192 = (to_string_l " " pat_to_string pats)
in (let _149_1191 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _149_1192 _149_1191)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _149_1194 = (to_string_l " " pat_to_string pats)
in (let _149_1193 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _149_1194 _149_1193)))
end
| App (t1, t2, imp) -> begin
(let _149_1196 = (FStar_All.pipe_right t1 term_to_string)
in (let _149_1195 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _149_1196 (imp_to_string imp) _149_1195)))
end
| Let (Rec, lbs, body) -> begin
(let _149_1201 = (to_string_l " and " (fun _58_452 -> (match (_58_452) with
| (p, b) -> begin
(let _149_1199 = (FStar_All.pipe_right p pat_to_string)
in (let _149_1198 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _149_1199 _149_1198)))
end)) lbs)
in (let _149_1200 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _149_1201 _149_1200)))
end
| Let (q, ((pat, tm))::[], body) -> begin
(let _149_1204 = (FStar_All.pipe_right pat pat_to_string)
in (let _149_1203 = (FStar_All.pipe_right tm term_to_string)
in (let _149_1202 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) _149_1204 _149_1203 _149_1202))))
end
| Seq (t1, t2) -> begin
(let _149_1206 = (FStar_All.pipe_right t1 term_to_string)
in (let _149_1205 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _149_1206 _149_1205)))
end
| If (t1, t2, t3) -> begin
(let _149_1209 = (FStar_All.pipe_right t1 term_to_string)
in (let _149_1208 = (FStar_All.pipe_right t2 term_to_string)
in (let _149_1207 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _149_1209 _149_1208 _149_1207))))
end
| Match (t, branches) -> begin
(let _149_1216 = (FStar_All.pipe_right t term_to_string)
in (let _149_1215 = (to_string_l " | " (fun _58_477 -> (match (_58_477) with
| (p, w, e) -> begin
(let _149_1214 = (FStar_All.pipe_right p pat_to_string)
in (let _149_1213 = (match (w) with
>>>>>>> master
| None -> begin
""
end
| Some (e) -> begin
<<<<<<< HEAD
(let _148_1193 = (term_to_string e)
in (FStar_Util.format1 "when %s" _148_1193))
end)
in (let _148_1194 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _148_1196 _148_1195 _148_1194))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _148_1198 _148_1197)))
end
| Ascribed (t1, t2) -> begin
(let _148_1200 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1199 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _148_1200 _148_1199)))
end
| Record (Some (e), fields) -> begin
(let _148_1204 = (FStar_All.pipe_right e term_to_string)
in (let _148_1203 = (to_string_l " " (fun _58_485 -> (match (_58_485) with
| (l, e) -> begin
(let _148_1202 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _148_1202))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _148_1204 _148_1203)))
end
| Record (None, fields) -> begin
(let _148_1207 = (to_string_l " " (fun _58_492 -> (match (_58_492) with
| (l, e) -> begin
(let _148_1206 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _148_1206))
end)) fields)
in (FStar_Util.format1 "{%s}" _148_1207))
end
| Project (e, l) -> begin
(let _148_1208 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _148_1208 l.FStar_Ident.str))
=======
(let _149_1211 = (term_to_string e)
in (FStar_Util.format1 "when %s" _149_1211))
end)
in (let _149_1212 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _149_1214 _149_1213 _149_1212))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _149_1216 _149_1215)))
end
| Ascribed (t1, t2) -> begin
(let _149_1218 = (FStar_All.pipe_right t1 term_to_string)
in (let _149_1217 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _149_1218 _149_1217)))
end
| Record (Some (e), fields) -> begin
(let _149_1222 = (FStar_All.pipe_right e term_to_string)
in (let _149_1221 = (to_string_l " " (fun _58_492 -> (match (_58_492) with
| (l, e) -> begin
(let _149_1220 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _149_1220))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _149_1222 _149_1221)))
end
| Record (None, fields) -> begin
(let _149_1225 = (to_string_l " " (fun _58_499 -> (match (_58_499) with
| (l, e) -> begin
(let _149_1224 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _149_1224))
end)) fields)
in (FStar_Util.format1 "{%s}" _149_1225))
end
| Project (e, l) -> begin
(let _149_1226 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _149_1226 l.FStar_Ident.str))
>>>>>>> master
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd)::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product ((b)::[], t) when (x.level = Type) -> begin
<<<<<<< HEAD
(let _148_1210 = (FStar_All.pipe_right b binder_to_string)
in (let _148_1209 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _148_1210 _148_1209)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(let _148_1212 = (FStar_All.pipe_right b binder_to_string)
in (let _148_1211 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _148_1212 _148_1211)))
end
| Sum (binders, t) -> begin
(let _148_1215 = (let _148_1213 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _148_1213 (FStar_String.concat " * ")))
in (let _148_1214 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _148_1215 _148_1214)))
end
| QForall (bs, pats, t) -> begin
(let _148_1218 = (to_string_l " " binder_to_string bs)
in (let _148_1217 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _148_1216 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _148_1218 _148_1217 _148_1216))))
end
| QExists (bs, pats, t) -> begin
(let _148_1221 = (to_string_l " " binder_to_string bs)
in (let _148_1220 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _148_1219 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _148_1221 _148_1220 _148_1219))))
end
| Refine (b, t) -> begin
(let _148_1223 = (FStar_All.pipe_right b binder_to_string)
in (let _148_1222 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _148_1223 _148_1222)))
end
| NamedTyp (x, t) -> begin
(let _148_1224 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _148_1224))
end
| Paren (t) -> begin
(let _148_1225 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _148_1225))
end
| Product (bs, t) -> begin
(let _148_1228 = (let _148_1226 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _148_1226 (FStar_String.concat ",")))
in (let _148_1227 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _148_1228 _148_1227)))
=======
(let _149_1228 = (FStar_All.pipe_right b binder_to_string)
in (let _149_1227 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _149_1228 _149_1227)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(let _149_1230 = (FStar_All.pipe_right b binder_to_string)
in (let _149_1229 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _149_1230 _149_1229)))
end
| Sum (binders, t) -> begin
(let _149_1233 = (let _149_1231 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _149_1231 (FStar_String.concat " * ")))
in (let _149_1232 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _149_1233 _149_1232)))
end
| QForall (bs, pats, t) -> begin
(let _149_1236 = (to_string_l " " binder_to_string bs)
in (let _149_1235 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _149_1234 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _149_1236 _149_1235 _149_1234))))
end
| QExists (bs, pats, t) -> begin
(let _149_1239 = (to_string_l " " binder_to_string bs)
in (let _149_1238 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _149_1237 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _149_1239 _149_1238 _149_1237))))
end
| Refine (b, t) -> begin
(let _149_1241 = (FStar_All.pipe_right b binder_to_string)
in (let _149_1240 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _149_1241 _149_1240)))
end
| NamedTyp (x, t) -> begin
(let _149_1242 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _149_1242))
end
| Paren (t) -> begin
(let _149_1243 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _149_1243))
end
| Product (bs, t) -> begin
(let _149_1246 = (let _149_1244 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _149_1244 (FStar_String.concat ",")))
in (let _149_1245 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _149_1246 _149_1245)))
>>>>>>> master
end
| t -> begin
(FStar_All.failwith "Missing case in term_to_string")
end))
and binder_to_string : binder  ->  Prims.string = (fun x -> (

let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Ident.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Ident.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
<<<<<<< HEAD
(let _148_1230 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _148_1230))
=======
(let _149_1248 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _149_1248))
>>>>>>> master
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
<<<<<<< HEAD
in (let _148_1231 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _148_1231 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _58_2 -> (match (_58_2) with
=======
in (let _149_1249 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _149_1249 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _58_3 -> (match (_58_3) with
>>>>>>> master
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _58_575 -> begin
""
end))
and pat_to_string : pattern  ->  Prims.string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
<<<<<<< HEAD
(let _148_1235 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1234 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _148_1235 _148_1234)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _148_1236 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _148_1236 i.FStar_Ident.idText))
=======
(let _149_1253 = (FStar_All.pipe_right p pat_to_string)
in (let _149_1252 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _149_1253 _149_1252)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _149_1254 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _149_1254 i.FStar_Ident.idText))
>>>>>>> master
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
<<<<<<< HEAD
(let _148_1237 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _148_1237))
end
| PatTuple (l, false) -> begin
(let _148_1238 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _148_1238))
end
| PatTuple (l, true) -> begin
(let _148_1239 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _148_1239))
end
| PatRecord (l) -> begin
(let _148_1242 = (to_string_l "; " (fun _58_599 -> (match (_58_599) with
| (f, e) -> begin
(let _148_1241 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _148_1241))
end)) l)
in (FStar_Util.format1 "{%s}" _148_1242))
=======
(let _149_1255 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _149_1255))
end
| PatTuple (l, false) -> begin
(let _149_1256 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _149_1256))
end
| PatTuple (l, true) -> begin
(let _149_1257 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _149_1257))
end
| PatRecord (l) -> begin
(let _149_1260 = (to_string_l "; " (fun _58_606 -> (match (_58_606) with
| (f, e) -> begin
(let _149_1259 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _149_1259))
end)) l)
in (FStar_Util.format1 "{%s}" _149_1260))
>>>>>>> master
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
<<<<<<< HEAD
(let _148_1244 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1243 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _148_1244 _148_1243)))
=======
(let _149_1262 = (FStar_All.pipe_right p pat_to_string)
in (let _149_1261 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _149_1262 _149_1261)))
>>>>>>> master
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
<<<<<<< HEAD
| PatVar (i, _58_611) -> begin
(let _148_1247 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_148_1247)::[])
=======
| PatVar (i, _58_618) -> begin
(let _149_1265 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_149_1265)::[])
>>>>>>> master
end
| PatApp (p, _58_623) -> begin
(head_id_of_pat p)
end
| PatAscribed (p, _58_628) -> begin
(head_id_of_pat p)
end
| _58_632 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _58_637 -> (match (_58_637) with
| (p, _58_636) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun _58_4 -> (match (_58_4) with
| (TyconAbstract (i, _, _)) | (TyconAbbrev (i, _, _, _)) | (TyconRecord (i, _, _, _)) | (TyconVariant (i, _, _, _)) -> begin
i.FStar_Ident.idText
end))


let decl_to_string : decl  ->  Prims.string = (fun d -> (match (d.d) with
| TopLevelModule (l) -> begin
(Prims.strcat "module " l.FStar_Ident.str)
end
| Open (l) -> begin
(Prims.strcat "open " l.FStar_Ident.str)
end
| ModuleAbbrev (i, l) -> begin
(FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText l.FStar_Ident.str)
end
| KindAbbrev (i, _58_681, _58_683) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
<<<<<<< HEAD
| ToplevelLet (_58_680, _58_682, pats) -> begin
(let _148_1257 = (let _148_1256 = (let _148_1255 = (lids_of_let pats)
in (FStar_All.pipe_right _148_1255 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _148_1256 (FStar_String.concat ", ")))
in (Prims.strcat "let " _148_1257))
=======
| ToplevelLet (_58_687, _58_689, pats) -> begin
(let _149_1275 = (let _149_1274 = (let _149_1273 = (lids_of_let pats)
in (FStar_All.pipe_right _149_1273 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _149_1274 (FStar_String.concat ", ")))
in (Prims.strcat "let " _149_1275))
>>>>>>> master
end
| Main (_58_695) -> begin
"main ..."
end
| Assume (_58_698, i, _58_701) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
<<<<<<< HEAD
| Tycon (_58_698, tys) -> begin
(let _148_1259 = (let _148_1258 = (FStar_All.pipe_right tys (FStar_List.map id_of_tycon))
in (FStar_All.pipe_right _148_1258 (FStar_String.concat ", ")))
in (Prims.strcat "type " _148_1259))
=======
| Tycon (_58_705, tys) -> begin
(let _149_1277 = (let _149_1276 = (FStar_All.pipe_right tys (FStar_List.map id_of_tycon))
in (FStar_All.pipe_right _149_1276 (FStar_String.concat ", ")))
in (Prims.strcat "type " _149_1277))
>>>>>>> master
end
| Val (_58_710, i, _58_713) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, _58_718) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (NewEffect (_, DefineEffect (i, _, _, _))) | (NewEffect (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (NewEffectForFree (DefineEffect (i, _, _, _))) | (NewEffectForFree (RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| SubEffect (_58_762) -> begin
"sub_effect"
end
| Pragma (_58_765) -> begin
"pragma"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| (Module (_, decls)) | (Interface (_, decls, _)) -> begin
<<<<<<< HEAD
(let _148_1262 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _148_1262 (FStar_String.concat "\n")))
=======
(let _149_1280 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _149_1280 (FStar_String.concat "\n")))
>>>>>>> master
end))


let error = (fun msg tm r -> (

let tm = (FStar_All.pipe_right tm term_to_string)
in (

let tm = if ((FStar_String.length tm) >= 80) then begin
<<<<<<< HEAD
(let _148_1266 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _148_1266 "..."))
=======
(let _149_1284 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _149_1284 "..."))
>>>>>>> master
end else begin
tm
end
in if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end)))




