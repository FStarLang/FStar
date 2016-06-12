
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
| Let of (Prims.bool * (pattern * term) Prims.list * term)
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
| Const (_58_15) -> begin
_58_15
end))


let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_58_18) -> begin
_58_18
end))


let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_58_21) -> begin
_58_21
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_58_24) -> begin
_58_24
end))


let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_58_27) -> begin
_58_27
end))


let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_58_30) -> begin
_58_30
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_58_33) -> begin
_58_33
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_58_36) -> begin
_58_36
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_58_39) -> begin
_58_39
end))


let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_58_42) -> begin
_58_42
end))


let ___If____0 = (fun projectee -> (match (projectee) with
| If (_58_45) -> begin
_58_45
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_58_48) -> begin
_58_48
end))


let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_58_51) -> begin
_58_51
end))


let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_58_54) -> begin
_58_54
end))


let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_58_57) -> begin
_58_57
end))


let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_58_60) -> begin
_58_60
end))


let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_58_63) -> begin
_58_63
end))


let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_58_66) -> begin
_58_66
end))


let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_58_69) -> begin
_58_69
end))


let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_58_72) -> begin
_58_72
end))


let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_58_75) -> begin
_58_75
end))


let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_58_78) -> begin
_58_78
end))


let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_58_81) -> begin
_58_81
end))


let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_58_84) -> begin
_58_84
end))


let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_58_87) -> begin
_58_87
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_58_90) -> begin
_58_90
end))


let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_58_94) -> begin
_58_94
end))


let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_58_97) -> begin
_58_97
end))


let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_58_100) -> begin
_58_100
end))


let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_58_103) -> begin
_58_103
end))


let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_58_106) -> begin
_58_106
end))


let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_58_110) -> begin
_58_110
end))


let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_58_113) -> begin
_58_113
end))


let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_58_116) -> begin
_58_116
end))


let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_58_119) -> begin
_58_119
end))


let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_58_122) -> begin
_58_122
end))


let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_58_125) -> begin
_58_125
end))


let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_58_128) -> begin
_58_128
end))


let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_58_131) -> begin
_58_131
end))


let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_58_134) -> begin
_58_134
end))


let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_58_137) -> begin
_58_137
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
| TyconAbstract (_58_141) -> begin
_58_141
end))


let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_58_144) -> begin
_58_144
end))


let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_58_147) -> begin
_58_147
end))


let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_58_150) -> begin
_58_150
end))


type qualifier =
| Private
| Abstract
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
| SetOptions (_58_157) -> begin
_58_157
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_58_160) -> begin
_58_160
end))


type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| KindAbbrev of (FStar_Ident.ident * binder Prims.list * knd)
| ToplevelLet of (qualifiers * Prims.bool * (pattern * term) Prims.list)
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
| TopLevelModule (_58_165) -> begin
_58_165
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_58_168) -> begin
_58_168
end))


let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_58_171) -> begin
_58_171
end))


let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_58_174) -> begin
_58_174
end))


let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_58_177) -> begin
_58_177
end))


let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_58_180) -> begin
_58_180
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_58_183) -> begin
_58_183
end))


let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_58_186) -> begin
_58_186
end))


let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_58_189) -> begin
_58_189
end))


let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_58_192) -> begin
_58_192
end))


let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_58_195) -> begin
_58_195
end))


let ___NewEffectForFree____0 = (fun projectee -> (match (projectee) with
| NewEffectForFree (_58_198) -> begin
_58_198
end))


let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_58_201) -> begin
_58_201
end))


let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_58_204) -> begin
_58_204
end))


let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_58_208) -> begin
_58_208
end))


let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_58_211) -> begin
_58_211
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
| Module (_58_214) -> begin
_58_214
end))


let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_58_217) -> begin
_58_217
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
(let _148_986 = (let _148_985 = (let _148_984 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in (_148_984, id.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_148_985))
in (Prims.raise _148_986))
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
| _58_238 -> begin
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
in (let _148_1026 = (let _148_1025 = (let _148_1024 = (let _148_1023 = (let _148_1022 = (let _148_1021 = (let _148_1020 = (let _148_1019 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_148_1019))
in (mk_term _148_1020 r1 Expr))
in (_148_1021, branches))
in Match (_148_1022))
in (mk_term _148_1023 r2 Expr))
in (((mk_pattern (PatVar ((x, None))) r1))::[], _148_1024))
in Abs (_148_1025))
in (mk_term _148_1026 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_58_247), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _58_255 -> begin
None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _148_1035 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _148_1035 r)))


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
| _58_282 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _58_286 -> begin
(FStar_List.fold_left (fun t _58_290 -> (match (_58_290) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let empty = (let _148_1079 = (let _148_1078 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_148_1078))
in (mk_term _148_1079 r Expr))
in (

let ref_constr = (let _148_1081 = (let _148_1080 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_148_1080))
in (mk_term _148_1081 r Expr))
in (

let singleton = (let _148_1083 = (let _148_1082 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_148_1082))
in (mk_term _148_1083 r Expr))
in (

let union = (let _148_1085 = (let _148_1084 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_148_1084))
in (mk_term _148_1085 r Expr))
in (FStar_List.fold_right (fun e tl -> (

let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (

let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))


let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _58_306 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _148_1097 = (let _148_1096 = (let _148_1095 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _148_1095))
in Construct (_148_1096))
in (mk_term _148_1097 r Un))
end
| _58_311 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (

let admit = (

let admit_name = (let _148_1103 = (let _148_1102 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_148_1102))
in (mk_term _148_1103 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (

let magic = (

let magic_name = (let _148_1105 = (let _148_1104 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_148_1104))
in (mk_term _148_1105 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (

let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))


let mkWildAdmitMagic = (fun r -> (let _148_1107 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _148_1107)))


let focusBranches = (fun branches r -> (

let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(

let _58_325 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (

let focussed = (let _148_1110 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _148_1110 (FStar_List.map Prims.snd)))
in (let _148_1112 = (let _148_1111 = (mkWildAdmitMagic r)
in (_148_1111)::[])
in (FStar_List.append focussed _148_1112))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))


let focusLetBindings = (fun lbs r -> (

let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(

let _58_331 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _58_335 -> (match (_58_335) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _148_1116 = (mkAdmitMagic r)
in ((Prims.fst lb), _148_1116))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _148_1124 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _148_1124 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
in (let _148_1130 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _148_1130 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
in (let _148_1136 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _148_1136 r))))


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
| Refine ({b = Annotated (x, t); brange = _58_367; blevel = _58_365; aqual = _58_363}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _58_379 -> begin
None
end))


let to_string_l = (fun sep f l -> (let _148_1155 = (FStar_List.map f l)
in (FStar_String.concat sep _148_1155)))


let imp_to_string : imp  ->  Prims.string = (fun _58_1 -> (match (_58_1) with
| Hash -> begin
"#"
end
| _58_386 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _58_391) -> begin
(let _148_1163 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _148_1163))
end
| Ensures (t, _58_396) -> begin
(let _148_1164 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _148_1164))
end
| Labeled (t, l, _58_402) -> begin
(let _148_1165 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _148_1165))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _148_1168 = (let _148_1167 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _148_1167))
in (FStar_Util.format2 "%s(%s)" s _148_1168))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _148_1171 = (to_string_l " " (fun _58_423 -> (match (_58_423) with
| (a, imp) -> begin
(let _148_1170 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _148_1170))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _148_1171))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _148_1173 = (to_string_l " " pat_to_string pats)
in (let _148_1172 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _148_1173 _148_1172)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _148_1175 = (to_string_l " " pat_to_string pats)
in (let _148_1174 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _148_1175 _148_1174)))
end
| App (t1, t2, imp) -> begin
(let _148_1177 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1176 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _148_1177 (imp_to_string imp) _148_1176)))
end
| Let (false, ((pat, tm))::[], body) -> begin
(let _148_1180 = (FStar_All.pipe_right pat pat_to_string)
in (let _148_1179 = (FStar_All.pipe_right tm term_to_string)
in (let _148_1178 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _148_1180 _148_1179 _148_1178))))
end
| Let (_58_446, lbs, body) -> begin
(let _148_1185 = (to_string_l " and " (fun _58_453 -> (match (_58_453) with
| (p, b) -> begin
(let _148_1183 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1182 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _148_1183 _148_1182)))
end)) lbs)
in (let _148_1184 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _148_1185 _148_1184)))
end
| Seq (t1, t2) -> begin
(let _148_1187 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1186 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _148_1187 _148_1186)))
end
| If (t1, t2, t3) -> begin
(let _148_1190 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1189 = (FStar_All.pipe_right t2 term_to_string)
in (let _148_1188 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _148_1190 _148_1189 _148_1188))))
end
| Match (t, branches) -> begin
(let _148_1197 = (FStar_All.pipe_right t term_to_string)
in (let _148_1196 = (to_string_l " | " (fun _58_470 -> (match (_58_470) with
| (p, w, e) -> begin
(let _148_1195 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1194 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _148_1192 = (term_to_string e)
in (FStar_Util.format1 "when %s" _148_1192))
end)
in (let _148_1193 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _148_1195 _148_1194 _148_1193))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _148_1197 _148_1196)))
end
| Ascribed (t1, t2) -> begin
(let _148_1199 = (FStar_All.pipe_right t1 term_to_string)
in (let _148_1198 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _148_1199 _148_1198)))
end
| Record (Some (e), fields) -> begin
(let _148_1203 = (FStar_All.pipe_right e term_to_string)
in (let _148_1202 = (to_string_l " " (fun _58_485 -> (match (_58_485) with
| (l, e) -> begin
(let _148_1201 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _148_1201))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _148_1203 _148_1202)))
end
| Record (None, fields) -> begin
(let _148_1206 = (to_string_l " " (fun _58_492 -> (match (_58_492) with
| (l, e) -> begin
(let _148_1205 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _148_1205))
end)) fields)
in (FStar_Util.format1 "{%s}" _148_1206))
end
| Project (e, l) -> begin
(let _148_1207 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _148_1207 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd)::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product ((b)::[], t) when (x.level = Type) -> begin
(let _148_1209 = (FStar_All.pipe_right b binder_to_string)
in (let _148_1208 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _148_1209 _148_1208)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(let _148_1211 = (FStar_All.pipe_right b binder_to_string)
in (let _148_1210 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _148_1211 _148_1210)))
end
| Sum (binders, t) -> begin
(let _148_1214 = (let _148_1212 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _148_1212 (FStar_String.concat " * ")))
in (let _148_1213 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _148_1214 _148_1213)))
end
| QForall (bs, pats, t) -> begin
(let _148_1217 = (to_string_l " " binder_to_string bs)
in (let _148_1216 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _148_1215 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _148_1217 _148_1216 _148_1215))))
end
| QExists (bs, pats, t) -> begin
(let _148_1220 = (to_string_l " " binder_to_string bs)
in (let _148_1219 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _148_1218 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _148_1220 _148_1219 _148_1218))))
end
| Refine (b, t) -> begin
(let _148_1222 = (FStar_All.pipe_right b binder_to_string)
in (let _148_1221 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _148_1222 _148_1221)))
end
| NamedTyp (x, t) -> begin
(let _148_1223 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _148_1223))
end
| Paren (t) -> begin
(let _148_1224 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _148_1224))
end
| Product (bs, t) -> begin
(let _148_1227 = (let _148_1225 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _148_1225 (FStar_String.concat ",")))
in (let _148_1226 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _148_1227 _148_1226)))
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
(let _148_1229 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _148_1229))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (let _148_1230 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _148_1230 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _58_2 -> (match (_58_2) with
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _58_568 -> begin
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
(let _148_1234 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1233 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _148_1234 _148_1233)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _148_1235 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _148_1235 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _148_1236 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _148_1236))
end
| PatTuple (l, false) -> begin
(let _148_1237 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _148_1237))
end
| PatTuple (l, true) -> begin
(let _148_1238 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _148_1238))
end
| PatRecord (l) -> begin
(let _148_1241 = (to_string_l "; " (fun _58_599 -> (match (_58_599) with
| (f, e) -> begin
(let _148_1240 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _148_1240))
end)) l)
in (FStar_Util.format1 "{%s}" _148_1241))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _148_1243 = (FStar_All.pipe_right p pat_to_string)
in (let _148_1242 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _148_1243 _148_1242)))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, _58_611) -> begin
(let _148_1246 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_148_1246)::[])
end
| PatApp (p, _58_616) -> begin
(head_id_of_pat p)
end
| PatAscribed (p, _58_621) -> begin
(head_id_of_pat p)
end
| _58_625 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _58_630 -> (match (_58_630) with
| (p, _58_629) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun _58_3 -> (match (_58_3) with
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
| KindAbbrev (i, _58_674, _58_676) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| ToplevelLet (_58_680, _58_682, pats) -> begin
(let _148_1256 = (let _148_1255 = (let _148_1254 = (lids_of_let pats)
in (FStar_All.pipe_right _148_1254 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _148_1255 (FStar_String.concat ", ")))
in (Prims.strcat "let " _148_1256))
end
| Main (_58_688) -> begin
"main ..."
end
| Assume (_58_691, i, _58_694) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (_58_698, tys) -> begin
(let _148_1258 = (let _148_1257 = (FStar_All.pipe_right tys (FStar_List.map id_of_tycon))
in (FStar_All.pipe_right _148_1257 (FStar_String.concat ", ")))
in (Prims.strcat "type " _148_1258))
end
| Val (_58_703, i, _58_706) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, _58_711) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (NewEffect (_, DefineEffect (i, _, _, _))) | (NewEffect (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (NewEffectForFree (DefineEffect (i, _, _, _))) | (NewEffectForFree (RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| SubEffect (_58_755) -> begin
"sub_effect"
end
| Pragma (_58_758) -> begin
"pragma"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| (Module (_, decls)) | (Interface (_, decls, _)) -> begin
(let _148_1261 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _148_1261 (FStar_String.concat "\n")))
end))


let error = (fun msg tm r -> (

let tm = (FStar_All.pipe_right tm term_to_string)
in (

let tm = if ((FStar_String.length tm) >= 80) then begin
(let _148_1265 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _148_1265 "..."))
end else begin
tm
end
in if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end)))




