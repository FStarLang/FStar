
open Prims
type level =
| Un
| Expr
| Type
| Kind
| Formula

let is_Un = (fun _discr_ -> (match (_discr_) with
| Un -> begin
true
end
| _ -> begin
false
end))

let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type = (fun _discr_ -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

let is_Formula = (fun _discr_ -> (match (_discr_) with
| Formula -> begin
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
| FsTypApp -> begin
true
end
| _ -> begin
false
end))

let is_Hash = (fun _discr_ -> (match (_discr_) with
| Hash -> begin
true
end
| _ -> begin
false
end))

let is_Nothing = (fun _discr_ -> (match (_discr_) with
| Nothing -> begin
true
end
| _ -> begin
false
end))

type arg_qualifier =
| Implicit
| Equality

let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit -> begin
true
end
| _ -> begin
false
end))

let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality -> begin
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
| PatVar of (FStar_Ident.ident * Prims.bool)
| PatName of FStar_Ident.lid
| PatTvar of (FStar_Ident.ident * Prims.bool)
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
| Wild -> begin
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

let is_Mkterm = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

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

let is_Mkbinder = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))

let is_PatWild = (fun _discr_ -> (match (_discr_) with
| PatWild -> begin
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

let is_Mkpattern = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_55_13) -> begin
_55_13
end))

let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_55_16) -> begin
_55_16
end))

let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_55_19) -> begin
_55_19
end))

let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_55_22) -> begin
_55_22
end))

let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_55_25) -> begin
_55_25
end))

let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_55_28) -> begin
_55_28
end))

let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_55_31) -> begin
_55_31
end))

let ___App____0 = (fun projectee -> (match (projectee) with
| App (_55_34) -> begin
_55_34
end))

let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_55_37) -> begin
_55_37
end))

let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_55_40) -> begin
_55_40
end))

let ___If____0 = (fun projectee -> (match (projectee) with
| If (_55_43) -> begin
_55_43
end))

let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_55_46) -> begin
_55_46
end))

let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_55_49) -> begin
_55_49
end))

let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_55_52) -> begin
_55_52
end))

let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_55_55) -> begin
_55_55
end))

let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_55_58) -> begin
_55_58
end))

let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_55_61) -> begin
_55_61
end))

let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_55_64) -> begin
_55_64
end))

let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_55_67) -> begin
_55_67
end))

let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_55_70) -> begin
_55_70
end))

let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_55_73) -> begin
_55_73
end))

let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_55_76) -> begin
_55_76
end))

let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_55_79) -> begin
_55_79
end))

let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_55_82) -> begin
_55_82
end))

let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_55_85) -> begin
_55_85
end))

let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_55_88) -> begin
_55_88
end))

let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_55_92) -> begin
_55_92
end))

let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_55_95) -> begin
_55_95
end))

let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_55_98) -> begin
_55_98
end))

let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_55_101) -> begin
_55_101
end))

let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_55_104) -> begin
_55_104
end))

let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_55_108) -> begin
_55_108
end))

let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_55_111) -> begin
_55_111
end))

let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_55_114) -> begin
_55_114
end))

let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_55_117) -> begin
_55_117
end))

let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_55_120) -> begin
_55_120
end))

let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_55_123) -> begin
_55_123
end))

let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_55_126) -> begin
_55_126
end))

let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_55_129) -> begin
_55_129
end))

let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_55_132) -> begin
_55_132
end))

let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_55_135) -> begin
_55_135
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
| TyconAbstract (_55_139) -> begin
_55_139
end))

let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_55_142) -> begin
_55_142
end))

let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_55_145) -> begin
_55_145
end))

let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_55_148) -> begin
_55_148
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
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract -> begin
true
end
| _ -> begin
false
end))

let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect -> begin
true
end
| _ -> begin
false
end))

let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect -> begin
true
end
| _ -> begin
false
end))

let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect -> begin
true
end
| _ -> begin
false
end))

let is_New = (fun _discr_ -> (match (_discr_) with
| New -> begin
true
end
| _ -> begin
false
end))

let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline -> begin
true
end
| _ -> begin
false
end))

let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable -> begin
true
end
| _ -> begin
false
end))

let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible -> begin
true
end
| _ -> begin
false
end))

let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque -> begin
true
end
| _ -> begin
false
end))

let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic -> begin
true
end
| _ -> begin
false
end))

type qualifiers =
qualifier Prims.list

type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : term}

let is_Mklift = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklift"))))

type pragma =
| SetOptions of Prims.string
| ResetOptions

let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions -> begin
true
end
| _ -> begin
false
end))

let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_55_155) -> begin
_55_155
end))

type decl' =
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
| SubEffect of lift
| Pragma of pragma 
 and decl =
{d : decl'; drange : FStar_Range.range} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)

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

let is_Mkdecl = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdecl"))))

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

let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_55_160) -> begin
_55_160
end))

let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_55_163) -> begin
_55_163
end))

let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_55_166) -> begin
_55_166
end))

let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_55_169) -> begin
_55_169
end))

let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_55_172) -> begin
_55_172
end))

let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_55_175) -> begin
_55_175
end))

let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_55_178) -> begin
_55_178
end))

let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_55_181) -> begin
_55_181
end))

let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_55_184) -> begin
_55_184
end))

let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_55_187) -> begin
_55_187
end))

let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_55_190) -> begin
_55_190
end))

let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_55_193) -> begin
_55_193
end))

let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_55_197) -> begin
_55_197
end))

let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_55_200) -> begin
_55_200
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
| Module (_55_203) -> begin
_55_203
end))

let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_55_206) -> begin
_55_206
end))

type file =
modul Prims.list

type inputFragment =
(file, decl Prims.list) FStar_Util.either

let mk_decl = (fun d r -> {d = d; drange = r})

let mk_binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

let mk_term = (fun t r l -> {tm = t; range = r; level = l})

let mk_pattern = (fun p r -> {pat = p; prange = r})

let un_curry_abs = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((FStar_List.append ps p'), body'))
end
| _55_225 -> begin
Abs ((ps, body))
end))

let mk_function = (fun branches r1 r2 -> (let x = (FStar_Absyn_Util.genident (Some (r1)))
in (let _146_980 = (let _146_979 = (let _146_978 = (let _146_977 = (let _146_976 = (let _146_975 = (let _146_974 = (let _146_973 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_146_973))
in (mk_term _146_974 r1 Expr))
in (_146_975, branches))
in Match (_146_976))
in (mk_term _146_977 r2 Expr))
in (((mk_pattern (PatVar ((x, false))) r1))::[], _146_978))
in Abs (_146_979))
in (mk_term _146_980 r2 Expr))))

let un_function = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_55_233), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _55_241 -> begin
None
end))

let lid_with_range = (fun lid r -> (let _146_989 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _146_989 r)))

let to_string_l = (fun sep f l -> (let _146_996 = (FStar_List.map f l)
in (FStar_String.concat sep _146_996)))

let imp_to_string = (fun _55_1 -> (match (_55_1) with
| Hash -> begin
"#"
end
| _55_250 -> begin
""
end))

let rec term_to_string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _55_255) -> begin
(let _146_1003 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _146_1003))
end
| Ensures (t, _55_260) -> begin
(let _146_1004 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _146_1004))
end
| Labeled (t, l, _55_266) -> begin
(let _146_1005 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _146_1005))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _146_1008 = (let _146_1007 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _146_1007))
in (FStar_Util.format2 "%s(%s)" s _146_1008))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _146_1011 = (to_string_l " " (fun _55_287 -> (match (_55_287) with
| (a, imp) -> begin
(let _146_1010 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _146_1010))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _146_1011))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _146_1013 = (to_string_l " " pat_to_string pats)
in (let _146_1012 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _146_1013 _146_1012)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _146_1015 = (to_string_l " " pat_to_string pats)
in (let _146_1014 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _146_1015 _146_1014)))
end
| App (t1, t2, imp) -> begin
(let _146_1017 = (FStar_All.pipe_right t1 term_to_string)
in (let _146_1016 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _146_1017 (imp_to_string imp) _146_1016)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _146_1020 = (FStar_All.pipe_right pat pat_to_string)
in (let _146_1019 = (FStar_All.pipe_right tm term_to_string)
in (let _146_1018 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _146_1020 _146_1019 _146_1018))))
end
| Let (_55_310, lbs, body) -> begin
(let _146_1025 = (to_string_l " and " (fun _55_317 -> (match (_55_317) with
| (p, b) -> begin
(let _146_1023 = (FStar_All.pipe_right p pat_to_string)
in (let _146_1022 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _146_1023 _146_1022)))
end)) lbs)
in (let _146_1024 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _146_1025 _146_1024)))
end
| Seq (t1, t2) -> begin
(let _146_1027 = (FStar_All.pipe_right t1 term_to_string)
in (let _146_1026 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _146_1027 _146_1026)))
end
| If (t1, t2, t3) -> begin
(let _146_1030 = (FStar_All.pipe_right t1 term_to_string)
in (let _146_1029 = (FStar_All.pipe_right t2 term_to_string)
in (let _146_1028 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _146_1030 _146_1029 _146_1028))))
end
| Match (t, branches) -> begin
(let _146_1037 = (FStar_All.pipe_right t term_to_string)
in (let _146_1036 = (to_string_l " | " (fun _55_334 -> (match (_55_334) with
| (p, w, e) -> begin
(let _146_1035 = (FStar_All.pipe_right p pat_to_string)
in (let _146_1034 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _146_1032 = (term_to_string e)
in (FStar_Util.format1 "when %s" _146_1032))
end)
in (let _146_1033 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _146_1035 _146_1034 _146_1033))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _146_1037 _146_1036)))
end
| Ascribed (t1, t2) -> begin
(let _146_1039 = (FStar_All.pipe_right t1 term_to_string)
in (let _146_1038 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _146_1039 _146_1038)))
end
| Record (Some (e), fields) -> begin
(let _146_1043 = (FStar_All.pipe_right e term_to_string)
in (let _146_1042 = (to_string_l " " (fun _55_349 -> (match (_55_349) with
| (l, e) -> begin
(let _146_1041 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _146_1041))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _146_1043 _146_1042)))
end
| Record (None, fields) -> begin
(let _146_1046 = (to_string_l " " (fun _55_356 -> (match (_55_356) with
| (l, e) -> begin
(let _146_1045 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _146_1045))
end)) fields)
in (FStar_Util.format1 "{%s}" _146_1046))
end
| Project (e, l) -> begin
(let _146_1047 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _146_1047 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _146_1049 = (FStar_All.pipe_right b binder_to_string)
in (let _146_1048 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _146_1049 _146_1048)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _146_1051 = (FStar_All.pipe_right b binder_to_string)
in (let _146_1050 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _146_1051 _146_1050)))
end
| Sum (binders, t) -> begin
(let _146_1054 = (let _146_1052 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _146_1052 (FStar_String.concat " * ")))
in (let _146_1053 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _146_1054 _146_1053)))
end
| QForall (bs, pats, t) -> begin
(let _146_1057 = (to_string_l " " binder_to_string bs)
in (let _146_1056 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _146_1055 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _146_1057 _146_1056 _146_1055))))
end
| QExists (bs, pats, t) -> begin
(let _146_1060 = (to_string_l " " binder_to_string bs)
in (let _146_1059 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _146_1058 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _146_1060 _146_1059 _146_1058))))
end
| Refine (b, t) -> begin
(let _146_1062 = (FStar_All.pipe_right b binder_to_string)
in (let _146_1061 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _146_1062 _146_1061)))
end
| NamedTyp (x, t) -> begin
(let _146_1063 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _146_1063))
end
| Paren (t) -> begin
(let _146_1064 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _146_1064))
end
| Product (bs, t) -> begin
(let _146_1067 = (let _146_1065 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _146_1065 (FStar_String.concat ",")))
in (let _146_1066 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _146_1067 _146_1066)))
end
| t -> begin
(FStar_All.failwith "Missing case in term_to_string")
end))
and binder_to_string = (fun x -> (let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Ident.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Ident.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
(let _146_1069 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _146_1069))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (match (x.aqual) with
| Some (Implicit) -> begin
(FStar_Util.format1 "#%s" s)
end
| Some (Equality) -> begin
(FStar_Util.format1 "=%s" s)
end
| _55_431 -> begin
s
end)))
and pat_to_string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
(let _146_1072 = (FStar_All.pipe_right p pat_to_string)
in (let _146_1071 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _146_1072 _146_1071)))
end
| (PatTvar (i, true)) | (PatVar (i, true)) -> begin
(FStar_Util.format1 "#%s" i.FStar_Ident.idText)
end
| (PatTvar (i, false)) | (PatVar (i, false)) -> begin
i.FStar_Ident.idText
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _146_1073 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _146_1073))
end
| PatTuple (l, false) -> begin
(let _146_1074 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _146_1074))
end
| PatTuple (l, true) -> begin
(let _146_1075 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _146_1075))
end
| PatRecord (l) -> begin
(let _146_1078 = (to_string_l "; " (fun _55_470 -> (match (_55_470) with
| (f, e) -> begin
(let _146_1077 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _146_1077))
end)) l)
in (FStar_Util.format1 "{%s}" _146_1078))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _146_1080 = (FStar_All.pipe_right p pat_to_string)
in (let _146_1079 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _146_1080 _146_1079)))
end))

let error = (fun msg tm r -> (let tm = (FStar_All.pipe_right tm term_to_string)
in (let tm = if ((FStar_String.length tm) >= 80) then begin
(let _146_1084 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _146_1084 "..."))
end else begin
tm
end
in (Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r)))))))

let consPat = (fun r hd tl -> PatApp (((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

let consTerm = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let lexConsTerm = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let mkConsList = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.nil_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

let mkLexList = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

let mkApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _55_506 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _55_510 -> begin
(FStar_List.fold_left (fun t _55_514 -> (match (_55_514) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

let mkRefSet = (fun r elts -> (let empty = (let _146_1128 = (let _146_1127 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_146_1127))
in (mk_term _146_1128 r Expr))
in (let ref_constr = (let _146_1130 = (let _146_1129 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_146_1129))
in (mk_term _146_1130 r Expr))
in (let singleton = (let _146_1132 = (let _146_1131 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_146_1131))
in (mk_term _146_1132 r Expr))
in (let union = (let _146_1134 = (let _146_1133 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_146_1133))
in (mk_term _146_1134 r Expr))
in (FStar_List.fold_right (fun e tl -> (let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

let mkExplicitApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _55_530 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _146_1146 = (let _146_1145 = (let _146_1144 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _146_1144))
in Construct (_146_1145))
in (mk_term _146_1146 r Un))
end
| _55_535 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

let mkAdmitMagic = (fun r -> (let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (let admit = (let admit_name = (let _146_1152 = (let _146_1151 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_146_1151))
in (mk_term _146_1152 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (let magic = (let magic_name = (let _146_1154 = (let _146_1153 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_146_1153))
in (mk_term _146_1154 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

let mkWildAdmitMagic = (fun r -> (let _146_1156 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _146_1156)))

let focusBranches = (fun branches r -> (let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(let _55_549 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (let focussed = (let _146_1159 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _146_1159 (FStar_List.map Prims.snd)))
in (let _146_1161 = (let _146_1160 = (mkWildAdmitMagic r)
in (_146_1160)::[])
in (FStar_List.append focussed _146_1161))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))

let focusLetBindings = (fun lbs r -> (let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(let _55_555 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _55_559 -> (match (_55_559) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _146_1165 = (mkAdmitMagic r)
in ((Prims.fst lb), _146_1165))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))

let mkFsTypApp = (fun t args r -> (let _146_1173 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _146_1173 r)))

let mkTuple = (fun args r -> (let cons = (FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
in (let _146_1179 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _146_1179 r))))

let mkDTuple = (fun args r -> (let cons = (FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
in (let _146_1185 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _146_1185 r))))

let mkRefinedBinder = (fun id t refopt m implicit -> (let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))

let rec extract_named_refinement = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some ((x, t, None))
end
| Refine ({b = Annotated (x, t); brange = _55_591; blevel = _55_589; aqual = _55_587}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _55_603 -> begin
None
end))




