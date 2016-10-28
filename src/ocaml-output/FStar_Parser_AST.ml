
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
| LetOpen of (FStar_Ident.lid * term)
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
| PatOp of Prims.string 
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


let is_LetOpen = (fun _discr_ -> (match (_discr_) with
| LetOpen (_) -> begin
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


let is_PatOp = (fun _discr_ -> (match (_discr_) with
| PatOp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))


let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_60_16) -> begin
_60_16
end))


let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_60_19) -> begin
_60_19
end))


let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_60_22) -> begin
_60_22
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_60_25) -> begin
_60_25
end))


let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_60_28) -> begin
_60_28
end))


let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_60_31) -> begin
_60_31
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_60_34) -> begin
_60_34
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_60_37) -> begin
_60_37
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_60_40) -> begin
_60_40
end))


let ___LetOpen____0 = (fun projectee -> (match (projectee) with
| LetOpen (_60_43) -> begin
_60_43
end))


let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_60_46) -> begin
_60_46
end))


let ___If____0 = (fun projectee -> (match (projectee) with
| If (_60_49) -> begin
_60_49
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_60_52) -> begin
_60_52
end))


let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_60_55) -> begin
_60_55
end))


let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_60_58) -> begin
_60_58
end))


let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_60_61) -> begin
_60_61
end))


let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_60_64) -> begin
_60_64
end))


let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_60_67) -> begin
_60_67
end))


let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_60_70) -> begin
_60_70
end))


let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_60_73) -> begin
_60_73
end))


let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_60_76) -> begin
_60_76
end))


let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_60_79) -> begin
_60_79
end))


let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_60_82) -> begin
_60_82
end))


let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_60_85) -> begin
_60_85
end))


let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_60_88) -> begin
_60_88
end))


let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_60_91) -> begin
_60_91
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_60_94) -> begin
_60_94
end))


let ___Assign____0 = (fun projectee -> (match (projectee) with
| Assign (_60_97) -> begin
_60_97
end))


let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_60_101) -> begin
_60_101
end))


let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_60_104) -> begin
_60_104
end))


let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_60_107) -> begin
_60_107
end))


let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_60_110) -> begin
_60_110
end))


let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_60_113) -> begin
_60_113
end))


let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_60_117) -> begin
_60_117
end))


let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_60_120) -> begin
_60_120
end))


let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_60_123) -> begin
_60_123
end))


let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_60_126) -> begin
_60_126
end))


let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_60_129) -> begin
_60_129
end))


let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_60_132) -> begin
_60_132
end))


let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_60_135) -> begin
_60_135
end))


let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_60_138) -> begin
_60_138
end))


let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_60_141) -> begin
_60_141
end))


let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_60_144) -> begin
_60_144
end))


let ___PatOp____0 = (fun projectee -> (match (projectee) with
| PatOp (_60_147) -> begin
_60_147
end))


type knd =
term


type typ =
term


type expr =
term


type fsdoc =
(Prims.string * (Prims.string * Prims.string) Prims.list)


type tycon =
| TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd Prims.option)
| TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd Prims.option * term)
| TyconRecord of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term * fsdoc Prims.option) Prims.list)
| TyconVariant of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term Prims.option * fsdoc Prims.option * Prims.bool) Prims.list)


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
| TyconAbstract (_60_151) -> begin
_60_151
end))


let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_60_154) -> begin
_60_154
end))


let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_60_157) -> begin
_60_157
end))


let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_60_160) -> begin
_60_160
end))


type qualifier =
| Private
| Abstract
| Noeq
| Unopteq
| Assumption
| DefaultEffect
| TotalEffect
| Effect
| New
| Inline
| Visible
| Unfold_for_unification_and_vcgen
| Inline_for_extraction
| Irreducible
| Reifiable
| Reflectable
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


let is_Unopteq = (fun _discr_ -> (match (_discr_) with
| Unopteq (_) -> begin
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


let is_Visible = (fun _discr_ -> (match (_discr_) with
| Visible (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unfold_for_unification_and_vcgen = (fun _discr_ -> (match (_discr_) with
| Unfold_for_unification_and_vcgen (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inline_for_extraction = (fun _discr_ -> (match (_discr_) with
| Inline_for_extraction (_) -> begin
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


let is_Reifiable = (fun _discr_ -> (match (_discr_) with
| Reifiable (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reflectable = (fun _discr_ -> (match (_discr_) with
| Reflectable (_) -> begin
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


type lift_op =
| NonReifiableLift of term
| ReifiableLift of (term * term)
| LiftForFree of term


let is_NonReifiableLift = (fun _discr_ -> (match (_discr_) with
| NonReifiableLift (_) -> begin
true
end
| _ -> begin
false
end))


let is_ReifiableLift = (fun _discr_ -> (match (_discr_) with
| ReifiableLift (_) -> begin
true
end
| _ -> begin
false
end))


let is_LiftForFree = (fun _discr_ -> (match (_discr_) with
| LiftForFree (_) -> begin
true
end
| _ -> begin
false
end))


let ___NonReifiableLift____0 = (fun projectee -> (match (projectee) with
| NonReifiableLift (_60_163) -> begin
_60_163
end))


let ___ReifiableLift____0 = (fun projectee -> (match (projectee) with
| ReifiableLift (_60_166) -> begin
_60_166
end))


let ___LiftForFree____0 = (fun projectee -> (match (projectee) with
| LiftForFree (_60_169) -> begin
_60_169
end))


type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : lift_op}


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
| SetOptions (_60_176) -> begin
_60_176
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_60_179) -> begin
_60_179
end))


type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| KindAbbrev of (FStar_Ident.ident * binder Prims.list * knd)
| ToplevelLet of (qualifiers * let_qualifier * (pattern * term) Prims.list)
| Main of term
| Assume of (qualifiers * FStar_Ident.ident * term)
| Tycon of (qualifiers * (tycon * fsdoc Prims.option) Prims.list)
| Val of (qualifiers * FStar_Ident.ident * term)
| Exception of (FStar_Ident.ident * term Prims.option)
| NewEffect of (qualifiers * effect_decl)
| NewEffectForFree of (qualifiers * effect_decl)
| SubEffect of lift
| Pragma of pragma
| Fsdoc of fsdoc 
 and decl =
{d : decl'; drange : FStar_Range.range; doc : fsdoc Prims.option} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list * decl Prims.list)
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


let is_Fsdoc = (fun _discr_ -> (match (_discr_) with
| Fsdoc (_) -> begin
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
| TopLevelModule (_60_185) -> begin
_60_185
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_60_188) -> begin
_60_188
end))


let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_60_191) -> begin
_60_191
end))


let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_60_194) -> begin
_60_194
end))


let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_60_197) -> begin
_60_197
end))


let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_60_200) -> begin
_60_200
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_60_203) -> begin
_60_203
end))


let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_60_206) -> begin
_60_206
end))


let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_60_209) -> begin
_60_209
end))


let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_60_212) -> begin
_60_212
end))


let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_60_215) -> begin
_60_215
end))


let ___NewEffectForFree____0 = (fun projectee -> (match (projectee) with
| NewEffectForFree (_60_218) -> begin
_60_218
end))


let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_60_221) -> begin
_60_221
end))


let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_60_224) -> begin
_60_224
end))


let ___Fsdoc____0 = (fun projectee -> (match (projectee) with
| Fsdoc (_60_227) -> begin
_60_227
end))


let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_60_231) -> begin
_60_231
end))


let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_60_234) -> begin
_60_234
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
| Module (_60_237) -> begin
_60_237
end))


let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_60_240) -> begin
_60_240
end))


type file =
modul Prims.list


type inputFragment =
(file, decl Prims.list) FStar_Util.either


let check_id : FStar_Ident.ident  ->  Prims.unit = (fun id -> if (FStar_Options.universes ()) then begin
(

let first_char = (FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0") (Prims.parse_int "1"))
in if ((FStar_String.lowercase first_char) = first_char) then begin
()
end else begin
(let _155_1096 = (let _155_1095 = (let _155_1094 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in ((_155_1094), (id.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_155_1095))
in (Prims.raise _155_1096))
end)
end else begin
()
end)


let mk_decl : decl'  ->  FStar_Range.range  ->  fsdoc Prims.option  ->  decl = (fun d r doc -> {d = d; drange = r; doc = doc})


let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})


let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})


let mk_uminus : term  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> (

let t = (match (t.tm) with
| Const (FStar_Const.Const_int (s, Some (FStar_Const.Signed, width))) -> begin
Const (FStar_Const.Const_int ((((Prims.strcat "-" s)), (Some (((FStar_Const.Signed), (width)))))))
end
| _60_265 -> begin
Op ((("-"), ((t)::[])))
end)
in (mk_term t r l)))


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs ((((FStar_List.append ps p')), (body')))
end
| _60_276 -> begin
Abs (((ps), (body)))
end))


let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = if (FStar_Options.universes ()) then begin
(

let i = (FStar_Syntax_Syntax.next_id ())
in (FStar_Ident.gen r1))
end else begin
(FStar_Absyn_Util.genident (Some (r1)))
end
in (let _155_1144 = (let _155_1143 = (let _155_1142 = (let _155_1141 = (let _155_1140 = (let _155_1139 = (let _155_1138 = (let _155_1137 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_155_1137))
in (mk_term _155_1138 r1 Expr))
in ((_155_1139), (branches)))
in Match (_155_1140))
in (mk_term _155_1141 r2 Expr))
in ((((mk_pattern (PatVar (((x), (None)))) r1))::[]), (_155_1142)))
in Abs (_155_1143))
in (mk_term _155_1144 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match (((p.pat), (tm.tm))) with
| (PatVar (_60_285), Abs (pats, body)) -> begin
Some ((((mk_pattern (PatApp (((p), (pats)))) p.prange)), (body)))
end
| _60_293 -> begin
None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _155_1153 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _155_1153 r)))


let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd tl -> PatApp ((((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r)), ((hd)::(tl)::[]))))


let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct (((FStar_Absyn_Const.cons_lid), ((((hd), (Nothing)))::(((tl), (Nothing)))::[])))) r Expr))


let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct (((FStar_Absyn_Const.lexcons_lid), ((((hd), (Nothing)))::(((tl), (Nothing)))::[])))) r Expr))


let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct (((FStar_Absyn_Const.nil_lid), ([])))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))


let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct (((FStar_Absyn_Const.lextop_lid), ([])))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))


let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _60_320 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct (((s), (args)))) r Un)
end
| _60_324 -> begin
(FStar_List.fold_left (fun t _60_328 -> (match (_60_328) with
| (a, imp) -> begin
(mk_term (App (((t), (a), (imp)))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let univs = (FStar_Options.universes ())
in (

let _60_335 = if univs then begin
((FStar_Absyn_Const.tset_empty), (FStar_Absyn_Const.tset_singleton), (FStar_Absyn_Const.tset_union))
end else begin
((FStar_Absyn_Const.set_empty), (FStar_Absyn_Const.set_singleton), (FStar_Absyn_Const.set_union))
end
in (match (_60_335) with
| (empty_lid, singleton_lid, union_lid) -> begin
(

let empty = (mk_term (Var ((FStar_Ident.set_lid_range empty_lid r))) r Expr)
in (

let ref_constr = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r))) r Expr)
in (

let singleton = (mk_term (Var ((FStar_Ident.set_lid_range singleton_lid r))) r Expr)
in (

let union = (mk_term (Var ((FStar_Ident.set_lid_range union_lid r))) r Expr)
in (FStar_List.fold_right (fun e tl -> (

let e = (mkApp ref_constr ((((e), (Nothing)))::[]) r)
in (

let single_e = (mkApp singleton ((((e), (Nothing)))::[]) r)
in (mkApp union ((((single_e), (Nothing)))::(((tl), (Nothing)))::[]) r)))) elts empty)))))
end))))


let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _60_349 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _155_1207 = (let _155_1206 = (let _155_1205 = (FStar_List.map (fun a -> ((a), (Nothing))) args)
in ((s), (_155_1205)))
in Construct (_155_1206))
in (mk_term _155_1207 r Un))
end
| _60_354 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App (((t), (a), (Nothing)))) r Un)) t args)
end)
end))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (

let admit = (

let admit_name = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r))) r Expr)
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (

let magic = (

let magic_name = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r))) r Expr)
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (

let admit_magic = (mk_term (Seq (((admit), (magic)))) r Expr)
in admit_magic)))))


let mkWildAdmitMagic = (fun r -> (let _155_1213 = (mkAdmitMagic r)
in (((mk_pattern PatWild r)), (None), (_155_1213))))


let focusBranches = (fun branches r -> (

let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(

let _60_368 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (

let focussed = (let _155_1216 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _155_1216 (FStar_List.map Prims.snd)))
in (let _155_1218 = (let _155_1217 = (mkWildAdmitMagic r)
in (_155_1217)::[])
in (FStar_List.append focussed _155_1218))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))


let focusLetBindings = (fun lbs r -> (

let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(

let _60_374 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _60_378 -> (match (_60_378) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _155_1222 = (mkAdmitMagic r)
in (((Prims.fst lb)), (_155_1222)))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _155_1230 = (FStar_List.map (fun a -> ((a), (FsTypApp))) args)
in (mkApp t _155_1230 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
in (let _155_1236 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons)) r Expr) _155_1236 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
in (let _155_1242 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons)) r Expr) _155_1242 r))))


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t refopt m implicit -> (

let b = (mk_binder (Annotated (((id), (t)))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated (((id), ((mk_term (Refine (((b), (t)))) m Type))))) m Type implicit)
end)))


let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term Prims.option) Prims.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some (((x), (t), (None)))
end
| Refine ({b = Annotated (x, t); brange = _60_410; blevel = _60_408; aqual = _60_406}, t') -> begin
Some (((x), (t), (Some (t'))))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _60_422 -> begin
None
end))


let string_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  Prims.string = (fun _60_425 -> (match (_60_425) with
| (comment, keywords) -> begin
(let _155_1259 = (let _155_1258 = (FStar_List.map (fun _60_428 -> (match (_60_428) with
| (k, v) -> begin
(Prims.strcat k (Prims.strcat "->" v))
end)) keywords)
in (FStar_String.concat "," _155_1258))
in (Prims.strcat comment _155_1259))
end))


let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun _60_1 -> (match (_60_1) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end
| Mutable -> begin
"mutable"
end))


let to_string_l = (fun sep f l -> (let _155_1268 = (FStar_List.map f l)
in (FStar_String.concat sep _155_1268)))


let imp_to_string : imp  ->  Prims.string = (fun _60_2 -> (match (_60_2) with
| Hash -> begin
"#"
end
| _60_439 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _60_444) -> begin
(let _155_1276 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _155_1276))
end
| Ensures (t, _60_449) -> begin
(let _155_1277 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _155_1277))
end
| Labeled (t, l, _60_455) -> begin
(let _155_1278 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _155_1278))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _155_1281 = (let _155_1280 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _155_1280))
in (FStar_Util.format2 "%s(%s)" s _155_1281))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _155_1284 = (to_string_l " " (fun _60_476 -> (match (_60_476) with
| (a, imp) -> begin
(let _155_1283 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _155_1283))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _155_1284))
end
| Abs (pats, t) -> begin
(let _155_1286 = (to_string_l " " pat_to_string pats)
in (let _155_1285 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _155_1286 _155_1285)))
end
| App (t1, t2, imp) -> begin
(let _155_1288 = (FStar_All.pipe_right t1 term_to_string)
in (let _155_1287 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _155_1288 (imp_to_string imp) _155_1287)))
end
| Let (Rec, lbs, body) -> begin
(let _155_1293 = (to_string_l " and " (fun _60_493 -> (match (_60_493) with
| (p, b) -> begin
(let _155_1291 = (FStar_All.pipe_right p pat_to_string)
in (let _155_1290 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _155_1291 _155_1290)))
end)) lbs)
in (let _155_1292 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _155_1293 _155_1292)))
end
| Let (q, ((pat, tm))::[], body) -> begin
(let _155_1296 = (FStar_All.pipe_right pat pat_to_string)
in (let _155_1295 = (FStar_All.pipe_right tm term_to_string)
in (let _155_1294 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) _155_1296 _155_1295 _155_1294))))
end
| Seq (t1, t2) -> begin
(let _155_1298 = (FStar_All.pipe_right t1 term_to_string)
in (let _155_1297 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _155_1298 _155_1297)))
end
| If (t1, t2, t3) -> begin
(let _155_1301 = (FStar_All.pipe_right t1 term_to_string)
in (let _155_1300 = (FStar_All.pipe_right t2 term_to_string)
in (let _155_1299 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _155_1301 _155_1300 _155_1299))))
end
| Match (t, branches) -> begin
(let _155_1308 = (FStar_All.pipe_right t term_to_string)
in (let _155_1307 = (to_string_l " | " (fun _60_518 -> (match (_60_518) with
| (p, w, e) -> begin
(let _155_1306 = (FStar_All.pipe_right p pat_to_string)
in (let _155_1305 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _155_1303 = (term_to_string e)
in (FStar_Util.format1 "when %s" _155_1303))
end)
in (let _155_1304 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _155_1306 _155_1305 _155_1304))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _155_1308 _155_1307)))
end
| Ascribed (t1, t2) -> begin
(let _155_1310 = (FStar_All.pipe_right t1 term_to_string)
in (let _155_1309 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _155_1310 _155_1309)))
end
| Record (Some (e), fields) -> begin
(let _155_1314 = (FStar_All.pipe_right e term_to_string)
in (let _155_1313 = (to_string_l " " (fun _60_533 -> (match (_60_533) with
| (l, e) -> begin
(let _155_1312 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _155_1312))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _155_1314 _155_1313)))
end
| Record (None, fields) -> begin
(let _155_1317 = (to_string_l " " (fun _60_540 -> (match (_60_540) with
| (l, e) -> begin
(let _155_1316 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _155_1316))
end)) fields)
in (FStar_Util.format1 "{%s}" _155_1317))
end
| Project (e, l) -> begin
(let _155_1318 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _155_1318 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd)::tl, t) -> begin
(term_to_string (mk_term (Product ((((b)::[]), ((mk_term (Product ((((hd)::tl), (t)))) x.range x.level))))) x.range x.level))
end
| Product ((b)::[], t) when (x.level = Type) -> begin
(let _155_1320 = (FStar_All.pipe_right b binder_to_string)
in (let _155_1319 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _155_1320 _155_1319)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(let _155_1322 = (FStar_All.pipe_right b binder_to_string)
in (let _155_1321 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _155_1322 _155_1321)))
end
| Sum (binders, t) -> begin
(let _155_1325 = (let _155_1323 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _155_1323 (FStar_String.concat " * ")))
in (let _155_1324 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _155_1325 _155_1324)))
end
| QForall (bs, pats, t) -> begin
(let _155_1328 = (to_string_l " " binder_to_string bs)
in (let _155_1327 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _155_1326 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _155_1328 _155_1327 _155_1326))))
end
| QExists (bs, pats, t) -> begin
(let _155_1331 = (to_string_l " " binder_to_string bs)
in (let _155_1330 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _155_1329 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _155_1331 _155_1330 _155_1329))))
end
| Refine (b, t) -> begin
(let _155_1333 = (FStar_All.pipe_right b binder_to_string)
in (let _155_1332 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _155_1333 _155_1332)))
end
| NamedTyp (x, t) -> begin
(let _155_1334 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _155_1334))
end
| Paren (t) -> begin
(let _155_1335 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _155_1335))
end
| Product (bs, t) -> begin
(let _155_1338 = (let _155_1336 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _155_1336 (FStar_String.concat ",")))
in (let _155_1337 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _155_1338 _155_1337)))
end
| t -> begin
"_"
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
(let _155_1340 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _155_1340))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (let _155_1341 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _155_1341 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _60_3 -> (match (_60_3) with
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _60_616 -> begin
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
(let _155_1345 = (FStar_All.pipe_right p pat_to_string)
in (let _155_1344 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _155_1345 _155_1344)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _155_1346 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _155_1346 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _155_1347 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _155_1347))
end
| PatTuple (l, false) -> begin
(let _155_1348 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _155_1348))
end
| PatTuple (l, true) -> begin
(let _155_1349 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _155_1349))
end
| PatRecord (l) -> begin
(let _155_1352 = (to_string_l "; " (fun _60_647 -> (match (_60_647) with
| (f, e) -> begin
(let _155_1351 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _155_1351))
end)) l)
in (FStar_Util.format1 "{%s}" _155_1352))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatOp (op) -> begin
(FStar_Util.format1 "(%s)" op)
end
| PatAscribed (p, t) -> begin
(let _155_1354 = (FStar_All.pipe_right p pat_to_string)
in (let _155_1353 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _155_1354 _155_1353)))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, _60_661) -> begin
(let _155_1357 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_155_1357)::[])
end
| PatApp (p, _60_666) -> begin
(head_id_of_pat p)
end
| PatAscribed (p, _60_671) -> begin
(head_id_of_pat p)
end
| _60_675 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _60_680 -> (match (_60_680) with
| (p, _60_679) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun _60_4 -> (match (_60_4) with
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
| KindAbbrev (i, _60_724, _60_726) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| ToplevelLet (_60_730, _60_732, pats) -> begin
(let _155_1367 = (let _155_1366 = (let _155_1365 = (lids_of_let pats)
in (FStar_All.pipe_right _155_1365 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _155_1366 (FStar_String.concat ", ")))
in (Prims.strcat "let " _155_1367))
end
| Main (_60_738) -> begin
"main ..."
end
| Assume (_60_741, i, _60_744) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (_60_748, tys) -> begin
(let _155_1370 = (let _155_1369 = (FStar_All.pipe_right tys (FStar_List.map (fun _60_755 -> (match (_60_755) with
| (x, _60_754) -> begin
(id_of_tycon x)
end))))
in (FStar_All.pipe_right _155_1369 (FStar_String.concat ", ")))
in (Prims.strcat "type " _155_1370))
end
| Val (_60_757, i, _60_760) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, _60_765) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (NewEffect (_, DefineEffect (i, _, _, _, _))) | (NewEffect (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (NewEffectForFree (_, DefineEffect (i, _, _, _, _))) | (NewEffectForFree (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| SubEffect (_60_819) -> begin
"sub_effect"
end
| Pragma (_60_822) -> begin
"pragma"
end
| Fsdoc (_60_825) -> begin
"fsdoc"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| (Module (_, decls)) | (Interface (_, decls, _)) -> begin
(let _155_1373 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _155_1373 (FStar_String.concat "\n")))
end))


let error = (fun msg tm r -> (

let tm = (FStar_All.pipe_right tm term_to_string)
in (

let tm = if ((FStar_String.length tm) >= (Prims.parse_int "80")) then begin
(let _155_1377 = (FStar_Util.substring tm (Prims.parse_int "0") (Prims.parse_int "77"))
in (Prims.strcat _155_1377 "..."))
end else begin
tm
end
in if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat msg (Prims.strcat "\n" tm))), (r)))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat msg (Prims.strcat "\n" tm))), (r)))))
end)))




