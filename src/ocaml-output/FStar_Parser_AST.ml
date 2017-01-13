
open Prims

type level =
| Un
| Expr
| Type_level
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


let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
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
| UnivApp
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


let is_UnivApp = (fun _discr_ -> (match (_discr_) with
| UnivApp (_) -> begin
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
| Uvar of FStar_Ident.ident
| Var of FStar_Ident.lid
| Name of FStar_Ident.lid
| Projector of (FStar_Ident.lid * FStar_Ident.ident)
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
| Discrim of FStar_Ident.lid
| Attributes of term Prims.list 
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


let is_Uvar = (fun _discr_ -> (match (_discr_) with
| Uvar (_) -> begin
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


let is_Projector = (fun _discr_ -> (match (_discr_) with
| Projector (_) -> begin
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


let is_Discrim = (fun _discr_ -> (match (_discr_) with
| Discrim (_) -> begin
true
end
| _ -> begin
false
end))


let is_Attributes = (fun _discr_ -> (match (_discr_) with
| Attributes (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkterm"))))


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


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkbinder"))))


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


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkpattern"))))


let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_63_21) -> begin
_63_21
end))


let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_63_24) -> begin
_63_24
end))


let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_63_27) -> begin
_63_27
end))


let ___Uvar____0 = (fun projectee -> (match (projectee) with
| Uvar (_63_30) -> begin
_63_30
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_63_33) -> begin
_63_33
end))


let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_63_36) -> begin
_63_36
end))


let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_63_39) -> begin
_63_39
end))


let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_63_42) -> begin
_63_42
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_63_45) -> begin
_63_45
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_63_48) -> begin
_63_48
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_63_51) -> begin
_63_51
end))


let ___LetOpen____0 = (fun projectee -> (match (projectee) with
| LetOpen (_63_54) -> begin
_63_54
end))


let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_63_57) -> begin
_63_57
end))


let ___If____0 = (fun projectee -> (match (projectee) with
| If (_63_60) -> begin
_63_60
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_63_63) -> begin
_63_63
end))


let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_63_66) -> begin
_63_66
end))


let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_63_69) -> begin
_63_69
end))


let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_63_72) -> begin
_63_72
end))


let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_63_75) -> begin
_63_75
end))


let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_63_78) -> begin
_63_78
end))


let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_63_81) -> begin
_63_81
end))


let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_63_84) -> begin
_63_84
end))


let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_63_87) -> begin
_63_87
end))


let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_63_90) -> begin
_63_90
end))


let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_63_93) -> begin
_63_93
end))


let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_63_96) -> begin
_63_96
end))


let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_63_99) -> begin
_63_99
end))


let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_63_102) -> begin
_63_102
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_63_105) -> begin
_63_105
end))


let ___Assign____0 = (fun projectee -> (match (projectee) with
| Assign (_63_108) -> begin
_63_108
end))


let ___Discrim____0 = (fun projectee -> (match (projectee) with
| Discrim (_63_111) -> begin
_63_111
end))


let ___Attributes____0 = (fun projectee -> (match (projectee) with
| Attributes (_63_114) -> begin
_63_114
end))


let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_63_118) -> begin
_63_118
end))


let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_63_121) -> begin
_63_121
end))


let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_63_124) -> begin
_63_124
end))


let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_63_127) -> begin
_63_127
end))


let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_63_130) -> begin
_63_130
end))


let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_63_134) -> begin
_63_134
end))


let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_63_137) -> begin
_63_137
end))


let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_63_140) -> begin
_63_140
end))


let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_63_143) -> begin
_63_143
end))


let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_63_146) -> begin
_63_146
end))


let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_63_149) -> begin
_63_149
end))


let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_63_152) -> begin
_63_152
end))


let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_63_155) -> begin
_63_155
end))


let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_63_158) -> begin
_63_158
end))


let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_63_161) -> begin
_63_161
end))


let ___PatOp____0 = (fun projectee -> (match (projectee) with
| PatOp (_63_164) -> begin
_63_164
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
| TyconAbstract (_63_168) -> begin
_63_168
end))


let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_63_171) -> begin
_63_171
end))


let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_63_174) -> begin
_63_174
end))


let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_63_177) -> begin
_63_177
end))


type qualifier =
| Private
| Abstract
| Noeq
| Unopteq
| Assumption
| DefaultEffect
| TotalEffect
| Effect_qual
| New
| Inline
| Visible
| Unfold_for_unification_and_vcgen
| Inline_for_extraction
| Irreducible
| NoExtract
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


let is_Effect_qual = (fun _discr_ -> (match (_discr_) with
| Effect_qual (_) -> begin
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


let is_NoExtract = (fun _discr_ -> (match (_discr_) with
| NoExtract (_) -> begin
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


type attributes_ =
term Prims.list


type decoration =
| Qualifier of qualifier
| DeclAttributes of term Prims.list
| Doc of fsdoc


let is_Qualifier = (fun _discr_ -> (match (_discr_) with
| Qualifier (_) -> begin
true
end
| _ -> begin
false
end))


let is_DeclAttributes = (fun _discr_ -> (match (_discr_) with
| DeclAttributes (_) -> begin
true
end
| _ -> begin
false
end))


let is_Doc = (fun _discr_ -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))


let ___Qualifier____0 = (fun projectee -> (match (projectee) with
| Qualifier (_63_180) -> begin
_63_180
end))


let ___DeclAttributes____0 = (fun projectee -> (match (projectee) with
| DeclAttributes (_63_183) -> begin
_63_183
end))


let ___Doc____0 = (fun projectee -> (match (projectee) with
| Doc (_63_186) -> begin
_63_186
end))


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
| NonReifiableLift (_63_189) -> begin
_63_189
end))


let ___ReifiableLift____0 = (fun projectee -> (match (projectee) with
| ReifiableLift (_63_192) -> begin
_63_192
end))


let ___LiftForFree____0 = (fun projectee -> (match (projectee) with
| LiftForFree (_63_195) -> begin
_63_195
end))


type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : lift_op}


let is_Mklift : lift  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mklift"))))


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
| SetOptions (_63_202) -> begin
_63_202
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_63_205) -> begin
_63_205
end))


type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| Include of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| TopLevelLet of (let_qualifier * (pattern * term) Prims.list)
| Main of term
| Tycon of (Prims.bool * (tycon * fsdoc Prims.option) Prims.list)
| Val of (FStar_Ident.ident * term)
| Exception of (FStar_Ident.ident * term Prims.option)
| NewEffect of effect_decl
| NewEffectForFree of effect_decl
| SubEffect of lift
| Pragma of pragma
| Fsdoc of fsdoc
| KindAbbrev of (FStar_Ident.ident * binder Prims.list * knd)
| Assume of (FStar_Ident.ident * term) 
 and decl =
{d : decl'; drange : FStar_Range.range; doc : fsdoc Prims.option; quals : qualifiers; attrs : attributes_} 
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


let is_Include = (fun _discr_ -> (match (_discr_) with
| Include (_) -> begin
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


let is_TopLevelLet = (fun _discr_ -> (match (_discr_) with
| TopLevelLet (_) -> begin
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


let is_KindAbbrev = (fun _discr_ -> (match (_discr_) with
| KindAbbrev (_) -> begin
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


let is_Mkdecl : decl  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkdecl"))))


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
| TopLevelModule (_63_213) -> begin
_63_213
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_63_216) -> begin
_63_216
end))


let ___Include____0 = (fun projectee -> (match (projectee) with
| Include (_63_219) -> begin
_63_219
end))


let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_63_222) -> begin
_63_222
end))


let ___TopLevelLet____0 = (fun projectee -> (match (projectee) with
| TopLevelLet (_63_225) -> begin
_63_225
end))


let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_63_228) -> begin
_63_228
end))


let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_63_231) -> begin
_63_231
end))


let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_63_234) -> begin
_63_234
end))


let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_63_237) -> begin
_63_237
end))


let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_63_240) -> begin
_63_240
end))


let ___NewEffectForFree____0 = (fun projectee -> (match (projectee) with
| NewEffectForFree (_63_243) -> begin
_63_243
end))


let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_63_246) -> begin
_63_246
end))


let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_63_249) -> begin
_63_249
end))


let ___Fsdoc____0 = (fun projectee -> (match (projectee) with
| Fsdoc (_63_252) -> begin
_63_252
end))


let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_63_255) -> begin
_63_255
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_63_258) -> begin
_63_258
end))


let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_63_262) -> begin
_63_262
end))


let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_63_265) -> begin
_63_265
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
| Module (_63_268) -> begin
_63_268
end))


let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_63_271) -> begin
_63_271
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
(let _164_1216 = (let _164_1215 = (let _164_1214 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in ((_164_1214), (id.FStar_Ident.idRange)))
in FStar_Errors.Error (_164_1215))
in (Prims.raise _164_1216))
end)
end else begin
()
end)


let at_most_one = (fun s r l -> (match (l) with
| (x)::[] -> begin
Some (x)
end
| [] -> begin
None
end
| _63_281 -> begin
(let _164_1222 = (let _164_1221 = (let _164_1220 = (FStar_Util.format1 "At most one %s is allowed on declarations" s)
in ((_164_1220), (r)))
in FStar_Errors.Error (_164_1221))
in (Prims.raise _164_1222))
end))


let mk_decl : decl'  ->  FStar_Range.range  ->  decoration Prims.list  ->  decl = (fun d r decorations -> (

let doc = (let _164_1230 = (FStar_List.choose (fun _63_1 -> (match (_63_1) with
| Doc (d) -> begin
Some (d)
end
| _63_289 -> begin
None
end)) decorations)
in (at_most_one "fsdoc" r _164_1230))
in (

let attributes_ = (let _164_1232 = (FStar_List.choose (fun _63_2 -> (match (_63_2) with
| DeclAttributes (a) -> begin
Some (a)
end
| _63_295 -> begin
None
end)) decorations)
in (at_most_one "attribute set" r _164_1232))
in (

let attributes_ = (FStar_Util.dflt [] attributes_)
in (

let qualifiers = (FStar_List.choose (fun _63_3 -> (match (_63_3) with
| Qualifier (q) -> begin
Some (q)
end
| _63_302 -> begin
None
end)) decorations)
in {d = d; drange = r; doc = doc; quals = qualifiers; attrs = attributes_})))))


let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})


let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})


let mk_uminus : term  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> (

let t = (match (t.tm) with
| Const (FStar_Const.Const_int (s, Some (FStar_Const.Signed, width))) -> begin
Const (FStar_Const.Const_int ((((Prims.strcat "-" s)), (Some (((FStar_Const.Signed), (width)))))))
end
| _63_323 -> begin
Op ((("-"), ((t)::[])))
end)
in (mk_term t r l)))


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs ((((FStar_List.append ps p')), (body')))
end
| _63_334 -> begin
Abs (((ps), (body)))
end))


let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = (

let i = (FStar_Syntax_Syntax.next_id ())
in (FStar_Ident.gen r1))
in (let _164_1275 = (let _164_1274 = (let _164_1273 = (let _164_1272 = (let _164_1271 = (let _164_1270 = (let _164_1269 = (let _164_1268 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_164_1268))
in (mk_term _164_1269 r1 Expr))
in ((_164_1270), (branches)))
in Match (_164_1271))
in (mk_term _164_1272 r2 Expr))
in ((((mk_pattern (PatVar (((x), (None)))) r1))::[]), (_164_1273)))
in Abs (_164_1274))
in (mk_term _164_1275 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match (((p.pat), (tm.tm))) with
| (PatVar (_63_343), Abs (pats, body)) -> begin
Some ((((mk_pattern (PatApp (((p), (pats)))) p.prange)), (body)))
end
| _63_351 -> begin
None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _164_1284 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _164_1284 r)))


let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd tl -> PatApp ((((mk_pattern (PatName (FStar_Syntax_Const.cons_lid)) r)), ((hd)::(tl)::[]))))


let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct (((FStar_Syntax_Const.cons_lid), ((((hd), (Nothing)))::(((tl), (Nothing)))::[])))) r Expr))


let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct (((FStar_Syntax_Const.lexcons_lid), ((((hd), (Nothing)))::(((tl), (Nothing)))::[])))) r Expr))


let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct (((FStar_Syntax_Const.nil_lid), ([])))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))


let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct (((FStar_Syntax_Const.lextop_lid), ([])))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))


let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _63_378 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct (((s), (args)))) r Un)
end
| _63_382 -> begin
(FStar_List.fold_left (fun t _63_386 -> (match (_63_386) with
| (a, imp) -> begin
(mk_term (App (((t), (a), (imp)))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let univs = (FStar_Options.universes ())
in (

let _63_393 = if univs then begin
((FStar_Syntax_Const.tset_empty), (FStar_Syntax_Const.tset_singleton), (FStar_Syntax_Const.tset_union))
end else begin
((FStar_Syntax_Const.set_empty), (FStar_Syntax_Const.set_singleton), (FStar_Syntax_Const.set_union))
end
in (match (_63_393) with
| (empty_lid, singleton_lid, union_lid) -> begin
(

let empty = (mk_term (Var ((FStar_Ident.set_lid_range empty_lid r))) r Expr)
in (

let ref_constr = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Syntax_Const.heap_ref r))) r Expr)
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
| _63_407 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _164_1338 = (let _164_1337 = (let _164_1336 = (FStar_List.map (fun a -> ((a), (Nothing))) args)
in ((s), (_164_1336)))
in Construct (_164_1337))
in (mk_term _164_1338 r Un))
end
| _63_412 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App (((t), (a), (Nothing)))) r Un)) t args)
end)
end))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (

let admit = (

let admit_name = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Syntax_Const.admit_lid r))) r Expr)
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (

let magic = (

let magic_name = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Syntax_Const.magic_lid r))) r Expr)
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (

let admit_magic = (mk_term (Seq (((admit), (magic)))) r Expr)
in admit_magic)))))


let mkWildAdmitMagic = (fun r -> (let _164_1344 = (mkAdmitMagic r)
in (((mk_pattern PatWild r)), (None), (_164_1344))))


let focusBranches = (fun branches r -> (

let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(

let _63_426 = (FStar_Errors.warn r "Focusing on only some cases")
in (

let focussed = (let _164_1347 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _164_1347 (FStar_List.map Prims.snd)))
in (let _164_1349 = (let _164_1348 = (mkWildAdmitMagic r)
in (_164_1348)::[])
in (FStar_List.append focussed _164_1349))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))


let focusLetBindings = (fun lbs r -> (

let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(

let _63_432 = (FStar_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _63_436 -> (match (_63_436) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _164_1353 = (mkAdmitMagic r)
in (((Prims.fst lb)), (_164_1353)))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _164_1361 = (FStar_List.map (fun a -> ((a), (FsTypApp))) args)
in (mkApp t _164_1361 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
in (let _164_1367 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons)) r Expr) _164_1367 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
in (let _164_1373 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons)) r Expr) _164_1373 r))))


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  Prims.bool  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t should_bind_var refopt m implicit -> (

let b = (mk_binder (Annotated (((id), (t)))) m Type_level implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (phi) -> begin
if should_bind_var then begin
(mk_binder (Annotated (((id), ((mk_term (Refine (((b), (phi)))) m Type_level))))) m Type_level implicit)
end else begin
(

let x = (FStar_Ident.gen t.range)
in (

let b = (mk_binder (Annotated (((x), (t)))) m Type_level implicit)
in (mk_binder (Annotated (((id), ((mk_term (Refine (((b), (phi)))) m Type_level))))) m Type_level implicit)))
end
end)))


let mkRefinedPattern : pattern  ->  term  ->  Prims.bool  ->  term Prims.option  ->  FStar_Range.range  ->  FStar_Range.range  ->  pattern = (fun pat t should_bind_pat phi_opt t_range range -> (

let t = (match (phi_opt) with
| None -> begin
t
end
| Some (phi) -> begin
if should_bind_pat then begin
(match (pat.pat) with
| PatVar (x, _63_472) -> begin
(mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level None)), (phi)))) range Type_level)
end
| _63_476 -> begin
(

let x = (FStar_Ident.gen t_range)
in (

let phi = (

let x_var = (let _164_1399 = (let _164_1398 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_164_1398))
in (mk_term _164_1399 phi.range Formula))
in (

let pat_branch = ((pat), (None), (phi))
in (

let otherwise_branch = (let _164_1402 = (let _164_1401 = (let _164_1400 = (FStar_Ident.lid_of_path (("False")::[]) phi.range)
in Name (_164_1400))
in (mk_term _164_1401 phi.range Formula))
in (((mk_pattern PatWild phi.range)), (None), (_164_1402)))
in (mk_term (Match (((x_var), ((pat_branch)::(otherwise_branch)::[])))) phi.range Formula))))
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level None)), (phi)))) range Type_level)))
end)
end else begin
(

let x = (FStar_Ident.gen t.range)
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level None)), (phi)))) range Type_level))
end
end)
in (mk_pattern (PatAscribed (((pat), (t)))) range)))


let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term Prims.option) Prims.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some (((x), (t), (None)))
end
| Refine ({b = Annotated (x, t); brange = _63_494; blevel = _63_492; aqual = _63_490}, t') -> begin
Some (((x), (t), (Some (t'))))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _63_506 -> begin
None
end))


let rec as_mlist : modul Prims.list  ->  ((FStar_Ident.lid * decl) * decl Prims.list)  ->  decl Prims.list  ->  modul Prims.list = (fun out cur ds -> (

let _63_514 = cur
in (match (_63_514) with
| ((m_name, m_decl), cur) -> begin
(match (ds) with
| [] -> begin
(FStar_List.rev ((Module (((m_name), ((m_decl)::(FStar_List.rev cur)))))::out))
end
| (d)::ds -> begin
(match (d.d) with
| TopLevelModule (m') -> begin
(as_mlist ((Module (((m_name), ((m_decl)::(FStar_List.rev cur)))))::out) ((((m'), (d))), ([])) ds)
end
| _63_522 -> begin
(as_mlist out ((((m_name), (m_decl))), ((d)::cur)) ds)
end)
end)
end)))


let as_frag : decl  ->  decl Prims.list  ->  (modul Prims.list, decl Prims.list) FStar_Util.either = (fun d ds -> (match (d.d) with
| TopLevelModule (m) -> begin
(

let ms = (as_mlist [] ((((m), (d))), ([])) ds)
in (

let _63_539 = (match ((FStar_List.tl ms)) with
| (Module (m', _63_532))::_63_529 -> begin
(

let msg = "Support for more than one module in a file is deprecated"
in (let _164_1415 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid m'))
in (FStar_Util.print2_warning "%s (Warning): %s\n" _164_1415 msg)))
end
| _63_538 -> begin
()
end)
in FStar_Util.Inl (ms)))
end
| _63_542 -> begin
(

let ds = (d)::ds
in (

let _63_558 = (FStar_List.iter (fun _63_4 -> (match (_63_4) with
| {d = TopLevelModule (_63_553); drange = r; doc = _63_550; quals = _63_548; attrs = _63_546} -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected module declaration"), (r)))))
end
| _63_557 -> begin
()
end)) ds)
in FStar_Util.Inr (ds)))
end))


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _63_5 -> (match (_63_5) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = (Prims.parse_int "1")) -> begin
"Minus"
end
| '-' -> begin
"Subtraction"
end
| '/' -> begin
"Slash"
end
| '<' -> begin
"Less"
end
| '=' -> begin
"Equals"
end
| '>' -> begin
"Greater"
end
| '_' -> begin
"Underscore"
end
| '|' -> begin
"Bar"
end
| '!' -> begin
"Bang"
end
| '^' -> begin
"Hat"
end
| '%' -> begin
"Percent"
end
| '*' -> begin
"Star"
end
| '?' -> begin
"Question"
end
| ':' -> begin
"Colon"
end
| _63_581 -> begin
"UNKNOWN"
end))
in (match (s) with
| ".[]<-" -> begin
"op_String_Assignment"
end
| ".()<-" -> begin
"op_Array_Assignment"
end
| ".[]" -> begin
"op_String_Access"
end
| ".()" -> begin
"op_Array_Access"
end
| _63_588 -> begin
(let _164_1425 = (let _164_1424 = (let _164_1423 = (FStar_String.list_of_string s)
in (FStar_List.map name_of_char _164_1423))
in (FStar_String.concat "_" _164_1424))
in (Prims.strcat "op_" _164_1425))
end)))


let compile_op' : Prims.string  ->  Prims.string = (fun s -> (compile_op (~- ((Prims.parse_int "1"))) s))


let string_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  Prims.string = (fun _63_592 -> (match (_63_592) with
| (comment, keywords) -> begin
(let _164_1432 = (let _164_1431 = (FStar_List.map (fun _63_595 -> (match (_63_595) with
| (k, v) -> begin
(Prims.strcat k (Prims.strcat "->" v))
end)) keywords)
in (FStar_String.concat "," _164_1431))
in (Prims.strcat comment _164_1432))
end))


let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun _63_6 -> (match (_63_6) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end
| Mutable -> begin
"mutable"
end))


let to_string_l = (fun sep f l -> (let _164_1441 = (FStar_List.map f l)
in (FStar_String.concat sep _164_1441)))


let imp_to_string : imp  ->  Prims.string = (fun _63_7 -> (match (_63_7) with
| Hash -> begin
"#"
end
| _63_606 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _63_611) -> begin
(let _164_1449 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _164_1449))
end
| Ensures (t, _63_616) -> begin
(let _164_1450 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _164_1450))
end
| Labeled (t, l, _63_622) -> begin
(let _164_1451 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _164_1451))
end
| Const (c) -> begin
(FStar_Syntax_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _164_1454 = (let _164_1453 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _164_1453))
in (FStar_Util.format2 "%s(%s)" s _164_1454))
end
| (Tvar (id)) | (Uvar (id)) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _164_1457 = (to_string_l " " (fun _63_644 -> (match (_63_644) with
| (a, imp) -> begin
(let _164_1456 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _164_1456))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _164_1457))
end
| Abs (pats, t) -> begin
(let _164_1459 = (to_string_l " " pat_to_string pats)
in (let _164_1458 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _164_1459 _164_1458)))
end
| App (t1, t2, imp) -> begin
(let _164_1461 = (FStar_All.pipe_right t1 term_to_string)
in (let _164_1460 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _164_1461 (imp_to_string imp) _164_1460)))
end
| Let (Rec, lbs, body) -> begin
(let _164_1466 = (to_string_l " and " (fun _63_661 -> (match (_63_661) with
| (p, b) -> begin
(let _164_1464 = (FStar_All.pipe_right p pat_to_string)
in (let _164_1463 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _164_1464 _164_1463)))
end)) lbs)
in (let _164_1465 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _164_1466 _164_1465)))
end
| Let (q, ((pat, tm))::[], body) -> begin
(let _164_1469 = (FStar_All.pipe_right pat pat_to_string)
in (let _164_1468 = (FStar_All.pipe_right tm term_to_string)
in (let _164_1467 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) _164_1469 _164_1468 _164_1467))))
end
| Seq (t1, t2) -> begin
(let _164_1471 = (FStar_All.pipe_right t1 term_to_string)
in (let _164_1470 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _164_1471 _164_1470)))
end
| If (t1, t2, t3) -> begin
(let _164_1474 = (FStar_All.pipe_right t1 term_to_string)
in (let _164_1473 = (FStar_All.pipe_right t2 term_to_string)
in (let _164_1472 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _164_1474 _164_1473 _164_1472))))
end
| Match (t, branches) -> begin
(let _164_1481 = (FStar_All.pipe_right t term_to_string)
in (let _164_1480 = (to_string_l " | " (fun _63_686 -> (match (_63_686) with
| (p, w, e) -> begin
(let _164_1479 = (FStar_All.pipe_right p pat_to_string)
in (let _164_1478 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _164_1476 = (term_to_string e)
in (FStar_Util.format1 "when %s" _164_1476))
end)
in (let _164_1477 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _164_1479 _164_1478 _164_1477))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _164_1481 _164_1480)))
end
| Ascribed (t1, t2) -> begin
(let _164_1483 = (FStar_All.pipe_right t1 term_to_string)
in (let _164_1482 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _164_1483 _164_1482)))
end
| Record (Some (e), fields) -> begin
(let _164_1487 = (FStar_All.pipe_right e term_to_string)
in (let _164_1486 = (to_string_l " " (fun _63_701 -> (match (_63_701) with
| (l, e) -> begin
(let _164_1485 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _164_1485))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _164_1487 _164_1486)))
end
| Record (None, fields) -> begin
(let _164_1490 = (to_string_l " " (fun _63_708 -> (match (_63_708) with
| (l, e) -> begin
(let _164_1489 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _164_1489))
end)) fields)
in (FStar_Util.format1 "{%s}" _164_1490))
end
| Project (e, l) -> begin
(let _164_1491 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _164_1491 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd)::tl, t) -> begin
(term_to_string (mk_term (Product ((((b)::[]), ((mk_term (Product ((((hd)::tl), (t)))) x.range x.level))))) x.range x.level))
end
| Product ((b)::[], t) when (x.level = Type_level) -> begin
(let _164_1493 = (FStar_All.pipe_right b binder_to_string)
in (let _164_1492 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _164_1493 _164_1492)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(let _164_1495 = (FStar_All.pipe_right b binder_to_string)
in (let _164_1494 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _164_1495 _164_1494)))
end
| Sum (binders, t) -> begin
(let _164_1498 = (let _164_1496 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _164_1496 (FStar_String.concat " * ")))
in (let _164_1497 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _164_1498 _164_1497)))
end
| QForall (bs, pats, t) -> begin
(let _164_1501 = (to_string_l " " binder_to_string bs)
in (let _164_1500 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _164_1499 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _164_1501 _164_1500 _164_1499))))
end
| QExists (bs, pats, t) -> begin
(let _164_1504 = (to_string_l " " binder_to_string bs)
in (let _164_1503 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _164_1502 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _164_1504 _164_1503 _164_1502))))
end
| Refine (b, t) -> begin
(let _164_1506 = (FStar_All.pipe_right b binder_to_string)
in (let _164_1505 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _164_1506 _164_1505)))
end
| NamedTyp (x, t) -> begin
(let _164_1507 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _164_1507))
end
| Paren (t) -> begin
(let _164_1508 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _164_1508))
end
| Product (bs, t) -> begin
(let _164_1511 = (let _164_1509 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _164_1509 (FStar_String.concat ",")))
in (let _164_1510 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _164_1511 _164_1510)))
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
(let _164_1513 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _164_1513))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (let _164_1514 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _164_1514 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _63_8 -> (match (_63_8) with
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _63_784 -> begin
""
end))
and pat_to_string : pattern  ->  Prims.string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Syntax_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
(let _164_1518 = (FStar_All.pipe_right p pat_to_string)
in (let _164_1517 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _164_1518 _164_1517)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _164_1519 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _164_1519 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _164_1520 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _164_1520))
end
| PatTuple (l, false) -> begin
(let _164_1521 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _164_1521))
end
| PatTuple (l, true) -> begin
(let _164_1522 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _164_1522))
end
| PatRecord (l) -> begin
(let _164_1525 = (to_string_l "; " (fun _63_815 -> (match (_63_815) with
| (f, e) -> begin
(let _164_1524 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _164_1524))
end)) l)
in (FStar_Util.format1 "{%s}" _164_1525))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatOp (op) -> begin
(FStar_Util.format1 "(%s)" op)
end
| PatAscribed (p, t) -> begin
(let _164_1527 = (FStar_All.pipe_right p pat_to_string)
in (let _164_1526 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _164_1527 _164_1526)))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, _63_829) -> begin
(let _164_1530 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_164_1530)::[])
end
| PatApp (p, _63_834) -> begin
(head_id_of_pat p)
end
| PatAscribed (p, _63_839) -> begin
(head_id_of_pat p)
end
| _63_843 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _63_848 -> (match (_63_848) with
| (p, _63_847) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun _63_9 -> (match (_63_9) with
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
| Include (l) -> begin
(Prims.strcat "include " l.FStar_Ident.str)
end
| ModuleAbbrev (i, l) -> begin
(FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText l.FStar_Ident.str)
end
| KindAbbrev (i, _63_894, _63_896) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| TopLevelLet (_63_900, pats) -> begin
(let _164_1540 = (let _164_1539 = (let _164_1538 = (lids_of_let pats)
in (FStar_All.pipe_right _164_1538 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _164_1539 (FStar_String.concat ", ")))
in (Prims.strcat "let " _164_1540))
end
| Main (_63_906) -> begin
"main ..."
end
| Assume (i, _63_910) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (_63_914, tys) -> begin
(let _164_1543 = (let _164_1542 = (FStar_All.pipe_right tys (FStar_List.map (fun _63_921 -> (match (_63_921) with
| (x, _63_920) -> begin
(id_of_tycon x)
end))))
in (FStar_All.pipe_right _164_1542 (FStar_String.concat ", ")))
in (Prims.strcat "type " _164_1543))
end
| Val (i, _63_924) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, _63_929) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (NewEffect (DefineEffect (i, _, _, _, _))) | (NewEffect (RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (NewEffectForFree (DefineEffect (i, _, _, _, _))) | (NewEffectForFree (RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| SubEffect (_63_971) -> begin
"sub_effect"
end
| Pragma (_63_974) -> begin
"pragma"
end
| Fsdoc (_63_977) -> begin
"fsdoc"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| (Module (_, decls)) | (Interface (_, decls, _)) -> begin
(let _164_1546 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _164_1546 (FStar_String.concat "\n")))
end))


let error = (fun msg tm r -> (

let tm = (FStar_All.pipe_right tm term_to_string)
in (

let tm = if ((FStar_String.length tm) >= (Prims.parse_int "80")) then begin
(let _164_1550 = (FStar_Util.substring tm (Prims.parse_int "0") (Prims.parse_int "77"))
in (Prims.strcat _164_1550 "..."))
end else begin
tm
end
in (Prims.raise (FStar_Errors.Error ((((Prims.strcat msg (Prims.strcat "\n" tm))), (r))))))))




