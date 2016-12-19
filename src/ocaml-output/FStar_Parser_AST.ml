
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
| Const (_61_16) -> begin
_61_16
end))


let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_61_19) -> begin
_61_19
end))


let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_61_22) -> begin
_61_22
end))


let ___Uvar____0 = (fun projectee -> (match (projectee) with
| Uvar (_61_25) -> begin
_61_25
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_61_28) -> begin
_61_28
end))


let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_61_31) -> begin
_61_31
end))


let ___Projector____0 = (fun projectee -> (match (projectee) with
| Projector (_61_34) -> begin
_61_34
end))


let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_61_37) -> begin
_61_37
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_61_40) -> begin
_61_40
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_61_43) -> begin
_61_43
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_61_46) -> begin
_61_46
end))


let ___LetOpen____0 = (fun projectee -> (match (projectee) with
| LetOpen (_61_49) -> begin
_61_49
end))


let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_61_52) -> begin
_61_52
end))


let ___If____0 = (fun projectee -> (match (projectee) with
| If (_61_55) -> begin
_61_55
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_61_58) -> begin
_61_58
end))


let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_61_61) -> begin
_61_61
end))


let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_61_64) -> begin
_61_64
end))


let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_61_67) -> begin
_61_67
end))


let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_61_70) -> begin
_61_70
end))


let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_61_73) -> begin
_61_73
end))


let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_61_76) -> begin
_61_76
end))


let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_61_79) -> begin
_61_79
end))


let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_61_82) -> begin
_61_82
end))


let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_61_85) -> begin
_61_85
end))


let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_61_88) -> begin
_61_88
end))


let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_61_91) -> begin
_61_91
end))


let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_61_94) -> begin
_61_94
end))


let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_61_97) -> begin
_61_97
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_61_100) -> begin
_61_100
end))


let ___Assign____0 = (fun projectee -> (match (projectee) with
| Assign (_61_103) -> begin
_61_103
end))


let ___Discrim____0 = (fun projectee -> (match (projectee) with
| Discrim (_61_106) -> begin
_61_106
end))


let ___Attributes____0 = (fun projectee -> (match (projectee) with
| Attributes (_61_109) -> begin
_61_109
end))


let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_61_113) -> begin
_61_113
end))


let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_61_116) -> begin
_61_116
end))


let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_61_119) -> begin
_61_119
end))


let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_61_122) -> begin
_61_122
end))


let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_61_125) -> begin
_61_125
end))


let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_61_129) -> begin
_61_129
end))


let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_61_132) -> begin
_61_132
end))


let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_61_135) -> begin
_61_135
end))


let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_61_138) -> begin
_61_138
end))


let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_61_141) -> begin
_61_141
end))


let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_61_144) -> begin
_61_144
end))


let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_61_147) -> begin
_61_147
end))


let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_61_150) -> begin
_61_150
end))


let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_61_153) -> begin
_61_153
end))


let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_61_156) -> begin
_61_156
end))


let ___PatOp____0 = (fun projectee -> (match (projectee) with
| PatOp (_61_159) -> begin
_61_159
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
| TyconAbstract (_61_163) -> begin
_61_163
end))


let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_61_166) -> begin
_61_166
end))


let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_61_169) -> begin
_61_169
end))


let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_61_172) -> begin
_61_172
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
| NonReifiableLift (_61_175) -> begin
_61_175
end))


let ___ReifiableLift____0 = (fun projectee -> (match (projectee) with
| ReifiableLift (_61_178) -> begin
_61_178
end))


let ___LiftForFree____0 = (fun projectee -> (match (projectee) with
| LiftForFree (_61_181) -> begin
_61_181
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
| SetOptions (_61_188) -> begin
_61_188
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_61_191) -> begin
_61_191
end))


type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| KindAbbrev of (FStar_Ident.ident * binder Prims.list * knd)
| TopLevelLet of (qualifiers * let_qualifier * (pattern * term) Prims.list)
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
| TopLevelModule (_61_197) -> begin
_61_197
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_61_200) -> begin
_61_200
end))


let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_61_203) -> begin
_61_203
end))


let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_61_206) -> begin
_61_206
end))


let ___TopLevelLet____0 = (fun projectee -> (match (projectee) with
| TopLevelLet (_61_209) -> begin
_61_209
end))


let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_61_212) -> begin
_61_212
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_61_215) -> begin
_61_215
end))


let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_61_218) -> begin
_61_218
end))


let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_61_221) -> begin
_61_221
end))


let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_61_224) -> begin
_61_224
end))


let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_61_227) -> begin
_61_227
end))


let ___NewEffectForFree____0 = (fun projectee -> (match (projectee) with
| NewEffectForFree (_61_230) -> begin
_61_230
end))


let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_61_233) -> begin
_61_233
end))


let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_61_236) -> begin
_61_236
end))


let ___Fsdoc____0 = (fun projectee -> (match (projectee) with
| Fsdoc (_61_239) -> begin
_61_239
end))


let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_61_243) -> begin
_61_243
end))


let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_61_246) -> begin
_61_246
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
| Module (_61_249) -> begin
_61_249
end))


let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_61_252) -> begin
_61_252
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
(let _158_1154 = (let _158_1153 = (let _158_1152 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in ((_158_1152), (id.FStar_Ident.idRange)))
in FStar_Syntax_Syntax.Error (_158_1153))
in (Prims.raise _158_1154))
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
| _61_277 -> begin
Op ((("-"), ((t)::[])))
end)
in (mk_term t r l)))


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs ((((FStar_List.append ps p')), (body')))
end
| _61_288 -> begin
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
in (let _158_1202 = (let _158_1201 = (let _158_1200 = (let _158_1199 = (let _158_1198 = (let _158_1197 = (let _158_1196 = (let _158_1195 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_158_1195))
in (mk_term _158_1196 r1 Expr))
in ((_158_1197), (branches)))
in Match (_158_1198))
in (mk_term _158_1199 r2 Expr))
in ((((mk_pattern (PatVar (((x), (None)))) r1))::[]), (_158_1200)))
in Abs (_158_1201))
in (mk_term _158_1202 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match (((p.pat), (tm.tm))) with
| (PatVar (_61_297), Abs (pats, body)) -> begin
Some ((((mk_pattern (PatApp (((p), (pats)))) p.prange)), (body)))
end
| _61_305 -> begin
None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _158_1211 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _158_1211 r)))


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
| _61_332 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct (((s), (args)))) r Un)
end
| _61_336 -> begin
(FStar_List.fold_left (fun t _61_340 -> (match (_61_340) with
| (a, imp) -> begin
(mk_term (App (((t), (a), (imp)))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let univs = (FStar_Options.universes ())
in (

let _61_347 = if univs then begin
((FStar_Absyn_Const.tset_empty), (FStar_Absyn_Const.tset_singleton), (FStar_Absyn_Const.tset_union))
end else begin
((FStar_Absyn_Const.set_empty), (FStar_Absyn_Const.set_singleton), (FStar_Absyn_Const.set_union))
end
in (match (_61_347) with
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
| _61_361 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _158_1265 = (let _158_1264 = (let _158_1263 = (FStar_List.map (fun a -> ((a), (Nothing))) args)
in ((s), (_158_1263)))
in Construct (_158_1264))
in (mk_term _158_1265 r Un))
end
| _61_366 -> begin
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


let mkWildAdmitMagic = (fun r -> (let _158_1271 = (mkAdmitMagic r)
in (((mk_pattern PatWild r)), (None), (_158_1271))))


let focusBranches = (fun branches r -> (

let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(

let _61_380 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (

let focussed = (let _158_1274 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _158_1274 (FStar_List.map Prims.snd)))
in (let _158_1276 = (let _158_1275 = (mkWildAdmitMagic r)
in (_158_1275)::[])
in (FStar_List.append focussed _158_1276))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))


let focusLetBindings = (fun lbs r -> (

let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(

let _61_386 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _61_390 -> (match (_61_390) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _158_1280 = (mkAdmitMagic r)
in (((Prims.fst lb)), (_158_1280)))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _158_1288 = (FStar_List.map (fun a -> ((a), (FsTypApp))) args)
in (mkApp t _158_1288 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
in (let _158_1294 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons)) r Expr) _158_1294 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_Options.universes ()) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
in (let _158_1300 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons)) r Expr) _158_1300 r))))


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  Prims.bool  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t should_bind_var refopt m implicit -> (

let b = (mk_binder (Annotated (((id), (t)))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (phi) -> begin
if should_bind_var then begin
(mk_binder (Annotated (((id), ((mk_term (Refine (((b), (phi)))) m Type))))) m Type implicit)
end else begin
(

let x = (FStar_Ident.gen t.range)
in (

let b = (mk_binder (Annotated (((x), (t)))) m Type implicit)
in (mk_binder (Annotated (((id), ((mk_term (Refine (((b), (phi)))) m Type))))) m Type implicit)))
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
| PatVar (x, _61_426) -> begin
(mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type None)), (phi)))) range Type)
end
| _61_430 -> begin
(

let x = (FStar_Ident.gen t_range)
in (

let phi = (

let x_var = (let _158_1326 = (let _158_1325 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_158_1325))
in (mk_term _158_1326 phi.range Formula))
in (

let pat_branch = ((pat), (None), (phi))
in (

let otherwise_branch = (let _158_1329 = (let _158_1328 = (let _158_1327 = (FStar_Ident.lid_of_path (("False")::[]) phi.range)
in Name (_158_1327))
in (mk_term _158_1328 phi.range Formula))
in (((mk_pattern PatWild phi.range)), (None), (_158_1329)))
in (mk_term (Match (((x_var), ((pat_branch)::(otherwise_branch)::[])))) phi.range Formula))))
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type None)), (phi)))) range Type)))
end)
end else begin
(

let x = (FStar_Ident.gen t.range)
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type None)), (phi)))) range Type))
end
end)
in (mk_pattern (PatAscribed (((pat), (t)))) range)))


let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term Prims.option) Prims.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some (((x), (t), (None)))
end
| Refine ({b = Annotated (x, t); brange = _61_448; blevel = _61_446; aqual = _61_444}, t') -> begin
Some (((x), (t), (Some (t'))))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _61_460 -> begin
None
end))


let string_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  Prims.string = (fun _61_463 -> (match (_61_463) with
| (comment, keywords) -> begin
(let _158_1336 = (let _158_1335 = (FStar_List.map (fun _61_466 -> (match (_61_466) with
| (k, v) -> begin
(Prims.strcat k (Prims.strcat "->" v))
end)) keywords)
in (FStar_String.concat "," _158_1335))
in (Prims.strcat comment _158_1336))
end))


let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun _61_1 -> (match (_61_1) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end
| Mutable -> begin
"mutable"
end))


let to_string_l = (fun sep f l -> (let _158_1345 = (FStar_List.map f l)
in (FStar_String.concat sep _158_1345)))


let imp_to_string : imp  ->  Prims.string = (fun _61_2 -> (match (_61_2) with
| Hash -> begin
"#"
end
| _61_477 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _61_482) -> begin
(let _158_1353 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _158_1353))
end
| Ensures (t, _61_487) -> begin
(let _158_1354 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _158_1354))
end
| Labeled (t, l, _61_493) -> begin
(let _158_1355 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _158_1355))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _158_1358 = (let _158_1357 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _158_1357))
in (FStar_Util.format2 "%s(%s)" s _158_1358))
end
| (Tvar (id)) | (Uvar (id)) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _158_1361 = (to_string_l " " (fun _61_515 -> (match (_61_515) with
| (a, imp) -> begin
(let _158_1360 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _158_1360))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _158_1361))
end
| Abs (pats, t) -> begin
(let _158_1363 = (to_string_l " " pat_to_string pats)
in (let _158_1362 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _158_1363 _158_1362)))
end
| App (t1, t2, imp) -> begin
(let _158_1365 = (FStar_All.pipe_right t1 term_to_string)
in (let _158_1364 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _158_1365 (imp_to_string imp) _158_1364)))
end
| Let (Rec, lbs, body) -> begin
(let _158_1370 = (to_string_l " and " (fun _61_532 -> (match (_61_532) with
| (p, b) -> begin
(let _158_1368 = (FStar_All.pipe_right p pat_to_string)
in (let _158_1367 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _158_1368 _158_1367)))
end)) lbs)
in (let _158_1369 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _158_1370 _158_1369)))
end
| Let (q, ((pat, tm))::[], body) -> begin
(let _158_1373 = (FStar_All.pipe_right pat pat_to_string)
in (let _158_1372 = (FStar_All.pipe_right tm term_to_string)
in (let _158_1371 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) _158_1373 _158_1372 _158_1371))))
end
| Seq (t1, t2) -> begin
(let _158_1375 = (FStar_All.pipe_right t1 term_to_string)
in (let _158_1374 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _158_1375 _158_1374)))
end
| If (t1, t2, t3) -> begin
(let _158_1378 = (FStar_All.pipe_right t1 term_to_string)
in (let _158_1377 = (FStar_All.pipe_right t2 term_to_string)
in (let _158_1376 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _158_1378 _158_1377 _158_1376))))
end
| Match (t, branches) -> begin
(let _158_1385 = (FStar_All.pipe_right t term_to_string)
in (let _158_1384 = (to_string_l " | " (fun _61_557 -> (match (_61_557) with
| (p, w, e) -> begin
(let _158_1383 = (FStar_All.pipe_right p pat_to_string)
in (let _158_1382 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _158_1380 = (term_to_string e)
in (FStar_Util.format1 "when %s" _158_1380))
end)
in (let _158_1381 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _158_1383 _158_1382 _158_1381))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _158_1385 _158_1384)))
end
| Ascribed (t1, t2) -> begin
(let _158_1387 = (FStar_All.pipe_right t1 term_to_string)
in (let _158_1386 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _158_1387 _158_1386)))
end
| Record (Some (e), fields) -> begin
(let _158_1391 = (FStar_All.pipe_right e term_to_string)
in (let _158_1390 = (to_string_l " " (fun _61_572 -> (match (_61_572) with
| (l, e) -> begin
(let _158_1389 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _158_1389))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _158_1391 _158_1390)))
end
| Record (None, fields) -> begin
(let _158_1394 = (to_string_l " " (fun _61_579 -> (match (_61_579) with
| (l, e) -> begin
(let _158_1393 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _158_1393))
end)) fields)
in (FStar_Util.format1 "{%s}" _158_1394))
end
| Project (e, l) -> begin
(let _158_1395 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _158_1395 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd)::tl, t) -> begin
(term_to_string (mk_term (Product ((((b)::[]), ((mk_term (Product ((((hd)::tl), (t)))) x.range x.level))))) x.range x.level))
end
| Product ((b)::[], t) when (x.level = Type) -> begin
(let _158_1397 = (FStar_All.pipe_right b binder_to_string)
in (let _158_1396 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _158_1397 _158_1396)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(let _158_1399 = (FStar_All.pipe_right b binder_to_string)
in (let _158_1398 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _158_1399 _158_1398)))
end
| Sum (binders, t) -> begin
(let _158_1402 = (let _158_1400 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _158_1400 (FStar_String.concat " * ")))
in (let _158_1401 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _158_1402 _158_1401)))
end
| QForall (bs, pats, t) -> begin
(let _158_1405 = (to_string_l " " binder_to_string bs)
in (let _158_1404 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _158_1403 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _158_1405 _158_1404 _158_1403))))
end
| QExists (bs, pats, t) -> begin
(let _158_1408 = (to_string_l " " binder_to_string bs)
in (let _158_1407 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _158_1406 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _158_1408 _158_1407 _158_1406))))
end
| Refine (b, t) -> begin
(let _158_1410 = (FStar_All.pipe_right b binder_to_string)
in (let _158_1409 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _158_1410 _158_1409)))
end
| NamedTyp (x, t) -> begin
(let _158_1411 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _158_1411))
end
| Paren (t) -> begin
(let _158_1412 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _158_1412))
end
| Product (bs, t) -> begin
(let _158_1415 = (let _158_1413 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _158_1413 (FStar_String.concat ",")))
in (let _158_1414 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _158_1415 _158_1414)))
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
(let _158_1417 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _158_1417))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (let _158_1418 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _158_1418 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _61_3 -> (match (_61_3) with
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _61_655 -> begin
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
(let _158_1422 = (FStar_All.pipe_right p pat_to_string)
in (let _158_1421 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _158_1422 _158_1421)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _158_1423 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _158_1423 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _158_1424 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _158_1424))
end
| PatTuple (l, false) -> begin
(let _158_1425 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _158_1425))
end
| PatTuple (l, true) -> begin
(let _158_1426 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _158_1426))
end
| PatRecord (l) -> begin
(let _158_1429 = (to_string_l "; " (fun _61_686 -> (match (_61_686) with
| (f, e) -> begin
(let _158_1428 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _158_1428))
end)) l)
in (FStar_Util.format1 "{%s}" _158_1429))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatOp (op) -> begin
(FStar_Util.format1 "(%s)" op)
end
| PatAscribed (p, t) -> begin
(let _158_1431 = (FStar_All.pipe_right p pat_to_string)
in (let _158_1430 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _158_1431 _158_1430)))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, _61_700) -> begin
(let _158_1434 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_158_1434)::[])
end
| PatApp (p, _61_705) -> begin
(head_id_of_pat p)
end
| PatAscribed (p, _61_710) -> begin
(head_id_of_pat p)
end
| _61_714 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _61_719 -> (match (_61_719) with
| (p, _61_718) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun _61_4 -> (match (_61_4) with
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
| KindAbbrev (i, _61_763, _61_765) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| TopLevelLet (_61_769, _61_771, pats) -> begin
(let _158_1444 = (let _158_1443 = (let _158_1442 = (lids_of_let pats)
in (FStar_All.pipe_right _158_1442 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _158_1443 (FStar_String.concat ", ")))
in (Prims.strcat "let " _158_1444))
end
| Main (_61_777) -> begin
"main ..."
end
| Assume (_61_780, i, _61_783) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (_61_787, tys) -> begin
(let _158_1447 = (let _158_1446 = (FStar_All.pipe_right tys (FStar_List.map (fun _61_794 -> (match (_61_794) with
| (x, _61_793) -> begin
(id_of_tycon x)
end))))
in (FStar_All.pipe_right _158_1446 (FStar_String.concat ", ")))
in (Prims.strcat "type " _158_1447))
end
| Val (_61_796, i, _61_799) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, _61_804) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (NewEffect (_, DefineEffect (i, _, _, _, _))) | (NewEffect (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| (NewEffectForFree (_, DefineEffect (i, _, _, _, _))) | (NewEffectForFree (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect_for_free " i.FStar_Ident.idText)
end
| SubEffect (_61_858) -> begin
"sub_effect"
end
| Pragma (_61_861) -> begin
"pragma"
end
| Fsdoc (_61_864) -> begin
"fsdoc"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| (Module (_, decls)) | (Interface (_, decls, _)) -> begin
(let _158_1450 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _158_1450 (FStar_String.concat "\n")))
end))


let error = (fun msg tm r -> (

let tm = (FStar_All.pipe_right tm term_to_string)
in (

let tm = if ((FStar_String.length tm) >= (Prims.parse_int "80")) then begin
(let _158_1454 = (FStar_Util.substring tm (Prims.parse_int "0") (Prims.parse_int "77"))
in (Prims.strcat _158_1454 "..."))
end else begin
tm
end
in if (FStar_Options.universes ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat msg (Prims.strcat "\n" tm))), (r)))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat msg (Prims.strcat "\n" tm))), (r)))))
end)))




