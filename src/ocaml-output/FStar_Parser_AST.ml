
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
| Const (_51_14) -> begin
_51_14
end))


let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_51_17) -> begin
_51_17
end))


let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_51_20) -> begin
_51_20
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_51_23) -> begin
_51_23
end))


let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_51_26) -> begin
_51_26
end))


let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_51_29) -> begin
_51_29
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_51_32) -> begin
_51_32
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_51_35) -> begin
_51_35
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_51_38) -> begin
_51_38
end))


let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_51_41) -> begin
_51_41
end))


let ___If____0 = (fun projectee -> (match (projectee) with
| If (_51_44) -> begin
_51_44
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_51_47) -> begin
_51_47
end))


let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_51_50) -> begin
_51_50
end))


let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_51_53) -> begin
_51_53
end))


let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_51_56) -> begin
_51_56
end))


let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_51_59) -> begin
_51_59
end))


let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_51_62) -> begin
_51_62
end))


let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_51_65) -> begin
_51_65
end))


let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_51_68) -> begin
_51_68
end))


let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_51_71) -> begin
_51_71
end))


let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_51_74) -> begin
_51_74
end))


let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_51_77) -> begin
_51_77
end))


let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_51_80) -> begin
_51_80
end))


let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_51_83) -> begin
_51_83
end))


let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_51_86) -> begin
_51_86
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_51_89) -> begin
_51_89
end))


let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_51_93) -> begin
_51_93
end))


let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_51_96) -> begin
_51_96
end))


let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_51_99) -> begin
_51_99
end))


let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_51_102) -> begin
_51_102
end))


let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_51_105) -> begin
_51_105
end))


let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_51_109) -> begin
_51_109
end))


let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_51_112) -> begin
_51_112
end))


let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_51_115) -> begin
_51_115
end))


let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_51_118) -> begin
_51_118
end))


let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_51_121) -> begin
_51_121
end))


let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_51_124) -> begin
_51_124
end))


let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_51_127) -> begin
_51_127
end))


let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_51_130) -> begin
_51_130
end))


let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_51_133) -> begin
_51_133
end))


let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_51_136) -> begin
_51_136
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
| TyconAbstract (_51_140) -> begin
_51_140
end))


let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_51_143) -> begin
_51_143
end))


let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_51_146) -> begin
_51_146
end))


let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_51_149) -> begin
_51_149
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
| SetOptions (_51_156) -> begin
_51_156
end))


let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_51_159) -> begin
_51_159
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
| TopLevelModule (_51_164) -> begin
_51_164
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_51_167) -> begin
_51_167
end))


let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_51_170) -> begin
_51_170
end))


let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_51_173) -> begin
_51_173
end))


let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_51_176) -> begin
_51_176
end))


let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_51_179) -> begin
_51_179
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_51_182) -> begin
_51_182
end))


let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_51_185) -> begin
_51_185
end))


let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_51_188) -> begin
_51_188
end))


let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_51_191) -> begin
_51_191
end))


let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_51_194) -> begin
_51_194
end))


let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_51_197) -> begin
_51_197
end))


let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_51_200) -> begin
_51_200
end))


let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_51_204) -> begin
_51_204
end))


let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_51_207) -> begin
_51_207
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
| Module (_51_210) -> begin
_51_210
end))


let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_51_213) -> begin
_51_213
end))


type file =
modul Prims.list


type inputFragment =
(file, decl Prims.list) FStar_Util.either


let check_id : FStar_Ident.ident  ->  Prims.unit = (fun id -> if (FStar_ST.read FStar_Options.universes) then begin
(

let first_char = (FStar_String.substring id.FStar_Ident.idText 0 1)
in if ((FStar_String.lowercase first_char) = first_char) then begin
()
end else begin
(let _140_972 = (let _140_971 = (let _140_970 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in (_140_970, id.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_140_971))
in (Prims.raise _140_972))
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
| _51_234 -> begin
Abs ((ps, body))
end))


let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = if (FStar_ST.read FStar_Options.universes) then begin
(

let i = (FStar_Syntax_Syntax.next_id ())
in (FStar_Ident.gen r1))
end else begin
(FStar_Absyn_Util.genident (Some (r1)))
end
in (let _140_1012 = (let _140_1011 = (let _140_1010 = (let _140_1009 = (let _140_1008 = (let _140_1007 = (let _140_1006 = (let _140_1005 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_140_1005))
in (mk_term _140_1006 r1 Expr))
in (_140_1007, branches))
in Match (_140_1008))
in (mk_term _140_1009 r2 Expr))
in (((mk_pattern (PatVar ((x, None))) r1))::[], _140_1010))
in Abs (_140_1011))
in (mk_term _140_1012 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_51_243), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _51_251 -> begin
None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _140_1021 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _140_1021 r)))


let to_string_l = (fun sep f l -> (let _140_1028 = (FStar_List.map f l)
in (FStar_String.concat sep _140_1028)))


let imp_to_string : imp  ->  Prims.string = (fun _51_1 -> (match (_51_1) with
| Hash -> begin
"#"
end
| _51_260 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _51_265) -> begin
(let _140_1036 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _140_1036))
end
| Ensures (t, _51_270) -> begin
(let _140_1037 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _140_1037))
end
| Labeled (t, l, _51_276) -> begin
(let _140_1038 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _140_1038))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _140_1041 = (let _140_1040 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _140_1040))
in (FStar_Util.format2 "%s(%s)" s _140_1041))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _140_1044 = (to_string_l " " (fun _51_297 -> (match (_51_297) with
| (a, imp) -> begin
(let _140_1043 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _140_1043))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _140_1044))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _140_1046 = (to_string_l " " pat_to_string pats)
in (let _140_1045 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _140_1046 _140_1045)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _140_1048 = (to_string_l " " pat_to_string pats)
in (let _140_1047 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _140_1048 _140_1047)))
end
| App (t1, t2, imp) -> begin
(let _140_1050 = (FStar_All.pipe_right t1 term_to_string)
in (let _140_1049 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _140_1050 (imp_to_string imp) _140_1049)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _140_1053 = (FStar_All.pipe_right pat pat_to_string)
in (let _140_1052 = (FStar_All.pipe_right tm term_to_string)
in (let _140_1051 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _140_1053 _140_1052 _140_1051))))
end
| Let (_51_320, lbs, body) -> begin
(let _140_1058 = (to_string_l " and " (fun _51_327 -> (match (_51_327) with
| (p, b) -> begin
(let _140_1056 = (FStar_All.pipe_right p pat_to_string)
in (let _140_1055 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _140_1056 _140_1055)))
end)) lbs)
in (let _140_1057 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _140_1058 _140_1057)))
end
| Seq (t1, t2) -> begin
(let _140_1060 = (FStar_All.pipe_right t1 term_to_string)
in (let _140_1059 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _140_1060 _140_1059)))
end
| If (t1, t2, t3) -> begin
(let _140_1063 = (FStar_All.pipe_right t1 term_to_string)
in (let _140_1062 = (FStar_All.pipe_right t2 term_to_string)
in (let _140_1061 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _140_1063 _140_1062 _140_1061))))
end
| Match (t, branches) -> begin
(let _140_1070 = (FStar_All.pipe_right t term_to_string)
in (let _140_1069 = (to_string_l " | " (fun _51_344 -> (match (_51_344) with
| (p, w, e) -> begin
(let _140_1068 = (FStar_All.pipe_right p pat_to_string)
in (let _140_1067 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _140_1065 = (term_to_string e)
in (FStar_Util.format1 "when %s" _140_1065))
end)
in (let _140_1066 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _140_1068 _140_1067 _140_1066))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _140_1070 _140_1069)))
end
| Ascribed (t1, t2) -> begin
(let _140_1072 = (FStar_All.pipe_right t1 term_to_string)
in (let _140_1071 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _140_1072 _140_1071)))
end
| Record (Some (e), fields) -> begin
(let _140_1076 = (FStar_All.pipe_right e term_to_string)
in (let _140_1075 = (to_string_l " " (fun _51_359 -> (match (_51_359) with
| (l, e) -> begin
(let _140_1074 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _140_1074))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _140_1076 _140_1075)))
end
| Record (None, fields) -> begin
(let _140_1079 = (to_string_l " " (fun _51_366 -> (match (_51_366) with
| (l, e) -> begin
(let _140_1078 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _140_1078))
end)) fields)
in (FStar_Util.format1 "{%s}" _140_1079))
end
| Project (e, l) -> begin
(let _140_1080 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _140_1080 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _140_1082 = (FStar_All.pipe_right b binder_to_string)
in (let _140_1081 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _140_1082 _140_1081)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _140_1084 = (FStar_All.pipe_right b binder_to_string)
in (let _140_1083 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _140_1084 _140_1083)))
end
| Sum (binders, t) -> begin
(let _140_1087 = (let _140_1085 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _140_1085 (FStar_String.concat " * ")))
in (let _140_1086 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _140_1087 _140_1086)))
end
| QForall (bs, pats, t) -> begin
(let _140_1090 = (to_string_l " " binder_to_string bs)
in (let _140_1089 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _140_1088 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _140_1090 _140_1089 _140_1088))))
end
| QExists (bs, pats, t) -> begin
(let _140_1093 = (to_string_l " " binder_to_string bs)
in (let _140_1092 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _140_1091 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _140_1093 _140_1092 _140_1091))))
end
| Refine (b, t) -> begin
(let _140_1095 = (FStar_All.pipe_right b binder_to_string)
in (let _140_1094 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _140_1095 _140_1094)))
end
| NamedTyp (x, t) -> begin
(let _140_1096 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _140_1096))
end
| Paren (t) -> begin
(let _140_1097 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _140_1097))
end
| Product (bs, t) -> begin
(let _140_1100 = (let _140_1098 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _140_1098 (FStar_String.concat ",")))
in (let _140_1099 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _140_1100 _140_1099)))
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
(let _140_1102 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _140_1102))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (let _140_1103 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _140_1103 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _51_2 -> (match (_51_2) with
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _51_442 -> begin
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
(let _140_1107 = (FStar_All.pipe_right p pat_to_string)
in (let _140_1106 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _140_1107 _140_1106)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _140_1108 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _140_1108 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _140_1109 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _140_1109))
end
| PatTuple (l, false) -> begin
(let _140_1110 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _140_1110))
end
| PatTuple (l, true) -> begin
(let _140_1111 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _140_1111))
end
| PatRecord (l) -> begin
(let _140_1114 = (to_string_l "; " (fun _51_473 -> (match (_51_473) with
| (f, e) -> begin
(let _140_1113 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _140_1113))
end)) l)
in (FStar_Util.format1 "{%s}" _140_1114))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _140_1116 = (FStar_All.pipe_right p pat_to_string)
in (let _140_1115 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _140_1116 _140_1115)))
end))


let error = (fun msg tm r -> (

let tm = (FStar_All.pipe_right tm term_to_string)
in (

let tm = if ((FStar_String.length tm) >= 80) then begin
(let _140_1120 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _140_1120 "..."))
end else begin
tm
end
in if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end)))


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
| _51_509 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _51_513 -> begin
(FStar_List.fold_left (fun t _51_517 -> (match (_51_517) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let empty = (let _140_1164 = (let _140_1163 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_140_1163))
in (mk_term _140_1164 r Expr))
in (

let ref_constr = (let _140_1166 = (let _140_1165 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_140_1165))
in (mk_term _140_1166 r Expr))
in (

let singleton = (let _140_1168 = (let _140_1167 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_140_1167))
in (mk_term _140_1168 r Expr))
in (

let union = (let _140_1170 = (let _140_1169 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_140_1169))
in (mk_term _140_1170 r Expr))
in (FStar_List.fold_right (fun e tl -> (

let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (

let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))


let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _51_533 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _140_1182 = (let _140_1181 = (let _140_1180 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _140_1180))
in Construct (_140_1181))
in (mk_term _140_1182 r Un))
end
| _51_538 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (

let admit = (

let admit_name = (let _140_1188 = (let _140_1187 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_140_1187))
in (mk_term _140_1188 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (

let magic = (

let magic_name = (let _140_1190 = (let _140_1189 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_140_1189))
in (mk_term _140_1190 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (

let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))


let mkWildAdmitMagic = (fun r -> (let _140_1192 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _140_1192)))


let focusBranches = (fun branches r -> (

let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(

let _51_552 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (

let focussed = (let _140_1195 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _140_1195 (FStar_List.map Prims.snd)))
in (let _140_1197 = (let _140_1196 = (mkWildAdmitMagic r)
in (_140_1196)::[])
in (FStar_List.append focussed _140_1197))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))


let focusLetBindings = (fun lbs r -> (

let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(

let _51_558 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _51_562 -> (match (_51_562) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _140_1201 = (mkAdmitMagic r)
in ((Prims.fst lb), _140_1201))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _140_1209 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _140_1209 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_ST.read FStar_Options.universes) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
in (let _140_1215 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _140_1215 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons = if (FStar_ST.read FStar_Options.universes) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
in (let _140_1221 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _140_1221 r))))


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
| Refine ({b = Annotated (x, t); brange = _51_594; blevel = _51_592; aqual = _51_590}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _51_606 -> begin
None
end))




