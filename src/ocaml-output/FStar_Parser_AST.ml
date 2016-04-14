
open Prims
# 34 "FStar.Parser.AST.fst"
type level =
| Un
| Expr
| Type
| Kind
| Formula

# 34 "FStar.Parser.AST.fst"
let is_Un = (fun _discr_ -> (match (_discr_) with
| Un (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Parser.AST.fst"
let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Parser.AST.fst"
let is_Type = (fun _discr_ -> (match (_discr_) with
| Type (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Parser.AST.fst"
let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Parser.AST.fst"
let is_Formula = (fun _discr_ -> (match (_discr_) with
| Formula (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Parser.AST.fst"
type imp =
| FsTypApp
| Hash
| Nothing

# 36 "FStar.Parser.AST.fst"
let is_FsTypApp = (fun _discr_ -> (match (_discr_) with
| FsTypApp (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.Parser.AST.fst"
let is_Hash = (fun _discr_ -> (match (_discr_) with
| Hash (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "FStar.Parser.AST.fst"
let is_Nothing = (fun _discr_ -> (match (_discr_) with
| Nothing (_) -> begin
true
end
| _ -> begin
false
end))

# 39 "FStar.Parser.AST.fst"
type arg_qualifier =
| Implicit
| Equality

# 40 "FStar.Parser.AST.fst"
let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "FStar.Parser.AST.fst"
let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Parser.AST.fst"
type aqual =
arg_qualifier Prims.option

# 44 "FStar.Parser.AST.fst"
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

# 45 "FStar.Parser.AST.fst"
let is_Wild = (fun _discr_ -> (match (_discr_) with
| Wild (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Parser.AST.fst"
let is_Const = (fun _discr_ -> (match (_discr_) with
| Const (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Parser.AST.fst"
let is_Op = (fun _discr_ -> (match (_discr_) with
| Op (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "FStar.Parser.AST.fst"
let is_Tvar = (fun _discr_ -> (match (_discr_) with
| Tvar (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.Parser.AST.fst"
let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Parser.AST.fst"
let is_Name = (fun _discr_ -> (match (_discr_) with
| Name (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.Parser.AST.fst"
let is_Construct = (fun _discr_ -> (match (_discr_) with
| Construct (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Parser.AST.fst"
let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.Parser.AST.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.Parser.AST.fst"
let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.Parser.AST.fst"
let is_Seq = (fun _discr_ -> (match (_discr_) with
| Seq (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.Parser.AST.fst"
let is_If = (fun _discr_ -> (match (_discr_) with
| If (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.Parser.AST.fst"
let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.Parser.AST.fst"
let is_TryWith = (fun _discr_ -> (match (_discr_) with
| TryWith (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.Parser.AST.fst"
let is_Ascribed = (fun _discr_ -> (match (_discr_) with
| Ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.Parser.AST.fst"
let is_Record = (fun _discr_ -> (match (_discr_) with
| Record (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.Parser.AST.fst"
let is_Project = (fun _discr_ -> (match (_discr_) with
| Project (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.Parser.AST.fst"
let is_Product = (fun _discr_ -> (match (_discr_) with
| Product (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.Parser.AST.fst"
let is_Sum = (fun _discr_ -> (match (_discr_) with
| Sum (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Parser.AST.fst"
let is_QForall = (fun _discr_ -> (match (_discr_) with
| QForall (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.Parser.AST.fst"
let is_QExists = (fun _discr_ -> (match (_discr_) with
| QExists (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.Parser.AST.fst"
let is_Refine = (fun _discr_ -> (match (_discr_) with
| Refine (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.Parser.AST.fst"
let is_NamedTyp = (fun _discr_ -> (match (_discr_) with
| NamedTyp (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.Parser.AST.fst"
let is_Paren = (fun _discr_ -> (match (_discr_) with
| Paren (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.Parser.AST.fst"
let is_Requires = (fun _discr_ -> (match (_discr_) with
| Requires (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "FStar.Parser.AST.fst"
let is_Ensures = (fun _discr_ -> (match (_discr_) with
| Ensures (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.Parser.AST.fst"
let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Parser.AST.fst"
let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 76 "FStar.Parser.AST.fst"
let is_Variable = (fun _discr_ -> (match (_discr_) with
| Variable (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "FStar.Parser.AST.fst"
let is_TVariable = (fun _discr_ -> (match (_discr_) with
| TVariable (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "FStar.Parser.AST.fst"
let is_Annotated = (fun _discr_ -> (match (_discr_) with
| Annotated (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.Parser.AST.fst"
let is_TAnnotated = (fun _discr_ -> (match (_discr_) with
| TAnnotated (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.Parser.AST.fst"
let is_NoName = (fun _discr_ -> (match (_discr_) with
| NoName (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.Parser.AST.fst"
let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))

# 84 "FStar.Parser.AST.fst"
let is_PatWild = (fun _discr_ -> (match (_discr_) with
| PatWild (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.Parser.AST.fst"
let is_PatConst = (fun _discr_ -> (match (_discr_) with
| PatConst (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.Parser.AST.fst"
let is_PatApp = (fun _discr_ -> (match (_discr_) with
| PatApp (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Parser.AST.fst"
let is_PatVar = (fun _discr_ -> (match (_discr_) with
| PatVar (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.Parser.AST.fst"
let is_PatName = (fun _discr_ -> (match (_discr_) with
| PatName (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.Parser.AST.fst"
let is_PatTvar = (fun _discr_ -> (match (_discr_) with
| PatTvar (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.Parser.AST.fst"
let is_PatList = (fun _discr_ -> (match (_discr_) with
| PatList (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.Parser.AST.fst"
let is_PatTuple = (fun _discr_ -> (match (_discr_) with
| PatTuple (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "FStar.Parser.AST.fst"
let is_PatRecord = (fun _discr_ -> (match (_discr_) with
| PatRecord (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "FStar.Parser.AST.fst"
let is_PatAscribed = (fun _discr_ -> (match (_discr_) with
| PatAscribed (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "FStar.Parser.AST.fst"
let is_PatOr = (fun _discr_ -> (match (_discr_) with
| PatOr (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "FStar.Parser.AST.fst"
let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 46 "FStar.Parser.AST.fst"
let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_58_15) -> begin
_58_15
end))

# 47 "FStar.Parser.AST.fst"
let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_58_18) -> begin
_58_18
end))

# 48 "FStar.Parser.AST.fst"
let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_58_21) -> begin
_58_21
end))

# 49 "FStar.Parser.AST.fst"
let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_58_24) -> begin
_58_24
end))

# 50 "FStar.Parser.AST.fst"
let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_58_27) -> begin
_58_27
end))

# 51 "FStar.Parser.AST.fst"
let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_58_30) -> begin
_58_30
end))

# 52 "FStar.Parser.AST.fst"
let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_58_33) -> begin
_58_33
end))

# 53 "FStar.Parser.AST.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_58_36) -> begin
_58_36
end))

# 54 "FStar.Parser.AST.fst"
let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_58_39) -> begin
_58_39
end))

# 55 "FStar.Parser.AST.fst"
let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_58_42) -> begin
_58_42
end))

# 56 "FStar.Parser.AST.fst"
let ___If____0 = (fun projectee -> (match (projectee) with
| If (_58_45) -> begin
_58_45
end))

# 57 "FStar.Parser.AST.fst"
let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_58_48) -> begin
_58_48
end))

# 58 "FStar.Parser.AST.fst"
let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_58_51) -> begin
_58_51
end))

# 59 "FStar.Parser.AST.fst"
let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_58_54) -> begin
_58_54
end))

# 60 "FStar.Parser.AST.fst"
let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_58_57) -> begin
_58_57
end))

# 61 "FStar.Parser.AST.fst"
let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_58_60) -> begin
_58_60
end))

# 62 "FStar.Parser.AST.fst"
let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_58_63) -> begin
_58_63
end))

# 63 "FStar.Parser.AST.fst"
let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_58_66) -> begin
_58_66
end))

# 64 "FStar.Parser.AST.fst"
let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_58_69) -> begin
_58_69
end))

# 65 "FStar.Parser.AST.fst"
let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_58_72) -> begin
_58_72
end))

# 66 "FStar.Parser.AST.fst"
let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_58_75) -> begin
_58_75
end))

# 67 "FStar.Parser.AST.fst"
let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_58_78) -> begin
_58_78
end))

# 68 "FStar.Parser.AST.fst"
let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_58_81) -> begin
_58_81
end))

# 69 "FStar.Parser.AST.fst"
let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_58_84) -> begin
_58_84
end))

# 70 "FStar.Parser.AST.fst"
let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_58_87) -> begin
_58_87
end))

# 71 "FStar.Parser.AST.fst"
let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_58_90) -> begin
_58_90
end))

# 76 "FStar.Parser.AST.fst"
let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_58_94) -> begin
_58_94
end))

# 77 "FStar.Parser.AST.fst"
let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_58_97) -> begin
_58_97
end))

# 78 "FStar.Parser.AST.fst"
let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_58_100) -> begin
_58_100
end))

# 79 "FStar.Parser.AST.fst"
let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_58_103) -> begin
_58_103
end))

# 80 "FStar.Parser.AST.fst"
let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_58_106) -> begin
_58_106
end))

# 85 "FStar.Parser.AST.fst"
let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_58_110) -> begin
_58_110
end))

# 86 "FStar.Parser.AST.fst"
let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_58_113) -> begin
_58_113
end))

# 87 "FStar.Parser.AST.fst"
let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_58_116) -> begin
_58_116
end))

# 88 "FStar.Parser.AST.fst"
let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_58_119) -> begin
_58_119
end))

# 89 "FStar.Parser.AST.fst"
let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_58_122) -> begin
_58_122
end))

# 90 "FStar.Parser.AST.fst"
let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_58_125) -> begin
_58_125
end))

# 91 "FStar.Parser.AST.fst"
let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_58_128) -> begin
_58_128
end))

# 92 "FStar.Parser.AST.fst"
let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_58_131) -> begin
_58_131
end))

# 93 "FStar.Parser.AST.fst"
let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_58_134) -> begin
_58_134
end))

# 94 "FStar.Parser.AST.fst"
let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_58_137) -> begin
_58_137
end))

# 99 "FStar.Parser.AST.fst"
type knd =
term

# 100 "FStar.Parser.AST.fst"
type typ =
term

# 101 "FStar.Parser.AST.fst"
type expr =
term

# 103 "FStar.Parser.AST.fst"
type tycon =
| TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd Prims.option)
| TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd Prims.option * term)
| TyconRecord of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term) Prims.list)
| TyconVariant of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term Prims.option * Prims.bool) Prims.list)

# 104 "FStar.Parser.AST.fst"
let is_TyconAbstract = (fun _discr_ -> (match (_discr_) with
| TyconAbstract (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.Parser.AST.fst"
let is_TyconAbbrev = (fun _discr_ -> (match (_discr_) with
| TyconAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.Parser.AST.fst"
let is_TyconRecord = (fun _discr_ -> (match (_discr_) with
| TyconRecord (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "FStar.Parser.AST.fst"
let is_TyconVariant = (fun _discr_ -> (match (_discr_) with
| TyconVariant (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.Parser.AST.fst"
let ___TyconAbstract____0 = (fun projectee -> (match (projectee) with
| TyconAbstract (_58_141) -> begin
_58_141
end))

# 105 "FStar.Parser.AST.fst"
let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_58_144) -> begin
_58_144
end))

# 106 "FStar.Parser.AST.fst"
let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_58_147) -> begin
_58_147
end))

# 107 "FStar.Parser.AST.fst"
let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_58_150) -> begin
_58_150
end))

# 109 "FStar.Parser.AST.fst"
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

# 110 "FStar.Parser.AST.fst"
let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "FStar.Parser.AST.fst"
let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "FStar.Parser.AST.fst"
let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 113 "FStar.Parser.AST.fst"
let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 114 "FStar.Parser.AST.fst"
let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 115 "FStar.Parser.AST.fst"
let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 116 "FStar.Parser.AST.fst"
let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 117 "FStar.Parser.AST.fst"
let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "FStar.Parser.AST.fst"
let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "FStar.Parser.AST.fst"
let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "FStar.Parser.AST.fst"
let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "FStar.Parser.AST.fst"
let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 126 "FStar.Parser.AST.fst"
type qualifiers =
qualifier Prims.list

# 128 "FStar.Parser.AST.fst"
type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : term}

# 128 "FStar.Parser.AST.fst"
let is_Mklift : lift  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklift"))))

# 134 "FStar.Parser.AST.fst"
type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string Prims.option

# 135 "FStar.Parser.AST.fst"
let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.Parser.AST.fst"
let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "FStar.Parser.AST.fst"
let ___SetOptions____0 = (fun projectee -> (match (projectee) with
| SetOptions (_58_157) -> begin
_58_157
end))

# 136 "FStar.Parser.AST.fst"
let ___ResetOptions____0 = (fun projectee -> (match (projectee) with
| ResetOptions (_58_160) -> begin
_58_160
end))

# 138 "FStar.Parser.AST.fst"
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

# 139 "FStar.Parser.AST.fst"
let is_TopLevelModule = (fun _discr_ -> (match (_discr_) with
| TopLevelModule (_) -> begin
true
end
| _ -> begin
false
end))

# 140 "FStar.Parser.AST.fst"
let is_Open = (fun _discr_ -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "FStar.Parser.AST.fst"
let is_ModuleAbbrev = (fun _discr_ -> (match (_discr_) with
| ModuleAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "FStar.Parser.AST.fst"
let is_KindAbbrev = (fun _discr_ -> (match (_discr_) with
| KindAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "FStar.Parser.AST.fst"
let is_ToplevelLet = (fun _discr_ -> (match (_discr_) with
| ToplevelLet (_) -> begin
true
end
| _ -> begin
false
end))

# 144 "FStar.Parser.AST.fst"
let is_Main = (fun _discr_ -> (match (_discr_) with
| Main (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "FStar.Parser.AST.fst"
let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "FStar.Parser.AST.fst"
let is_Tycon = (fun _discr_ -> (match (_discr_) with
| Tycon (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "FStar.Parser.AST.fst"
let is_Val = (fun _discr_ -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))

# 148 "FStar.Parser.AST.fst"
let is_Exception = (fun _discr_ -> (match (_discr_) with
| Exception (_) -> begin
true
end
| _ -> begin
false
end))

# 149 "FStar.Parser.AST.fst"
let is_NewEffect = (fun _discr_ -> (match (_discr_) with
| NewEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 150 "FStar.Parser.AST.fst"
let is_SubEffect = (fun _discr_ -> (match (_discr_) with
| SubEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 151 "FStar.Parser.AST.fst"
let is_Pragma = (fun _discr_ -> (match (_discr_) with
| Pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 152 "FStar.Parser.AST.fst"
let is_Mkdecl : decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdecl"))))

# 154 "FStar.Parser.AST.fst"
let is_DefineEffect = (fun _discr_ -> (match (_discr_) with
| DefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 155 "FStar.Parser.AST.fst"
let is_RedefineEffect = (fun _discr_ -> (match (_discr_) with
| RedefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 139 "FStar.Parser.AST.fst"
let ___TopLevelModule____0 = (fun projectee -> (match (projectee) with
| TopLevelModule (_58_165) -> begin
_58_165
end))

# 140 "FStar.Parser.AST.fst"
let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_58_168) -> begin
_58_168
end))

# 141 "FStar.Parser.AST.fst"
let ___ModuleAbbrev____0 = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_58_171) -> begin
_58_171
end))

# 142 "FStar.Parser.AST.fst"
let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_58_174) -> begin
_58_174
end))

# 143 "FStar.Parser.AST.fst"
let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_58_177) -> begin
_58_177
end))

# 144 "FStar.Parser.AST.fst"
let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_58_180) -> begin
_58_180
end))

# 145 "FStar.Parser.AST.fst"
let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_58_183) -> begin
_58_183
end))

# 146 "FStar.Parser.AST.fst"
let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_58_186) -> begin
_58_186
end))

# 147 "FStar.Parser.AST.fst"
let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_58_189) -> begin
_58_189
end))

# 148 "FStar.Parser.AST.fst"
let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_58_192) -> begin
_58_192
end))

# 149 "FStar.Parser.AST.fst"
let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_58_195) -> begin
_58_195
end))

# 150 "FStar.Parser.AST.fst"
let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_58_198) -> begin
_58_198
end))

# 151 "FStar.Parser.AST.fst"
let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_58_201) -> begin
_58_201
end))

# 154 "FStar.Parser.AST.fst"
let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_58_205) -> begin
_58_205
end))

# 155 "FStar.Parser.AST.fst"
let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_58_208) -> begin
_58_208
end))

# 157 "FStar.Parser.AST.fst"
type modul =
| Module of (FStar_Ident.lid * decl Prims.list)
| Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool)

# 158 "FStar.Parser.AST.fst"
let is_Module = (fun _discr_ -> (match (_discr_) with
| Module (_) -> begin
true
end
| _ -> begin
false
end))

# 159 "FStar.Parser.AST.fst"
let is_Interface = (fun _discr_ -> (match (_discr_) with
| Interface (_) -> begin
true
end
| _ -> begin
false
end))

# 158 "FStar.Parser.AST.fst"
let ___Module____0 = (fun projectee -> (match (projectee) with
| Module (_58_211) -> begin
_58_211
end))

# 159 "FStar.Parser.AST.fst"
let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_58_214) -> begin
_58_214
end))

# 160 "FStar.Parser.AST.fst"
type file =
modul Prims.list

# 161 "FStar.Parser.AST.fst"
type inputFragment =
(file, decl Prims.list) FStar_Util.either

# 164 "FStar.Parser.AST.fst"
let check_id : FStar_Ident.ident  ->  Prims.unit = (fun id -> if (FStar_ST.read FStar_Options.universes) then begin
(
# 166 "FStar.Parser.AST.fst"
let first_char = (FStar_String.substring id.FStar_Ident.idText 0 1)
in if ((FStar_String.lowercase first_char) = first_char) then begin
()
end else begin
(let _147_972 = (let _147_971 = (let _147_970 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in (_147_970, id.FStar_Ident.idRange))
in FStar_Syntax_Syntax.Error (_147_971))
in (Prims.raise _147_972))
end)
end else begin
()
end)

# 172 "FStar.Parser.AST.fst"
let mk_decl : decl'  ->  FStar_Range.range  ->  decl = (fun d r -> {d = d; drange = r})

# 173 "FStar.Parser.AST.fst"
let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

# 174 "FStar.Parser.AST.fst"
let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})

# 175 "FStar.Parser.AST.fst"
let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})

# 176 "FStar.Parser.AST.fst"
let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((FStar_List.append ps p'), body'))
end
| _58_235 -> begin
Abs ((ps, body))
end))

# 179 "FStar.Parser.AST.fst"
let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (
# 180 "FStar.Parser.AST.fst"
let x = if (FStar_ST.read FStar_Options.universes) then begin
(
# 182 "FStar.Parser.AST.fst"
let i = (FStar_Syntax_Syntax.next_id ())
in (FStar_Ident.gen r1))
end else begin
(FStar_Absyn_Util.genident (Some (r1)))
end
in (let _147_1012 = (let _147_1011 = (let _147_1010 = (let _147_1009 = (let _147_1008 = (let _147_1007 = (let _147_1006 = (let _147_1005 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_147_1005))
in (mk_term _147_1006 r1 Expr))
in (_147_1007, branches))
in Match (_147_1008))
in (mk_term _147_1009 r2 Expr))
in (((mk_pattern (PatVar ((x, None))) r1))::[], _147_1010))
in Abs (_147_1011))
in (mk_term _147_1012 r2 Expr))))

# 188 "FStar.Parser.AST.fst"
let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_58_244), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _58_252 -> begin
None
end))

# 192 "FStar.Parser.AST.fst"
let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _147_1021 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _147_1021 r)))

# 194 "FStar.Parser.AST.fst"
let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd tl -> PatApp (((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

# 195 "FStar.Parser.AST.fst"
let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

# 196 "FStar.Parser.AST.fst"
let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

# 198 "FStar.Parser.AST.fst"
let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (
# 199 "FStar.Parser.AST.fst"
let nil = (mk_term (Construct ((FStar_Absyn_Const.nil_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

# 202 "FStar.Parser.AST.fst"
let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (
# 203 "FStar.Parser.AST.fst"
let nil = (mk_term (Construct ((FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

# 206 "FStar.Parser.AST.fst"
let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _58_279 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _58_283 -> begin
(FStar_List.fold_left (fun t _58_287 -> (match (_58_287) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

# 212 "FStar.Parser.AST.fst"
let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (
# 213 "FStar.Parser.AST.fst"
let empty = (let _147_1065 = (let _147_1064 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_147_1064))
in (mk_term _147_1065 r Expr))
in (
# 214 "FStar.Parser.AST.fst"
let ref_constr = (let _147_1067 = (let _147_1066 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_147_1066))
in (mk_term _147_1067 r Expr))
in (
# 215 "FStar.Parser.AST.fst"
let singleton = (let _147_1069 = (let _147_1068 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_147_1068))
in (mk_term _147_1069 r Expr))
in (
# 216 "FStar.Parser.AST.fst"
let union = (let _147_1071 = (let _147_1070 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_147_1070))
in (mk_term _147_1071 r Expr))
in (FStar_List.fold_right (fun e tl -> (
# 218 "FStar.Parser.AST.fst"
let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (
# 219 "FStar.Parser.AST.fst"
let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

# 222 "FStar.Parser.AST.fst"
let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _58_303 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _147_1083 = (let _147_1082 = (let _147_1081 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _147_1081))
in Construct (_147_1082))
in (mk_term _147_1083 r Un))
end
| _58_308 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

# 228 "FStar.Parser.AST.fst"
let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (
# 229 "FStar.Parser.AST.fst"
let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (
# 230 "FStar.Parser.AST.fst"
let admit = (
# 231 "FStar.Parser.AST.fst"
let admit_name = (let _147_1089 = (let _147_1088 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_147_1088))
in (mk_term _147_1089 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (
# 233 "FStar.Parser.AST.fst"
let magic = (
# 234 "FStar.Parser.AST.fst"
let magic_name = (let _147_1091 = (let _147_1090 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_147_1090))
in (mk_term _147_1091 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (
# 236 "FStar.Parser.AST.fst"
let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

# 239 "FStar.Parser.AST.fst"
let mkWildAdmitMagic = (fun r -> (let _147_1093 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _147_1093)))

# 241 "FStar.Parser.AST.fst"
let focusBranches = (fun branches r -> (
# 242 "FStar.Parser.AST.fst"
let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(
# 244 "FStar.Parser.AST.fst"
let _58_322 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (
# 245 "FStar.Parser.AST.fst"
let focussed = (let _147_1096 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _147_1096 (FStar_List.map Prims.snd)))
in (let _147_1098 = (let _147_1097 = (mkWildAdmitMagic r)
in (_147_1097)::[])
in (FStar_List.append focussed _147_1098))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))

# 249 "FStar.Parser.AST.fst"
let focusLetBindings = (fun lbs r -> (
# 250 "FStar.Parser.AST.fst"
let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(
# 252 "FStar.Parser.AST.fst"
let _58_328 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _58_332 -> (match (_58_332) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _147_1102 = (mkAdmitMagic r)
in ((Prims.fst lb), _147_1102))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))

# 258 "FStar.Parser.AST.fst"
let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _147_1110 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _147_1110 r)))

# 261 "FStar.Parser.AST.fst"
let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (
# 262 "FStar.Parser.AST.fst"
let cons = if (FStar_ST.read FStar_Options.universes) then begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
end
in (let _147_1116 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _147_1116 r))))

# 268 "FStar.Parser.AST.fst"
let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (
# 269 "FStar.Parser.AST.fst"
let cons = if (FStar_ST.read FStar_Options.universes) then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end else begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
end
in (let _147_1122 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _147_1122 r))))

# 275 "FStar.Parser.AST.fst"
let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t refopt m implicit -> (
# 276 "FStar.Parser.AST.fst"
let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))

# 281 "FStar.Parser.AST.fst"
let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term Prims.option) Prims.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some ((x, t, None))
end
| Refine ({b = Annotated (x, t); brange = _58_364; blevel = _58_362; aqual = _58_360}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _58_376 -> begin
None
end))

# 291 "FStar.Parser.AST.fst"
let to_string_l = (fun sep f l -> (let _147_1141 = (FStar_List.map f l)
in (FStar_String.concat sep _147_1141)))

# 293 "FStar.Parser.AST.fst"
let imp_to_string : imp  ->  Prims.string = (fun _58_1 -> (match (_58_1) with
| Hash -> begin
"#"
end
| _58_383 -> begin
""
end))

# 296 "FStar.Parser.AST.fst"
let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _58_388) -> begin
(let _147_1149 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _147_1149))
end
| Ensures (t, _58_393) -> begin
(let _147_1150 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _147_1150))
end
| Labeled (t, l, _58_399) -> begin
(let _147_1151 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _147_1151))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _147_1154 = (let _147_1153 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _147_1153))
in (FStar_Util.format2 "%s(%s)" s _147_1154))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _147_1157 = (to_string_l " " (fun _58_420 -> (match (_58_420) with
| (a, imp) -> begin
(let _147_1156 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _147_1156))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _147_1157))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _147_1159 = (to_string_l " " pat_to_string pats)
in (let _147_1158 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _147_1159 _147_1158)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _147_1161 = (to_string_l " " pat_to_string pats)
in (let _147_1160 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _147_1161 _147_1160)))
end
| App (t1, t2, imp) -> begin
(let _147_1163 = (FStar_All.pipe_right t1 term_to_string)
in (let _147_1162 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _147_1163 (imp_to_string imp) _147_1162)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _147_1166 = (FStar_All.pipe_right pat pat_to_string)
in (let _147_1165 = (FStar_All.pipe_right tm term_to_string)
in (let _147_1164 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _147_1166 _147_1165 _147_1164))))
end
| Let (_58_443, lbs, body) -> begin
(let _147_1171 = (to_string_l " and " (fun _58_450 -> (match (_58_450) with
| (p, b) -> begin
(let _147_1169 = (FStar_All.pipe_right p pat_to_string)
in (let _147_1168 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _147_1169 _147_1168)))
end)) lbs)
in (let _147_1170 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _147_1171 _147_1170)))
end
| Seq (t1, t2) -> begin
(let _147_1173 = (FStar_All.pipe_right t1 term_to_string)
in (let _147_1172 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _147_1173 _147_1172)))
end
| If (t1, t2, t3) -> begin
(let _147_1176 = (FStar_All.pipe_right t1 term_to_string)
in (let _147_1175 = (FStar_All.pipe_right t2 term_to_string)
in (let _147_1174 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _147_1176 _147_1175 _147_1174))))
end
| Match (t, branches) -> begin
(let _147_1183 = (FStar_All.pipe_right t term_to_string)
in (let _147_1182 = (to_string_l " | " (fun _58_467 -> (match (_58_467) with
| (p, w, e) -> begin
(let _147_1181 = (FStar_All.pipe_right p pat_to_string)
in (let _147_1180 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _147_1178 = (term_to_string e)
in (FStar_Util.format1 "when %s" _147_1178))
end)
in (let _147_1179 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _147_1181 _147_1180 _147_1179))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _147_1183 _147_1182)))
end
| Ascribed (t1, t2) -> begin
(let _147_1185 = (FStar_All.pipe_right t1 term_to_string)
in (let _147_1184 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _147_1185 _147_1184)))
end
| Record (Some (e), fields) -> begin
(let _147_1189 = (FStar_All.pipe_right e term_to_string)
in (let _147_1188 = (to_string_l " " (fun _58_482 -> (match (_58_482) with
| (l, e) -> begin
(let _147_1187 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _147_1187))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _147_1189 _147_1188)))
end
| Record (None, fields) -> begin
(let _147_1192 = (to_string_l " " (fun _58_489 -> (match (_58_489) with
| (l, e) -> begin
(let _147_1191 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _147_1191))
end)) fields)
in (FStar_Util.format1 "{%s}" _147_1192))
end
| Project (e, l) -> begin
(let _147_1193 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _147_1193 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _147_1195 = (FStar_All.pipe_right b binder_to_string)
in (let _147_1194 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _147_1195 _147_1194)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _147_1197 = (FStar_All.pipe_right b binder_to_string)
in (let _147_1196 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _147_1197 _147_1196)))
end
| Sum (binders, t) -> begin
(let _147_1200 = (let _147_1198 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _147_1198 (FStar_String.concat " * ")))
in (let _147_1199 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _147_1200 _147_1199)))
end
| QForall (bs, pats, t) -> begin
(let _147_1203 = (to_string_l " " binder_to_string bs)
in (let _147_1202 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _147_1201 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _147_1203 _147_1202 _147_1201))))
end
| QExists (bs, pats, t) -> begin
(let _147_1206 = (to_string_l " " binder_to_string bs)
in (let _147_1205 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _147_1204 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _147_1206 _147_1205 _147_1204))))
end
| Refine (b, t) -> begin
(let _147_1208 = (FStar_All.pipe_right b binder_to_string)
in (let _147_1207 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _147_1208 _147_1207)))
end
| NamedTyp (x, t) -> begin
(let _147_1209 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _147_1209))
end
| Paren (t) -> begin
(let _147_1210 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _147_1210))
end
| Product (bs, t) -> begin
(let _147_1213 = (let _147_1211 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _147_1211 (FStar_String.concat ",")))
in (let _147_1212 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _147_1213 _147_1212)))
end
| t -> begin
(FStar_All.failwith "Missing case in term_to_string")
end))
and binder_to_string : binder  ->  Prims.string = (fun x -> (
# 367 "FStar.Parser.AST.fst"
let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Ident.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Ident.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
(let _147_1215 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _147_1215))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (let _147_1216 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" _147_1216 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun _58_2 -> (match (_58_2) with
| Some (Equality) -> begin
"$"
end
| Some (Implicit) -> begin
"#"
end
| _58_565 -> begin
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
(let _147_1220 = (FStar_All.pipe_right p pat_to_string)
in (let _147_1219 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _147_1220 _147_1219)))
end
| (PatTvar (i, aq)) | (PatVar (i, aq)) -> begin
(let _147_1221 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" _147_1221 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _147_1222 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _147_1222))
end
| PatTuple (l, false) -> begin
(let _147_1223 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _147_1223))
end
| PatTuple (l, true) -> begin
(let _147_1224 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _147_1224))
end
| PatRecord (l) -> begin
(let _147_1227 = (to_string_l "; " (fun _58_596 -> (match (_58_596) with
| (f, e) -> begin
(let _147_1226 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _147_1226))
end)) l)
in (FStar_Util.format1 "{%s}" _147_1227))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _147_1229 = (FStar_All.pipe_right p pat_to_string)
in (let _147_1228 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _147_1229 _147_1228)))
end))

# 394 "FStar.Parser.AST.fst"
let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, _58_608) -> begin
(let _147_1232 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_147_1232)::[])
end
| PatApp (p, _58_613) -> begin
(head_id_of_pat p)
end
| PatAscribed (p, _58_618) -> begin
(head_id_of_pat p)
end
| _58_622 -> begin
[]
end))

# 401 "FStar.Parser.AST.fst"
let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _58_627 -> (match (_58_627) with
| (p, _58_626) -> begin
(head_id_of_pat p)
end)))))

# 403 "FStar.Parser.AST.fst"
let id_of_tycon : tycon  ->  Prims.string = (fun _58_3 -> (match (_58_3) with
| (TyconAbstract (i, _, _)) | (TyconAbbrev (i, _, _, _)) | (TyconRecord (i, _, _, _)) | (TyconVariant (i, _, _, _)) -> begin
i.FStar_Ident.idText
end))

# 409 "FStar.Parser.AST.fst"
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
| KindAbbrev (i, _58_671, _58_673) -> begin
(Prims.strcat "kind " i.FStar_Ident.idText)
end
| ToplevelLet (_58_677, _58_679, pats) -> begin
(let _147_1242 = (let _147_1241 = (let _147_1240 = (lids_of_let pats)
in (FStar_All.pipe_right _147_1240 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _147_1241 (FStar_String.concat ", ")))
in (Prims.strcat "let " _147_1242))
end
| Main (_58_685) -> begin
"main ..."
end
| Assume (_58_688, i, _58_691) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (_58_695, tys) -> begin
(let _147_1244 = (let _147_1243 = (FStar_All.pipe_right tys (FStar_List.map id_of_tycon))
in (FStar_All.pipe_right _147_1243 (FStar_String.concat ", ")))
in (Prims.strcat "type " _147_1244))
end
| Val (_58_700, i, _58_703) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, _58_708) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| (NewEffect (_, DefineEffect (i, _, _, _))) | (NewEffect (_, RedefineEffect (i, _, _))) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| SubEffect (_58_735) -> begin
"sub_effect"
end
| Pragma (_58_738) -> begin
"pragma"
end))

# 426 "FStar.Parser.AST.fst"
let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| (Module (_, decls)) | (Interface (_, decls, _)) -> begin
(let _147_1247 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right _147_1247 (FStar_String.concat "\n")))
end))

# 436 "FStar.Parser.AST.fst"
let error = (fun msg tm r -> (
# 437 "FStar.Parser.AST.fst"
let tm = (FStar_All.pipe_right tm term_to_string)
in (
# 438 "FStar.Parser.AST.fst"
let tm = if ((FStar_String.length tm) >= 80) then begin
(let _147_1251 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _147_1251 "..."))
end else begin
tm
end
in if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r))))
end)))




