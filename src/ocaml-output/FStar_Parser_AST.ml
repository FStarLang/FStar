
open Prims
type level =
| Un
| Expr
| Type
| Kind
| Formula

let is_Un : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Un -> begin
true
end
| _ -> begin
false
end))

let is_Expr : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

let is_Formula : level  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_FsTypApp : imp  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| FsTypApp -> begin
true
end
| _ -> begin
false
end))

let is_Hash : imp  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Hash -> begin
true
end
| _ -> begin
false
end))

let is_Nothing : imp  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Nothing -> begin
true
end
| _ -> begin
false
end))

type arg_qualifier =
| Implicit
| Equality

let is_Implicit : arg_qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Implicit -> begin
true
end
| _ -> begin
false
end))

let is_Equality : arg_qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_Wild : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Wild -> begin
true
end
| _ -> begin
false
end))

let is_Const : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_Op : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Op (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tvar : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Var : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Name : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Construct : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Construct (_) -> begin
true
end
| _ -> begin
false
end))

let is_Abs : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_App : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

let is_Let : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Seq : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Seq (_) -> begin
true
end
| _ -> begin
false
end))

let is_If : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| If (_) -> begin
true
end
| _ -> begin
false
end))

let is_Match : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_TryWith : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TryWith (_) -> begin
true
end
| _ -> begin
false
end))

let is_Ascribed : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Record : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_Project : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Project (_) -> begin
true
end
| _ -> begin
false
end))

let is_Product : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Product (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sum : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Sum (_) -> begin
true
end
| _ -> begin
false
end))

let is_QForall : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| QForall (_) -> begin
true
end
| _ -> begin
false
end))

let is_QExists : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| QExists (_) -> begin
true
end
| _ -> begin
false
end))

let is_Refine : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_NamedTyp : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NamedTyp (_) -> begin
true
end
| _ -> begin
false
end))

let is_Paren : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Paren (_) -> begin
true
end
| _ -> begin
false
end))

let is_Requires : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Requires (_) -> begin
true
end
| _ -> begin
false
end))

let is_Ensures : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Ensures (_) -> begin
true
end
| _ -> begin
false
end))

let is_Labeled : term'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

let is_Variable : binder'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Variable (_) -> begin
true
end
| _ -> begin
false
end))

let is_TVariable : binder'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TVariable (_) -> begin
true
end
| _ -> begin
false
end))

let is_Annotated : binder'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Annotated (_) -> begin
true
end
| _ -> begin
false
end))

let is_TAnnotated : binder'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TAnnotated (_) -> begin
true
end
| _ -> begin
false
end))

let is_NoName : binder'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NoName (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))

let is_PatWild : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatWild -> begin
true
end
| _ -> begin
false
end))

let is_PatConst : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatConst (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatApp : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatApp (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatVar : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatVar (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatName : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatName (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatTvar : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatTvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatList : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatList (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatTuple : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatTuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatRecord : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatRecord (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatAscribed : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatAscribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatOr : pattern'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| PatOr (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

let ___Const____0 : term'  ->  FStar_Const.sconst = (fun projectee -> (match (projectee) with
| Const (_60_13) -> begin
_60_13
end))

let ___Op____0 : term'  ->  (Prims.string * term Prims.list) = (fun projectee -> (match (projectee) with
| Op (_60_16) -> begin
_60_16
end))

let ___Tvar____0 : term'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Tvar (_60_19) -> begin
_60_19
end))

let ___Var____0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Var (_60_22) -> begin
_60_22
end))

let ___Name____0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Name (_60_25) -> begin
_60_25
end))

let ___Construct____0 : term'  ->  (FStar_Ident.lid * (term * imp) Prims.list) = (fun projectee -> (match (projectee) with
| Construct (_60_28) -> begin
_60_28
end))

let ___Abs____0 : term'  ->  (pattern Prims.list * term) = (fun projectee -> (match (projectee) with
| Abs (_60_31) -> begin
_60_31
end))

let ___App____0 : term'  ->  (term * term * imp) = (fun projectee -> (match (projectee) with
| App (_60_34) -> begin
_60_34
end))

let ___Let____0 : term'  ->  (Prims.bool * (pattern * term) Prims.list * term) = (fun projectee -> (match (projectee) with
| Let (_60_37) -> begin
_60_37
end))

let ___Seq____0 : term'  ->  (term * term) = (fun projectee -> (match (projectee) with
| Seq (_60_40) -> begin
_60_40
end))

let ___If____0 : term'  ->  (term * term * term) = (fun projectee -> (match (projectee) with
| If (_60_43) -> begin
_60_43
end))

let ___Match____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Match (_60_46) -> begin
_60_46
end))

let ___TryWith____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| TryWith (_60_49) -> begin
_60_49
end))

let ___Ascribed____0 : term'  ->  (term * term) = (fun projectee -> (match (projectee) with
| Ascribed (_60_52) -> begin
_60_52
end))

let ___Record____0 : term'  ->  (term Prims.option * (FStar_Ident.lid * term) Prims.list) = (fun projectee -> (match (projectee) with
| Record (_60_55) -> begin
_60_55
end))

let ___Project____0 : term'  ->  (term * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| Project (_60_58) -> begin
_60_58
end))

let ___Product____0 : term'  ->  (binder Prims.list * term) = (fun projectee -> (match (projectee) with
| Product (_60_61) -> begin
_60_61
end))

let ___Sum____0 : term'  ->  (binder Prims.list * term) = (fun projectee -> (match (projectee) with
| Sum (_60_64) -> begin
_60_64
end))

let ___QForall____0 : term'  ->  (binder Prims.list * term Prims.list Prims.list * term) = (fun projectee -> (match (projectee) with
| QForall (_60_67) -> begin
_60_67
end))

let ___QExists____0 : term'  ->  (binder Prims.list * term Prims.list Prims.list * term) = (fun projectee -> (match (projectee) with
| QExists (_60_70) -> begin
_60_70
end))

let ___Refine____0 : term'  ->  (binder * term) = (fun projectee -> (match (projectee) with
| Refine (_60_73) -> begin
_60_73
end))

let ___NamedTyp____0 : term'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| NamedTyp (_60_76) -> begin
_60_76
end))

let ___Paren____0 : term'  ->  term = (fun projectee -> (match (projectee) with
| Paren (_60_79) -> begin
_60_79
end))

let ___Requires____0 : term'  ->  (term * Prims.string Prims.option) = (fun projectee -> (match (projectee) with
| Requires (_60_82) -> begin
_60_82
end))

let ___Ensures____0 : term'  ->  (term * Prims.string Prims.option) = (fun projectee -> (match (projectee) with
| Ensures (_60_85) -> begin
_60_85
end))

let ___Labeled____0 : term'  ->  (term * Prims.string * Prims.bool) = (fun projectee -> (match (projectee) with
| Labeled (_60_88) -> begin
_60_88
end))

let ___Variable____0 : binder'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Variable (_60_92) -> begin
_60_92
end))

let ___TVariable____0 : binder'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| TVariable (_60_95) -> begin
_60_95
end))

let ___Annotated____0 : binder'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Annotated (_60_98) -> begin
_60_98
end))

let ___TAnnotated____0 : binder'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| TAnnotated (_60_101) -> begin
_60_101
end))

let ___NoName____0 : binder'  ->  term = (fun projectee -> (match (projectee) with
| NoName (_60_104) -> begin
_60_104
end))

let ___PatConst____0 : pattern'  ->  FStar_Const.sconst = (fun projectee -> (match (projectee) with
| PatConst (_60_108) -> begin
_60_108
end))

let ___PatApp____0 : pattern'  ->  (pattern * pattern Prims.list) = (fun projectee -> (match (projectee) with
| PatApp (_60_111) -> begin
_60_111
end))

let ___PatVar____0 : pattern'  ->  (FStar_Ident.ident * Prims.bool) = (fun projectee -> (match (projectee) with
| PatVar (_60_114) -> begin
_60_114
end))

let ___PatName____0 : pattern'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| PatName (_60_117) -> begin
_60_117
end))

let ___PatTvar____0 : pattern'  ->  (FStar_Ident.ident * Prims.bool) = (fun projectee -> (match (projectee) with
| PatTvar (_60_120) -> begin
_60_120
end))

let ___PatList____0 : pattern'  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PatList (_60_123) -> begin
_60_123
end))

let ___PatTuple____0 : pattern'  ->  (pattern Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| PatTuple (_60_126) -> begin
_60_126
end))

let ___PatRecord____0 : pattern'  ->  (FStar_Ident.lid * pattern) Prims.list = (fun projectee -> (match (projectee) with
| PatRecord (_60_129) -> begin
_60_129
end))

let ___PatAscribed____0 : pattern'  ->  (pattern * term) = (fun projectee -> (match (projectee) with
| PatAscribed (_60_132) -> begin
_60_132
end))

let ___PatOr____0 : pattern'  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PatOr (_60_135) -> begin
_60_135
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

let is_TyconAbstract : tycon  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TyconAbstract (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconAbbrev : tycon  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TyconAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconRecord : tycon  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TyconRecord (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconVariant : tycon  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TyconVariant (_) -> begin
true
end
| _ -> begin
false
end))

let ___TyconAbstract____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option) = (fun projectee -> (match (projectee) with
| TyconAbstract (_60_139) -> begin
_60_139
end))

let ___TyconAbbrev____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option * term) = (fun projectee -> (match (projectee) with
| TyconAbbrev (_60_142) -> begin
_60_142
end))

let ___TyconRecord____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term) Prims.list) = (fun projectee -> (match (projectee) with
| TyconRecord (_60_145) -> begin
_60_145
end))

let ___TyconVariant____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term Prims.option * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| TyconVariant (_60_148) -> begin
_60_148
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

let is_Private : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Abstract : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Abstract -> begin
true
end
| _ -> begin
false
end))

let is_Assumption : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_DefaultEffect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DefaultEffect -> begin
true
end
| _ -> begin
false
end))

let is_TotalEffect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TotalEffect -> begin
true
end
| _ -> begin
false
end))

let is_Effect : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Effect -> begin
true
end
| _ -> begin
false
end))

let is_New : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| New -> begin
true
end
| _ -> begin
false
end))

let is_Inline : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Inline -> begin
true
end
| _ -> begin
false
end))

let is_Unfoldable : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Unfoldable -> begin
true
end
| _ -> begin
false
end))

let is_Irreducible : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Irreducible -> begin
true
end
| _ -> begin
false
end))

let is_Opaque : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Opaque -> begin
true
end
| _ -> begin
false
end))

let is_Logic : qualifier  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_Mklift : lift  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklift"))))

type pragma =
| SetOptions of Prims.string
| ResetOptions

let is_SetOptions : pragma  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

let is_ResetOptions : pragma  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ResetOptions -> begin
true
end
| _ -> begin
false
end))

let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_60_155) -> begin
_60_155
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

let is_Open : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))

let is_ModuleAbbrev : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ModuleAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_KindAbbrev : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| KindAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_ToplevelLet : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ToplevelLet (_) -> begin
true
end
| _ -> begin
false
end))

let is_Main : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Main (_) -> begin
true
end
| _ -> begin
false
end))

let is_Assume : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tycon : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Tycon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Val : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exception : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exception (_) -> begin
true
end
| _ -> begin
false
end))

let is_NewEffect : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NewEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_SubEffect : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SubEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pragma : decl'  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pragma (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkdecl : decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdecl"))))

let is_DefineEffect : effect_decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_RedefineEffect : effect_decl  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| RedefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

let ___Open____0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Open (_60_160) -> begin
_60_160
end))

let ___ModuleAbbrev____0 : decl'  ->  (FStar_Ident.ident * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_60_163) -> begin
_60_163
end))

let ___KindAbbrev____0 : decl'  ->  (FStar_Ident.ident * binder Prims.list * knd) = (fun projectee -> (match (projectee) with
| KindAbbrev (_60_166) -> begin
_60_166
end))

let ___ToplevelLet____0 : decl'  ->  (qualifiers * Prims.bool * (pattern * term) Prims.list) = (fun projectee -> (match (projectee) with
| ToplevelLet (_60_169) -> begin
_60_169
end))

let ___Main____0 : decl'  ->  term = (fun projectee -> (match (projectee) with
| Main (_60_172) -> begin
_60_172
end))

let ___Assume____0 : decl'  ->  (qualifiers * FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Assume (_60_175) -> begin
_60_175
end))

let ___Tycon____0 : decl'  ->  (qualifiers * tycon Prims.list) = (fun projectee -> (match (projectee) with
| Tycon (_60_178) -> begin
_60_178
end))

let ___Val____0 : decl'  ->  (qualifiers * FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Val (_60_181) -> begin
_60_181
end))

let ___Exception____0 : decl'  ->  (FStar_Ident.ident * term Prims.option) = (fun projectee -> (match (projectee) with
| Exception (_60_184) -> begin
_60_184
end))

let ___NewEffect____0 : decl'  ->  (qualifiers * effect_decl) = (fun projectee -> (match (projectee) with
| NewEffect (_60_187) -> begin
_60_187
end))

let ___SubEffect____0 : decl'  ->  lift = (fun projectee -> (match (projectee) with
| SubEffect (_60_190) -> begin
_60_190
end))

let ___Pragma____0 : decl'  ->  pragma = (fun projectee -> (match (projectee) with
| Pragma (_60_193) -> begin
_60_193
end))

let ___DefineEffect____0 : effect_decl  ->  (FStar_Ident.ident * binder Prims.list * term * decl Prims.list) = (fun projectee -> (match (projectee) with
| DefineEffect (_60_197) -> begin
_60_197
end))

let ___RedefineEffect____0 : effect_decl  ->  (FStar_Ident.ident * binder Prims.list * term) = (fun projectee -> (match (projectee) with
| RedefineEffect (_60_200) -> begin
_60_200
end))

type modul =
| Module of (FStar_Ident.lid * decl Prims.list)
| Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool)

let is_Module : modul  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Module (_) -> begin
true
end
| _ -> begin
false
end))

let is_Interface : modul  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Interface (_) -> begin
true
end
| _ -> begin
false
end))

let ___Module____0 : modul  ->  (FStar_Ident.lid * decl Prims.list) = (fun projectee -> (match (projectee) with
| Module (_60_203) -> begin
_60_203
end))

let ___Interface____0 : modul  ->  (FStar_Ident.lid * decl Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| Interface (_60_206) -> begin
_60_206
end))

type file =
modul Prims.list

type inputFragment =
(file, decl Prims.list) FStar_Util.either

let mk_decl : decl'  ->  FStar_Range.range  ->  decl = (fun d r -> {d = d; drange = r})

let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})

let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})

let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((FStar_List.append ps p'), body'))
end
| _60_225 -> begin
Abs ((ps, body))
end))

let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (let x = (FStar_Absyn_Util.genident (Some (r1)))
in (let _163_980 = (let _163_979 = (let _163_978 = (let _163_977 = (let _163_976 = (let _163_975 = (let _163_974 = (let _163_973 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_163_973))
in (mk_term _163_974 r1 Expr))
in (_163_975, branches))
in Match (_163_976))
in (mk_term _163_977 r2 Expr))
in (((mk_pattern (PatVar ((x, false))) r1))::[], _163_978))
in Abs (_163_979))
in (mk_term _163_980 r2 Expr))))

let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_60_233), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _60_241 -> begin
None
end))

let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _163_989 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _163_989 r)))

let to_string_l = (fun sep f l -> (let _163_996 = (FStar_List.map f l)
in (FStar_String.concat sep _163_996)))

let imp_to_string : imp  ->  Prims.string = (fun _60_1 -> (match (_60_1) with
| Hash -> begin
"#"
end
| _60_250 -> begin
""
end))

let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _60_255) -> begin
(let _163_1003 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _163_1003))
end
| Ensures (t, _60_260) -> begin
(let _163_1004 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _163_1004))
end
| Labeled (t, l, _60_266) -> begin
(let _163_1005 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _163_1005))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _163_1008 = (let _163_1007 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _163_1007))
in (FStar_Util.format2 "%s(%s)" s _163_1008))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _163_1011 = (to_string_l " " (fun _60_287 -> (match (_60_287) with
| (a, imp) -> begin
(let _163_1010 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _163_1010))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _163_1011))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _163_1013 = (to_string_l " " pat_to_string pats)
in (let _163_1012 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _163_1013 _163_1012)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _163_1015 = (to_string_l " " pat_to_string pats)
in (let _163_1014 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _163_1015 _163_1014)))
end
| App (t1, t2, imp) -> begin
(let _163_1017 = (FStar_All.pipe_right t1 term_to_string)
in (let _163_1016 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _163_1017 (imp_to_string imp) _163_1016)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _163_1020 = (FStar_All.pipe_right pat pat_to_string)
in (let _163_1019 = (FStar_All.pipe_right tm term_to_string)
in (let _163_1018 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _163_1020 _163_1019 _163_1018))))
end
| Let (_60_310, lbs, body) -> begin
(let _163_1025 = (to_string_l " and " (fun _60_317 -> (match (_60_317) with
| (p, b) -> begin
(let _163_1023 = (FStar_All.pipe_right p pat_to_string)
in (let _163_1022 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _163_1023 _163_1022)))
end)) lbs)
in (let _163_1024 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _163_1025 _163_1024)))
end
| Seq (t1, t2) -> begin
(let _163_1027 = (FStar_All.pipe_right t1 term_to_string)
in (let _163_1026 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _163_1027 _163_1026)))
end
| If (t1, t2, t3) -> begin
(let _163_1030 = (FStar_All.pipe_right t1 term_to_string)
in (let _163_1029 = (FStar_All.pipe_right t2 term_to_string)
in (let _163_1028 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _163_1030 _163_1029 _163_1028))))
end
| Match (t, branches) -> begin
(let _163_1037 = (FStar_All.pipe_right t term_to_string)
in (let _163_1036 = (to_string_l " | " (fun _60_334 -> (match (_60_334) with
| (p, w, e) -> begin
(let _163_1035 = (FStar_All.pipe_right p pat_to_string)
in (let _163_1034 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _163_1032 = (term_to_string e)
in (FStar_Util.format1 "when %s" _163_1032))
end)
in (let _163_1033 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _163_1035 _163_1034 _163_1033))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _163_1037 _163_1036)))
end
| Ascribed (t1, t2) -> begin
(let _163_1039 = (FStar_All.pipe_right t1 term_to_string)
in (let _163_1038 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _163_1039 _163_1038)))
end
| Record (Some (e), fields) -> begin
(let _163_1043 = (FStar_All.pipe_right e term_to_string)
in (let _163_1042 = (to_string_l " " (fun _60_349 -> (match (_60_349) with
| (l, e) -> begin
(let _163_1041 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _163_1041))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _163_1043 _163_1042)))
end
| Record (None, fields) -> begin
(let _163_1046 = (to_string_l " " (fun _60_356 -> (match (_60_356) with
| (l, e) -> begin
(let _163_1045 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _163_1045))
end)) fields)
in (FStar_Util.format1 "{%s}" _163_1046))
end
| Project (e, l) -> begin
(let _163_1047 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _163_1047 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _163_1049 = (FStar_All.pipe_right b binder_to_string)
in (let _163_1048 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _163_1049 _163_1048)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _163_1051 = (FStar_All.pipe_right b binder_to_string)
in (let _163_1050 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _163_1051 _163_1050)))
end
| Sum (binders, t) -> begin
(let _163_1054 = (let _163_1052 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _163_1052 (FStar_String.concat " * ")))
in (let _163_1053 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _163_1054 _163_1053)))
end
| QForall (bs, pats, t) -> begin
(let _163_1057 = (to_string_l " " binder_to_string bs)
in (let _163_1056 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _163_1055 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _163_1057 _163_1056 _163_1055))))
end
| QExists (bs, pats, t) -> begin
(let _163_1060 = (to_string_l " " binder_to_string bs)
in (let _163_1059 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _163_1058 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _163_1060 _163_1059 _163_1058))))
end
| Refine (b, t) -> begin
(let _163_1062 = (FStar_All.pipe_right b binder_to_string)
in (let _163_1061 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _163_1062 _163_1061)))
end
| NamedTyp (x, t) -> begin
(let _163_1063 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _163_1063))
end
| Paren (t) -> begin
(let _163_1064 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _163_1064))
end
| Product (bs, t) -> begin
(let _163_1067 = (let _163_1065 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _163_1065 (FStar_String.concat ",")))
in (let _163_1066 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _163_1067 _163_1066)))
end
| t -> begin
(FStar_All.failwith "Missing case in term_to_string")
end))
and binder_to_string : binder  ->  Prims.string = (fun x -> (let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Ident.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Ident.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
(let _163_1069 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _163_1069))
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
| _60_431 -> begin
s
end)))
and pat_to_string : pattern  ->  Prims.string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
(let _163_1072 = (FStar_All.pipe_right p pat_to_string)
in (let _163_1071 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _163_1072 _163_1071)))
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
(let _163_1073 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _163_1073))
end
| PatTuple (l, false) -> begin
(let _163_1074 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _163_1074))
end
| PatTuple (l, true) -> begin
(let _163_1075 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _163_1075))
end
| PatRecord (l) -> begin
(let _163_1078 = (to_string_l "; " (fun _60_470 -> (match (_60_470) with
| (f, e) -> begin
(let _163_1077 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _163_1077))
end)) l)
in (FStar_Util.format1 "{%s}" _163_1078))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _163_1080 = (FStar_All.pipe_right p pat_to_string)
in (let _163_1079 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _163_1080 _163_1079)))
end))

let error = (fun msg tm r -> (let tm = (FStar_All.pipe_right tm term_to_string)
in (let tm = if ((FStar_String.length tm) >= 80) then begin
(let _163_1084 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _163_1084 "..."))
end else begin
tm
end
in (Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r)))))))

let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd tl -> PatApp (((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.nil_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _60_506 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _60_510 -> begin
(FStar_List.fold_left (fun t _60_514 -> (match (_60_514) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (let empty = (let _163_1128 = (let _163_1127 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_163_1127))
in (mk_term _163_1128 r Expr))
in (let ref_constr = (let _163_1130 = (let _163_1129 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_163_1129))
in (mk_term _163_1130 r Expr))
in (let singleton = (let _163_1132 = (let _163_1131 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_163_1131))
in (mk_term _163_1132 r Expr))
in (let union = (let _163_1134 = (let _163_1133 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_163_1133))
in (mk_term _163_1134 r Expr))
in (FStar_List.fold_right (fun e tl -> (let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _60_530 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _163_1146 = (let _163_1145 = (let _163_1144 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _163_1144))
in Construct (_163_1145))
in (mk_term _163_1146 r Un))
end
| _60_535 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (let admit = (let admit_name = (let _163_1152 = (let _163_1151 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_163_1151))
in (mk_term _163_1152 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (let magic = (let magic_name = (let _163_1154 = (let _163_1153 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_163_1153))
in (mk_term _163_1154 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

let mkWildAdmitMagic = (fun r -> (let _163_1156 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _163_1156)))

let focusBranches = (fun branches r -> (let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(let _60_549 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (let focussed = (let _163_1159 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _163_1159 (FStar_List.map Prims.snd)))
in (let _163_1161 = (let _163_1160 = (mkWildAdmitMagic r)
in (_163_1160)::[])
in (FStar_List.append focussed _163_1161))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))

let focusLetBindings = (fun lbs r -> (let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(let _60_555 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _60_559 -> (match (_60_559) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _163_1165 = (mkAdmitMagic r)
in ((Prims.fst lb), _163_1165))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))

let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _163_1173 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _163_1173 r)))

let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (let cons = (FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
in (let _163_1179 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _163_1179 r))))

let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (let cons = (FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
in (let _163_1185 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _163_1185 r))))

let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t refopt m implicit -> (let b = (mk_binder (Annotated ((id, t))) m Type implicit)
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
| Refine ({b = Annotated (x, t); brange = _60_591; blevel = _60_589; aqual = _60_587}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _60_603 -> begin
None
end))




