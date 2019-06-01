
open Prims
open FStar_Pervasives
type level =
| Un
| Expr
| Type_level
| Kind
| Formula


let uu___is_Un : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un -> begin
true
end
| uu____26 -> begin
false
end))


let uu___is_Expr : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Expr -> begin
true
end
| uu____37 -> begin
false
end))


let uu___is_Type_level : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Type_level -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_Kind : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kind -> begin
true
end
| uu____59 -> begin
false
end))


let uu___is_Formula : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Formula -> begin
true
end
| uu____70 -> begin
false
end))

type let_qualifier =
| NoLetQualifier
| Rec


let uu___is_NoLetQualifier : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoLetQualifier -> begin
true
end
| uu____81 -> begin
false
end))


let uu___is_Rec : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec -> begin
true
end
| uu____92 -> begin
false
end))

type quote_kind =
| Static
| Dynamic


let uu___is_Static : quote_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Static -> begin
true
end
| uu____103 -> begin
false
end))


let uu___is_Dynamic : quote_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dynamic -> begin
true
end
| uu____114 -> begin
false
end))

type term' =
| Wild
| Const of FStar_Const.sconst
| Op of (FStar_Ident.ident * term Prims.list)
| Tvar of FStar_Ident.ident
| Uvar of FStar_Ident.ident
| Var of FStar_Ident.lid
| Name of FStar_Ident.lid
| Projector of (FStar_Ident.lid * FStar_Ident.ident)
| Construct of (FStar_Ident.lid * (term * imp) Prims.list)
| Abs of (pattern Prims.list * term)
| App of (term * term * imp)
| Let of (let_qualifier * (term Prims.list FStar_Pervasives_Native.option * (pattern * term)) Prims.list * term)
| LetOpen of (FStar_Ident.lid * term)
| Seq of (term * term)
| Bind of (FStar_Ident.ident * term * term)
| If of (term * term * term)
| Match of (term * (pattern * term FStar_Pervasives_Native.option * term) Prims.list)
| TryWith of (term * (pattern * term FStar_Pervasives_Native.option * term) Prims.list)
| Ascribed of (term * term * term FStar_Pervasives_Native.option)
| Record of (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term) Prims.list)
| Project of (term * FStar_Ident.lid)
| Product of (binder Prims.list * term)
| Sum of ((binder, term) FStar_Util.either Prims.list * term)
| QForall of (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term)
| QExists of (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term)
| Refine of (binder * term)
| NamedTyp of (FStar_Ident.ident * term)
| Paren of term
| Requires of (term * Prims.string FStar_Pervasives_Native.option)
| Ensures of (term * Prims.string FStar_Pervasives_Native.option)
| Labeled of (term * Prims.string * Prims.bool)
| Discrim of FStar_Ident.lid
| Attributes of term Prims.list
| Antiquote of term
| Quote of (term * quote_kind)
| VQuote of term
| CalcProof of (term * term * calc_step Prims.list) 
 and term =
{tm : term'; range : FStar_Range.range; level : level} 
 and calc_step =
| CalcStep of (term * term * term) 
 and binder' =
| Variable of FStar_Ident.ident
| TVariable of FStar_Ident.ident
| Annotated of (FStar_Ident.ident * term)
| TAnnotated of (FStar_Ident.ident * term)
| NoName of term 
 and binder =
{b : binder'; brange : FStar_Range.range; blevel : level; aqual : arg_qualifier FStar_Pervasives_Native.option} 
 and pattern' =
| PatWild of arg_qualifier FStar_Pervasives_Native.option
| PatConst of FStar_Const.sconst
| PatApp of (pattern * pattern Prims.list)
| PatVar of (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option)
| PatName of FStar_Ident.lid
| PatTvar of (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option)
| PatList of pattern Prims.list
| PatTuple of (pattern Prims.list * Prims.bool)
| PatRecord of (FStar_Ident.lid * pattern) Prims.list
| PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option))
| PatOr of pattern Prims.list
| PatOp of FStar_Ident.ident 
 and pattern =
{pat : pattern'; prange : FStar_Range.range} 
 and arg_qualifier =
| Implicit
| Equality
| Meta of term 
 and imp =
| FsTypApp
| Hash
| UnivApp
| HashBrace of term
| Infix
| Nothing


let uu___is_Wild : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Wild -> begin
true
end
| uu____733 -> begin
false
end))


let uu___is_Const : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____745 -> begin
false
end))


let __proj__Const__item___0 : term'  ->  FStar_Const.sconst = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
_0
end))


let uu___is_Op : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Op (_0) -> begin
true
end
| uu____770 -> begin
false
end))


let __proj__Op__item___0 : term'  ->  (FStar_Ident.ident * term Prims.list) = (fun projectee -> (match (projectee) with
| Op (_0) -> begin
_0
end))


let uu___is_Tvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tvar (_0) -> begin
true
end
| uu____807 -> begin
false
end))


let __proj__Tvar__item___0 : term'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Tvar (_0) -> begin
_0
end))


let uu___is_Uvar : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Uvar (_0) -> begin
true
end
| uu____826 -> begin
false
end))


let __proj__Uvar__item___0 : term'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Uvar (_0) -> begin
_0
end))


let uu___is_Var : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____845 -> begin
false
end))


let __proj__Var__item___0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
_0
end))


let uu___is_Name : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Name (_0) -> begin
true
end
| uu____864 -> begin
false
end))


let __proj__Name__item___0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Name (_0) -> begin
_0
end))


let uu___is_Projector : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Projector (_0) -> begin
true
end
| uu____887 -> begin
false
end))


let __proj__Projector__item___0 : term'  ->  (FStar_Ident.lid * FStar_Ident.ident) = (fun projectee -> (match (projectee) with
| Projector (_0) -> begin
_0
end))


let uu___is_Construct : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Construct (_0) -> begin
true
end
| uu____928 -> begin
false
end))


let __proj__Construct__item___0 : term'  ->  (FStar_Ident.lid * (term * imp) Prims.list) = (fun projectee -> (match (projectee) with
| Construct (_0) -> begin
_0
end))


let uu___is_Abs : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
true
end
| uu____983 -> begin
false
end))


let __proj__Abs__item___0 : term'  ->  (pattern Prims.list * term) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____1026 -> begin
false
end))


let __proj__App__item___0 : term'  ->  (term * term * imp) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Let : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____1083 -> begin
false
end))


let __proj__Let__item___0 : term'  ->  (let_qualifier * (term Prims.list FStar_Pervasives_Native.option * (pattern * term)) Prims.list * term) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_LetOpen : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LetOpen (_0) -> begin
true
end
| uu____1166 -> begin
false
end))


let __proj__LetOpen__item___0 : term'  ->  (FStar_Ident.lid * term) = (fun projectee -> (match (projectee) with
| LetOpen (_0) -> begin
_0
end))


let uu___is_Seq : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Seq (_0) -> begin
true
end
| uu____1201 -> begin
false
end))


let __proj__Seq__item___0 : term'  ->  (term * term) = (fun projectee -> (match (projectee) with
| Seq (_0) -> begin
_0
end))


let uu___is_Bind : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bind (_0) -> begin
true
end
| uu____1238 -> begin
false
end))


let __proj__Bind__item___0 : term'  ->  (FStar_Ident.ident * term * term) = (fun projectee -> (match (projectee) with
| Bind (_0) -> begin
_0
end))


let uu___is_If : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| If (_0) -> begin
true
end
| uu____1281 -> begin
false
end))


let __proj__If__item___0 : term'  ->  (term * term * term) = (fun projectee -> (match (projectee) with
| If (_0) -> begin
_0
end))


let uu___is_Match : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
true
end
| uu____1332 -> begin
false
end))


let __proj__Match__item___0 : term'  ->  (term * (pattern * term FStar_Pervasives_Native.option * term) Prims.list) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_TryWith : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TryWith (_0) -> begin
true
end
| uu____1407 -> begin
false
end))


let __proj__TryWith__item___0 : term'  ->  (term * (pattern * term FStar_Pervasives_Native.option * term) Prims.list) = (fun projectee -> (match (projectee) with
| TryWith (_0) -> begin
_0
end))


let uu___is_Ascribed : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Ascribed (_0) -> begin
true
end
| uu____1476 -> begin
false
end))


let __proj__Ascribed__item___0 : term'  ->  (term * term * term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Ascribed (_0) -> begin
_0
end))


let uu___is_Record : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record (_0) -> begin
true
end
| uu____1531 -> begin
false
end))


let __proj__Record__item___0 : term'  ->  (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term) Prims.list) = (fun projectee -> (match (projectee) with
| Record (_0) -> begin
_0
end))


let uu___is_Project : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Project (_0) -> begin
true
end
| uu____1590 -> begin
false
end))


let __proj__Project__item___0 : term'  ->  (term * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| Project (_0) -> begin
_0
end))


let uu___is_Product : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Product (_0) -> begin
true
end
| uu____1627 -> begin
false
end))


let __proj__Product__item___0 : term'  ->  (binder Prims.list * term) = (fun projectee -> (match (projectee) with
| Product (_0) -> begin
_0
end))


let uu___is_Sum : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Sum (_0) -> begin
true
end
| uu____1674 -> begin
false
end))


let __proj__Sum__item___0 : term'  ->  ((binder, term) FStar_Util.either Prims.list * term) = (fun projectee -> (match (projectee) with
| Sum (_0) -> begin
_0
end))


let uu___is_QForall : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QForall (_0) -> begin
true
end
| uu____1741 -> begin
false
end))


let __proj__QForall__item___0 : term'  ->  (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term) = (fun projectee -> (match (projectee) with
| QForall (_0) -> begin
_0
end))


let uu___is_QExists : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QExists (_0) -> begin
true
end
| uu____1832 -> begin
false
end))


let __proj__QExists__item___0 : term'  ->  (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list Prims.list) * term) = (fun projectee -> (match (projectee) with
| QExists (_0) -> begin
_0
end))


let uu___is_Refine : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Refine (_0) -> begin
true
end
| uu____1909 -> begin
false
end))


let __proj__Refine__item___0 : term'  ->  (binder * term) = (fun projectee -> (match (projectee) with
| Refine (_0) -> begin
_0
end))


let uu___is_NamedTyp : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NamedTyp (_0) -> begin
true
end
| uu____1944 -> begin
false
end))


let __proj__NamedTyp__item___0 : term'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| NamedTyp (_0) -> begin
_0
end))


let uu___is_Paren : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Paren (_0) -> begin
true
end
| uu____1975 -> begin
false
end))


let __proj__Paren__item___0 : term'  ->  term = (fun projectee -> (match (projectee) with
| Paren (_0) -> begin
_0
end))


let uu___is_Requires : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Requires (_0) -> begin
true
end
| uu____2001 -> begin
false
end))


let __proj__Requires__item___0 : term'  ->  (term * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Requires (_0) -> begin
_0
end))


let uu___is_Ensures : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Ensures (_0) -> begin
true
end
| uu____2048 -> begin
false
end))


let __proj__Ensures__item___0 : term'  ->  (term * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Ensures (_0) -> begin
_0
end))


let uu___is_Labeled : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
true
end
| uu____2096 -> begin
false
end))


let __proj__Labeled__item___0 : term'  ->  (term * Prims.string * Prims.bool) = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
_0
end))


let uu___is_Discrim : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Discrim (_0) -> begin
true
end
| uu____2139 -> begin
false
end))


let __proj__Discrim__item___0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Discrim (_0) -> begin
_0
end))


let uu___is_Attributes : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Attributes (_0) -> begin
true
end
| uu____2160 -> begin
false
end))


let __proj__Attributes__item___0 : term'  ->  term Prims.list = (fun projectee -> (match (projectee) with
| Attributes (_0) -> begin
_0
end))


let uu___is_Antiquote : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Antiquote (_0) -> begin
true
end
| uu____2185 -> begin
false
end))


let __proj__Antiquote__item___0 : term'  ->  term = (fun projectee -> (match (projectee) with
| Antiquote (_0) -> begin
_0
end))


let uu___is_Quote : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quote (_0) -> begin
true
end
| uu____2208 -> begin
false
end))


let __proj__Quote__item___0 : term'  ->  (term * quote_kind) = (fun projectee -> (match (projectee) with
| Quote (_0) -> begin
_0
end))


let uu___is_VQuote : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VQuote (_0) -> begin
true
end
| uu____2239 -> begin
false
end))


let __proj__VQuote__item___0 : term'  ->  term = (fun projectee -> (match (projectee) with
| VQuote (_0) -> begin
_0
end))


let uu___is_CalcProof : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CalcProof (_0) -> begin
true
end
| uu____2266 -> begin
false
end))


let __proj__CalcProof__item___0 : term'  ->  (term * term * calc_step Prims.list) = (fun projectee -> (match (projectee) with
| CalcProof (_0) -> begin
_0
end))


let __proj__Mkterm__item__tm : term  ->  term' = (fun projectee -> (match (projectee) with
| {tm = tm; range = range; level = level} -> begin
tm
end))


let __proj__Mkterm__item__range : term  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {tm = tm; range = range; level = level} -> begin
range
end))


let __proj__Mkterm__item__level : term  ->  level = (fun projectee -> (match (projectee) with
| {tm = tm; range = range; level = level} -> begin
level
end))


let uu___is_CalcStep : calc_step  ->  Prims.bool = (fun projectee -> true)


let __proj__CalcStep__item___0 : calc_step  ->  (term * term * term) = (fun projectee -> (match (projectee) with
| CalcStep (_0) -> begin
_0
end))


let uu___is_Variable : binder'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Variable (_0) -> begin
true
end
| uu____2369 -> begin
false
end))


let __proj__Variable__item___0 : binder'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Variable (_0) -> begin
_0
end))


let uu___is_TVariable : binder'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TVariable (_0) -> begin
true
end
| uu____2388 -> begin
false
end))


let __proj__TVariable__item___0 : binder'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| TVariable (_0) -> begin
_0
end))


let uu___is_Annotated : binder'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Annotated (_0) -> begin
true
end
| uu____2411 -> begin
false
end))


let __proj__Annotated__item___0 : binder'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Annotated (_0) -> begin
_0
end))


let uu___is_TAnnotated : binder'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TAnnotated (_0) -> begin
true
end
| uu____2446 -> begin
false
end))


let __proj__TAnnotated__item___0 : binder'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| TAnnotated (_0) -> begin
_0
end))


let uu___is_NoName : binder'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoName (_0) -> begin
true
end
| uu____2477 -> begin
false
end))


let __proj__NoName__item___0 : binder'  ->  term = (fun projectee -> (match (projectee) with
| NoName (_0) -> begin
_0
end))


let __proj__Mkbinder__item__b : binder  ->  binder' = (fun projectee -> (match (projectee) with
| {b = b; brange = brange; blevel = blevel; aqual = aqual} -> begin
b
end))


let __proj__Mkbinder__item__brange : binder  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {b = b; brange = brange; blevel = blevel; aqual = aqual} -> begin
brange
end))


let __proj__Mkbinder__item__blevel : binder  ->  level = (fun projectee -> (match (projectee) with
| {b = b; brange = brange; blevel = blevel; aqual = aqual} -> begin
blevel
end))


let __proj__Mkbinder__item__aqual : binder  ->  arg_qualifier FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {b = b; brange = brange; blevel = blevel; aqual = aqual} -> begin
aqual
end))


let uu___is_PatWild : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatWild (_0) -> begin
true
end
| uu____2550 -> begin
false
end))


let __proj__PatWild__item___0 : pattern'  ->  arg_qualifier FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| PatWild (_0) -> begin
_0
end))


let uu___is_PatConst : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatConst (_0) -> begin
true
end
| uu____2575 -> begin
false
end))


let __proj__PatConst__item___0 : pattern'  ->  FStar_Const.sconst = (fun projectee -> (match (projectee) with
| PatConst (_0) -> begin
_0
end))


let uu___is_PatApp : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatApp (_0) -> begin
true
end
| uu____2600 -> begin
false
end))


let __proj__PatApp__item___0 : pattern'  ->  (pattern * pattern Prims.list) = (fun projectee -> (match (projectee) with
| PatApp (_0) -> begin
_0
end))


let uu___is_PatVar : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatVar (_0) -> begin
true
end
| uu____2643 -> begin
false
end))


let __proj__PatVar__item___0 : pattern'  ->  (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| PatVar (_0) -> begin
_0
end))


let uu___is_PatName : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatName (_0) -> begin
true
end
| uu____2680 -> begin
false
end))


let __proj__PatName__item___0 : pattern'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| PatName (_0) -> begin
_0
end))


let uu___is_PatTvar : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatTvar (_0) -> begin
true
end
| uu____2705 -> begin
false
end))


let __proj__PatTvar__item___0 : pattern'  ->  (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| PatTvar (_0) -> begin
_0
end))


let uu___is_PatList : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatList (_0) -> begin
true
end
| uu____2744 -> begin
false
end))


let __proj__PatList__item___0 : pattern'  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PatList (_0) -> begin
_0
end))


let uu___is_PatTuple : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatTuple (_0) -> begin
true
end
| uu____2776 -> begin
false
end))


let __proj__PatTuple__item___0 : pattern'  ->  (pattern Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| PatTuple (_0) -> begin
_0
end))


let uu___is_PatRecord : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatRecord (_0) -> begin
true
end
| uu____2822 -> begin
false
end))


let __proj__PatRecord__item___0 : pattern'  ->  (FStar_Ident.lid * pattern) Prims.list = (fun projectee -> (match (projectee) with
| PatRecord (_0) -> begin
_0
end))


let uu___is_PatAscribed : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatAscribed (_0) -> begin
true
end
| uu____2869 -> begin
false
end))


let __proj__PatAscribed__item___0 : pattern'  ->  (pattern * (term * term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| PatAscribed (_0) -> begin
_0
end))


let uu___is_PatOr : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatOr (_0) -> begin
true
end
| uu____2920 -> begin
false
end))


let __proj__PatOr__item___0 : pattern'  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PatOr (_0) -> begin
_0
end))


let uu___is_PatOp : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatOp (_0) -> begin
true
end
| uu____2945 -> begin
false
end))


let __proj__PatOp__item___0 : pattern'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| PatOp (_0) -> begin
_0
end))


let __proj__Mkpattern__item__pat : pattern  ->  pattern' = (fun projectee -> (match (projectee) with
| {pat = pat; prange = prange} -> begin
pat
end))


let __proj__Mkpattern__item__prange : pattern  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {pat = pat; prange = prange} -> begin
prange
end))


let uu___is_Implicit : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit -> begin
true
end
| uu____2979 -> begin
false
end))


let uu___is_Equality : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equality -> begin
true
end
| uu____2990 -> begin
false
end))


let uu___is_Meta : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____3002 -> begin
false
end))


let __proj__Meta__item___0 : arg_qualifier  ->  term = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_FsTypApp : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FsTypApp -> begin
true
end
| uu____3020 -> begin
false
end))


let uu___is_Hash : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Hash -> begin
true
end
| uu____3031 -> begin
false
end))


let uu___is_UnivApp : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivApp -> begin
true
end
| uu____3042 -> begin
false
end))


let uu___is_HashBrace : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HashBrace (_0) -> begin
true
end
| uu____3054 -> begin
false
end))


let __proj__HashBrace__item___0 : imp  ->  term = (fun projectee -> (match (projectee) with
| HashBrace (_0) -> begin
_0
end))


let uu___is_Infix : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Infix -> begin
true
end
| uu____3072 -> begin
false
end))


let uu___is_Nothing : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Nothing -> begin
true
end
| uu____3083 -> begin
false
end))


type patterns =
(FStar_Ident.ident Prims.list * term Prims.list Prims.list)


type attributes_ =
term Prims.list


type branch =
(pattern * term FStar_Pervasives_Native.option * term)


type aqual =
arg_qualifier FStar_Pervasives_Native.option


type knd =
term


type typ =
term


type expr =
term


type fsdoc =
(Prims.string * (Prims.string * Prims.string) Prims.list)

type tycon =
| TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option)
| TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option * term)
| TyconRecord of (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc FStar_Pervasives_Native.option) Prims.list)
| TyconVariant of (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option * (FStar_Ident.ident * term FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option * Prims.bool) Prims.list)


let uu___is_TyconAbstract : tycon  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TyconAbstract (_0) -> begin
true
end
| uu____3231 -> begin
false
end))


let __proj__TyconAbstract__item___0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| TyconAbstract (_0) -> begin
_0
end))


let uu___is_TyconAbbrev : tycon  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TyconAbbrev (_0) -> begin
true
end
| uu____3292 -> begin
false
end))


let __proj__TyconAbbrev__item___0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option * term) = (fun projectee -> (match (projectee) with
| TyconAbbrev (_0) -> begin
_0
end))


let uu___is_TyconRecord : tycon  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TyconRecord (_0) -> begin
true
end
| uu____3369 -> begin
false
end))


let __proj__TyconRecord__item___0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc FStar_Pervasives_Native.option) Prims.list) = (fun projectee -> (match (projectee) with
| TyconRecord (_0) -> begin
_0
end))


let uu___is_TyconVariant : tycon  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TyconVariant (_0) -> begin
true
end
| uu____3481 -> begin
false
end))


let __proj__TyconVariant__item___0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd FStar_Pervasives_Native.option * (FStar_Ident.ident * term FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| TyconVariant (_0) -> begin
_0
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


let uu___is_Private : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Private -> begin
true
end
| uu____3580 -> begin
false
end))


let uu___is_Abstract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____3591 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____3602 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____3613 -> begin
false
end))


let uu___is_Assumption : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumption -> begin
true
end
| uu____3624 -> begin
false
end))


let uu___is_DefaultEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefaultEffect -> begin
true
end
| uu____3635 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____3646 -> begin
false
end))


let uu___is_Effect_qual : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect_qual -> begin
true
end
| uu____3657 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____3668 -> begin
false
end))


let uu___is_Inline : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline -> begin
true
end
| uu____3679 -> begin
false
end))


let uu___is_Visible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible -> begin
true
end
| uu____3690 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____3701 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____3712 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____3723 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____3734 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____3745 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable -> begin
true
end
| uu____3756 -> begin
false
end))


let uu___is_Opaque : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Opaque -> begin
true
end
| uu____3767 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____3778 -> begin
false
end))


type qualifiers =
qualifier Prims.list

type decoration =
| Qualifier of qualifier
| DeclAttributes of term Prims.list
| Doc of fsdoc


let uu___is_Qualifier : decoration  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Qualifier (_0) -> begin
true
end
| uu____3809 -> begin
false
end))


let __proj__Qualifier__item___0 : decoration  ->  qualifier = (fun projectee -> (match (projectee) with
| Qualifier (_0) -> begin
_0
end))


let uu___is_DeclAttributes : decoration  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DeclAttributes (_0) -> begin
true
end
| uu____3830 -> begin
false
end))


let __proj__DeclAttributes__item___0 : decoration  ->  term Prims.list = (fun projectee -> (match (projectee) with
| DeclAttributes (_0) -> begin
_0
end))


let uu___is_Doc : decoration  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Doc (_0) -> begin
true
end
| uu____3855 -> begin
false
end))


let __proj__Doc__item___0 : decoration  ->  fsdoc = (fun projectee -> (match (projectee) with
| Doc (_0) -> begin
_0
end))

type lift_op =
| NonReifiableLift of term
| ReifiableLift of (term * term)
| LiftForFree of term


let uu___is_NonReifiableLift : lift_op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonReifiableLift (_0) -> begin
true
end
| uu____3893 -> begin
false
end))


let __proj__NonReifiableLift__item___0 : lift_op  ->  term = (fun projectee -> (match (projectee) with
| NonReifiableLift (_0) -> begin
_0
end))


let uu___is_ReifiableLift : lift_op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ReifiableLift (_0) -> begin
true
end
| uu____3916 -> begin
false
end))


let __proj__ReifiableLift__item___0 : lift_op  ->  (term * term) = (fun projectee -> (match (projectee) with
| ReifiableLift (_0) -> begin
_0
end))


let uu___is_LiftForFree : lift_op  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LiftForFree (_0) -> begin
true
end
| uu____3947 -> begin
false
end))


let __proj__LiftForFree__item___0 : lift_op  ->  term = (fun projectee -> (match (projectee) with
| LiftForFree (_0) -> begin
_0
end))

type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : lift_op}


let __proj__Mklift__item__msource : lift  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {msource = msource; mdest = mdest; lift_op = lift_op} -> begin
msource
end))


let __proj__Mklift__item__mdest : lift  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {msource = msource; mdest = mdest; lift_op = lift_op} -> begin
mdest
end))


let __proj__Mklift__item__lift_op : lift  ->  lift_op = (fun projectee -> (match (projectee) with
| {msource = msource; mdest = mdest; lift_op = lift_op} -> begin
lift_op
end))

type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string FStar_Pervasives_Native.option
| PushOptions of Prims.string FStar_Pervasives_Native.option
| PopOptions
| LightOff


let uu___is_SetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
true
end
| uu____4031 -> begin
false
end))


let __proj__SetOptions__item___0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
_0
end))


let uu___is_ResetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
true
end
| uu____4056 -> begin
false
end))


let __proj__ResetOptions__item___0 : pragma  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
_0
end))


let uu___is_PushOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PushOptions (_0) -> begin
true
end
| uu____4087 -> begin
false
end))


let __proj__PushOptions__item___0 : pragma  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| PushOptions (_0) -> begin
_0
end))


let uu___is_PopOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PopOptions -> begin
true
end
| uu____4114 -> begin
false
end))


let uu___is_LightOff : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LightOff -> begin
true
end
| uu____4125 -> begin
false
end))

type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| Friend of FStar_Ident.lid
| Include of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| TopLevelLet of (let_qualifier * (pattern * term) Prims.list)
| Main of term
| Tycon of (Prims.bool * Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option) Prims.list)
| Val of (FStar_Ident.ident * term)
| Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option)
| NewEffect of effect_decl
| SubEffect of lift
| Pragma of pragma
| Fsdoc of fsdoc
| Assume of (FStar_Ident.ident * term)
| Splice of (FStar_Ident.ident Prims.list * term) 
 and decl =
{d : decl'; drange : FStar_Range.range; doc : fsdoc FStar_Pervasives_Native.option; quals : qualifiers; attrs : attributes_} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)


let uu___is_TopLevelModule : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopLevelModule (_0) -> begin
true
end
| uu____4324 -> begin
false
end))


let __proj__TopLevelModule__item___0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| TopLevelModule (_0) -> begin
_0
end))


let uu___is_Open : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open (_0) -> begin
true
end
| uu____4343 -> begin
false
end))


let __proj__Open__item___0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Open (_0) -> begin
_0
end))


let uu___is_Friend : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Friend (_0) -> begin
true
end
| uu____4362 -> begin
false
end))


let __proj__Friend__item___0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Friend (_0) -> begin
_0
end))


let uu___is_Include : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Include (_0) -> begin
true
end
| uu____4381 -> begin
false
end))


let __proj__Include__item___0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Include (_0) -> begin
_0
end))


let uu___is_ModuleAbbrev : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_0) -> begin
true
end
| uu____4404 -> begin
false
end))


let __proj__ModuleAbbrev__item___0 : decl'  ->  (FStar_Ident.ident * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_0) -> begin
_0
end))


let uu___is_TopLevelLet : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopLevelLet (_0) -> begin
true
end
| uu____4445 -> begin
false
end))


let __proj__TopLevelLet__item___0 : decl'  ->  (let_qualifier * (pattern * term) Prims.list) = (fun projectee -> (match (projectee) with
| TopLevelLet (_0) -> begin
_0
end))


let uu___is_Main : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Main (_0) -> begin
true
end
| uu____4494 -> begin
false
end))


let __proj__Main__item___0 : decl'  ->  term = (fun projectee -> (match (projectee) with
| Main (_0) -> begin
_0
end))


let uu___is_Tycon : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tycon (_0) -> begin
true
end
| uu____4529 -> begin
false
end))


let __proj__Tycon__item___0 : decl'  ->  (Prims.bool * Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option) Prims.list) = (fun projectee -> (match (projectee) with
| Tycon (_0) -> begin
_0
end))


let uu___is_Val : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Val (_0) -> begin
true
end
| uu____4600 -> begin
false
end))


let __proj__Val__item___0 : decl'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Val (_0) -> begin
_0
end))


let uu___is_Exception : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exception (_0) -> begin
true
end
| uu____4637 -> begin
false
end))


let __proj__Exception__item___0 : decl'  ->  (FStar_Ident.ident * term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Exception (_0) -> begin
_0
end))


let uu___is_NewEffect : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NewEffect (_0) -> begin
true
end
| uu____4674 -> begin
false
end))


let __proj__NewEffect__item___0 : decl'  ->  effect_decl = (fun projectee -> (match (projectee) with
| NewEffect (_0) -> begin
_0
end))


let uu___is_SubEffect : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SubEffect (_0) -> begin
true
end
| uu____4693 -> begin
false
end))


let __proj__SubEffect__item___0 : decl'  ->  lift = (fun projectee -> (match (projectee) with
| SubEffect (_0) -> begin
_0
end))


let uu___is_Pragma : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pragma (_0) -> begin
true
end
| uu____4712 -> begin
false
end))


let __proj__Pragma__item___0 : decl'  ->  pragma = (fun projectee -> (match (projectee) with
| Pragma (_0) -> begin
_0
end))


let uu___is_Fsdoc : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fsdoc (_0) -> begin
true
end
| uu____4731 -> begin
false
end))


let __proj__Fsdoc__item___0 : decl'  ->  fsdoc = (fun projectee -> (match (projectee) with
| Fsdoc (_0) -> begin
_0
end))


let uu___is_Assume : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
true
end
| uu____4754 -> begin
false
end))


let __proj__Assume__item___0 : decl'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
_0
end))


let uu___is_Splice : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Splice (_0) -> begin
true
end
| uu____4791 -> begin
false
end))


let __proj__Splice__item___0 : decl'  ->  (FStar_Ident.ident Prims.list * term) = (fun projectee -> (match (projectee) with
| Splice (_0) -> begin
_0
end))


let __proj__Mkdecl__item__d : decl  ->  decl' = (fun projectee -> (match (projectee) with
| {d = d; drange = drange; doc = doc1; quals = quals; attrs = attrs} -> begin
d
end))


let __proj__Mkdecl__item__drange : decl  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {d = d; drange = drange; doc = doc1; quals = quals; attrs = attrs} -> begin
drange
end))


let __proj__Mkdecl__item__doc : decl  ->  fsdoc FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {d = d; drange = drange; doc = doc1; quals = quals; attrs = attrs} -> begin
doc1
end))


let __proj__Mkdecl__item__quals : decl  ->  qualifiers = (fun projectee -> (match (projectee) with
| {d = d; drange = drange; doc = doc1; quals = quals; attrs = attrs} -> begin
quals
end))


let __proj__Mkdecl__item__attrs : decl  ->  attributes_ = (fun projectee -> (match (projectee) with
| {d = d; drange = drange; doc = doc1; quals = quals; attrs = attrs} -> begin
attrs
end))


let uu___is_DefineEffect : effect_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefineEffect (_0) -> begin
true
end
| uu____4909 -> begin
false
end))


let __proj__DefineEffect__item___0 : effect_decl  ->  (FStar_Ident.ident * binder Prims.list * term * decl Prims.list) = (fun projectee -> (match (projectee) with
| DefineEffect (_0) -> begin
_0
end))


let uu___is_RedefineEffect : effect_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RedefineEffect (_0) -> begin
true
end
| uu____4972 -> begin
false
end))


let __proj__RedefineEffect__item___0 : effect_decl  ->  (FStar_Ident.ident * binder Prims.list * term) = (fun projectee -> (match (projectee) with
| RedefineEffect (_0) -> begin
_0
end))

type modul =
| Module of (FStar_Ident.lid * decl Prims.list)
| Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool)


let uu___is_Module : modul  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
true
end
| uu____5046 -> begin
false
end))


let __proj__Module__item___0 : modul  ->  (FStar_Ident.lid * decl Prims.list) = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
_0
end))


let uu___is_Interface : modul  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Interface (_0) -> begin
true
end
| uu____5092 -> begin
false
end))


let __proj__Interface__item___0 : modul  ->  (FStar_Ident.lid * decl Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| Interface (_0) -> begin
_0
end))


type file =
modul


type inputFragment =
(file, decl Prims.list) FStar_Util.either


let decl_drange : decl  ->  FStar_Range.range = (fun decl -> decl.drange)


let check_id : FStar_Ident.ident  ->  unit = (fun id1 -> (

let first_char = (FStar_String.substring id1.FStar_Ident.idText (Prims.parse_int "0") (Prims.parse_int "1"))
in (match ((Prims.op_Equality (FStar_String.lowercase first_char) first_char)) with
| true -> begin
()
end
| uu____5152 -> begin
(

let uu____5154 = (

let uu____5160 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id1.FStar_Ident.idText)
in ((FStar_Errors.Fatal_InvalidIdentifier), (uu____5160)))
in (FStar_Errors.raise_error uu____5154 id1.FStar_Ident.idRange))
end)))


let at_most_one : 'Auu____5173 . Prims.string  ->  FStar_Range.range  ->  'Auu____5173 Prims.list  ->  'Auu____5173 FStar_Pervasives_Native.option = (fun s r l -> (match (l) with
| (x)::[] -> begin
FStar_Pervasives_Native.Some (x)
end
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____5198 -> begin
(

let uu____5201 = (

let uu____5207 = (FStar_Util.format1 "At most one %s is allowed on declarations" s)
in ((FStar_Errors.Fatal_MoreThanOneDeclaration), (uu____5207)))
in (FStar_Errors.raise_error uu____5201 r))
end))


let mk_decl : decl'  ->  FStar_Range.range  ->  decoration Prims.list  ->  decl = (fun d r decorations -> (

let doc1 = (

let uu____5236 = (FStar_List.choose (fun uu___0_5241 -> (match (uu___0_5241) with
| Doc (d1) -> begin
FStar_Pervasives_Native.Some (d1)
end
| uu____5245 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in (at_most_one "fsdoc" r uu____5236))
in (

let attributes_ = (

let uu____5252 = (FStar_List.choose (fun uu___1_5261 -> (match (uu___1_5261) with
| DeclAttributes (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____5271 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in (at_most_one "attribute set" r uu____5252))
in (

let attributes_1 = (FStar_Util.dflt [] attributes_)
in (

let qualifiers = (FStar_List.choose (fun uu___2_5287 -> (match (uu___2_5287) with
| Qualifier (q) -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____5291 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in {d = d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1})))))


let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  arg_qualifier FStar_Pervasives_Native.option  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})


let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})


let mk_uminus : term  ->  FStar_Range.range  ->  FStar_Range.range  ->  level  ->  term = (fun t rminus r l -> (

let t1 = (match (t.tm) with
| Const (FStar_Const.Const_int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, width))) -> begin
Const (FStar_Const.Const_int ((((Prims.op_Hat "-" s)), (FStar_Pervasives_Native.Some (((FStar_Const.Signed), (width)))))))
end
| uu____5381 -> begin
(

let uu____5382 = (

let uu____5389 = (FStar_Ident.mk_ident (("-"), (rminus)))
in ((uu____5389), ((t)::[])))
in Op (uu____5382))
end)
in (mk_term t1 r l)))


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs ((((FStar_List.append ps p')), (body')))
end
| uu____5428 -> begin
Abs (((ps), (body)))
end))


let mk_function : (pattern * term FStar_Pervasives_Native.option * term) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = (FStar_Ident.gen r1)
in (

let uu____5468 = (

let uu____5469 = (

let uu____5476 = (

let uu____5477 = (

let uu____5478 = (

let uu____5493 = (

let uu____5494 = (

let uu____5495 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (uu____5495))
in (mk_term uu____5494 r1 Expr))
in ((uu____5493), (branches)))
in Match (uu____5478))
in (mk_term uu____5477 r2 Expr))
in ((((mk_pattern (PatVar (((x), (FStar_Pervasives_Native.None)))) r1))::[]), (uu____5476)))
in Abs (uu____5469))
in (mk_term uu____5468 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) FStar_Pervasives_Native.option = (fun p tm -> (match (((p.pat), (tm.tm))) with
| (PatVar (uu____5533), Abs (pats, body)) -> begin
FStar_Pervasives_Native.Some ((((mk_pattern (PatApp (((p), (pats)))) p.prange)), (body)))
end
| uu____5552 -> begin
FStar_Pervasives_Native.None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (

let uu____5572 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path uu____5572 r)))


let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd1 tl1 -> PatApp ((((mk_pattern (PatName (FStar_Parser_Const.cons_lid)) r)), ((hd1)::(tl1)::[]))))


let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd1 tl1 -> (mk_term (Construct (((FStar_Parser_Const.cons_lid), ((((hd1), (Nothing)))::(((tl1), (Nothing)))::[])))) r Expr))


let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd1 tl1 -> (mk_term (Construct (((FStar_Parser_Const.lexcons_lid), ((((hd1), (Nothing)))::(((tl1), (Nothing)))::[])))) r Expr))


let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct (((FStar_Parser_Const.nil_lid), ([])))) r Expr)
in (FStar_List.fold_right (fun e tl1 -> (consTerm r e tl1)) elts nil)))


let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let nil = (mk_term (Construct (((FStar_Parser_Const.lextop_lid), ([])))) r Expr)
in (FStar_List.fold_right (fun e tl1 -> (lexConsTerm r e tl1)) elts nil)))


let ml_comp : term  ->  term = (fun t -> (

let ml = (mk_term (Name (FStar_Parser_Const.effect_ML_lid)) t.range Expr)
in (

let t1 = (mk_term (App (((ml), (t), (Nothing)))) t.range Expr)
in t1)))


let tot_comp : term  ->  term = (fun t -> (

let ml = (mk_term (Name (FStar_Parser_Const.effect_Tot_lid)) t.range Expr)
in (

let t1 = (mk_term (App (((ml), (t), (Nothing)))) t.range Expr)
in t1)))


let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| uu____5767 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct (((s), (args)))) r Un)
end
| uu____5781 -> begin
(FStar_List.fold_left (fun t1 uu____5791 -> (match (uu____5791) with
| (a, imp) -> begin
(mk_term (App (((t1), (a), (imp)))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let uu____5813 = ((FStar_Parser_Const.set_empty), (FStar_Parser_Const.set_singleton), (FStar_Parser_Const.set_union), (FStar_Parser_Const.heap_addr_of_lid))
in (match (uu____5813) with
| (empty_lid, singleton_lid, union_lid, addr_of_lid) -> begin
(

let empty1 = (

let uu____5827 = (

let uu____5828 = (FStar_Ident.set_lid_range empty_lid r)
in Var (uu____5828))
in (mk_term uu____5827 r Expr))
in (

let addr_of = (

let uu____5830 = (

let uu____5831 = (FStar_Ident.set_lid_range addr_of_lid r)
in Var (uu____5831))
in (mk_term uu____5830 r Expr))
in (

let singleton1 = (

let uu____5833 = (

let uu____5834 = (FStar_Ident.set_lid_range singleton_lid r)
in Var (uu____5834))
in (mk_term uu____5833 r Expr))
in (

let union1 = (

let uu____5836 = (

let uu____5837 = (FStar_Ident.set_lid_range union_lid r)
in Var (uu____5837))
in (mk_term uu____5836 r Expr))
in (FStar_List.fold_right (fun e tl1 -> (

let e1 = (mkApp addr_of ((((e), (Nothing)))::[]) r)
in (

let single_e = (mkApp singleton1 ((((e1), (Nothing)))::[]) r)
in (mkApp union1 ((((single_e), (Nothing)))::(((tl1), (Nothing)))::[]) r)))) elts empty1)))))
end)))


let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| uu____5894 -> begin
(match (t.tm) with
| Name (s) -> begin
(

let uu____5898 = (

let uu____5899 = (

let uu____5910 = (FStar_List.map (fun a -> ((a), (Nothing))) args)
in ((s), (uu____5910)))
in Construct (uu____5899))
in (mk_term uu____5898 r Un))
end
| uu____5929 -> begin
(FStar_List.fold_left (fun t1 a -> (mk_term (App (((t1), (a), (Nothing)))) r Un)) t args)
end)
end))


let unit_const : FStar_Range.range  ->  term = (fun r -> (mk_term (Const (FStar_Const.Const_unit)) r Expr))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let admit1 = (

let admit_name = (

let uu____5948 = (

let uu____5949 = (FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r)
in Var (uu____5949))
in (mk_term uu____5948 r Expr))
in (mkExplicitApp admit_name (((unit_const r))::[]) r))
in (

let magic1 = (

let magic_name = (

let uu____5952 = (

let uu____5953 = (FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r)
in Var (uu____5953))
in (mk_term uu____5952 r Expr))
in (mkExplicitApp magic_name (((unit_const r))::[]) r))
in (

let admit_magic = (mk_term (Seq (((admit1), (magic1)))) r Expr)
in admit_magic))))


let mkWildAdmitMagic : 'Auu____5960 . FStar_Range.range  ->  (pattern * 'Auu____5960 FStar_Pervasives_Native.option * term) = (fun r -> (

let uu____5974 = (mkAdmitMagic r)
in (((mk_pattern (PatWild (FStar_Pervasives_Native.None)) r)), (FStar_Pervasives_Native.None), (uu____5974))))


let focusBranches : 'Auu____5984 . (Prims.bool * (pattern * 'Auu____5984 FStar_Pervasives_Native.option * term)) Prims.list  ->  FStar_Range.range  ->  (pattern * 'Auu____5984 FStar_Pervasives_Native.option * term) Prims.list = (fun branches r -> (

let should_filter = (FStar_Util.for_some FStar_Pervasives_Native.fst branches)
in (match (should_filter) with
| true -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_Filtered), ("Focusing on only some cases")));
(

let focussed = (

let uu____6084 = (FStar_List.filter FStar_Pervasives_Native.fst branches)
in (FStar_All.pipe_right uu____6084 (FStar_List.map FStar_Pervasives_Native.snd)))
in (

let uu____6177 = (

let uu____6188 = (mkWildAdmitMagic r)
in (uu____6188)::[])
in (FStar_List.append focussed uu____6177)));
)
end
| uu____6221 -> begin
(FStar_All.pipe_right branches (FStar_List.map FStar_Pervasives_Native.snd))
end)))


let focusLetBindings : 'Auu____6285 . (Prims.bool * ('Auu____6285 * term)) Prims.list  ->  FStar_Range.range  ->  ('Auu____6285 * term) Prims.list = (fun lbs r -> (

let should_filter = (FStar_Util.for_some FStar_Pervasives_Native.fst lbs)
in (match (should_filter) with
| true -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_Filtered), ("Focusing on only some cases in this (mutually) recursive definition")));
(FStar_List.map (fun uu____6366 -> (match (uu____6366) with
| (f, lb) -> begin
(match (f) with
| true -> begin
lb
end
| uu____6397 -> begin
(

let uu____6399 = (mkAdmitMagic r)
in (((FStar_Pervasives_Native.fst lb)), (uu____6399)))
end)
end)) lbs);
)
end
| uu____6400 -> begin
(FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd))
end)))


let focusAttrLetBindings : 'Auu____6446 'Auu____6447 . ('Auu____6446 * (Prims.bool * ('Auu____6447 * term))) Prims.list  ->  FStar_Range.range  ->  ('Auu____6446 * ('Auu____6447 * term)) Prims.list = (fun lbs r -> (

let should_filter = (FStar_Util.for_some (fun uu____6517 -> (match (uu____6517) with
| (attr, (focus, uu____6534)) -> begin
focus
end)) lbs)
in (match (should_filter) with
| true -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_Filtered), ("Focusing on only some cases in this (mutually) recursive definition")));
(FStar_List.map (fun uu____6593 -> (match (uu____6593) with
| (attr, (f, lb)) -> begin
(match (f) with
| true -> begin
((attr), (lb))
end
| uu____6650 -> begin
(

let uu____6652 = (

let uu____6657 = (mkAdmitMagic r)
in (((FStar_Pervasives_Native.fst lb)), (uu____6657)))
in ((attr), (uu____6652)))
end)
end)) lbs);
)
end
| uu____6662 -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun uu____6714 -> (match (uu____6714) with
| (attr, (uu____6737, lb)) -> begin
((attr), (lb))
end))))
end)))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (

let uu____6782 = (FStar_List.map (fun a -> ((a), (FsTypApp))) args)
in (mkApp t uu____6782 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons1 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r)
in (

let uu____6811 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons1)) r Expr) uu____6811 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons1 = (FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r)
in (

let uu____6840 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons1)) r Expr) uu____6840 r))))


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  Prims.bool  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  arg_qualifier FStar_Pervasives_Native.option  ->  binder = (fun id1 t should_bind_var refopt m implicit -> (

let b = (mk_binder (Annotated (((id1), (t)))) m Type_level implicit)
in (match (refopt) with
| FStar_Pervasives_Native.None -> begin
b
end
| FStar_Pervasives_Native.Some (phi) -> begin
(match (should_bind_var) with
| true -> begin
(mk_binder (Annotated (((id1), ((mk_term (Refine (((b), (phi)))) m Type_level))))) m Type_level implicit)
end
| uu____6897 -> begin
(

let x = (FStar_Ident.gen t.range)
in (

let b1 = (mk_binder (Annotated (((x), (t)))) m Type_level implicit)
in (mk_binder (Annotated (((id1), ((mk_term (Refine (((b1), (phi)))) m Type_level))))) m Type_level implicit)))
end)
end)))


let mkRefinedPattern : pattern  ->  term  ->  Prims.bool  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_Range.range  ->  pattern = (fun pat t should_bind_pat phi_opt t_range range -> (

let t1 = (match (phi_opt) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (phi) -> begin
(match (should_bind_pat) with
| true -> begin
(match (pat.pat) with
| PatVar (x, uu____6942) -> begin
(mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi)))) range Type_level)
end
| uu____6947 -> begin
(

let x = (FStar_Ident.gen t_range)
in (

let phi1 = (

let x_var = (

let uu____6951 = (

let uu____6952 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (uu____6952))
in (mk_term uu____6951 phi.range Formula))
in (

let pat_branch = ((pat), (FStar_Pervasives_Native.None), (phi))
in (

let otherwise_branch = (

let uu____6973 = (

let uu____6974 = (

let uu____6975 = (FStar_Ident.lid_of_path (("False")::[]) phi.range)
in Name (uu____6975))
in (mk_term uu____6974 phi.range Formula))
in (((mk_pattern (PatWild (FStar_Pervasives_Native.None)) phi.range)), (FStar_Pervasives_Native.None), (uu____6973)))
in (mk_term (Match (((x_var), ((pat_branch)::(otherwise_branch)::[])))) phi.range Formula))))
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi1)))) range Type_level)))
end)
end
| uu____7015 -> begin
(

let x = (FStar_Ident.gen t.range)
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi)))) range Type_level))
end)
end)
in (mk_pattern (PatAscribed (((pat), (((t1), (FStar_Pervasives_Native.None)))))) range)))


let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
FStar_Pervasives_Native.Some (((x), (t), (FStar_Pervasives_Native.None)))
end
| Refine ({b = Annotated (x, t); brange = uu____7066; blevel = uu____7067; aqual = uu____7068}, t') -> begin
FStar_Pervasives_Native.Some (((x), (t), (FStar_Pervasives_Native.Some (t'))))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| uu____7083 -> begin
FStar_Pervasives_Native.None
end))


let rec as_mlist : ((FStar_Ident.lid * decl) * decl Prims.list)  ->  decl Prims.list  ->  modul = (fun cur ds -> (

let uu____7127 = cur
in (match (uu____7127) with
| ((m_name, m_decl), cur1) -> begin
(match (ds) with
| [] -> begin
Module (((m_name), ((m_decl)::(FStar_List.rev cur1))))
end
| (d)::ds1 -> begin
(match (d.d) with
| TopLevelModule (m') -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedModuleDeclaration), ("Unexpected module declaration")) d.drange)
end
| uu____7158 -> begin
(as_mlist ((((m_name), (m_decl))), ((d)::cur1)) ds1)
end)
end)
end)))


let as_frag : Prims.bool  ->  FStar_Range.range  ->  decl Prims.list  ->  inputFragment = (fun is_light light_range ds -> (

let uu____7187 = (match (ds) with
| (d)::ds1 -> begin
((d), (ds1))
end
| [] -> begin
(FStar_Exn.raise FStar_Errors.Empty_frag)
end)
in (match (uu____7187) with
| (d, ds1) -> begin
(match (d.d) with
| TopLevelModule (m) -> begin
(

let ds2 = (match (is_light) with
| true -> begin
(

let uu____7225 = (mk_decl (Pragma (LightOff)) light_range [])
in (uu____7225)::ds1)
end
| uu____7226 -> begin
ds1
end)
in (

let m1 = (as_mlist ((((m), (d))), ([])) ds2)
in FStar_Util.Inl (m1)))
end
| uu____7237 -> begin
(

let ds2 = (d)::ds1
in ((FStar_List.iter (fun uu___3_7248 -> (match (uu___3_7248) with
| {d = TopLevelModule (uu____7249); drange = r; doc = uu____7251; quals = uu____7252; attrs = uu____7253} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedModuleDeclaration), ("Unexpected module declaration")) r)
end
| uu____7258 -> begin
()
end)) ds2);
FStar_Util.Inr (ds2);
))
end)
end)))


let compile_op : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun arity s r -> (

let name_of_char = (fun uu___4_7289 -> (match (uu___4_7289) with
| 38 (*&*) -> begin
"Amp"
end
| 64 (*@*) -> begin
"At"
end
| 43 (*+*) -> begin
"Plus"
end
| 45 (*-*) when (Prims.op_Equality arity (Prims.parse_int "1")) -> begin
"Minus"
end
| 45 (*-*) -> begin
"Subtraction"
end
| 126 (*~*) -> begin
"Tilde"
end
| 47 (*/*) -> begin
"Slash"
end
| 92 (*\*) -> begin
"Backslash"
end
| 60 (*<*) -> begin
"Less"
end
| 61 (*=*) -> begin
"Equals"
end
| 62 (*>*) -> begin
"Greater"
end
| 95 (*_*) -> begin
"Underscore"
end
| 124 (*|*) -> begin
"Bar"
end
| 33 (*!*) -> begin
"Bang"
end
| 94 (*^*) -> begin
"Hat"
end
| 37 (*%*) -> begin
"Percent"
end
| 42 (***) -> begin
"Star"
end
| 63 (*?*) -> begin
"Question"
end
| 58 (*:*) -> begin
"Colon"
end
| 36 (*$*) -> begin
"Dollar"
end
| 46 (*.*) -> begin
"Dot"
end
| c -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedOperatorSymbol), ((Prims.op_Hat "Unexpected operator symbol: \'" (Prims.op_Hat (FStar_Util.string_of_char c) "\'")))) r)
end))
in (match (s) with
| ".[]<-" -> begin
"op_String_Assignment"
end
| ".()<-" -> begin
"op_Array_Assignment"
end
| ".[||]<-" -> begin
"op_Brack_Lens_Assignment"
end
| ".(||)<-" -> begin
"op_Lens_Assignment"
end
| ".[]" -> begin
"op_String_Access"
end
| ".()" -> begin
"op_Array_Access"
end
| ".[||]" -> begin
"op_Brack_Lens_Access"
end
| ".(||)" -> begin
"op_Lens_Access"
end
| uu____7359 -> begin
(

let uu____7361 = (

let uu____7363 = (

let uu____7367 = (FStar_String.list_of_string s)
in (FStar_List.map name_of_char uu____7367))
in (FStar_String.concat "_" uu____7363))
in (Prims.op_Hat "op_" uu____7361))
end)))


let compile_op' : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun s r -> (compile_op (~- ((Prims.parse_int "1"))) s r))


let string_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  Prims.string = (fun uu____7409 -> (match (uu____7409) with
| (comment, keywords) -> begin
(

let uu____7444 = (

let uu____7446 = (FStar_List.map (fun uu____7460 -> (match (uu____7460) with
| (k, v1) -> begin
(Prims.op_Hat k (Prims.op_Hat "->" v1))
end)) keywords)
in (FStar_String.concat "," uu____7446))
in (Prims.op_Hat comment uu____7444))
end))


let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun uu___5_7482 -> (match (uu___5_7482) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end))


let to_string_l : 'Auu____7495 . Prims.string  ->  ('Auu____7495  ->  Prims.string)  ->  'Auu____7495 Prims.list  ->  Prims.string = (fun sep f l -> (

let uu____7525 = (FStar_List.map f l)
in (FStar_String.concat sep uu____7525)))


let imp_to_string : imp  ->  Prims.string = (fun uu___6_7536 -> (match (uu___6_7536) with
| Hash -> begin
"#"
end
| uu____7539 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, uu____7582) -> begin
(

let uu____7589 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" uu____7589))
end
| Ensures (t, uu____7593) -> begin
(

let uu____7600 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" uu____7600))
end
| Labeled (t, l, uu____7605) -> begin
(

let uu____7610 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l uu____7610))
end
| Const (c) -> begin
(FStar_Parser_Const.const_to_string c)
end
| Op (s, xs) -> begin
(

let uu____7620 = (FStar_Ident.text_of_id s)
in (

let uu____7622 = (

let uu____7624 = (FStar_List.map (fun x1 -> (FStar_All.pipe_right x1 term_to_string)) xs)
in (FStar_String.concat ", " uu____7624))
in (FStar_Util.format2 "%s(%s)" uu____7620 uu____7622)))
end
| Tvar (id1) -> begin
id1.FStar_Ident.idText
end
| Uvar (id1) -> begin
id1.FStar_Ident.idText
end
| Var (l) -> begin
l.FStar_Ident.str
end
| Name (l) -> begin
l.FStar_Ident.str
end
| Projector (rec_lid, field_id) -> begin
(

let uu____7640 = (FStar_Ident.string_of_lid rec_lid)
in (FStar_Util.format2 "%s?.%s" uu____7640 field_id.FStar_Ident.idText))
end
| Construct (l, args) -> begin
(

let uu____7657 = (to_string_l " " (fun uu____7668 -> (match (uu____7668) with
| (a, imp) -> begin
(

let uu____7676 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) uu____7676))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____7657))
end
| Abs (pats, t) -> begin
(

let uu____7686 = (to_string_l " " pat_to_string pats)
in (

let uu____7689 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" uu____7686 uu____7689)))
end
| App (t1, t2, imp) -> begin
(

let uu____7696 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____7699 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" uu____7696 (imp_to_string imp) uu____7699)))
end
| Let (Rec, ((a, (p, b)))::lbs, body) -> begin
(

let uu____7760 = (attrs_opt_to_string a)
in (

let uu____7762 = (

let uu____7764 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____7767 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" uu____7764 uu____7767)))
in (

let uu____7771 = (to_string_l " " (fun uu____7793 -> (match (uu____7793) with
| (a1, (p1, b1)) -> begin
(

let uu____7822 = (attrs_opt_to_string a1)
in (

let uu____7824 = (FStar_All.pipe_right p1 pat_to_string)
in (

let uu____7827 = (FStar_All.pipe_right b1 term_to_string)
in (FStar_Util.format3 "%sand %s=%s" uu____7822 uu____7824 uu____7827))))
end)) lbs)
in (

let uu____7831 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "%slet rec %s%s in %s" uu____7760 uu____7762 uu____7771 uu____7831)))))
end
| Let (q, ((attrs, (pat, tm)))::[], body) -> begin
(

let uu____7890 = (attrs_opt_to_string attrs)
in (

let uu____7892 = (FStar_All.pipe_right pat pat_to_string)
in (

let uu____7895 = (FStar_All.pipe_right tm term_to_string)
in (

let uu____7898 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format5 "%slet %s %s = %s in %s" uu____7890 (string_of_let_qualifier q) uu____7892 uu____7895 uu____7898)))))
end
| Let (uu____7902, uu____7903, uu____7904) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_EmptySurfaceLet), ("Internal error: found an invalid surface Let")) x.range)
end
| LetOpen (lid, t) -> begin
(

let uu____7938 = (FStar_Ident.string_of_lid lid)
in (

let uu____7940 = (term_to_string t)
in (FStar_Util.format2 "let open %s in %s" uu____7938 uu____7940)))
end
| Seq (t1, t2) -> begin
(

let uu____7945 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____7948 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" uu____7945 uu____7948)))
end
| Bind (id1, t1, t2) -> begin
(

let uu____7955 = (term_to_string t1)
in (

let uu____7957 = (term_to_string t2)
in (FStar_Util.format3 "%s <- %s; %s" id1.FStar_Ident.idText uu____7955 uu____7957)))
end
| If (t1, t2, t3) -> begin
(

let uu____7963 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____7966 = (FStar_All.pipe_right t2 term_to_string)
in (

let uu____7969 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" uu____7963 uu____7966 uu____7969))))
end
| Match (t, branches) -> begin
(

let s = (match (x.tm) with
| Match (uu____7998) -> begin
"match"
end
| TryWith (uu____8014) -> begin
"try"
end
| uu____8030 -> begin
(failwith "impossible")
end)
in (

let uu____8033 = (FStar_All.pipe_right t term_to_string)
in (

let uu____8036 = (to_string_l " | " (fun uu____8054 -> (match (uu____8054) with
| (p, w, e) -> begin
(

let uu____8071 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____8074 = (match (w) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____8079 = (term_to_string e1)
in (FStar_Util.format1 "when %s" uu____8079))
end)
in (

let uu____8082 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____8071 uu____8074 uu____8082))))
end)) branches)
in (FStar_Util.format3 "%s %s with %s" s uu____8033 uu____8036))))
end
| TryWith (t, branches) -> begin
(

let s = (match (x.tm) with
| Match (uu____8112) -> begin
"match"
end
| TryWith (uu____8128) -> begin
"try"
end
| uu____8144 -> begin
(failwith "impossible")
end)
in (

let uu____8147 = (FStar_All.pipe_right t term_to_string)
in (

let uu____8150 = (to_string_l " | " (fun uu____8168 -> (match (uu____8168) with
| (p, w, e) -> begin
(

let uu____8185 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____8188 = (match (w) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____8193 = (term_to_string e1)
in (FStar_Util.format1 "when %s" uu____8193))
end)
in (

let uu____8196 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____8185 uu____8188 uu____8196))))
end)) branches)
in (FStar_Util.format3 "%s %s with %s" s uu____8147 uu____8150))))
end
| Ascribed (t1, t2, FStar_Pervasives_Native.None) -> begin
(

let uu____8205 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____8208 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" uu____8205 uu____8208)))
end
| Ascribed (t1, t2, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____8217 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____8220 = (FStar_All.pipe_right t2 term_to_string)
in (

let uu____8223 = (FStar_All.pipe_right tac term_to_string)
in (FStar_Util.format3 "(%s : %s by %s)" uu____8217 uu____8220 uu____8223))))
end
| Record (FStar_Pervasives_Native.Some (e), fields) -> begin
(

let uu____8243 = (FStar_All.pipe_right e term_to_string)
in (

let uu____8246 = (to_string_l " " (fun uu____8257 -> (match (uu____8257) with
| (l, e1) -> begin
(

let uu____8265 = (FStar_All.pipe_right e1 term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____8265))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" uu____8243 uu____8246)))
end
| Record (FStar_Pervasives_Native.None, fields) -> begin
(

let uu____8285 = (to_string_l " " (fun uu____8296 -> (match (uu____8296) with
| (l, e) -> begin
(

let uu____8304 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____8304))
end)) fields)
in (FStar_Util.format1 "{%s}" uu____8285))
end
| Project (e, l) -> begin
(

let uu____8311 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" uu____8311 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd1)::tl1, t) -> begin
(term_to_string (mk_term (Product ((((b)::[]), ((mk_term (Product ((((hd1)::tl1), (t)))) x.range x.level))))) x.range x.level))
end
| Product ((b)::[], t) when (Prims.op_Equality x.level Type_level) -> begin
(

let uu____8334 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____8337 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" uu____8334 uu____8337)))
end
| Product ((b)::[], t) when (Prims.op_Equality x.level Kind) -> begin
(

let uu____8345 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____8348 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" uu____8345 uu____8348)))
end
| Sum (binders, t) -> begin
(

let uu____8366 = (FStar_All.pipe_right (FStar_List.append binders ((FStar_Util.Inr (t))::[])) (FStar_List.map (fun uu___7_8398 -> (match (uu___7_8398) with
| FStar_Util.Inl (b) -> begin
(binder_to_string b)
end
| FStar_Util.Inr (t1) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____8366 (FStar_String.concat " & ")))
end
| QForall (bs, (uu____8412, pats), t) -> begin
(

let uu____8441 = (to_string_l " " binder_to_string bs)
in (

let uu____8444 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (

let uu____8450 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____8441 uu____8444 uu____8450))))
end
| QExists (bs, (uu____8455, pats), t) -> begin
(

let uu____8484 = (to_string_l " " binder_to_string bs)
in (

let uu____8487 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (

let uu____8493 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____8484 uu____8487 uu____8493))))
end
| Refine (b, t) -> begin
(

let uu____8499 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____8502 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" uu____8499 uu____8502)))
end
| NamedTyp (x1, t) -> begin
(

let uu____8508 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____8508))
end
| Paren (t) -> begin
(

let uu____8513 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" uu____8513))
end
| Product (bs, t) -> begin
(

let uu____8523 = (

let uu____8525 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____8525 (FStar_String.concat ",")))
in (

let uu____8540 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" uu____8523 uu____8540)))
end
| Discrim (lid) -> begin
(

let uu____8545 = (FStar_Ident.string_of_lid lid)
in (FStar_Util.format1 "%s?" uu____8545))
end
| Attributes (ts) -> begin
(

let uu____8551 = (

let uu____8553 = (FStar_List.map term_to_string ts)
in (FStar_All.pipe_left (FStar_String.concat " ") uu____8553))
in (FStar_Util.format1 "(attributes %s)" uu____8551))
end
| Antiquote (t) -> begin
(

let uu____8565 = (term_to_string t)
in (FStar_Util.format1 "(`#%s)" uu____8565))
end
| Quote (t, Static) -> begin
(

let uu____8569 = (term_to_string t)
in (FStar_Util.format1 "(`(%s))" uu____8569))
end
| Quote (t, Dynamic) -> begin
(

let uu____8573 = (term_to_string t)
in (FStar_Util.format1 "quote (%s)" uu____8573))
end
| VQuote (t) -> begin
(

let uu____8577 = (term_to_string t)
in (FStar_Util.format1 "`%%%s" uu____8577))
end
| CalcProof (rel, init1, steps) -> begin
(

let uu____8587 = (term_to_string rel)
in (

let uu____8589 = (term_to_string init1)
in (

let uu____8591 = (

let uu____8593 = (FStar_List.map calc_step_to_string steps)
in (FStar_All.pipe_left (FStar_String.concat " ") uu____8593))
in (FStar_Util.format3 "calc (%s) { %s %s }" uu____8587 uu____8589 uu____8591))))
end))
and calc_step_to_string : calc_step  ->  Prims.string = (fun uu____8604 -> (match (uu____8604) with
| CalcStep (rel, just, next) -> begin
(

let uu____8609 = (term_to_string rel)
in (

let uu____8611 = (term_to_string just)
in (

let uu____8613 = (term_to_string next)
in (FStar_Util.format3 "%s{ %s } %s" uu____8609 uu____8611 uu____8613))))
end))
and binder_to_string : binder  ->  Prims.string = (fun x -> (

let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Ident.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Ident.idText)
end
| TAnnotated (i, t) -> begin
(

let uu____8625 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____8625))
end
| Annotated (i, t) -> begin
(

let uu____8631 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____8631))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (

let uu____8637 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" uu____8637 s))))
and aqual_to_string : arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___8_8640 -> (match (uu___8_8640) with
| FStar_Pervasives_Native.Some (Equality) -> begin
"$"
end
| FStar_Pervasives_Native.Some (Implicit) -> begin
"#"
end
| uu____8646 -> begin
""
end))
and pat_to_string : pattern  ->  Prims.string = (fun x -> (match (x.pat) with
| PatWild (FStar_Pervasives_Native.None) -> begin
"_"
end
| PatWild (uu____8653) -> begin
"#_"
end
| PatConst (c) -> begin
(FStar_Parser_Const.const_to_string c)
end
| PatApp (p, ps) -> begin
(

let uu____8664 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____8667 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" uu____8664 uu____8667)))
end
| PatTvar (i, aq) -> begin
(

let uu____8677 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" uu____8677 i.FStar_Ident.idText))
end
| PatVar (i, aq) -> begin
(

let uu____8686 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" uu____8686 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(

let uu____8693 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" uu____8693))
end
| PatTuple (l, false) -> begin
(

let uu____8704 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" uu____8704))
end
| PatTuple (l, true) -> begin
(

let uu____8715 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" uu____8715))
end
| PatRecord (l) -> begin
(

let uu____8726 = (to_string_l "; " (fun uu____8737 -> (match (uu____8737) with
| (f, e) -> begin
(

let uu____8745 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____8745))
end)) l)
in (FStar_Util.format1 "{%s}" uu____8726))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatOp (op) -> begin
(

let uu____8755 = (FStar_Ident.text_of_id op)
in (FStar_Util.format1 "(%s)" uu____8755))
end
| PatAscribed (p, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____8768 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____8771 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" uu____8768 uu____8771)))
end
| PatAscribed (p, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____8786 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____8789 = (FStar_All.pipe_right t term_to_string)
in (

let uu____8792 = (FStar_All.pipe_right tac term_to_string)
in (FStar_Util.format3 "(%s:%s by %s)" uu____8786 uu____8789 uu____8792))))
end))
and attrs_opt_to_string : term Prims.list FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___9_8796 -> (match (uu___9_8796) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (attrs) -> begin
(

let uu____8810 = (

let uu____8812 = (FStar_List.map term_to_string attrs)
in (FStar_All.pipe_right uu____8812 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____8810))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lident Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, uu____8835) -> begin
(

let uu____8840 = (FStar_Ident.lid_of_ids ((i)::[]))
in (uu____8840)::[])
end
| PatApp (p1, uu____8842) -> begin
(head_id_of_pat p1)
end
| PatAscribed (p1, uu____8848) -> begin
(head_id_of_pat p1)
end
| uu____8861 -> begin
[]
end))


let lids_of_let : 'Auu____8867 . (pattern * 'Auu____8867) Prims.list  ->  FStar_Ident.lident Prims.list = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun uu____8902 -> (match (uu____8902) with
| (p, uu____8910) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun uu___10_8917 -> (match (uu___10_8917) with
| TyconAbstract (i, uu____8920, uu____8921) -> begin
i.FStar_Ident.idText
end
| TyconAbbrev (i, uu____8931, uu____8932, uu____8933) -> begin
i.FStar_Ident.idText
end
| TyconRecord (i, uu____8943, uu____8944, uu____8945) -> begin
i.FStar_Ident.idText
end
| TyconVariant (i, uu____8975, uu____8976, uu____8977) -> begin
i.FStar_Ident.idText
end))


let decl_to_string : decl  ->  Prims.string = (fun d -> (match (d.d) with
| TopLevelModule (l) -> begin
(Prims.op_Hat "module " l.FStar_Ident.str)
end
| Open (l) -> begin
(Prims.op_Hat "open " l.FStar_Ident.str)
end
| Friend (l) -> begin
(Prims.op_Hat "friend " l.FStar_Ident.str)
end
| Include (l) -> begin
(Prims.op_Hat "include " l.FStar_Ident.str)
end
| ModuleAbbrev (i, l) -> begin
(FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText l.FStar_Ident.str)
end
| TopLevelLet (uu____9035, pats) -> begin
(

let uu____9049 = (

let uu____9051 = (

let uu____9055 = (lids_of_let pats)
in (FStar_All.pipe_right uu____9055 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right uu____9051 (FStar_String.concat ", ")))
in (Prims.op_Hat "let " uu____9049))
end
| Main (uu____9072) -> begin
"main ..."
end
| Assume (i, uu____9075) -> begin
(Prims.op_Hat "assume " i.FStar_Ident.idText)
end
| Tycon (uu____9077, uu____9078, tys) -> begin
(

let uu____9100 = (

let uu____9102 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____9127 -> (match (uu____9127) with
| (x, uu____9136) -> begin
(id_of_tycon x)
end))))
in (FStar_All.pipe_right uu____9102 (FStar_String.concat ", ")))
in (Prims.op_Hat "type " uu____9100))
end
| Val (i, uu____9148) -> begin
(Prims.op_Hat "val " i.FStar_Ident.idText)
end
| Exception (i, uu____9151) -> begin
(Prims.op_Hat "exception " i.FStar_Ident.idText)
end
| NewEffect (DefineEffect (i, uu____9158, uu____9159, uu____9160)) -> begin
(Prims.op_Hat "new_effect " i.FStar_Ident.idText)
end
| NewEffect (RedefineEffect (i, uu____9171, uu____9172)) -> begin
(Prims.op_Hat "new_effect " i.FStar_Ident.idText)
end
| Splice (ids, t) -> begin
(

let uu____9184 = (

let uu____9186 = (

let uu____9188 = (FStar_List.map (fun i -> i.FStar_Ident.idText) ids)
in (FStar_All.pipe_left (FStar_String.concat ";") uu____9188))
in (

let uu____9200 = (

let uu____9202 = (

let uu____9204 = (term_to_string t)
in (Prims.op_Hat uu____9204 ")"))
in (Prims.op_Hat "] (" uu____9202))
in (Prims.op_Hat uu____9186 uu____9200)))
in (Prims.op_Hat "splice[" uu____9184))
end
| SubEffect (uu____9209) -> begin
"sub_effect"
end
| Pragma (uu____9211) -> begin
"pragma"
end
| Fsdoc (uu____9213) -> begin
"fsdoc"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| Module (uu____9223, decls) -> begin
(

let uu____9229 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right uu____9229 (FStar_String.concat "\n")))
end
| Interface (uu____9244, decls, uu____9246) -> begin
(

let uu____9253 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right uu____9253 (FStar_String.concat "\n")))
end))


let decl_is_val : FStar_Ident.ident  ->  decl  ->  Prims.bool = (fun id1 decl -> (match (decl.d) with
| Val (id', uu____9282) -> begin
(FStar_Ident.ident_equals id1 id')
end
| uu____9283 -> begin
false
end))


let thunk : term  ->  term = (fun ens -> (

let wildpat = (mk_pattern (PatWild (FStar_Pervasives_Native.None)) ens.range)
in (mk_term (Abs ((((wildpat)::[]), (ens)))) ens.range Expr)))


let idents_of_binders : binder Prims.list  ->  FStar_Range.range  ->  FStar_Ident.ident Prims.list = (fun bs r -> (FStar_All.pipe_right bs (FStar_List.map (fun b -> (match (b.b) with
| Variable (i) -> begin
i
end
| TVariable (i) -> begin
i
end
| Annotated (i, uu____9321) -> begin
i
end
| TAnnotated (i, uu____9323) -> begin
i
end
| NoName (uu____9324) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingQuantifierBinder), ("Wildcard binders in quantifiers are not allowed")) r)
end)))))




