
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
| uu____4 -> begin
false
end))


let uu___is_Expr : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Expr -> begin
true
end
| uu____8 -> begin
false
end))


let uu___is_Type_level : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Type_level -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Kind : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kind -> begin
true
end
| uu____16 -> begin
false
end))


let uu___is_Formula : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Formula -> begin
true
end
| uu____20 -> begin
false
end))

type imp =
| FsTypApp
| Hash
| UnivApp
| Nothing


let uu___is_FsTypApp : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FsTypApp -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Hash : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Hash -> begin
true
end
| uu____28 -> begin
false
end))


let uu___is_UnivApp : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivApp -> begin
true
end
| uu____32 -> begin
false
end))


let uu___is_Nothing : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Nothing -> begin
true
end
| uu____36 -> begin
false
end))

type arg_qualifier =
| Implicit
| Equality


let uu___is_Implicit : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Equality : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equality -> begin
true
end
| uu____44 -> begin
false
end))


type aqual =
arg_qualifier FStar_Pervasives_Native.option

type let_qualifier =
| NoLetQualifier
| Rec
| Mutable


let uu___is_NoLetQualifier : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoLetQualifier -> begin
true
end
| uu____50 -> begin
false
end))


let uu___is_Rec : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec -> begin
true
end
| uu____54 -> begin
false
end))


let uu___is_Mutable : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable -> begin
true
end
| uu____58 -> begin
false
end))

type quote_kind =
| Static
| Dynamic


let uu___is_Static : quote_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Static -> begin
true
end
| uu____62 -> begin
false
end))


let uu___is_Dynamic : quote_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dynamic -> begin
true
end
| uu____66 -> begin
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
| Sum of (binder Prims.list * term)
| QForall of (binder Prims.list * term Prims.list Prims.list * term)
| QExists of (binder Prims.list * term Prims.list Prims.list * term)
| Refine of (binder * term)
| NamedTyp of (FStar_Ident.ident * term)
| Paren of term
| Requires of (term * Prims.string FStar_Pervasives_Native.option)
| Ensures of (term * Prims.string FStar_Pervasives_Native.option)
| Labeled of (term * Prims.string * Prims.bool)
| Discrim of FStar_Ident.lid
| Attributes of term Prims.list
| Antiquote of (Prims.bool * term)
| Quote of (term * quote_kind)
| VQuote of term 
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


let uu___is_Wild : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Wild -> begin
true
end
| uu____558 -> begin
false
end))


let uu___is_Const : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____563 -> begin
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
| uu____581 -> begin
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
| uu____611 -> begin
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
| uu____623 -> begin
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
| uu____635 -> begin
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
| uu____647 -> begin
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
| uu____663 -> begin
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
| uu____697 -> begin
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
| uu____745 -> begin
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
| uu____781 -> begin
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
| uu____831 -> begin
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
| uu____907 -> begin
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
| uu____935 -> begin
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
| uu____965 -> begin
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
| uu____1001 -> begin
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
| uu____1045 -> begin
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
| uu____1113 -> begin
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
| uu____1175 -> begin
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
| uu____1223 -> begin
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
| uu____1275 -> begin
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
| uu____1305 -> begin
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
| uu____1341 -> begin
false
end))


let __proj__Sum__item___0 : term'  ->  (binder Prims.list * term) = (fun projectee -> (match (projectee) with
| Sum (_0) -> begin
_0
end))


let uu___is_QForall : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QForall (_0) -> begin
true
end
| uu____1383 -> begin
false
end))


let __proj__QForall__item___0 : term'  ->  (binder Prims.list * term Prims.list Prims.list * term) = (fun projectee -> (match (projectee) with
| QForall (_0) -> begin
_0
end))


let uu___is_QExists : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QExists (_0) -> begin
true
end
| uu____1443 -> begin
false
end))


let __proj__QExists__item___0 : term'  ->  (binder Prims.list * term Prims.list Prims.list * term) = (fun projectee -> (match (projectee) with
| QExists (_0) -> begin
_0
end))


let uu___is_Refine : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Refine (_0) -> begin
true
end
| uu____1495 -> begin
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
| uu____1523 -> begin
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
| uu____1547 -> begin
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
| uu____1565 -> begin
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
| uu____1601 -> begin
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
| uu____1637 -> begin
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
| uu____1667 -> begin
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
| uu____1681 -> begin
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
| uu____1703 -> begin
false
end))


let __proj__Antiquote__item___0 : term'  ->  (Prims.bool * term) = (fun projectee -> (match (projectee) with
| Antiquote (_0) -> begin
_0
end))


let uu___is_Quote : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quote (_0) -> begin
true
end
| uu____1731 -> begin
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
| uu____1755 -> begin
false
end))


let __proj__VQuote__item___0 : term'  ->  term = (fun projectee -> (match (projectee) with
| VQuote (_0) -> begin
_0
end))


let __proj__Mkterm__item__tm : term  ->  term' = (fun projectee -> (match (projectee) with
| {tm = __fname__tm; range = __fname__range; level = __fname__level} -> begin
__fname__tm
end))


let __proj__Mkterm__item__range : term  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {tm = __fname__tm; range = __fname__range; level = __fname__level} -> begin
__fname__range
end))


let __proj__Mkterm__item__level : term  ->  level = (fun projectee -> (match (projectee) with
| {tm = __fname__tm; range = __fname__range; level = __fname__level} -> begin
__fname__level
end))


let uu___is_Variable : binder'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Variable (_0) -> begin
true
end
| uu____1785 -> begin
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
| uu____1797 -> begin
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
| uu____1813 -> begin
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
| uu____1841 -> begin
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
| uu____1865 -> begin
false
end))


let __proj__NoName__item___0 : binder'  ->  term = (fun projectee -> (match (projectee) with
| NoName (_0) -> begin
_0
end))


let __proj__Mkbinder__item__b : binder  ->  binder' = (fun projectee -> (match (projectee) with
| {b = __fname__b; brange = __fname__brange; blevel = __fname__blevel; aqual = __fname__aqual} -> begin
__fname__b
end))


let __proj__Mkbinder__item__brange : binder  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {b = __fname__b; brange = __fname__brange; blevel = __fname__blevel; aqual = __fname__aqual} -> begin
__fname__brange
end))


let __proj__Mkbinder__item__blevel : binder  ->  level = (fun projectee -> (match (projectee) with
| {b = __fname__b; brange = __fname__brange; blevel = __fname__blevel; aqual = __fname__aqual} -> begin
__fname__blevel
end))


let __proj__Mkbinder__item__aqual : binder  ->  aqual = (fun projectee -> (match (projectee) with
| {b = __fname__b; brange = __fname__brange; blevel = __fname__blevel; aqual = __fname__aqual} -> begin
__fname__aqual
end))


let uu___is_PatWild : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatWild -> begin
true
end
| uu____1904 -> begin
false
end))


let uu___is_PatConst : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatConst (_0) -> begin
true
end
| uu____1909 -> begin
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
| uu____1927 -> begin
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
| uu____1963 -> begin
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
| uu____1993 -> begin
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
| uu____2011 -> begin
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
| uu____2043 -> begin
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
| uu____2067 -> begin
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
| uu____2103 -> begin
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
| uu____2143 -> begin
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
| uu____2187 -> begin
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
| uu____2205 -> begin
false
end))


let __proj__PatOp__item___0 : pattern'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| PatOp (_0) -> begin
_0
end))


let __proj__Mkpattern__item__pat : pattern  ->  pattern' = (fun projectee -> (match (projectee) with
| {pat = __fname__pat; prange = __fname__prange} -> begin
__fname__pat
end))


let __proj__Mkpattern__item__prange : pattern  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {pat = __fname__pat; prange = __fname__prange} -> begin
__fname__prange
end))


type attributes_ =
term Prims.list


type branch =
(pattern * term FStar_Pervasives_Native.option * term)


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
| uu____2343 -> begin
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
| uu____2397 -> begin
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
| uu____2467 -> begin
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
| uu____2571 -> begin
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
| uu____2660 -> begin
false
end))


let uu___is_Abstract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abstract -> begin
true
end
| uu____2664 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____2668 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____2672 -> begin
false
end))


let uu___is_Assumption : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumption -> begin
true
end
| uu____2676 -> begin
false
end))


let uu___is_DefaultEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefaultEffect -> begin
true
end
| uu____2680 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____2684 -> begin
false
end))


let uu___is_Effect_qual : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect_qual -> begin
true
end
| uu____2688 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____2692 -> begin
false
end))


let uu___is_Inline : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline -> begin
true
end
| uu____2696 -> begin
false
end))


let uu___is_Visible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible -> begin
true
end
| uu____2700 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____2704 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____2708 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____2712 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____2716 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____2720 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable -> begin
true
end
| uu____2724 -> begin
false
end))


let uu___is_Opaque : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Opaque -> begin
true
end
| uu____2728 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____2732 -> begin
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
| uu____2753 -> begin
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
| uu____2767 -> begin
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
| uu____2785 -> begin
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
| uu____2813 -> begin
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
| uu____2829 -> begin
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
| uu____2853 -> begin
false
end))


let __proj__LiftForFree__item___0 : lift_op  ->  term = (fun projectee -> (match (projectee) with
| LiftForFree (_0) -> begin
_0
end))

type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : lift_op}


let __proj__Mklift__item__msource : lift  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mdest = __fname__mdest; lift_op = __fname__lift_op} -> begin
__fname__msource
end))


let __proj__Mklift__item__mdest : lift  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mdest = __fname__mdest; lift_op = __fname__lift_op} -> begin
__fname__mdest
end))


let __proj__Mklift__item__lift_op : lift  ->  lift_op = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mdest = __fname__mdest; lift_op = __fname__lift_op} -> begin
__fname__lift_op
end))

type pragma =
| SetOptions of Prims.string
| ResetOptions of Prims.string FStar_Pervasives_Native.option
| LightOff


let uu___is_SetOptions : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SetOptions (_0) -> begin
true
end
| uu____2905 -> begin
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
| uu____2919 -> begin
false
end))


let __proj__ResetOptions__item___0 : pragma  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| ResetOptions (_0) -> begin
_0
end))


let uu___is_LightOff : pragma  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LightOff -> begin
true
end
| uu____2936 -> begin
false
end))

type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| Include of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| TopLevelLet of (let_qualifier * (pattern * term) Prims.list)
| Main of term
| Tycon of (Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option) Prims.list)
| Val of (FStar_Ident.ident * term)
| Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option)
| NewEffect of effect_decl
| SubEffect of lift
| Pragma of pragma
| Fsdoc of fsdoc
| Assume of (FStar_Ident.ident * term)
| Splice of term 
 and decl =
{d : decl'; drange : FStar_Range.range; doc : fsdoc FStar_Pervasives_Native.option; quals : qualifiers; attrs : attributes_} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)


let uu___is_TopLevelModule : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopLevelModule (_0) -> begin
true
end
| uu____3091 -> begin
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
| uu____3103 -> begin
false
end))


let __proj__Open__item___0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Open (_0) -> begin
_0
end))


let uu___is_Include : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Include (_0) -> begin
true
end
| uu____3115 -> begin
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
| uu____3131 -> begin
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
| uu____3165 -> begin
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
| uu____3207 -> begin
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
| uu____3231 -> begin
false
end))


let __proj__Tycon__item___0 : decl'  ->  (Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option) Prims.list) = (fun projectee -> (match (projectee) with
| Tycon (_0) -> begin
_0
end))


let uu___is_Val : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Val (_0) -> begin
true
end
| uu____3283 -> begin
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
| uu____3313 -> begin
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
| uu____3343 -> begin
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
| uu____3355 -> begin
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
| uu____3367 -> begin
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
| uu____3379 -> begin
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
| uu____3395 -> begin
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
| uu____3419 -> begin
false
end))


let __proj__Splice__item___0 : decl'  ->  term = (fun projectee -> (match (projectee) with
| Splice (_0) -> begin
_0
end))


let __proj__Mkdecl__item__d : decl  ->  decl' = (fun projectee -> (match (projectee) with
| {d = __fname__d; drange = __fname__drange; doc = __fname__doc; quals = __fname__quals; attrs = __fname__attrs} -> begin
__fname__d
end))


let __proj__Mkdecl__item__drange : decl  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {d = __fname__d; drange = __fname__drange; doc = __fname__doc; quals = __fname__quals; attrs = __fname__attrs} -> begin
__fname__drange
end))


let __proj__Mkdecl__item__doc : decl  ->  fsdoc FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {d = __fname__d; drange = __fname__drange; doc = __fname__doc; quals = __fname__quals; attrs = __fname__attrs} -> begin
__fname__doc
end))


let __proj__Mkdecl__item__quals : decl  ->  qualifiers = (fun projectee -> (match (projectee) with
| {d = __fname__d; drange = __fname__drange; doc = __fname__doc; quals = __fname__quals; attrs = __fname__attrs} -> begin
__fname__quals
end))


let __proj__Mkdecl__item__attrs : decl  ->  attributes_ = (fun projectee -> (match (projectee) with
| {d = __fname__d; drange = __fname__drange; doc = __fname__doc; quals = __fname__quals; attrs = __fname__attrs} -> begin
__fname__attrs
end))


let uu___is_DefineEffect : effect_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefineEffect (_0) -> begin
true
end
| uu____3497 -> begin
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
| uu____3553 -> begin
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
| uu____3617 -> begin
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
| uu____3655 -> begin
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


let check_id : FStar_Ident.ident  ->  Prims.unit = (fun id1 -> (

let first_char = (FStar_String.substring id1.FStar_Ident.idText (Prims.parse_int "0") (Prims.parse_int "1"))
in (match ((Prims.op_Equality (FStar_String.lowercase first_char) first_char)) with
| true -> begin
()
end
| uu____3700 -> begin
(

let uu____3701 = (

let uu____3706 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id1.FStar_Ident.idText)
in ((FStar_Errors.Fatal_InvalidIdentifier), (uu____3706)))
in (FStar_Errors.raise_error uu____3701 id1.FStar_Ident.idRange))
end)))


let at_most_one : 'Auu____3711 . Prims.string  ->  FStar_Range.range  ->  'Auu____3711 Prims.list  ->  'Auu____3711 FStar_Pervasives_Native.option = (fun s r l -> (match (l) with
| (x)::[] -> begin
FStar_Pervasives_Native.Some (x)
end
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____3731 -> begin
(

let uu____3734 = (

let uu____3739 = (FStar_Util.format1 "At most one %s is allowed on declarations" s)
in ((FStar_Errors.Fatal_MoreThanOneDeclaration), (uu____3739)))
in (FStar_Errors.raise_error uu____3734 r))
end))


let mk_decl : decl'  ->  FStar_Range.range  ->  decoration Prims.list  ->  decl = (fun d r decorations -> (

let doc1 = (

let uu____3758 = (FStar_List.choose (fun uu___39_3763 -> (match (uu___39_3763) with
| Doc (d1) -> begin
FStar_Pervasives_Native.Some (d1)
end
| uu____3767 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in (at_most_one "fsdoc" r uu____3758))
in (

let attributes_ = (

let uu____3773 = (FStar_List.choose (fun uu___40_3782 -> (match (uu___40_3782) with
| DeclAttributes (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____3792 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in (at_most_one "attribute set" r uu____3773))
in (

let attributes_1 = (FStar_Util.dflt [] attributes_)
in (

let qualifiers = (FStar_List.choose (fun uu___41_3807 -> (match (uu___41_3807) with
| Qualifier (q) -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____3811 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in {d = d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1})))))


let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})


let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})


let mk_uminus : term  ->  FStar_Range.range  ->  FStar_Range.range  ->  level  ->  term = (fun t rminus r l -> (

let t1 = (match (t.tm) with
| Const (FStar_Const.Const_int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, width))) -> begin
Const (FStar_Const.Const_int ((((Prims.strcat "-" s)), (FStar_Pervasives_Native.Some (((FStar_Const.Signed), (width)))))))
end
| uu____3868 -> begin
Op ((((FStar_Ident.mk_ident (("-"), (rminus)))), ((t)::[])))
end)
in (mk_term t1 r l)))


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs ((((FStar_List.append ps p')), (body')))
end
| uu____3895 -> begin
Abs (((ps), (body)))
end))


let mk_function : (pattern * term FStar_Pervasives_Native.option * term) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = (

let i = (FStar_Parser_Const.next_id ())
in (FStar_Ident.gen r1))
in (

let uu____3929 = (

let uu____3930 = (

let uu____3937 = (

let uu____3938 = (

let uu____3939 = (

let uu____3954 = (

let uu____3955 = (

let uu____3956 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (uu____3956))
in (mk_term uu____3955 r1 Expr))
in ((uu____3954), (branches)))
in Match (uu____3939))
in (mk_term uu____3938 r2 Expr))
in ((((mk_pattern (PatVar (((x), (FStar_Pervasives_Native.None)))) r1))::[]), (uu____3937)))
in Abs (uu____3930))
in (mk_term uu____3929 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) FStar_Pervasives_Native.option = (fun p tm -> (match (((p.pat), (tm.tm))) with
| (PatVar (uu____3989), Abs (pats, body)) -> begin
FStar_Pervasives_Native.Some ((((mk_pattern (PatApp (((p), (pats)))) p.prange)), (body)))
end
| uu____4008 -> begin
FStar_Pervasives_Native.None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (

let uu____4023 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path uu____4023 r)))


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
| uu____4176 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct (((s), (args)))) r Un)
end
| uu____4190 -> begin
(FStar_List.fold_left (fun t1 uu____4200 -> (match (uu____4200) with
| (a, imp) -> begin
(mk_term (App (((t1), (a), (imp)))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let uu____4217 = ((FStar_Parser_Const.set_empty), (FStar_Parser_Const.set_singleton), (FStar_Parser_Const.set_union), (FStar_Parser_Const.heap_addr_of_lid))
in (match (uu____4217) with
| (empty_lid, singleton_lid, union_lid, addr_of_lid) -> begin
(

let empty1 = (mk_term (Var ((FStar_Ident.set_lid_range empty_lid r))) r Expr)
in (

let addr_of1 = (mk_term (Var ((FStar_Ident.set_lid_range addr_of_lid r))) r Expr)
in (

let singleton1 = (mk_term (Var ((FStar_Ident.set_lid_range singleton_lid r))) r Expr)
in (

let union1 = (mk_term (Var ((FStar_Ident.set_lid_range union_lid r))) r Expr)
in (FStar_List.fold_right (fun e tl1 -> (

let e1 = (mkApp addr_of1 ((((e), (Nothing)))::[]) r)
in (

let single_e = (mkApp singleton1 ((((e1), (Nothing)))::[]) r)
in (mkApp union1 ((((single_e), (Nothing)))::(((tl1), (Nothing)))::[]) r)))) elts empty1)))))
end)))


let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| uu____4283 -> begin
(match (t.tm) with
| Name (s) -> begin
(

let uu____4287 = (

let uu____4288 = (

let uu____4299 = (FStar_List.map (fun a -> ((a), (Nothing))) args)
in ((s), (uu____4299)))
in Construct (uu____4288))
in (mk_term uu____4287 r Un))
end
| uu____4318 -> begin
(FStar_List.fold_left (fun t1 a -> (mk_term (App (((t1), (a), (Nothing)))) r Un)) t args)
end)
end))


let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (

let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (

let admit1 = (

let admit_name = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r))) r Expr)
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (

let magic1 = (

let magic_name = (mk_term (Var ((FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r))) r Expr)
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (

let admit_magic = (mk_term (Seq (((admit1), (magic1)))) r Expr)
in admit_magic)))))


let mkWildAdmitMagic : 'Auu____4334 . FStar_Range.range  ->  (pattern * 'Auu____4334 FStar_Pervasives_Native.option * term) = (fun r -> (

let uu____4347 = (mkAdmitMagic r)
in (((mk_pattern PatWild r)), (FStar_Pervasives_Native.None), (uu____4347))))


let focusBranches : 'Auu____4353 . (Prims.bool * (pattern * 'Auu____4353 FStar_Pervasives_Native.option * term)) Prims.list  ->  FStar_Range.range  ->  (pattern * 'Auu____4353 FStar_Pervasives_Native.option * term) Prims.list = (fun branches r -> (

let should_filter = (FStar_Util.for_some FStar_Pervasives_Native.fst branches)
in (match (should_filter) with
| true -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_Filtered), ("Focusing on only some cases")));
(

let focussed = (

let uu____4443 = (FStar_List.filter FStar_Pervasives_Native.fst branches)
in (FStar_All.pipe_right uu____4443 (FStar_List.map FStar_Pervasives_Native.snd)))
in (

let uu____4530 = (

let uu____4541 = (mkWildAdmitMagic r)
in (uu____4541)::[])
in (FStar_List.append focussed uu____4530)));
)
end
| uu____4574 -> begin
(FStar_All.pipe_right branches (FStar_List.map FStar_Pervasives_Native.snd))
end)))


let focusLetBindings : 'Auu____4630 . (Prims.bool * ('Auu____4630 * term)) Prims.list  ->  FStar_Range.range  ->  ('Auu____4630 * term) Prims.list = (fun lbs r -> (

let should_filter = (FStar_Util.for_some FStar_Pervasives_Native.fst lbs)
in (match (should_filter) with
| true -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_Filtered), ("Focusing on only some cases in this (mutually) recursive definition")));
(FStar_List.map (fun uu____4700 -> (match (uu____4700) with
| (f, lb) -> begin
(match (f) with
| true -> begin
lb
end
| uu____4727 -> begin
(

let uu____4728 = (mkAdmitMagic r)
in (((FStar_Pervasives_Native.fst lb)), (uu____4728)))
end)
end)) lbs);
)
end
| uu____4729 -> begin
(FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd))
end)))


let focusAttrLetBindings : 'Auu____4766 'Auu____4767 . ('Auu____4766 * (Prims.bool * ('Auu____4767 * term))) Prims.list  ->  FStar_Range.range  ->  ('Auu____4766 * ('Auu____4767 * term)) Prims.list = (fun lbs r -> (

let should_filter = (FStar_Util.for_some (fun uu____4831 -> (match (uu____4831) with
| (attr, (focus, uu____4846)) -> begin
focus
end)) lbs)
in (match (should_filter) with
| true -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_Filtered), ("Focusing on only some cases in this (mutually) recursive definition")));
(FStar_List.map (fun uu____4898 -> (match (uu____4898) with
| (attr, (f, lb)) -> begin
(match (f) with
| true -> begin
((attr), (lb))
end
| uu____4950 -> begin
(

let uu____4951 = (

let uu____4956 = (mkAdmitMagic r)
in (((FStar_Pervasives_Native.fst lb)), (uu____4956)))
in ((attr), (uu____4951)))
end)
end)) lbs);
)
end
| uu____4961 -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun uu____5010 -> (match (uu____5010) with
| (attr, (uu____5032, lb)) -> begin
((attr), (lb))
end))))
end)))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (

let uu____5067 = (FStar_List.map (fun a -> ((a), (FsTypApp))) args)
in (mkApp t uu____5067 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons1 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r)
in (

let uu____5091 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons1)) r Expr) uu____5091 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons1 = (FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r)
in (

let uu____5115 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons1)) r Expr) uu____5115 r))))


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  Prims.bool  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id1 t should_bind_var refopt m implicit -> (

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
| uu____5152 -> begin
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
| PatVar (x, uu____5180) -> begin
(mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi)))) range Type_level)
end
| uu____5185 -> begin
(

let x = (FStar_Ident.gen t_range)
in (

let phi1 = (

let x_var = (

let uu____5189 = (

let uu____5190 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (uu____5190))
in (mk_term uu____5189 phi.range Formula))
in (

let pat_branch = ((pat), (FStar_Pervasives_Native.None), (phi))
in (

let otherwise_branch = (

let uu____5211 = (

let uu____5212 = (

let uu____5213 = (FStar_Ident.lid_of_path (("False")::[]) phi.range)
in Name (uu____5213))
in (mk_term uu____5212 phi.range Formula))
in (((mk_pattern PatWild phi.range)), (FStar_Pervasives_Native.None), (uu____5211)))
in (mk_term (Match (((x_var), ((pat_branch)::(otherwise_branch)::[])))) phi.range Formula))))
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi1)))) range Type_level)))
end)
end
| uu____5250 -> begin
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
| Refine ({b = Annotated (x, t); brange = uu____5297; blevel = uu____5298; aqual = uu____5299}, t') -> begin
FStar_Pervasives_Native.Some (((x), (t), (FStar_Pervasives_Native.Some (t'))))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| uu____5312 -> begin
FStar_Pervasives_Native.None
end))


let rec as_mlist : ((FStar_Ident.lid * decl) * decl Prims.list)  ->  decl Prims.list  ->  modul = (fun cur ds -> (

let uu____5351 = cur
in (match (uu____5351) with
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
| uu____5380 -> begin
(as_mlist ((((m_name), (m_decl))), ((d)::cur1)) ds1)
end)
end)
end)))


let as_frag : Prims.bool  ->  FStar_Range.range  ->  decl Prims.list  ->  inputFragment = (fun is_light light_range ds -> (

let uu____5400 = (match (ds) with
| (d)::ds1 -> begin
((d), (ds1))
end
| [] -> begin
(FStar_Exn.raise FStar_Errors.Empty_frag)
end)
in (match (uu____5400) with
| (d, ds1) -> begin
(match (d.d) with
| TopLevelModule (m) -> begin
(

let ds2 = (match (is_light) with
| true -> begin
(

let uu____5437 = (mk_decl (Pragma (LightOff)) light_range [])
in (uu____5437)::ds1)
end
| uu____5438 -> begin
ds1
end)
in (

let m1 = (as_mlist ((((m), (d))), ([])) ds2)
in FStar_Util.Inl (m1)))
end
| uu____5448 -> begin
(

let ds2 = (d)::ds1
in ((FStar_List.iter (fun uu___42_5459 -> (match (uu___42_5459) with
| {d = TopLevelModule (uu____5460); drange = r; doc = uu____5462; quals = uu____5463; attrs = uu____5464} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedModuleDeclaration), ("Unexpected module declaration")) r)
end
| uu____5467 -> begin
()
end)) ds2);
FStar_Util.Inr (ds2);
))
end)
end)))


let compile_op : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun arity s r -> (

let name_of_char = (fun uu___43_5483 -> (match (uu___43_5483) with
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
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedOperatorSymbol), ((Prims.strcat "Unexpected operator symbol: \'" (Prims.strcat (FStar_Util.string_of_char c) "\'")))) r)
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
| uu____5508 -> begin
(

let uu____5509 = (

let uu____5510 = (

let uu____5513 = (FStar_String.list_of_string s)
in (FStar_List.map name_of_char uu____5513))
in (FStar_String.concat "_" uu____5510))
in (Prims.strcat "op_" uu____5509))
end)))


let compile_op' : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun s r -> (compile_op (~- ((Prims.parse_int "1"))) s r))


let string_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  Prims.string = (fun uu____5536 -> (match (uu____5536) with
| (comment, keywords) -> begin
(

let uu____5561 = (

let uu____5562 = (FStar_List.map (fun uu____5572 -> (match (uu____5572) with
| (k, v1) -> begin
(Prims.strcat k (Prims.strcat "->" v1))
end)) keywords)
in (FStar_String.concat "," uu____5562))
in (Prims.strcat comment uu____5561))
end))


let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun uu___44_5581 -> (match (uu___44_5581) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end
| Mutable -> begin
"mutable"
end))


let to_string_l : 'Auu____5586 . Prims.string  ->  ('Auu____5586  ->  Prims.string)  ->  'Auu____5586 Prims.list  ->  Prims.string = (fun sep f l -> (

let uu____5608 = (FStar_List.map f l)
in (FStar_String.concat sep uu____5608)))


let imp_to_string : imp  ->  Prims.string = (fun uu___45_5613 -> (match (uu___45_5613) with
| Hash -> begin
"#"
end
| uu____5614 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, uu____5631) -> begin
(

let uu____5636 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" uu____5636))
end
| Ensures (t, uu____5638) -> begin
(

let uu____5643 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" uu____5643))
end
| Labeled (t, l, uu____5646) -> begin
(

let uu____5647 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l uu____5647))
end
| Const (c) -> begin
(FStar_Parser_Const.const_to_string c)
end
| Op (s, xs) -> begin
(

let uu____5655 = (

let uu____5656 = (FStar_List.map (fun x1 -> (FStar_All.pipe_right x1 term_to_string)) xs)
in (FStar_String.concat ", " uu____5656))
in (FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____5655))
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
| Construct (l, args) -> begin
(

let uu____5679 = (to_string_l " " (fun uu____5688 -> (match (uu____5688) with
| (a, imp) -> begin
(

let uu____5695 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) uu____5695))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____5679))
end
| Abs (pats, t) -> begin
(

let uu____5702 = (to_string_l " " pat_to_string pats)
in (

let uu____5703 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" uu____5702 uu____5703)))
end
| App (t1, t2, imp) -> begin
(

let uu____5707 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5708 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" uu____5707 (imp_to_string imp) uu____5708)))
end
| Let (Rec, ((a, (p, b)))::lbs, body) -> begin
(

let uu____5766 = (attrs_opt_to_string a)
in (

let uu____5767 = (

let uu____5768 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____5769 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" uu____5768 uu____5769)))
in (

let uu____5770 = (to_string_l " " (fun uu____5790 -> (match (uu____5790) with
| (a1, (p1, b1)) -> begin
(

let uu____5818 = (attrs_opt_to_string a1)
in (

let uu____5819 = (FStar_All.pipe_right p1 pat_to_string)
in (

let uu____5820 = (FStar_All.pipe_right b1 term_to_string)
in (FStar_Util.format3 "%sand %s=%s" uu____5818 uu____5819 uu____5820))))
end)) lbs)
in (

let uu____5821 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "%slet rec %s%s in %s" uu____5766 uu____5767 uu____5770 uu____5821)))))
end
| Let (q, ((attrs, (pat, tm)))::[], body) -> begin
(

let uu____5877 = (attrs_opt_to_string attrs)
in (

let uu____5878 = (FStar_All.pipe_right pat pat_to_string)
in (

let uu____5879 = (FStar_All.pipe_right tm term_to_string)
in (

let uu____5880 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format5 "%slet %s %s = %s in %s" uu____5877 (string_of_let_qualifier q) uu____5878 uu____5879 uu____5880)))))
end
| Seq (t1, t2) -> begin
(

let uu____5883 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5884 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" uu____5883 uu____5884)))
end
| If (t1, t2, t3) -> begin
(

let uu____5888 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5889 = (FStar_All.pipe_right t2 term_to_string)
in (

let uu____5890 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" uu____5888 uu____5889 uu____5890))))
end
| Match (t, branches) -> begin
(

let uu____5913 = (FStar_All.pipe_right t term_to_string)
in (

let uu____5914 = (to_string_l " | " (fun uu____5930 -> (match (uu____5930) with
| (p, w, e) -> begin
(

let uu____5946 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____5947 = (match (w) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____5949 = (term_to_string e1)
in (FStar_Util.format1 "when %s" uu____5949))
end)
in (

let uu____5950 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____5946 uu____5947 uu____5950))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" uu____5913 uu____5914)))
end
| Ascribed (t1, t2, FStar_Pervasives_Native.None) -> begin
(

let uu____5955 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5956 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" uu____5955 uu____5956)))
end
| Ascribed (t1, t2, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____5962 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5963 = (FStar_All.pipe_right t2 term_to_string)
in (

let uu____5964 = (FStar_All.pipe_right tac term_to_string)
in (FStar_Util.format3 "(%s : %s by %s)" uu____5962 uu____5963 uu____5964))))
end
| Record (FStar_Pervasives_Native.Some (e), fields) -> begin
(

let uu____5981 = (FStar_All.pipe_right e term_to_string)
in (

let uu____5982 = (to_string_l " " (fun uu____5991 -> (match (uu____5991) with
| (l, e1) -> begin
(

let uu____5998 = (FStar_All.pipe_right e1 term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5998))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" uu____5981 uu____5982)))
end
| Record (FStar_Pervasives_Native.None, fields) -> begin
(

let uu____6014 = (to_string_l " " (fun uu____6023 -> (match (uu____6023) with
| (l, e) -> begin
(

let uu____6030 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____6030))
end)) fields)
in (FStar_Util.format1 "{%s}" uu____6014))
end
| Project (e, l) -> begin
(

let uu____6033 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" uu____6033 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd1)::tl1, t) -> begin
(term_to_string (mk_term (Product ((((b)::[]), ((mk_term (Product ((((hd1)::tl1), (t)))) x.range x.level))))) x.range x.level))
end
| Product ((b)::[], t) when (Prims.op_Equality x.level Type_level) -> begin
(

let uu____6053 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____6054 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" uu____6053 uu____6054)))
end
| Product ((b)::[], t) when (Prims.op_Equality x.level Kind) -> begin
(

let uu____6059 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____6060 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" uu____6059 uu____6060)))
end
| Sum (binders, t) -> begin
(

let uu____6067 = (

let uu____6068 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____6068 (FStar_String.concat " * ")))
in (

let uu____6077 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" uu____6067 uu____6077)))
end
| QForall (bs, pats, t) -> begin
(

let uu____6093 = (to_string_l " " binder_to_string bs)
in (

let uu____6094 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (

let uu____6097 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____6093 uu____6094 uu____6097))))
end
| QExists (bs, pats, t) -> begin
(

let uu____6113 = (to_string_l " " binder_to_string bs)
in (

let uu____6114 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (

let uu____6117 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____6113 uu____6114 uu____6117))))
end
| Refine (b, t) -> begin
(

let uu____6120 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____6121 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" uu____6120 uu____6121)))
end
| NamedTyp (x1, t) -> begin
(

let uu____6124 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____6124))
end
| Paren (t) -> begin
(

let uu____6126 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" uu____6126))
end
| Product (bs, t) -> begin
(

let uu____6133 = (

let uu____6134 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____6134 (FStar_String.concat ",")))
in (

let uu____6143 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" uu____6133 uu____6143)))
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
| TAnnotated (i, t) -> begin
(

let uu____6151 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____6151))
end
| Annotated (i, t) -> begin
(

let uu____6154 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____6154))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (

let uu____6156 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" uu____6156 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun uu___46_6157 -> (match (uu___46_6157) with
| FStar_Pervasives_Native.Some (Equality) -> begin
"$"
end
| FStar_Pervasives_Native.Some (Implicit) -> begin
"#"
end
| uu____6158 -> begin
""
end))
and pat_to_string : pattern  ->  Prims.string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Parser_Const.const_to_string c)
end
| PatApp (p, ps) -> begin
(

let uu____6167 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____6168 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" uu____6167 uu____6168)))
end
| PatTvar (i, aq) -> begin
(

let uu____6175 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" uu____6175 i.FStar_Ident.idText))
end
| PatVar (i, aq) -> begin
(

let uu____6182 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" uu____6182 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(

let uu____6187 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" uu____6187))
end
| PatTuple (l, false) -> begin
(

let uu____6193 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" uu____6193))
end
| PatTuple (l, true) -> begin
(

let uu____6199 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" uu____6199))
end
| PatRecord (l) -> begin
(

let uu____6207 = (to_string_l "; " (fun uu____6216 -> (match (uu____6216) with
| (f, e) -> begin
(

let uu____6223 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____6223))
end)) l)
in (FStar_Util.format1 "{%s}" uu____6207))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatOp (op) -> begin
(FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op))
end
| PatAscribed (p, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____6238 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____6239 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" uu____6238 uu____6239)))
end
| PatAscribed (p, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____6251 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____6252 = (FStar_All.pipe_right t term_to_string)
in (

let uu____6253 = (FStar_All.pipe_right tac term_to_string)
in (FStar_Util.format3 "(%s:%s by %s)" uu____6251 uu____6252 uu____6253))))
end))
and attrs_opt_to_string : term Prims.list FStar_Pervasives_Native.option  ->  Prims.string = (fun uu___47_6254 -> (match (uu___47_6254) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (attrs) -> begin
(

let uu____6266 = (

let uu____6267 = (FStar_List.map term_to_string attrs)
in (FStar_All.pipe_right uu____6267 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____6266))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, uu____6281) -> begin
(

let uu____6286 = (FStar_Ident.lid_of_ids ((i)::[]))
in (uu____6286)::[])
end
| PatApp (p1, uu____6288) -> begin
(head_id_of_pat p1)
end
| PatAscribed (p1, uu____6294) -> begin
(head_id_of_pat p1)
end
| uu____6307 -> begin
[]
end))


let lids_of_let : 'Auu____6310 . (pattern * 'Auu____6310) Prims.list  ->  FStar_Ident.lid Prims.list = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun uu____6344 -> (match (uu____6344) with
| (p, uu____6352) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun uu___48_6355 -> (match (uu___48_6355) with
| TyconAbstract (i, uu____6357, uu____6358) -> begin
i.FStar_Ident.idText
end
| TyconAbbrev (i, uu____6368, uu____6369, uu____6370) -> begin
i.FStar_Ident.idText
end
| TyconRecord (i, uu____6380, uu____6381, uu____6382) -> begin
i.FStar_Ident.idText
end
| TyconVariant (i, uu____6412, uu____6413, uu____6414) -> begin
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
| TopLevelLet (uu____6459, pats) -> begin
(

let uu____6473 = (

let uu____6474 = (

let uu____6477 = (lids_of_let pats)
in (FStar_All.pipe_right uu____6477 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right uu____6474 (FStar_String.concat ", ")))
in (Prims.strcat "let " uu____6473))
end
| Main (uu____6488) -> begin
"main ..."
end
| Assume (i, uu____6490) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (uu____6491, tys) -> begin
(

let uu____6509 = (

let uu____6510 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____6532 -> (match (uu____6532) with
| (x, uu____6540) -> begin
(id_of_tycon x)
end))))
in (FStar_All.pipe_right uu____6510 (FStar_String.concat ", ")))
in (Prims.strcat "type " uu____6509))
end
| Val (i, uu____6548) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, uu____6550) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| NewEffect (DefineEffect (i, uu____6556, uu____6557, uu____6558)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| NewEffect (RedefineEffect (i, uu____6568, uu____6569)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| Splice (t) -> begin
(

let uu____6575 = (

let uu____6576 = (term_to_string t)
in (Prims.strcat uu____6576 ")"))
in (Prims.strcat "splice (" uu____6575))
end
| SubEffect (uu____6577) -> begin
"sub_effect"
end
| Pragma (uu____6578) -> begin
"pragma"
end
| Fsdoc (uu____6579) -> begin
"fsdoc"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| Module (uu____6583, decls) -> begin
(

let uu____6589 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right uu____6589 (FStar_String.concat "\n")))
end
| Interface (uu____6598, decls, uu____6600) -> begin
(

let uu____6605 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right uu____6605 (FStar_String.concat "\n")))
end))




