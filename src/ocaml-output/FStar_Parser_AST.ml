
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
| uu____5 -> begin
false
end))


let uu___is_Expr : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Expr -> begin
true
end
| uu____10 -> begin
false
end))


let uu___is_Type_level : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Type_level -> begin
true
end
| uu____15 -> begin
false
end))


let uu___is_Kind : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kind -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Formula : level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Formula -> begin
true
end
| uu____25 -> begin
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
| uu____30 -> begin
false
end))


let uu___is_Hash : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Hash -> begin
true
end
| uu____35 -> begin
false
end))


let uu___is_UnivApp : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivApp -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Nothing : imp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Nothing -> begin
true
end
| uu____45 -> begin
false
end))

type arg_qualifier =
| Implicit
| Equality


let uu___is_Implicit : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Implicit -> begin
true
end
| uu____50 -> begin
false
end))


let uu___is_Equality : arg_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equality -> begin
true
end
| uu____55 -> begin
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
| uu____62 -> begin
false
end))


let uu___is_Rec : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec -> begin
true
end
| uu____67 -> begin
false
end))


let uu___is_Mutable : let_qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Mutable -> begin
true
end
| uu____72 -> begin
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
| Let of (let_qualifier * (pattern * term) Prims.list * term)
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
| PatVar of (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option)
| PatName of FStar_Ident.lid
| PatTvar of (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option)
| PatList of pattern Prims.list
| PatTuple of (pattern Prims.list * Prims.bool)
| PatRecord of (FStar_Ident.lid * pattern) Prims.list
| PatAscribed of (pattern * term)
| PatOr of pattern Prims.list
| PatOp of FStar_Ident.ident 
 and pattern =
{pat : pattern'; prange : FStar_Range.range}


let uu___is_Wild : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Wild -> begin
true
end
| uu____539 -> begin
false
end))


let uu___is_Const : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____545 -> begin
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
| uu____565 -> begin
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
| uu____597 -> begin
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
| uu____611 -> begin
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
| uu____625 -> begin
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
| uu____639 -> begin
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
| uu____657 -> begin
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
| uu____693 -> begin
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
| uu____743 -> begin
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
| uu____825 -> begin
false
end))


let __proj__Let__item___0 : term'  ->  (let_qualifier * (pattern * term) Prims.list * term) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_LetOpen : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LetOpen (_0) -> begin
true
end
| uu____879 -> begin
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
| uu____909 -> begin
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
| uu____941 -> begin
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
| uu____979 -> begin
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
| uu____1025 -> begin
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
| uu____1095 -> begin
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
| uu____1159 -> begin
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
| uu____1209 -> begin
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
| uu____1263 -> begin
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
| uu____1295 -> begin
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
| uu____1333 -> begin
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
| uu____1377 -> begin
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
| uu____1439 -> begin
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
| uu____1493 -> begin
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
| uu____1549 -> begin
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
| uu____1569 -> begin
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
| uu____1607 -> begin
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
| uu____1645 -> begin
false
end))


let __proj__Labeled__item___0 : term'  ->  (term * Prims.string * Prims.bool) = (fun projectee -> (match (projectee) with
| Labeled (_0) -> begin
_0
end))


let uu___is_Assign : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assign (_0) -> begin
true
end
| uu____1681 -> begin
false
end))


let __proj__Assign__item___0 : term'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Assign (_0) -> begin
_0
end))


let uu___is_Discrim : term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Discrim (_0) -> begin
true
end
| uu____1707 -> begin
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
| uu____1723 -> begin
false
end))


let __proj__Attributes__item___0 : term'  ->  term Prims.list = (fun projectee -> (match (projectee) with
| Attributes (_0) -> begin
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
| uu____1764 -> begin
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
| uu____1778 -> begin
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
| uu____1796 -> begin
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
| uu____1826 -> begin
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
| uu____1852 -> begin
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
| uu____1897 -> begin
false
end))


let uu___is_PatConst : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatConst (_0) -> begin
true
end
| uu____1903 -> begin
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
| uu____1923 -> begin
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
| uu____1961 -> begin
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
| uu____2013 -> begin
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
| uu____2047 -> begin
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
| uu____2073 -> begin
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
| uu____2111 -> begin
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
| uu____2147 -> begin
false
end))


let __proj__PatAscribed__item___0 : pattern'  ->  (pattern * term) = (fun projectee -> (match (projectee) with
| PatAscribed (_0) -> begin
_0
end))


let uu___is_PatOr : pattern'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PatOr (_0) -> begin
true
end
| uu____2175 -> begin
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
| uu____2195 -> begin
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
| uu____2335 -> begin
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
| uu____2391 -> begin
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
| uu____2463 -> begin
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
| uu____2569 -> begin
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
| uu____2665 -> begin
false
end))


let uu___is_Noeq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noeq -> begin
true
end
| uu____2670 -> begin
false
end))


let uu___is_Unopteq : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unopteq -> begin
true
end
| uu____2675 -> begin
false
end))


let uu___is_Assumption : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Assumption -> begin
true
end
| uu____2680 -> begin
false
end))


let uu___is_DefaultEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DefaultEffect -> begin
true
end
| uu____2685 -> begin
false
end))


let uu___is_TotalEffect : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TotalEffect -> begin
true
end
| uu____2690 -> begin
false
end))


let uu___is_Effect_qual : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Effect_qual -> begin
true
end
| uu____2695 -> begin
false
end))


let uu___is_New : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| New -> begin
true
end
| uu____2700 -> begin
false
end))


let uu___is_Inline : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline -> begin
true
end
| uu____2705 -> begin
false
end))


let uu___is_Visible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Visible -> begin
true
end
| uu____2710 -> begin
false
end))


let uu___is_Unfold_for_unification_and_vcgen : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold_for_unification_and_vcgen -> begin
true
end
| uu____2715 -> begin
false
end))


let uu___is_Inline_for_extraction : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inline_for_extraction -> begin
true
end
| uu____2720 -> begin
false
end))


let uu___is_Irreducible : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Irreducible -> begin
true
end
| uu____2725 -> begin
false
end))


let uu___is_NoExtract : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoExtract -> begin
true
end
| uu____2730 -> begin
false
end))


let uu___is_Reifiable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reifiable -> begin
true
end
| uu____2735 -> begin
false
end))


let uu___is_Reflectable : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflectable -> begin
true
end
| uu____2740 -> begin
false
end))


let uu___is_Opaque : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Opaque -> begin
true
end
| uu____2745 -> begin
false
end))


let uu___is_Logic : qualifier  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Logic -> begin
true
end
| uu____2750 -> begin
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


let uu___is_Qualifier : decoration  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Qualifier (_0) -> begin
true
end
| uu____2774 -> begin
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
| uu____2790 -> begin
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
| uu____2810 -> begin
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
| uu____2840 -> begin
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
| uu____2858 -> begin
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
| uu____2884 -> begin
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
| uu____2941 -> begin
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
| uu____2957 -> begin
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
| uu____2976 -> begin
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
 and decl =
{d : decl'; drange : FStar_Range.range; doc : fsdoc FStar_Pervasives_Native.option; quals : qualifiers; attrs : attributes_} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)


let uu___is_TopLevelModule : decl'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TopLevelModule (_0) -> begin
true
end
| uu____3128 -> begin
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
| uu____3142 -> begin
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
| uu____3156 -> begin
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
| uu____3174 -> begin
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
| uu____3210 -> begin
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
| uu____3254 -> begin
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
| uu____3280 -> begin
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
| uu____3334 -> begin
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
| uu____3366 -> begin
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
| uu____3398 -> begin
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
| uu____3412 -> begin
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
| uu____3426 -> begin
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
| uu____3440 -> begin
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
| uu____3458 -> begin
false
end))


let __proj__Assume__item___0 : decl'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Assume (_0) -> begin
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
| uu____3555 -> begin
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
| uu____3613 -> begin
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
| uu____3679 -> begin
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
| uu____3719 -> begin
false
end))


let __proj__Interface__item___0 : modul  ->  (FStar_Ident.lid * decl Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| Interface (_0) -> begin
_0
end))


type file =
modul Prims.list


type inputFragment =
(file, decl Prims.list) FStar_Util.either


let check_id : FStar_Ident.ident  ->  Prims.unit = (fun id -> (

let first_char = (FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0") (Prims.parse_int "1"))
in (match (((FStar_String.lowercase first_char) = first_char)) with
| true -> begin
()
end
| uu____3765 -> begin
(

let uu____3766 = (

let uu____3767 = (

let uu____3772 = (FStar_Util.format1 "Invalid identifer \'%s\'; expected a symbol that begins with a lower-case character" id.FStar_Ident.idText)
in ((uu____3772), (id.FStar_Ident.idRange)))
in FStar_Errors.Error (uu____3767))
in (FStar_Exn.raise uu____3766))
end)))


let at_most_one : 'Auu____3781 . Prims.string  ->  FStar_Range.range  ->  'Auu____3781 Prims.list  ->  'Auu____3781 FStar_Pervasives_Native.option = (fun s r l -> (match (l) with
| (x)::[] -> begin
FStar_Pervasives_Native.Some (x)
end
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____3801 -> begin
(

let uu____3804 = (

let uu____3805 = (

let uu____3810 = (FStar_Util.format1 "At most one %s is allowed on declarations" s)
in ((uu____3810), (r)))
in FStar_Errors.Error (uu____3805))
in (FStar_Exn.raise uu____3804))
end))


let mk_decl : decl'  ->  FStar_Range.range  ->  decoration Prims.list  ->  decl = (fun d r decorations -> (

let doc1 = (

let uu____3832 = (FStar_List.choose (fun uu___74_3837 -> (match (uu___74_3837) with
| Doc (d1) -> begin
FStar_Pervasives_Native.Some (d1)
end
| uu____3841 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in (at_most_one "fsdoc" r uu____3832))
in (

let attributes_ = (

let uu____3847 = (FStar_List.choose (fun uu___75_3856 -> (match (uu___75_3856) with
| DeclAttributes (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____3866 -> begin
FStar_Pervasives_Native.None
end)) decorations)
in (at_most_one "attribute set" r uu____3847))
in (

let attributes_1 = (FStar_Util.dflt [] attributes_)
in (

let qualifiers = (FStar_List.choose (fun uu___76_3881 -> (match (uu___76_3881) with
| Qualifier (q) -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____3885 -> begin
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
| uu____3953 -> begin
Op ((((FStar_Ident.mk_ident (("-"), (rminus)))), ((t)::[])))
end)
in (mk_term t1 r l)))


let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})


let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs ((((FStar_List.append ps p')), (body')))
end
| uu____3984 -> begin
Abs (((ps), (body)))
end))


let mk_function : (pattern * term FStar_Pervasives_Native.option * term) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (

let x = (

let i = (FStar_Parser_Const.next_id ())
in (FStar_Ident.gen r1))
in (

let uu____4021 = (

let uu____4022 = (

let uu____4029 = (

let uu____4030 = (

let uu____4031 = (

let uu____4046 = (

let uu____4047 = (

let uu____4048 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (uu____4048))
in (mk_term uu____4047 r1 Expr))
in ((uu____4046), (branches)))
in Match (uu____4031))
in (mk_term uu____4030 r2 Expr))
in ((((mk_pattern (PatVar (((x), (FStar_Pervasives_Native.None)))) r1))::[]), (uu____4029)))
in Abs (uu____4022))
in (mk_term uu____4021 r2 Expr))))


let un_function : pattern  ->  term  ->  (pattern * term) FStar_Pervasives_Native.option = (fun p tm -> (match (((p.pat), (tm.tm))) with
| (PatVar (uu____4083), Abs (pats, body)) -> begin
FStar_Pervasives_Native.Some ((((mk_pattern (PatApp (((p), (pats)))) p.prange)), (body)))
end
| uu____4102 -> begin
FStar_Pervasives_Native.None
end))


let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (

let uu____4119 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path uu____4119 r)))


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
| uu____4290 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct (((s), (args)))) r Un)
end
| uu____4304 -> begin
(FStar_List.fold_left (fun t1 uu____4314 -> (match (uu____4314) with
| (a, imp) -> begin
(mk_term (App (((t1), (a), (imp)))) r Un)
end)) t args)
end)
end))


let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (

let uu____4333 = ((FStar_Parser_Const.set_empty), (FStar_Parser_Const.set_singleton), (FStar_Parser_Const.set_union), (FStar_Parser_Const.heap_addr_of_lid))
in (match (uu____4333) with
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
| uu____4402 -> begin
(match (t.tm) with
| Name (s) -> begin
(

let uu____4406 = (

let uu____4407 = (

let uu____4418 = (FStar_List.map (fun a -> ((a), (Nothing))) args)
in ((s), (uu____4418)))
in Construct (uu____4407))
in (mk_term uu____4406 r Un))
end
| uu____4437 -> begin
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


let mkWildAdmitMagic : 'Auu____4456 . FStar_Range.range  ->  (pattern * 'Auu____4456 FStar_Pervasives_Native.option * term) = (fun r -> (

let uu____4469 = (mkAdmitMagic r)
in (((mk_pattern PatWild r)), (FStar_Pervasives_Native.None), (uu____4469))))


let focusBranches : 'Auu____4478 . (Prims.bool * (pattern * 'Auu____4478 FStar_Pervasives_Native.option * term)) Prims.list  ->  FStar_Range.range  ->  (pattern * 'Auu____4478 FStar_Pervasives_Native.option * term) Prims.list = (fun branches r -> (

let should_filter = (FStar_Util.for_some FStar_Pervasives_Native.fst branches)
in (match (should_filter) with
| true -> begin
((FStar_Errors.warn r "Focusing on only some cases");
(

let focussed = (

let uu____4568 = (FStar_List.filter FStar_Pervasives_Native.fst branches)
in (FStar_All.pipe_right uu____4568 (FStar_List.map FStar_Pervasives_Native.snd)))
in (

let uu____4655 = (

let uu____4666 = (mkWildAdmitMagic r)
in (uu____4666)::[])
in (FStar_List.append focussed uu____4655)));
)
end
| uu____4699 -> begin
(FStar_All.pipe_right branches (FStar_List.map FStar_Pervasives_Native.snd))
end)))


let focusLetBindings : 'Auu____4758 . (Prims.bool * ('Auu____4758 * term)) Prims.list  ->  FStar_Range.range  ->  ('Auu____4758 * term) Prims.list = (fun lbs r -> (

let should_filter = (FStar_Util.for_some FStar_Pervasives_Native.fst lbs)
in (match (should_filter) with
| true -> begin
((FStar_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition");
(FStar_List.map (fun uu____4828 -> (match (uu____4828) with
| (f, lb) -> begin
(match (f) with
| true -> begin
lb
end
| uu____4855 -> begin
(

let uu____4856 = (mkAdmitMagic r)
in (((FStar_Pervasives_Native.fst lb)), (uu____4856)))
end)
end)) lbs);
)
end
| uu____4857 -> begin
(FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd))
end)))


let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (

let uu____4906 = (FStar_List.map (fun a -> ((a), (FsTypApp))) args)
in (mkApp t uu____4906 r)))


let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons1 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r)
in (

let uu____4932 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons1)) r Expr) uu____4932 r))))


let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (

let cons1 = (FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r)
in (

let uu____4958 = (FStar_List.map (fun x -> ((x), (Nothing))) args)
in (mkApp (mk_term (Name (cons1)) r Expr) uu____4958 r))))


let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  Prims.bool  ->  term FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t should_bind_var refopt m implicit -> (

let b = (mk_binder (Annotated (((id), (t)))) m Type_level implicit)
in (match (refopt) with
| FStar_Pervasives_Native.None -> begin
b
end
| FStar_Pervasives_Native.Some (phi) -> begin
(match (should_bind_var) with
| true -> begin
(mk_binder (Annotated (((id), ((mk_term (Refine (((b), (phi)))) m Type_level))))) m Type_level implicit)
end
| uu____5001 -> begin
(

let x = (FStar_Ident.gen t.range)
in (

let b1 = (mk_binder (Annotated (((x), (t)))) m Type_level implicit)
in (mk_binder (Annotated (((id), ((mk_term (Refine (((b1), (phi)))) m Type_level))))) m Type_level implicit)))
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
| PatVar (x, uu____5035) -> begin
(mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi)))) range Type_level)
end
| uu____5040 -> begin
(

let x = (FStar_Ident.gen t_range)
in (

let phi1 = (

let x_var = (

let uu____5044 = (

let uu____5045 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (uu____5045))
in (mk_term uu____5044 phi.range Formula))
in (

let pat_branch = ((pat), (FStar_Pervasives_Native.None), (phi))
in (

let otherwise_branch = (

let uu____5066 = (

let uu____5067 = (

let uu____5068 = (FStar_Ident.lid_of_path (("False")::[]) phi.range)
in Name (uu____5068))
in (mk_term uu____5067 phi.range Formula))
in (((mk_pattern PatWild phi.range)), (FStar_Pervasives_Native.None), (uu____5066)))
in (mk_term (Match (((x_var), ((pat_branch)::(otherwise_branch)::[])))) phi.range Formula))))
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi1)))) range Type_level)))
end)
end
| uu____5105 -> begin
(

let x = (FStar_Ident.gen t.range)
in (mk_term (Refine ((((mk_binder (Annotated (((x), (t)))) t_range Type_level FStar_Pervasives_Native.None)), (phi)))) range Type_level))
end)
end)
in (mk_pattern (PatAscribed (((pat), (t1)))) range)))


let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
FStar_Pervasives_Native.Some (((x), (t), (FStar_Pervasives_Native.None)))
end
| Refine ({b = Annotated (x, t); brange = uu____5145; blevel = uu____5146; aqual = uu____5147}, t') -> begin
FStar_Pervasives_Native.Some (((x), (t), (FStar_Pervasives_Native.Some (t'))))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| uu____5160 -> begin
FStar_Pervasives_Native.None
end))


let rec as_mlist : modul Prims.list  ->  ((FStar_Ident.lid * decl) * decl Prims.list)  ->  decl Prims.list  ->  modul Prims.list = (fun out cur ds -> (

let uu____5213 = cur
in (match (uu____5213) with
| ((m_name, m_decl), cur1) -> begin
(match (ds) with
| [] -> begin
(FStar_List.rev ((Module (((m_name), ((m_decl)::(FStar_List.rev cur1)))))::out))
end
| (d)::ds1 -> begin
(match (d.d) with
| TopLevelModule (m') -> begin
(as_mlist ((Module (((m_name), ((m_decl)::(FStar_List.rev cur1)))))::out) ((((m'), (d))), ([])) ds1)
end
| uu____5256 -> begin
(as_mlist out ((((m_name), (m_decl))), ((d)::cur1)) ds1)
end)
end)
end)))


let as_frag : Prims.bool  ->  FStar_Range.range  ->  decl Prims.list  ->  (modul Prims.list, decl Prims.list) FStar_Util.either = (fun is_light light_range ds -> (

let uu____5295 = (match (ds) with
| (d)::ds1 -> begin
((d), (ds1))
end
| [] -> begin
(FStar_Exn.raise FStar_Errors.Empty_frag)
end)
in (match (uu____5295) with
| (d, ds1) -> begin
(match (d.d) with
| TopLevelModule (m) -> begin
(

let ds2 = (match (is_light) with
| true -> begin
(

let uu____5348 = (mk_decl (Pragma (LightOff)) light_range [])
in (uu____5348)::ds1)
end
| uu____5349 -> begin
ds1
end)
in (

let ms = (as_mlist [] ((((m), (d))), ([])) ds2)
in ((

let uu____5360 = (FStar_List.tl ms)
in (match (uu____5360) with
| (Module (m', uu____5364))::uu____5365 -> begin
(

let msg = "Support for more than one module in a file is deprecated"
in (

let uu____5373 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid m'))
in (FStar_Util.print2_warning "%s (Warning): %s\n" uu____5373 msg)))
end
| uu____5374 -> begin
()
end));
FStar_Util.Inl (ms);
)))
end
| uu____5381 -> begin
(

let ds2 = (d)::ds1
in ((FStar_List.iter (fun uu___77_5392 -> (match (uu___77_5392) with
| {d = TopLevelModule (uu____5393); drange = r; doc = uu____5395; quals = uu____5396; attrs = uu____5397} -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected module declaration"), (r)))))
end
| uu____5400 -> begin
()
end)) ds2);
FStar_Util.Inr (ds2);
))
end)
end)))


let compile_op : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun arity s r -> (

let name_of_char = (fun uu___78_5420 -> (match (uu___78_5420) with
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
| '~' -> begin
"Tilde"
end
| '/' -> begin
"Slash"
end
| '\\' -> begin
"Backslash"
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
| '$' -> begin
"Dollar"
end
| '.' -> begin
"Dot"
end
| c -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected operator symbol: \'" (Prims.strcat (FStar_Util.string_of_char c) "\'"))), (r)))))
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
| uu____5422 -> begin
(

let uu____5423 = (

let uu____5424 = (

let uu____5427 = (FStar_String.list_of_string s)
in (FStar_List.map name_of_char uu____5427))
in (FStar_String.concat "_" uu____5424))
in (Prims.strcat "op_" uu____5423))
end)))


let compile_op' : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun s r -> (compile_op (~- ((Prims.parse_int "1"))) s r))


let string_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  Prims.string = (fun uu____5451 -> (match (uu____5451) with
| (comment, keywords) -> begin
(

let uu____5476 = (

let uu____5477 = (FStar_List.map (fun uu____5487 -> (match (uu____5487) with
| (k, v1) -> begin
(Prims.strcat k (Prims.strcat "->" v1))
end)) keywords)
in (FStar_String.concat "," uu____5477))
in (Prims.strcat comment uu____5476))
end))


let string_of_let_qualifier : let_qualifier  ->  Prims.string = (fun uu___79_5497 -> (match (uu___79_5497) with
| NoLetQualifier -> begin
""
end
| Rec -> begin
"rec"
end
| Mutable -> begin
"mutable"
end))


let to_string_l : 'Auu____5506 . Prims.string  ->  ('Auu____5506  ->  Prims.string)  ->  'Auu____5506 Prims.list  ->  Prims.string = (fun sep f l -> (

let uu____5528 = (FStar_List.map f l)
in (FStar_String.concat sep uu____5528)))


let imp_to_string : imp  ->  Prims.string = (fun uu___80_5534 -> (match (uu___80_5534) with
| Hash -> begin
"#"
end
| uu____5535 -> begin
""
end))


let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, uu____5546) -> begin
(

let uu____5551 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" uu____5551))
end
| Ensures (t, uu____5553) -> begin
(

let uu____5558 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" uu____5558))
end
| Labeled (t, l, uu____5561) -> begin
(

let uu____5562 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l uu____5562))
end
| Const (c) -> begin
(FStar_Parser_Const.const_to_string c)
end
| Op (s, xs) -> begin
(

let uu____5570 = (

let uu____5571 = (FStar_List.map (fun x1 -> (FStar_All.pipe_right x1 term_to_string)) xs)
in (FStar_String.concat ", " uu____5571))
in (FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____5570))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| Uvar (id) -> begin
id.FStar_Ident.idText
end
| Var (l) -> begin
l.FStar_Ident.str
end
| Name (l) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(

let uu____5594 = (to_string_l " " (fun uu____5603 -> (match (uu____5603) with
| (a, imp) -> begin
(

let uu____5610 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) uu____5610))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____5594))
end
| Abs (pats, t) -> begin
(

let uu____5617 = (to_string_l " " pat_to_string pats)
in (

let uu____5618 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" uu____5617 uu____5618)))
end
| App (t1, t2, imp) -> begin
(

let uu____5622 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5623 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" uu____5622 (imp_to_string imp) uu____5623)))
end
| Let (Rec, lbs, body) -> begin
(

let uu____5638 = (to_string_l " and " (fun uu____5648 -> (match (uu____5648) with
| (p, b) -> begin
(

let uu____5655 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____5656 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" uu____5655 uu____5656)))
end)) lbs)
in (

let uu____5657 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" uu____5638 uu____5657)))
end
| Let (q, ((pat, tm))::[], body) -> begin
(

let uu____5676 = (FStar_All.pipe_right pat pat_to_string)
in (

let uu____5677 = (FStar_All.pipe_right tm term_to_string)
in (

let uu____5678 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) uu____5676 uu____5677 uu____5678))))
end
| Seq (t1, t2) -> begin
(

let uu____5681 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5682 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" uu____5681 uu____5682)))
end
| If (t1, t2, t3) -> begin
(

let uu____5686 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5687 = (FStar_All.pipe_right t2 term_to_string)
in (

let uu____5688 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" uu____5686 uu____5687 uu____5688))))
end
| Match (t, branches) -> begin
(

let uu____5711 = (FStar_All.pipe_right t term_to_string)
in (

let uu____5712 = (to_string_l " | " (fun uu____5728 -> (match (uu____5728) with
| (p, w, e) -> begin
(

let uu____5744 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____5745 = (match (w) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____5747 = (term_to_string e1)
in (FStar_Util.format1 "when %s" uu____5747))
end)
in (

let uu____5748 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____5744 uu____5745 uu____5748))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" uu____5711 uu____5712)))
end
| Ascribed (t1, t2, FStar_Pervasives_Native.None) -> begin
(

let uu____5753 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5754 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" uu____5753 uu____5754)))
end
| Ascribed (t1, t2, FStar_Pervasives_Native.Some (tac)) -> begin
(

let uu____5760 = (FStar_All.pipe_right t1 term_to_string)
in (

let uu____5761 = (FStar_All.pipe_right t2 term_to_string)
in (

let uu____5762 = (FStar_All.pipe_right tac term_to_string)
in (FStar_Util.format3 "(%s : %s by %s)" uu____5760 uu____5761 uu____5762))))
end
| Record (FStar_Pervasives_Native.Some (e), fields) -> begin
(

let uu____5779 = (FStar_All.pipe_right e term_to_string)
in (

let uu____5780 = (to_string_l " " (fun uu____5789 -> (match (uu____5789) with
| (l, e1) -> begin
(

let uu____5796 = (FStar_All.pipe_right e1 term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5796))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" uu____5779 uu____5780)))
end
| Record (FStar_Pervasives_Native.None, fields) -> begin
(

let uu____5812 = (to_string_l " " (fun uu____5821 -> (match (uu____5821) with
| (l, e) -> begin
(

let uu____5828 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____5828))
end)) fields)
in (FStar_Util.format1 "{%s}" uu____5812))
end
| Project (e, l) -> begin
(

let uu____5831 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" uu____5831 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product ((b)::(hd1)::tl1, t) -> begin
(term_to_string (mk_term (Product ((((b)::[]), ((mk_term (Product ((((hd1)::tl1), (t)))) x.range x.level))))) x.range x.level))
end
| Product ((b)::[], t) when (x.level = Type_level) -> begin
(

let uu____5851 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____5852 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" uu____5851 uu____5852)))
end
| Product ((b)::[], t) when (x.level = Kind) -> begin
(

let uu____5857 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____5858 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" uu____5857 uu____5858)))
end
| Sum (binders, t) -> begin
(

let uu____5865 = (

let uu____5866 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____5866 (FStar_String.concat " * ")))
in (

let uu____5875 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" uu____5865 uu____5875)))
end
| QForall (bs, pats, t) -> begin
(

let uu____5891 = (to_string_l " " binder_to_string bs)
in (

let uu____5892 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (

let uu____5895 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____5891 uu____5892 uu____5895))))
end
| QExists (bs, pats, t) -> begin
(

let uu____5911 = (to_string_l " " binder_to_string bs)
in (

let uu____5912 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (

let uu____5915 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____5911 uu____5912 uu____5915))))
end
| Refine (b, t) -> begin
(

let uu____5918 = (FStar_All.pipe_right b binder_to_string)
in (

let uu____5919 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" uu____5918 uu____5919)))
end
| NamedTyp (x1, t) -> begin
(

let uu____5922 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____5922))
end
| Paren (t) -> begin
(

let uu____5924 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" uu____5924))
end
| Product (bs, t) -> begin
(

let uu____5931 = (

let uu____5932 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____5932 (FStar_String.concat ",")))
in (

let uu____5941 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" uu____5931 uu____5941)))
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

let uu____5949 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5949))
end
| Annotated (i, t) -> begin
(

let uu____5952 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____5952))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (

let uu____5954 = (aqual_to_string x.aqual)
in (FStar_Util.format2 "%s%s" uu____5954 s))))
and aqual_to_string : aqual  ->  Prims.string = (fun uu___81_5955 -> (match (uu___81_5955) with
| FStar_Pervasives_Native.Some (Equality) -> begin
"$"
end
| FStar_Pervasives_Native.Some (Implicit) -> begin
"#"
end
| uu____5956 -> begin
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

let uu____5965 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____5966 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" uu____5965 uu____5966)))
end
| PatTvar (i, aq) -> begin
(

let uu____5973 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" uu____5973 i.FStar_Ident.idText))
end
| PatVar (i, aq) -> begin
(

let uu____5980 = (aqual_to_string aq)
in (FStar_Util.format2 "%s%s" uu____5980 i.FStar_Ident.idText))
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(

let uu____5985 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" uu____5985))
end
| PatTuple (l, false) -> begin
(

let uu____5991 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" uu____5991))
end
| PatTuple (l, true) -> begin
(

let uu____5997 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" uu____5997))
end
| PatRecord (l) -> begin
(

let uu____6005 = (to_string_l "; " (fun uu____6014 -> (match (uu____6014) with
| (f, e) -> begin
(

let uu____6021 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____6021))
end)) l)
in (FStar_Util.format1 "{%s}" uu____6005))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatOp (op) -> begin
(FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op))
end
| PatAscribed (p, t) -> begin
(

let uu____6028 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____6029 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" uu____6028 uu____6029)))
end))


let rec head_id_of_pat : pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.pat) with
| PatName (l) -> begin
(l)::[]
end
| PatVar (i, uu____6040) -> begin
(

let uu____6045 = (FStar_Ident.lid_of_ids ((i)::[]))
in (uu____6045)::[])
end
| PatApp (p1, uu____6047) -> begin
(head_id_of_pat p1)
end
| PatAscribed (p1, uu____6053) -> begin
(head_id_of_pat p1)
end
| uu____6054 -> begin
[]
end))


let lids_of_let : 'Auu____6059 . (pattern * 'Auu____6059) Prims.list  ->  FStar_Ident.lid Prims.list = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun uu____6093 -> (match (uu____6093) with
| (p, uu____6101) -> begin
(head_id_of_pat p)
end)))))


let id_of_tycon : tycon  ->  Prims.string = (fun uu___82_6105 -> (match (uu___82_6105) with
| TyconAbstract (i, uu____6107, uu____6108) -> begin
i.FStar_Ident.idText
end
| TyconAbbrev (i, uu____6118, uu____6119, uu____6120) -> begin
i.FStar_Ident.idText
end
| TyconRecord (i, uu____6130, uu____6131, uu____6132) -> begin
i.FStar_Ident.idText
end
| TyconVariant (i, uu____6162, uu____6163, uu____6164) -> begin
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
| TopLevelLet (uu____6210, pats) -> begin
(

let uu____6224 = (

let uu____6225 = (

let uu____6228 = (lids_of_let pats)
in (FStar_All.pipe_right uu____6228 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right uu____6225 (FStar_String.concat ", ")))
in (Prims.strcat "let " uu____6224))
end
| Main (uu____6239) -> begin
"main ..."
end
| Assume (i, uu____6241) -> begin
(Prims.strcat "assume " i.FStar_Ident.idText)
end
| Tycon (uu____6242, tys) -> begin
(

let uu____6260 = (

let uu____6261 = (FStar_All.pipe_right tys (FStar_List.map (fun uu____6283 -> (match (uu____6283) with
| (x, uu____6291) -> begin
(id_of_tycon x)
end))))
in (FStar_All.pipe_right uu____6261 (FStar_String.concat ", ")))
in (Prims.strcat "type " uu____6260))
end
| Val (i, uu____6299) -> begin
(Prims.strcat "val " i.FStar_Ident.idText)
end
| Exception (i, uu____6301) -> begin
(Prims.strcat "exception " i.FStar_Ident.idText)
end
| NewEffect (DefineEffect (i, uu____6307, uu____6308, uu____6309)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| NewEffect (RedefineEffect (i, uu____6319, uu____6320)) -> begin
(Prims.strcat "new_effect " i.FStar_Ident.idText)
end
| SubEffect (uu____6325) -> begin
"sub_effect"
end
| Pragma (uu____6326) -> begin
"pragma"
end
| Fsdoc (uu____6327) -> begin
"fsdoc"
end))


let modul_to_string : modul  ->  Prims.string = (fun m -> (match (m) with
| Module (uu____6332, decls) -> begin
(

let uu____6338 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right uu____6338 (FStar_String.concat "\n")))
end
| Interface (uu____6347, decls, uu____6349) -> begin
(

let uu____6354 = (FStar_All.pipe_right decls (FStar_List.map decl_to_string))
in (FStar_All.pipe_right uu____6354 (FStar_String.concat "\n")))
end))


let error : 'Auu____6371 . Prims.string  ->  term  ->  FStar_Range.range  ->  'Auu____6371 = (fun msg tm r -> (

let tm1 = (FStar_All.pipe_right tm term_to_string)
in (

let tm2 = (match (((FStar_String.length tm1) >= (Prims.parse_int "80"))) with
| true -> begin
(

let uu____6386 = (FStar_Util.substring tm1 (Prims.parse_int "0") (Prims.parse_int "77"))
in (Prims.strcat uu____6386 "..."))
end
| uu____6387 -> begin
tm1
end)
in (FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat msg (Prims.strcat "\n" tm2))), (r))))))))




