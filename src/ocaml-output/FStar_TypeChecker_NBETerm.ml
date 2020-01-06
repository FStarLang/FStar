
open Prims
open FStar_Pervasives

type var =
FStar_Syntax_Syntax.bv


type sort =
Prims.int

type constant =
| Unit
| Bool of Prims.bool
| Int of FStar_BigInt.t
| String of (Prims.string * FStar_Range.range)
| Char of FStar_Char.char
| Range of FStar_Range.range


let uu___is_Unit : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unit -> begin
true
end
| uu____57 -> begin
false
end))


let uu___is_Bool : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
true
end
| uu____70 -> begin
false
end))


let __proj__Bool__item___0 : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
_0
end))


let uu___is_Int : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
true
end
| uu____92 -> begin
false
end))


let __proj__Int__item___0 : constant  ->  FStar_BigInt.t = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
_0
end))


let uu___is_String : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String (_0) -> begin
true
end
| uu____116 -> begin
false
end))


let __proj__String__item___0 : constant  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| String (_0) -> begin
_0
end))


let uu___is_Char : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Char (_0) -> begin
true
end
| uu____151 -> begin
false
end))


let __proj__Char__item___0 : constant  ->  FStar_Char.char = (fun projectee -> (match (projectee) with
| Char (_0) -> begin
_0
end))


let uu___is_Range : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Range (_0) -> begin
true
end
| uu____173 -> begin
false
end))


let __proj__Range__item___0 : constant  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| Range (_0) -> begin
_0
end))

type atom =
| Var of var
| Match of (t * (t  ->  t) * ((t  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.branch Prims.list)) 
 and t =
| Lam of ((t Prims.list  ->  t) * (t Prims.list  ->  (t * FStar_Syntax_Syntax.aqual)) Prims.list * Prims.int * (unit  ->  residual_comp) FStar_Pervasives_Native.option)
| Accu of (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)
| Construct of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list)
| FV of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list)
| Constant of constant
| Type_t of FStar_Syntax_Syntax.universe
| Univ of FStar_Syntax_Syntax.universe
| Unknown
| Arrow of ((t Prims.list  ->  comp) * (t Prims.list  ->  (t * FStar_Syntax_Syntax.aqual)) Prims.list)
| Refinement of ((t  ->  t) * (unit  ->  (t * FStar_Syntax_Syntax.aqual)))
| Reflect of t
| Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)
| Lazy of ((FStar_Syntax_Syntax.lazyinfo, (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t FStar_Thunk.t)
| Rec of (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list * (t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  t)) 
 and comp =
| Tot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
| GTot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
| Comp of comp_typ 
 and comp_typ =
{comp_univs : FStar_Syntax_Syntax.universes; effect_name : FStar_Ident.lident; result_typ : t; effect_args : (t * FStar_Syntax_Syntax.aqual) Prims.list; flags : cflag Prims.list} 
 and cflag =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| TRIVIAL_POSTCONDITION
| SHOULD_NOT_INLINE
| LEMMA
| CPS
| DECREASES of t 
 and residual_comp =
{residual_effect : FStar_Ident.lident; residual_typ : t FStar_Pervasives_Native.option; residual_flags : cflag Prims.list}


let uu___is_Var : atom  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
true
end
| uu____555 -> begin
false
end))


let __proj__Var__item___0 : atom  ->  var = (fun projectee -> (match (projectee) with
| Var (_0) -> begin
_0
end))


let uu___is_Match : atom  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
true
end
| uu____591 -> begin
false
end))


let __proj__Match__item___0 : atom  ->  (t * (t  ->  t) * ((t  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.branch Prims.list)) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_Lam : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lam (_0) -> begin
true
end
| uu____691 -> begin
false
end))


let __proj__Lam__item___0 : t  ->  ((t Prims.list  ->  t) * (t Prims.list  ->  (t * FStar_Syntax_Syntax.aqual)) Prims.list * Prims.int * (unit  ->  residual_comp) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Lam (_0) -> begin
_0
end))


let uu___is_Accu : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Accu (_0) -> begin
true
end
| uu____810 -> begin
false
end))


let __proj__Accu__item___0 : t  ->  (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list) = (fun projectee -> (match (projectee) with
| Accu (_0) -> begin
_0
end))


let uu___is_Construct : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Construct (_0) -> begin
true
end
| uu____873 -> begin
false
end))


let __proj__Construct__item___0 : t  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) = (fun projectee -> (match (projectee) with
| Construct (_0) -> begin
_0
end))


let uu___is_FV : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FV (_0) -> begin
true
end
| uu____948 -> begin
false
end))


let __proj__FV__item___0 : t  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) = (fun projectee -> (match (projectee) with
| FV (_0) -> begin
_0
end))


let uu___is_Constant : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Constant (_0) -> begin
true
end
| uu____1009 -> begin
false
end))


let __proj__Constant__item___0 : t  ->  constant = (fun projectee -> (match (projectee) with
| Constant (_0) -> begin
_0
end))


let uu___is_Type_t : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Type_t (_0) -> begin
true
end
| uu____1028 -> begin
false
end))


let __proj__Type_t__item___0 : t  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Type_t (_0) -> begin
_0
end))


let uu___is_Univ : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
true
end
| uu____1047 -> begin
false
end))


let __proj__Univ__item___0 : t  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
_0
end))


let uu___is_Unknown : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1065 -> begin
false
end))


let uu___is_Arrow : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
true
end
| uu____1097 -> begin
false
end))


let __proj__Arrow__item___0 : t  ->  ((t Prims.list  ->  comp) * (t Prims.list  ->  (t * FStar_Syntax_Syntax.aqual)) Prims.list) = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
_0
end))


let uu___is_Refinement : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Refinement (_0) -> begin
true
end
| uu____1190 -> begin
false
end))


let __proj__Refinement__item___0 : t  ->  ((t  ->  t) * (unit  ->  (t * FStar_Syntax_Syntax.aqual))) = (fun projectee -> (match (projectee) with
| Refinement (_0) -> begin
_0
end))


let uu___is_Reflect : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reflect (_0) -> begin
true
end
| uu____1251 -> begin
false
end))


let __proj__Reflect__item___0 : t  ->  t = (fun projectee -> (match (projectee) with
| Reflect (_0) -> begin
_0
end))


let uu___is_Quote : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Quote (_0) -> begin
true
end
| uu____1274 -> begin
false
end))


let __proj__Quote__item___0 : t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) = (fun projectee -> (match (projectee) with
| Quote (_0) -> begin
_0
end))


let uu___is_Lazy : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lazy (_0) -> begin
true
end
| uu____1319 -> begin
false
end))


let __proj__Lazy__item___0 : t  ->  ((FStar_Syntax_Syntax.lazyinfo, (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t FStar_Thunk.t) = (fun projectee -> (match (projectee) with
| Lazy (_0) -> begin
_0
end))


let uu___is_Rec : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec (_0) -> begin
true
end
| uu____1416 -> begin
false
end))


let __proj__Rec__item___0 : t  ->  (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list * (t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  t)) = (fun projectee -> (match (projectee) with
| Rec (_0) -> begin
_0
end))


let uu___is_Tot : comp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Tot (_0) -> begin
true
end
| uu____1549 -> begin
false
end))


let __proj__Tot__item___0 : comp  ->  (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Tot (_0) -> begin
_0
end))


let uu___is_GTot : comp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GTot (_0) -> begin
true
end
| uu____1592 -> begin
false
end))


let __proj__GTot__item___0 : comp  ->  (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| GTot (_0) -> begin
_0
end))


let uu___is_Comp : comp  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
true
end
| uu____1629 -> begin
false
end))


let __proj__Comp__item___0 : comp  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
_0
end))


let __proj__Mkcomp_typ__item__comp_univs : comp_typ  ->  FStar_Syntax_Syntax.universes = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
comp_univs
end))


let __proj__Mkcomp_typ__item__effect_name : comp_typ  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
effect_name
end))


let __proj__Mkcomp_typ__item__result_typ : comp_typ  ->  t = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
result_typ
end))


let __proj__Mkcomp_typ__item__effect_args : comp_typ  ->  (t * FStar_Syntax_Syntax.aqual) Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
effect_args
end))


let __proj__Mkcomp_typ__item__flags : comp_typ  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags} -> begin
flags
end))


let uu___is_TOTAL : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TOTAL -> begin
true
end
| uu____1758 -> begin
false
end))


let uu___is_MLEFFECT : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLEFFECT -> begin
true
end
| uu____1769 -> begin
false
end))


let uu___is_RETURN : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RETURN -> begin
true
end
| uu____1780 -> begin
false
end))


let uu___is_PARTIAL_RETURN : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PARTIAL_RETURN -> begin
true
end
| uu____1791 -> begin
false
end))


let uu___is_SOMETRIVIAL : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SOMETRIVIAL -> begin
true
end
| uu____1802 -> begin
false
end))


let uu___is_TRIVIAL_POSTCONDITION : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TRIVIAL_POSTCONDITION -> begin
true
end
| uu____1813 -> begin
false
end))


let uu___is_SHOULD_NOT_INLINE : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SHOULD_NOT_INLINE -> begin
true
end
| uu____1824 -> begin
false
end))


let uu___is_LEMMA : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LEMMA -> begin
true
end
| uu____1835 -> begin
false
end))


let uu___is_CPS : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPS -> begin
true
end
| uu____1846 -> begin
false
end))


let uu___is_DECREASES : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
true
end
| uu____1858 -> begin
false
end))


let __proj__DECREASES__item___0 : cflag  ->  t = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
_0
end))


let __proj__Mkresidual_comp__item__residual_effect : residual_comp  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {residual_effect = residual_effect; residual_typ = residual_typ; residual_flags = residual_flags} -> begin
residual_effect
end))


let __proj__Mkresidual_comp__item__residual_typ : residual_comp  ->  t FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {residual_effect = residual_effect; residual_typ = residual_typ; residual_flags = residual_flags} -> begin
residual_typ
end))


let __proj__Mkresidual_comp__item__residual_flags : residual_comp  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {residual_effect = residual_effect; residual_typ = residual_typ; residual_flags = residual_flags} -> begin
residual_flags
end))


type arg =
(t * FStar_Syntax_Syntax.aqual)


type args =
(t * FStar_Syntax_Syntax.aqual) Prims.list


type head =
t


type annot =
t FStar_Pervasives_Native.option


let isAccu : t  ->  Prims.bool = (fun trm -> (match (trm) with
| Accu (uu____1934) -> begin
true
end
| uu____1946 -> begin
false
end))


let isNotAccu : t  ->  Prims.bool = (fun x -> (match (x) with
| Accu (uu____1956, uu____1957) -> begin
false
end
| uu____1971 -> begin
true
end))


let mkConstruct : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun i us ts -> Construct (((i), (us), (ts))))


let mkFV : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun i us ts -> FV (((i), (us), (ts))))


let mkAccuVar : var  ->  t = (fun v1 -> Accu (((Var (v1)), ([]))))


let mkAccuMatch : t  ->  (t  ->  t)  ->  ((t  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.branch Prims.list)  ->  t = (fun s cases bs -> Accu (((Match (((s), (cases), (bs)))), ([]))))


let equal_if : Prims.bool  ->  FStar_Syntax_Util.eq_result = (fun uu___0_2107 -> (match (uu___0_2107) with
| true -> begin
FStar_Syntax_Util.Equal
end
| uu____2110 -> begin
FStar_Syntax_Util.Unknown
end))


let equal_iff : Prims.bool  ->  FStar_Syntax_Util.eq_result = (fun uu___1_2118 -> (match (uu___1_2118) with
| true -> begin
FStar_Syntax_Util.Equal
end
| uu____2121 -> begin
FStar_Syntax_Util.NotEqual
end))


let eq_inj : FStar_Syntax_Util.eq_result  ->  FStar_Syntax_Util.eq_result  ->  FStar_Syntax_Util.eq_result = (fun r1 r2 -> (match (((r1), (r2))) with
| (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) -> begin
FStar_Syntax_Util.Equal
end
| (FStar_Syntax_Util.NotEqual, uu____2134) -> begin
FStar_Syntax_Util.NotEqual
end
| (uu____2135, FStar_Syntax_Util.NotEqual) -> begin
FStar_Syntax_Util.NotEqual
end
| (FStar_Syntax_Util.Unknown, uu____2136) -> begin
FStar_Syntax_Util.Unknown
end
| (uu____2137, FStar_Syntax_Util.Unknown) -> begin
FStar_Syntax_Util.Unknown
end))


let eq_and : FStar_Syntax_Util.eq_result  ->  (unit  ->  FStar_Syntax_Util.eq_result)  ->  FStar_Syntax_Util.eq_result = (fun f g -> (match (f) with
| FStar_Syntax_Util.Equal -> begin
(g ())
end
| uu____2154 -> begin
FStar_Syntax_Util.Unknown
end))


let eq_constant : constant  ->  constant  ->  FStar_Syntax_Util.eq_result = (fun c1 c2 -> (match (((c1), (c2))) with
| (Unit, Unit) -> begin
FStar_Syntax_Util.Equal
end
| (Bool (b1), Bool (b2)) -> begin
(equal_iff (Prims.op_Equality b1 b2))
end
| (Int (i1), Int (i2)) -> begin
(equal_iff (Prims.op_Equality i1 i2))
end
| (String (s1, uu____2174), String (s2, uu____2176)) -> begin
(equal_iff (Prims.op_Equality s1 s2))
end
| (Char (c11), Char (c21)) -> begin
(equal_iff (Prims.op_Equality c11 c21))
end
| (Range (r1), Range (r2)) -> begin
FStar_Syntax_Util.Unknown
end
| (uu____2189, uu____2190) -> begin
FStar_Syntax_Util.NotEqual
end))


let rec eq_t : t  ->  t  ->  FStar_Syntax_Util.eq_result = (fun t1 t2 -> (match (((t1), (t2))) with
| (Lam (uu____2226), Lam (uu____2227)) -> begin
FStar_Syntax_Util.Unknown
end
| (Accu (a1, as1), Accu (a2, as2)) -> begin
(

let uu____2316 = (eq_atom a1 a2)
in (eq_and uu____2316 (fun uu____2318 -> (eq_args as1 as2))))
end
| (Construct (v1, us1, args1), Construct (v2, us2, args2)) -> begin
(

let uu____2357 = (FStar_Syntax_Syntax.fv_eq v1 v2)
in (match (uu____2357) with
| true -> begin
((match ((Prims.op_disEquality (FStar_List.length args1) (FStar_List.length args2))) with
| true -> begin
(failwith "eq_t, different number of args on Construct")
end
| uu____2371 -> begin
()
end);
(

let uu____2373 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2430 -> (match (uu____2430) with
| ((a1, uu____2444), (a2, uu____2446)) -> begin
(

let uu____2455 = (eq_t a1 a2)
in (eq_inj acc uu____2455))
end)) FStar_Syntax_Util.Equal) uu____2373));
)
end
| uu____2456 -> begin
FStar_Syntax_Util.NotEqual
end))
end
| (FV (v1, us1, args1), FV (v2, us2, args2)) -> begin
(

let uu____2496 = (FStar_Syntax_Syntax.fv_eq v1 v2)
in (match (uu____2496) with
| true -> begin
(

let uu____2499 = (

let uu____2500 = (FStar_Syntax_Util.eq_univs_list us1 us2)
in (equal_iff uu____2500))
in (eq_and uu____2499 (fun uu____2503 -> (eq_args args1 args2))))
end
| uu____2504 -> begin
FStar_Syntax_Util.Unknown
end))
end
| (Constant (c1), Constant (c2)) -> begin
(eq_constant c1 c2)
end
| (Type_t (u1), Type_t (u2)) -> begin
(

let uu____2510 = (FStar_Syntax_Util.eq_univs u1 u2)
in (equal_iff uu____2510))
end
| (Univ (u1), Univ (u2)) -> begin
(

let uu____2514 = (FStar_Syntax_Util.eq_univs u1 u2)
in (equal_iff uu____2514))
end
| (Refinement (r1, t11), Refinement (r2, t21)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (

let uu____2561 = (

let uu____2562 = (

let uu____2563 = (t11 ())
in (FStar_Pervasives_Native.fst uu____2563))
in (

let uu____2568 = (

let uu____2569 = (t21 ())
in (FStar_Pervasives_Native.fst uu____2569))
in (eq_t uu____2562 uu____2568)))
in (eq_and uu____2561 (fun uu____2577 -> (

let uu____2578 = (

let uu____2579 = (mkAccuVar x)
in (r1 uu____2579))
in (

let uu____2580 = (

let uu____2581 = (mkAccuVar x)
in (r2 uu____2581))
in (eq_t uu____2578 uu____2580)))))))
end
| (Unknown, Unknown) -> begin
FStar_Syntax_Util.Equal
end
| (uu____2582, uu____2583) -> begin
FStar_Syntax_Util.Unknown
end))
and eq_atom : atom  ->  atom  ->  FStar_Syntax_Util.eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| (Var (bv1), Var (bv2)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2))
end
| (uu____2588, uu____2589) -> begin
FStar_Syntax_Util.Unknown
end))
and eq_arg : arg  ->  arg  ->  FStar_Syntax_Util.eq_result = (fun a1 a2 -> (eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)))
and eq_args : args  ->  args  ->  FStar_Syntax_Util.eq_result = (fun as1 as2 -> (match (((as1), (as2))) with
| ([], []) -> begin
FStar_Syntax_Util.Equal
end
| ((x)::xs, (y)::ys) -> begin
(

let uu____2670 = (eq_arg x y)
in (eq_and uu____2670 (fun uu____2672 -> (eq_args xs ys))))
end
| (uu____2673, uu____2674) -> begin
FStar_Syntax_Util.Unknown
end))


let constant_to_string : constant  ->  Prims.string = (fun c -> (match (c) with
| Unit -> begin
"Unit"
end
| Bool (b) -> begin
(match (b) with
| true -> begin
"Bool true"
end
| uu____2713 -> begin
"Bool false"
end)
end
| Int (i) -> begin
(FStar_BigInt.string_of_big_int i)
end
| Char (c1) -> begin
(FStar_Util.format1 "\'%s\'" (FStar_Util.string_of_char c1))
end
| String (s, uu____2721) -> begin
(FStar_Util.format1 "\"%s\"" s)
end
| Range (r) -> begin
(

let uu____2726 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "Range %s" uu____2726))
end))


let rec t_to_string : t  ->  Prims.string = (fun x -> (match (x) with
| Lam (b, args, arity, uu____2745) -> begin
(

let uu____2790 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____2801 = (FStar_Util.string_of_int arity)
in (FStar_Util.format2 "Lam (_, %s args, %s)" uu____2790 uu____2801)))
end
| Accu (a, l) -> begin
(

let uu____2818 = (

let uu____2820 = (atom_to_string a)
in (

let uu____2822 = (

let uu____2824 = (

let uu____2826 = (

let uu____2828 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2828))
in (FStar_String.op_Hat uu____2826 ")"))
in (FStar_String.op_Hat ") (" uu____2824))
in (FStar_String.op_Hat uu____2820 uu____2822)))
in (FStar_String.op_Hat "Accu (" uu____2818))
end
| Construct (fv, us, l) -> begin
(

let uu____2866 = (

let uu____2868 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____2870 = (

let uu____2872 = (

let uu____2874 = (

let uu____2876 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_String.concat "; " uu____2876))
in (

let uu____2882 = (

let uu____2884 = (

let uu____2886 = (

let uu____2888 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2888))
in (FStar_String.op_Hat uu____2886 "]"))
in (FStar_String.op_Hat "] [" uu____2884))
in (FStar_String.op_Hat uu____2874 uu____2882)))
in (FStar_String.op_Hat ") [" uu____2872))
in (FStar_String.op_Hat uu____2868 uu____2870)))
in (FStar_String.op_Hat "Construct (" uu____2866))
end
| FV (fv, us, l) -> begin
(

let uu____2927 = (

let uu____2929 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____2931 = (

let uu____2933 = (

let uu____2935 = (

let uu____2937 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_String.concat "; " uu____2937))
in (

let uu____2943 = (

let uu____2945 = (

let uu____2947 = (

let uu____2949 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2949))
in (FStar_String.op_Hat uu____2947 "]"))
in (FStar_String.op_Hat "] [" uu____2945))
in (FStar_String.op_Hat uu____2935 uu____2943)))
in (FStar_String.op_Hat ") [" uu____2933))
in (FStar_String.op_Hat uu____2929 uu____2931)))
in (FStar_String.op_Hat "FV (" uu____2927))
end
| Constant (c) -> begin
(constant_to_string c)
end
| Univ (u) -> begin
(

let uu____2971 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_String.op_Hat "Universe " uu____2971))
end
| Type_t (u) -> begin
(

let uu____2975 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_String.op_Hat "Type_t " uu____2975))
end
| Arrow (uu____2978) -> begin
"Arrow"
end
| Refinement (f, t) -> begin
(

let x1 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (

let t1 = (

let uu____3024 = (t ())
in (FStar_Pervasives_Native.fst uu____3024))
in (

let uu____3029 = (

let uu____3031 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____3033 = (

let uu____3035 = (

let uu____3037 = (t_to_string t1)
in (

let uu____3039 = (

let uu____3041 = (

let uu____3043 = (

let uu____3045 = (

let uu____3046 = (mkAccuVar x1)
in (f uu____3046))
in (t_to_string uu____3045))
in (FStar_String.op_Hat uu____3043 "}"))
in (FStar_String.op_Hat "{" uu____3041))
in (FStar_String.op_Hat uu____3037 uu____3039)))
in (FStar_String.op_Hat ":" uu____3035))
in (FStar_String.op_Hat uu____3031 uu____3033)))
in (FStar_String.op_Hat "Refinement " uu____3029))))
end
| Unknown -> begin
"Unknown"
end
| Reflect (t) -> begin
(

let uu____3053 = (t_to_string t)
in (FStar_String.op_Hat "Reflect " uu____3053))
end
| Quote (uu____3056) -> begin
"Quote _"
end
| Lazy (FStar_Util.Inl (li), uu____3063) -> begin
(

let uu____3080 = (

let uu____3082 = (FStar_Syntax_Util.unfold_lazy li)
in (FStar_Syntax_Print.term_to_string uu____3082))
in (FStar_Util.format1 "Lazy (Inl {%s})" uu____3080))
end
| Lazy (FStar_Util.Inr (uu____3084, et), uu____3086) -> begin
(

let uu____3103 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3103))
end
| Rec (uu____3106, uu____3107, l, uu____3109, uu____3110, uu____3111, uu____3112) -> begin
(

let uu____3157 = (

let uu____3159 = (

let uu____3161 = (FStar_List.map t_to_string l)
in (FStar_String.concat "; " uu____3161))
in (FStar_String.op_Hat uu____3159 ")"))
in (FStar_String.op_Hat "Rec (" uu____3157))
end))
and atom_to_string : atom  ->  Prims.string = (fun a -> (match (a) with
| Var (v1) -> begin
(

let uu____3172 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_String.op_Hat "Var " uu____3172))
end
| Match (t, uu____3176, uu____3177) -> begin
(

let uu____3200 = (t_to_string t)
in (FStar_String.op_Hat "Match " uu____3200))
end))


let arg_to_string : arg  ->  Prims.string = (fun a -> (

let uu____3210 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3210 t_to_string)))


let args_to_string : args  ->  Prims.string = (fun args -> (

let uu____3223 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3223 (FStar_String.concat " "))))

type nbe_cbs =
{iapp : t  ->  args  ->  t; translate : FStar_Syntax_Syntax.term  ->  t}


let __proj__Mknbe_cbs__item__iapp : nbe_cbs  ->  t  ->  args  ->  t = (fun projectee -> (match (projectee) with
| {iapp = iapp; translate = translate} -> begin
iapp
end))


let __proj__Mknbe_cbs__item__translate : nbe_cbs  ->  FStar_Syntax_Syntax.term  ->  t = (fun projectee -> (match (projectee) with
| {iapp = iapp; translate = translate} -> begin
translate
end))


let iapp_cb : nbe_cbs  ->  t  ->  args  ->  t = (fun cbs h a -> (cbs.iapp h a))


let translate_cb : nbe_cbs  ->  FStar_Syntax_Syntax.term  ->  t = (fun cbs t -> (cbs.translate t))

type 'a embedding =
{em : nbe_cbs  ->  'a  ->  t; un : nbe_cbs  ->  t  ->  'a FStar_Pervasives_Native.option; typ : t; emb_typ : FStar_Syntax_Syntax.emb_typ}


let __proj__Mkembedding__item__em : 'a . 'a embedding  ->  nbe_cbs  ->  'a  ->  t = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; emb_typ = emb_typ} -> begin
em
end))


let __proj__Mkembedding__item__un : 'a . 'a embedding  ->  nbe_cbs  ->  t  ->  'a FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; emb_typ = emb_typ} -> begin
un
end))


let __proj__Mkembedding__item__typ : 'a . 'a embedding  ->  t = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; emb_typ = emb_typ} -> begin
typ
end))


let __proj__Mkembedding__item__emb_typ : 'a . 'a embedding  ->  FStar_Syntax_Syntax.emb_typ = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; emb_typ = emb_typ} -> begin
emb_typ
end))


let embed : 'a . 'a embedding  ->  nbe_cbs  ->  'a  ->  t = (fun e cb x -> (e.em cb x))


let unembed : 'a . 'a embedding  ->  nbe_cbs  ->  t  ->  'a FStar_Pervasives_Native.option = (fun e cb trm -> (e.un cb trm))


let type_of : 'a . 'a embedding  ->  t = (fun e -> e.typ)


let mk_emb : 'a . (nbe_cbs  ->  'a  ->  t)  ->  (nbe_cbs  ->  t  ->  'a FStar_Pervasives_Native.option)  ->  t  ->  FStar_Syntax_Syntax.emb_typ  ->  'a embedding = (fun em un typ et -> {em = em; un = un; typ = typ; emb_typ = et})


let lid_as_constr : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun l us args -> (

let uu____3694 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mkConstruct uu____3694 us args)))


let lid_as_typ : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun l us args -> (

let uu____3715 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____3715 us args)))


let as_iarg : t  ->  arg = (fun a -> ((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))


let as_arg : t  ->  arg = (fun a -> ((a), (FStar_Pervasives_Native.None)))


let make_arrow1 : t  ->  arg  ->  t = (fun t1 a -> Arrow ((((fun uu____3756 -> Tot (((t1), (FStar_Pervasives_Native.None))))), (((fun uu____3771 -> a))::[]))))


let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ  ->  'a  ->  (unit  ->  t)  ->  t = (fun et x f -> ((

let uu____3814 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____3814) with
| true -> begin
(

let uu____3838 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3838))
end
| uu____3841 -> begin
()
end));
(

let uu____3843 = (FStar_ST.op_Bang FStar_Options.eager_embedding)
in (match (uu____3843) with
| true -> begin
(f ())
end
| uu____3867 -> begin
(

let thunk1 = (FStar_Thunk.mk f)
in (

let li = (

let uu____3877 = (FStar_Dyn.mkdyn x)
in ((uu____3877), (et)))
in Lazy (((FStar_Util.Inr (li)), (thunk1)))))
end));
))


let lazy_unembed : 'Auu____3905 'a . 'Auu____3905  ->  FStar_Syntax_Syntax.emb_typ  ->  t  ->  (t  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun cb et x f -> (match (x) with
| Lazy (FStar_Util.Inl (li), thunk1) -> begin
(

let uu____3956 = (FStar_Thunk.force thunk1)
in (f uu____3956))
end
| Lazy (FStar_Util.Inr (b, et'), thunk1) -> begin
(

let uu____3976 = ((Prims.op_disEquality et et') || (FStar_ST.op_Bang FStar_Options.eager_embedding))
in (match (uu____3976) with
| true -> begin
(

let res = (

let uu____4005 = (FStar_Thunk.force thunk1)
in (f uu____4005))
in ((

let uu____4007 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4007) with
| true -> begin
(

let uu____4031 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____4033 = (FStar_Syntax_Print.emb_typ_to_string et')
in (FStar_Util.print2 "Unembed cancellation failed\n\t%s <> %s\n" uu____4031 uu____4033)))
end
| uu____4036 -> begin
()
end));
res;
))
end
| uu____4038 -> begin
(

let a = (FStar_Dyn.undyn b)
in ((

let uu____4042 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4042) with
| true -> begin
(

let uu____4066 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Unembed cancelled for %s\n" uu____4066))
end
| uu____4069 -> begin
()
end));
FStar_Pervasives_Native.Some (a);
))
end))
end
| uu____4071 -> begin
(

let aopt = (f x)
in ((

let uu____4076 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4076) with
| true -> begin
(

let uu____4100 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4100))
end
| uu____4103 -> begin
()
end));
aopt;
))
end))


let mk_any_emb : t  ->  t embedding = (fun ty -> (

let em = (fun _cb a -> a)
in (

let un = (fun _cb t -> FStar_Pervasives_Native.Some (t))
in (mk_emb em un ty FStar_Syntax_Syntax.ET_abstract))))


let e_any : t embedding = (

let em = (fun _cb a -> a)
in (

let un = (fun _cb t -> FStar_Pervasives_Native.Some (t))
in (

let uu____4168 = (lid_as_typ FStar_Parser_Const.term_lid [] [])
in (mk_emb em un uu____4168 FStar_Syntax_Syntax.ET_abstract))))


let e_unit : unit embedding = (

let em = (fun _cb a -> Constant (Unit))
in (

let un = (fun _cb t -> FStar_Pervasives_Native.Some (()))
in (

let uu____4202 = (lid_as_typ FStar_Parser_Const.unit_lid [] [])
in (

let uu____4207 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (mk_emb em un uu____4202 uu____4207)))))


let e_bool : Prims.bool embedding = (

let em = (fun _cb a -> Constant (Bool (a)))
in (

let un = (fun _cb t -> (match (t) with
| Constant (Bool (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4248 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4250 = (lid_as_typ FStar_Parser_Const.bool_lid [] [])
in (

let uu____4255 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (mk_emb em un uu____4250 uu____4255)))))


let e_char : FStar_Char.char embedding = (

let em = (fun _cb c -> Constant (Char (c)))
in (

let un = (fun _cb c -> (match (c) with
| Constant (Char (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4297 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4299 = (lid_as_typ FStar_Parser_Const.char_lid [] [])
in (

let uu____4304 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char)
in (mk_emb em un uu____4299 uu____4304)))))


let e_string : Prims.string embedding = (

let em = (fun _cb s -> Constant (String (((s), (FStar_Range.dummyRange)))))
in (

let un = (fun _cb s -> (match (s) with
| Constant (String (s1, uu____4346)) -> begin
FStar_Pervasives_Native.Some (s1)
end
| uu____4350 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4352 = (lid_as_typ FStar_Parser_Const.string_lid [] [])
in (

let uu____4357 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string)
in (mk_emb em un uu____4352 uu____4357)))))


let e_int : FStar_BigInt.t embedding = (

let em = (fun _cb c -> Constant (Int (c)))
in (

let un = (fun _cb c -> (match (c) with
| Constant (Int (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4392 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4393 = (lid_as_typ FStar_Parser_Const.int_lid [] [])
in (

let uu____4398 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int)
in (mk_emb em un uu____4393 uu____4398)))))


let e_option : 'a . 'a embedding  ->  'a FStar_Pervasives_Native.option embedding = (fun ea -> (

let etyp = (

let uu____4419 = (

let uu____4427 = (FStar_All.pipe_right FStar_Parser_Const.option_lid FStar_Ident.string_of_lid)
in ((uu____4427), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4419))
in (

let em = (fun cb o -> (lazy_embed etyp o (fun uu____4452 -> (match (o) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4453 = (

let uu____4454 = (

let uu____4459 = (type_of ea)
in (as_iarg uu____4459))
in (uu____4454)::[])
in (lid_as_constr FStar_Parser_Const.none_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4453))
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4469 = (

let uu____4470 = (

let uu____4475 = (embed ea cb x)
in (as_arg uu____4475))
in (

let uu____4476 = (

let uu____4483 = (

let uu____4488 = (type_of ea)
in (as_iarg uu____4488))
in (uu____4483)::[])
in (uu____4470)::uu____4476))
in (lid_as_constr FStar_Parser_Const.some_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4469))
end))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, args) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| Construct (fvar1, us, ((a, uu____4555))::(uu____4556)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid) -> begin
(

let uu____4583 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____4583 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (a1)))))
end
| uu____4592 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____4595 = (

let uu____4596 = (

let uu____4597 = (

let uu____4602 = (type_of ea)
in (as_arg uu____4602))
in (uu____4597)::[])
in (lid_as_typ FStar_Parser_Const.option_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4596))
in (mk_emb em un uu____4595 etyp))))))


let e_tuple2 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a * 'b) embedding = (fun ea eb -> (

let etyp = (

let uu____4649 = (

let uu____4657 = (FStar_All.pipe_right FStar_Parser_Const.lid_tuple2 FStar_Ident.string_of_lid)
in ((uu____4657), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4649))
in (

let em = (fun cb x -> (lazy_embed etyp x (fun uu____4688 -> (

let uu____4689 = (

let uu____4690 = (

let uu____4695 = (embed eb cb (FStar_Pervasives_Native.snd x))
in (as_arg uu____4695))
in (

let uu____4696 = (

let uu____4703 = (

let uu____4708 = (embed ea cb (FStar_Pervasives_Native.fst x))
in (as_arg uu____4708))
in (

let uu____4709 = (

let uu____4716 = (

let uu____4721 = (type_of eb)
in (as_iarg uu____4721))
in (

let uu____4722 = (

let uu____4729 = (

let uu____4734 = (type_of ea)
in (as_iarg uu____4734))
in (uu____4729)::[])
in (uu____4716)::uu____4722))
in (uu____4703)::uu____4709))
in (uu____4690)::uu____4696))
in (lid_as_constr FStar_Parser_Const.lid_Mktuple2 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4689)))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, ((b, uu____4802))::((a, uu____4804))::(uu____4805)::(uu____4806)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.lid_Mktuple2) -> begin
(

let uu____4845 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____4845 (fun a1 -> (

let uu____4855 = (unembed eb cb b)
in (FStar_Util.bind_opt uu____4855 (fun b1 -> FStar_Pervasives_Native.Some (((a1), (b1)))))))))
end
| uu____4868 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____4873 = (

let uu____4874 = (

let uu____4875 = (

let uu____4880 = (type_of eb)
in (as_arg uu____4880))
in (

let uu____4881 = (

let uu____4888 = (

let uu____4893 = (type_of ea)
in (as_arg uu____4893))
in (uu____4888)::[])
in (uu____4875)::uu____4881))
in (lid_as_typ FStar_Parser_Const.lid_tuple2 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4874))
in (mk_emb em un uu____4873 etyp))))))


let e_either : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a, 'b) FStar_Util.either embedding = (fun ea eb -> (

let etyp = (

let uu____4946 = (

let uu____4954 = (FStar_All.pipe_right FStar_Parser_Const.either_lid FStar_Ident.string_of_lid)
in ((uu____4954), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4946))
in (

let em = (fun cb s -> (lazy_embed etyp s (fun uu____4986 -> (match (s) with
| FStar_Util.Inl (a) -> begin
(

let uu____4988 = (

let uu____4989 = (

let uu____4994 = (embed ea cb a)
in (as_arg uu____4994))
in (

let uu____4995 = (

let uu____5002 = (

let uu____5007 = (type_of eb)
in (as_iarg uu____5007))
in (

let uu____5008 = (

let uu____5015 = (

let uu____5020 = (type_of ea)
in (as_iarg uu____5020))
in (uu____5015)::[])
in (uu____5002)::uu____5008))
in (uu____4989)::uu____4995))
in (lid_as_constr FStar_Parser_Const.inl_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4988))
end
| FStar_Util.Inr (b) -> begin
(

let uu____5038 = (

let uu____5039 = (

let uu____5044 = (embed eb cb b)
in (as_arg uu____5044))
in (

let uu____5045 = (

let uu____5052 = (

let uu____5057 = (type_of eb)
in (as_iarg uu____5057))
in (

let uu____5058 = (

let uu____5065 = (

let uu____5070 = (type_of ea)
in (as_iarg uu____5070))
in (uu____5065)::[])
in (uu____5052)::uu____5058))
in (uu____5039)::uu____5045))
in (lid_as_constr FStar_Parser_Const.inr_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5038))
end))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, ((a, uu____5132))::(uu____5133)::(uu____5134)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid) -> begin
(

let uu____5169 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____5169 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Util.Inl (a1)))))
end
| Construct (fvar1, us, ((b, uu____5185))::(uu____5186)::(uu____5187)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid) -> begin
(

let uu____5222 = (unembed eb cb b)
in (FStar_Util.bind_opt uu____5222 (fun b1 -> FStar_Pervasives_Native.Some (FStar_Util.Inr (b1)))))
end
| uu____5235 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5240 = (

let uu____5241 = (

let uu____5242 = (

let uu____5247 = (type_of eb)
in (as_arg uu____5247))
in (

let uu____5248 = (

let uu____5255 = (

let uu____5260 = (type_of ea)
in (as_arg uu____5260))
in (uu____5255)::[])
in (uu____5242)::uu____5248))
in (lid_as_typ FStar_Parser_Const.either_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5241))
in (mk_emb em un uu____5240 etyp))))))


let e_range : FStar_Range.range embedding = (

let em = (fun cb r -> Constant (Range (r)))
in (

let un = (fun cb t -> (match (t) with
| Constant (Range (r)) -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____5309 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5310 = (lid_as_typ FStar_Parser_Const.range_lid [] [])
in (

let uu____5315 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range)
in (mk_emb em un uu____5310 uu____5315)))))


let e_list : 'a . 'a embedding  ->  'a Prims.list embedding = (fun ea -> (

let etyp = (

let uu____5336 = (

let uu____5344 = (FStar_All.pipe_right FStar_Parser_Const.list_lid FStar_Ident.string_of_lid)
in ((uu____5344), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____5336))
in (

let em = (fun cb l -> (lazy_embed etyp l (fun uu____5371 -> (

let typ = (

let uu____5373 = (type_of ea)
in (as_iarg uu____5373))
in (

let nil = (lid_as_constr FStar_Parser_Const.nil_lid ((FStar_Syntax_Syntax.U_zero)::[]) ((typ)::[]))
in (

let cons1 = (fun hd1 tl1 -> (

let uu____5394 = (

let uu____5395 = (as_arg tl1)
in (

let uu____5400 = (

let uu____5407 = (

let uu____5412 = (embed ea cb hd1)
in (as_arg uu____5412))
in (uu____5407)::(typ)::[])
in (uu____5395)::uu____5400))
in (lid_as_constr FStar_Parser_Const.cons_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____5394)))
in (FStar_List.fold_right cons1 l nil)))))))
in (

let rec un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fv, uu____5460, uu____5461) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| Construct (fv, uu____5481, ((tl1, FStar_Pervasives_Native.None))::((hd1, FStar_Pervasives_Native.None))::((uu____5484, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5485))))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5513 = (unembed ea cb hd1)
in (FStar_Util.bind_opt uu____5513 (fun hd2 -> (

let uu____5521 = (un cb tl1)
in (FStar_Util.bind_opt uu____5521 (fun tl2 -> FStar_Pervasives_Native.Some ((hd2)::tl2)))))))
end
| Construct (fv, uu____5537, ((tl1, FStar_Pervasives_Native.None))::((hd1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5562 = (unembed ea cb hd1)
in (FStar_Util.bind_opt uu____5562 (fun hd2 -> (

let uu____5570 = (un cb tl1)
in (FStar_Util.bind_opt uu____5570 (fun tl2 -> FStar_Pervasives_Native.Some ((hd2)::tl2)))))))
end
| uu____5585 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5588 = (

let uu____5589 = (

let uu____5590 = (

let uu____5595 = (type_of ea)
in (as_arg uu____5595))
in (uu____5590)::[])
in (lid_as_typ FStar_Parser_Const.list_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____5589))
in (mk_emb em un uu____5588 etyp))))))


let e_string_list : Prims.string Prims.list embedding = (e_list e_string)


let e_arrow : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b) embedding = (fun ea eb -> (

let etyp = FStar_Syntax_Syntax.ET_fun (((ea.emb_typ), (eb.emb_typ)))
in (

let em = (fun cb f -> (lazy_embed etyp f (fun uu____5668 -> Lam ((((fun tas -> (

let uu____5698 = (

let uu____5701 = (FStar_List.hd tas)
in (unembed ea cb uu____5701))
in (match (uu____5698) with
| FStar_Pervasives_Native.Some (a) -> begin
(

let uu____5703 = (f a)
in (embed eb cb uu____5703))
end
| FStar_Pervasives_Native.None -> begin
(failwith "cannot unembed function argument")
end)))), (((fun uu____5716 -> (

let uu____5719 = (type_of eb)
in (as_arg uu____5719))))::[]), ((Prims.parse_int "1")), (FStar_Pervasives_Native.None))))))
in (

let un = (fun cb lam -> (

let k = (fun lam1 -> FStar_Pervasives_Native.Some ((fun x -> (

let uu____5777 = (

let uu____5780 = (

let uu____5781 = (

let uu____5782 = (

let uu____5787 = (embed ea cb x)
in (as_arg uu____5787))
in (uu____5782)::[])
in (cb.iapp lam1 uu____5781))
in (unembed eb cb uu____5780))
in (match (uu____5777) with
| FStar_Pervasives_Native.Some (y) -> begin
y
end
| FStar_Pervasives_Native.None -> begin
(failwith "cannot unembed function result")
end)))))
in (lazy_unembed cb etyp lam k)))
in (

let uu____5801 = (

let uu____5802 = (type_of ea)
in (

let uu____5803 = (

let uu____5804 = (type_of eb)
in (as_iarg uu____5804))
in (make_arrow1 uu____5802 uu____5803)))
in (mk_emb em un uu____5801 etyp))))))


let e_norm_step : FStar_Syntax_Embeddings.norm_step embedding = (

let em = (fun cb n1 -> (match (n1) with
| FStar_Syntax_Embeddings.Simpl -> begin
(

let uu____5822 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5822 [] []))
end
| FStar_Syntax_Embeddings.Weak -> begin
(

let uu____5827 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5827 [] []))
end
| FStar_Syntax_Embeddings.HNF -> begin
(

let uu____5832 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5832 [] []))
end
| FStar_Syntax_Embeddings.Primops -> begin
(

let uu____5837 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5837 [] []))
end
| FStar_Syntax_Embeddings.Delta -> begin
(

let uu____5842 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5842 [] []))
end
| FStar_Syntax_Embeddings.Zeta -> begin
(

let uu____5847 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5847 [] []))
end
| FStar_Syntax_Embeddings.Iota -> begin
(

let uu____5852 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5852 [] []))
end
| FStar_Syntax_Embeddings.Reify -> begin
(

let uu____5857 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5857 [] []))
end
| FStar_Syntax_Embeddings.NBE -> begin
(

let uu____5862 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5862 [] []))
end
| FStar_Syntax_Embeddings.UnfoldOnly (l) -> begin
(

let uu____5871 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5872 = (

let uu____5873 = (

let uu____5878 = (

let uu____5879 = (e_list e_string)
in (embed uu____5879 cb l))
in (as_arg uu____5878))
in (uu____5873)::[])
in (mkFV uu____5871 [] uu____5872)))
end
| FStar_Syntax_Embeddings.UnfoldFully (l) -> begin
(

let uu____5901 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5902 = (

let uu____5903 = (

let uu____5908 = (

let uu____5909 = (e_list e_string)
in (embed uu____5909 cb l))
in (as_arg uu____5908))
in (uu____5903)::[])
in (mkFV uu____5901 [] uu____5902)))
end
| FStar_Syntax_Embeddings.UnfoldAttr (l) -> begin
(

let uu____5931 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5932 = (

let uu____5933 = (

let uu____5938 = (

let uu____5939 = (e_list e_string)
in (embed uu____5939 cb l))
in (as_arg uu____5938))
in (uu____5933)::[])
in (mkFV uu____5931 [] uu____5932)))
end))
in (

let un = (fun cb t0 -> (match (t0) with
| FV (fv, uu____5973, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Simpl)
end
| FV (fv, uu____5989, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Weak)
end
| FV (fv, uu____6005, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.HNF)
end
| FV (fv, uu____6021, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Primops)
end
| FV (fv, uu____6037, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Delta)
end
| FV (fv, uu____6053, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Zeta)
end
| FV (fv, uu____6069, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Iota)
end
| FV (fv, uu____6085, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.NBE)
end
| FV (fv, uu____6101, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Reify)
end
| FV (fv, uu____6117, ((l, uu____6119))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly) -> begin
(

let uu____6138 = (

let uu____6144 = (e_list e_string)
in (unembed uu____6144 cb l))
in (FStar_Util.bind_opt uu____6138 (fun ss -> (FStar_All.pipe_left (fun _6164 -> FStar_Pervasives_Native.Some (_6164)) (FStar_Syntax_Embeddings.UnfoldOnly (ss))))))
end
| FV (fv, uu____6166, ((l, uu____6168))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully) -> begin
(

let uu____6187 = (

let uu____6193 = (e_list e_string)
in (unembed uu____6193 cb l))
in (FStar_Util.bind_opt uu____6187 (fun ss -> (FStar_All.pipe_left (fun _6213 -> FStar_Pervasives_Native.Some (_6213)) (FStar_Syntax_Embeddings.UnfoldFully (ss))))))
end
| FV (fv, uu____6215, ((l, uu____6217))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr) -> begin
(

let uu____6236 = (

let uu____6242 = (e_list e_string)
in (unembed uu____6242 cb l))
in (FStar_Util.bind_opt uu____6236 (fun ss -> (FStar_All.pipe_left (fun _6262 -> FStar_Pervasives_Native.Some (_6262)) (FStar_Syntax_Embeddings.UnfoldAttr (ss))))))
end
| uu____6263 -> begin
((

let uu____6265 = (

let uu____6271 = (

let uu____6273 = (t_to_string t0)
in (FStar_Util.format1 "Not an embedded norm_step: %s" uu____6273))
in ((FStar_Errors.Warning_NotEmbedded), (uu____6271)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____6265));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____6277 = (

let uu____6278 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____6278 [] []))
in (

let uu____6283 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step)
in (mk_emb em un uu____6277 uu____6283)))))


let bogus_cbs : nbe_cbs = {iapp = (fun h _args -> h); translate = (fun uu____6292 -> (failwith "bogus_cbs translate"))}


let arg_as_int : arg  ->  FStar_BigInt.t FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_int bogus_cbs)))


let arg_as_bool : arg  ->  Prims.bool FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_bool bogus_cbs)))


let arg_as_char : arg  ->  FStar_Char.char FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_char bogus_cbs)))


let arg_as_string : arg  ->  Prims.string FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_string bogus_cbs)))


let arg_as_list : 'a . 'a embedding  ->  arg  ->  'a Prims.list FStar_Pervasives_Native.option = (fun e a -> (

let uu____6369 = (

let uu____6378 = (e_list e)
in (unembed uu____6378 bogus_cbs))
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6369)))


let arg_as_bounded_int : arg  ->  (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option = (fun uu____6400 -> (match (uu____6400) with
| (a, uu____6408) -> begin
(match (a) with
| FV (fv1, [], ((Constant (Int (i)), uu____6423))::[]) when (

let uu____6440 = (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.ends_with uu____6440 "int_to_t")) -> begin
FStar_Pervasives_Native.Some (((fv1), (i)))
end
| uu____6447 -> begin
FStar_Pervasives_Native.None
end)
end))


let int_as_bounded : FStar_Syntax_Syntax.fv  ->  FStar_BigInt.t  ->  t = (fun int_to_t1 n1 -> (

let c = (embed e_int bogus_cbs n1)
in (

let int_to_t2 = (fun args -> FV (((int_to_t1), ([]), (args))))
in (

let uu____6490 = (

let uu____6497 = (as_arg c)
in (uu____6497)::[])
in (int_to_t2 uu____6490)))))


let lift_unary : 'a 'b . ('a  ->  'b)  ->  'a FStar_Pervasives_Native.option Prims.list  ->  'b FStar_Pervasives_Native.option = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____6551 = (f a)
in FStar_Pervasives_Native.Some (uu____6551))
end
| uu____6552 -> begin
FStar_Pervasives_Native.None
end))


let lift_binary : 'a 'b . ('a  ->  'a  ->  'b)  ->  'a FStar_Pervasives_Native.option Prims.list  ->  'b FStar_Pervasives_Native.option = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____6606 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____6606))
end
| uu____6607 -> begin
FStar_Pervasives_Native.None
end))


let unary_op : 'a . (arg  ->  'a FStar_Pervasives_Native.option)  ->  ('a  ->  t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a f args -> (

let uu____6651 = (FStar_List.map as_a args)
in (lift_unary f uu____6651)))


let binary_op : 'a . (arg  ->  'a FStar_Pervasives_Native.option)  ->  ('a  ->  'a  ->  t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a f args -> (

let uu____6706 = (FStar_List.map as_a args)
in (lift_binary f uu____6706)))


let unary_int_op : (FStar_BigInt.t  ->  FStar_BigInt.t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (unary_op arg_as_int (fun x -> (

let uu____6736 = (f x)
in (embed e_int bogus_cbs uu____6736)))))


let binary_int_op : (FStar_BigInt.t  ->  FStar_BigInt.t  ->  FStar_BigInt.t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_int (fun x y -> (

let uu____6763 = (f x y)
in (embed e_int bogus_cbs uu____6763)))))


let unary_bool_op : (Prims.bool  ->  Prims.bool)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (unary_op arg_as_bool (fun x -> (

let uu____6789 = (f x)
in (embed e_bool bogus_cbs uu____6789)))))


let binary_bool_op : (Prims.bool  ->  Prims.bool  ->  Prims.bool)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_bool (fun x y -> (

let uu____6827 = (f x y)
in (embed e_bool bogus_cbs uu____6827)))))


let binary_string_op : (Prims.string  ->  Prims.string  ->  Prims.string)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_string (fun x y -> (

let uu____6865 = (f x y)
in (embed e_string bogus_cbs uu____6865)))))


let mixed_binary_op : 'a 'b 'c . (arg  ->  'a FStar_Pervasives_Native.option)  ->  (arg  ->  'b FStar_Pervasives_Native.option)  ->  ('c  ->  t)  ->  ('a  ->  'b  ->  'c)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a as_b embed_c f args -> (match (args) with
| (a)::(b)::[] -> begin
(

let uu____6970 = (

let uu____6979 = (as_a a)
in (

let uu____6982 = (as_b b)
in ((uu____6979), (uu____6982))))
in (match (uu____6970) with
| (FStar_Pervasives_Native.Some (a1), FStar_Pervasives_Native.Some (b1)) -> begin
(

let uu____6997 = (

let uu____6998 = (f a1 b1)
in (embed_c uu____6998))
in FStar_Pervasives_Native.Some (uu____6997))
end
| uu____6999 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7008 -> begin
FStar_Pervasives_Native.None
end))


let list_of_string' : Prims.string  ->  t = (fun s -> (

let uu____7017 = (e_list e_char)
in (

let uu____7024 = (FStar_String.list_of_string s)
in (embed uu____7017 bogus_cbs uu____7024))))


let string_of_list' : FStar_Char.char Prims.list  ->  t = (fun l -> (

let s = (FStar_String.string_of_list l)
in Constant (String (((s), (FStar_Range.dummyRange))))))


let string_compare' : Prims.string  ->  Prims.string  ->  t = (fun s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____7063 = (

let uu____7064 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____7064))
in (embed e_int bogus_cbs uu____7063))))


let string_concat' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7098 = (arg_as_string a1)
in (match (uu____7098) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7107 = (arg_as_list e_string a2)
in (match (uu____7107) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____7125 = (embed e_string bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7125)))
end
| uu____7127 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7133 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7137 -> begin
FStar_Pervasives_Native.None
end))


let string_of_int : FStar_BigInt.t  ->  t = (fun i -> (

let uu____7144 = (FStar_BigInt.string_of_big_int i)
in (embed e_string bogus_cbs uu____7144)))


let string_of_bool : Prims.bool  ->  t = (fun b -> (embed e_string bogus_cbs (match (b) with
| true -> begin
"true"
end
| uu____7159 -> begin
"false"
end)))


let string_lowercase : Prims.string  ->  t = (fun s -> (embed e_string bogus_cbs (FStar_String.lowercase s)))


let string_uppercase : Prims.string  ->  t = (fun s -> (embed e_string bogus_cbs (FStar_String.lowercase s)))


let decidable_eq : Prims.bool  ->  args  ->  t FStar_Pervasives_Native.option = (fun neg args -> (

let tru = (embed e_bool bogus_cbs true)
in (

let fal = (embed e_bool bogus_cbs false)
in (match (args) with
| ((_typ, uu____7206))::((a1, uu____7208))::((a2, uu____7210))::[] -> begin
(

let uu____7227 = (eq_t a1 a2)
in (match (uu____7227) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____7231 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____7234 -> begin
fal
end))
end
| uu____7236 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7237 -> begin
(failwith "Unexpected number of arguments")
end))))


let interp_prop_eq2 : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((_u, uu____7252))::((_typ, uu____7254))::((a1, uu____7256))::((a2, uu____7258))::[] -> begin
(

let uu____7279 = (eq_t a1 a2)
in (match (uu____7279) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____7282 = (embed e_bool bogus_cbs true)
in FStar_Pervasives_Native.Some (uu____7282))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____7285 = (embed e_bool bogus_cbs false)
in FStar_Pervasives_Native.Some (uu____7285))
end
| FStar_Syntax_Util.Unknown -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7288 -> begin
(failwith "Unexpected number of arguments")
end))


let interp_prop_eq3 : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((_u, uu____7303))::((_v, uu____7305))::((t1, uu____7307))::((t2, uu____7309))::((a1, uu____7311))::((a2, uu____7313))::[] -> begin
(

let uu____7342 = (

let uu____7343 = (eq_t t1 t2)
in (

let uu____7344 = (eq_t a1 a2)
in (FStar_Syntax_Util.eq_inj uu____7343 uu____7344)))
in (match (uu____7342) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____7347 = (embed e_bool bogus_cbs true)
in FStar_Pervasives_Native.Some (uu____7347))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____7350 = (embed e_bool bogus_cbs false)
in FStar_Pervasives_Native.Some (uu____7350))
end
| FStar_Syntax_Util.Unknown -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7353 -> begin
(failwith "Unexpected number of arguments")
end))


let dummy_interp : FStar_Ident.lid  ->  args  ->  t FStar_Pervasives_Native.option = (fun lid args -> (

let uu____7372 = (

let uu____7374 = (FStar_Ident.string_of_lid lid)
in (FStar_String.op_Hat "No interpretation for " uu____7374))
in (failwith uu____7372)))


let prims_to_fstar_range_step : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((a1, uu____7390))::[] -> begin
(

let uu____7399 = (unembed e_range bogus_cbs a1)
in (match (uu____7399) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7405 = (embed e_range bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7405))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7406 -> begin
(failwith "Unexpected number of arguments")
end))


let string_split' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7442 = (arg_as_list e_char a1)
in (match (uu____7442) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7458 = (arg_as_string a2)
in (match (uu____7458) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.split s1 s2)
in (

let uu____7471 = (

let uu____7472 = (e_list e_string)
in (embed uu____7472 bogus_cbs r))
in FStar_Pervasives_Native.Some (uu____7471)))
end
| uu____7482 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7486 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7492 -> begin
FStar_Pervasives_Native.None
end))


let string_index : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7525 = (

let uu____7535 = (arg_as_string a1)
in (

let uu____7539 = (arg_as_int a2)
in ((uu____7535), (uu____7539))))
in (match (uu____7525) with
| (FStar_Pervasives_Native.Some (s), FStar_Pervasives_Native.Some (i)) -> begin
(FStar_All.try_with (fun uu___981_7563 -> (match (()) with
| () -> begin
(

let r = (FStar_String.index s i)
in (

let uu____7568 = (embed e_char bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7568)))
end)) (fun uu___980_7571 -> FStar_Pervasives_Native.None))
end
| uu____7574 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7584 -> begin
FStar_Pervasives_Native.None
end))


let string_index_of : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7617 = (

let uu____7628 = (arg_as_string a1)
in (

let uu____7632 = (arg_as_char a2)
in ((uu____7628), (uu____7632))))
in (match (uu____7617) with
| (FStar_Pervasives_Native.Some (s), FStar_Pervasives_Native.Some (c)) -> begin
(FStar_All.try_with (fun uu___999_7661 -> (match (()) with
| () -> begin
(

let r = (FStar_String.index_of s c)
in (

let uu____7665 = (embed e_int bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7665)))
end)) (fun uu___998_7667 -> FStar_Pervasives_Native.None))
end
| uu____7670 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7681 -> begin
FStar_Pervasives_Native.None
end))


let string_substring' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::(a3)::[] -> begin
(

let uu____7723 = (

let uu____7737 = (arg_as_string a1)
in (

let uu____7741 = (arg_as_int a2)
in (

let uu____7744 = (arg_as_int a3)
in ((uu____7737), (uu____7741), (uu____7744)))))
in (match (uu____7723) with
| (FStar_Pervasives_Native.Some (s1), FStar_Pervasives_Native.Some (n1), FStar_Pervasives_Native.Some (n2)) -> begin
(

let n11 = (FStar_BigInt.to_int_fs n1)
in (

let n21 = (FStar_BigInt.to_int_fs n2)
in (FStar_All.try_with (fun uu___1022_7777 -> (match (()) with
| () -> begin
(

let r = (FStar_String.substring s1 n11 n21)
in (

let uu____7782 = (embed e_string bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7782)))
end)) (fun uu___1021_7785 -> FStar_Pervasives_Native.None))))
end
| uu____7788 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7802 -> begin
FStar_Pervasives_Native.None
end))


let mk_range : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____7862 = (

let uu____7884 = (arg_as_string fn)
in (

let uu____7888 = (arg_as_int from_line)
in (

let uu____7891 = (arg_as_int from_col)
in (

let uu____7894 = (arg_as_int to_line)
in (

let uu____7897 = (arg_as_int to_col)
in ((uu____7884), (uu____7888), (uu____7891), (uu____7894), (uu____7897)))))))
in (match (uu____7862) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____7932 = (

let uu____7933 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____7935 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____7933 uu____7935)))
in (

let uu____7937 = (

let uu____7938 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____7940 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____7938 uu____7940)))
in (FStar_Range.mk_range fn1 uu____7932 uu____7937)))
in (

let uu____7942 = (embed e_range bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7942)))
end
| uu____7943 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7965 -> begin
FStar_Pervasives_Native.None
end))


let arrow_as_prim_step_1 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8055 = (FStar_List.splitAt n_tvars args)
in (match (uu____8055) with
| (_tvar_args, rest_args) -> begin
(

let uu____8104 = (FStar_List.hd rest_args)
in (match (uu____8104) with
| (x, uu____8116) -> begin
(

let uu____8117 = (unembed ea cb x)
in (FStar_Util.map_opt uu____8117 (fun x1 -> (

let uu____8123 = (f x1)
in (embed eb cb uu____8123)))))
end))
end)))
in f_wrapped))


let arrow_as_prim_step_2 : 'a 'b 'c . 'a embedding  ->  'b embedding  ->  'c embedding  ->  ('a  ->  'b  ->  'c)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb ec f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8232 = (FStar_List.splitAt n_tvars args)
in (match (uu____8232) with
| (_tvar_args, rest_args) -> begin
(

let uu____8281 = (FStar_List.hd rest_args)
in (match (uu____8281) with
| (x, uu____8293) -> begin
(

let uu____8294 = (

let uu____8299 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____8299))
in (match (uu____8294) with
| (y, uu____8317) -> begin
(

let uu____8318 = (unembed ea cb x)
in (FStar_Util.bind_opt uu____8318 (fun x1 -> (

let uu____8324 = (unembed eb cb y)
in (FStar_Util.bind_opt uu____8324 (fun y1 -> (

let uu____8330 = (

let uu____8331 = (f x1 y1)
in (embed ec cb uu____8331))
in FStar_Pervasives_Native.Some (uu____8330))))))))
end))
end))
end)))
in f_wrapped))


let arrow_as_prim_step_3 : 'a 'b 'c 'd . 'a embedding  ->  'b embedding  ->  'c embedding  ->  'd embedding  ->  ('a  ->  'b  ->  'c  ->  'd)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb ec ed f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8459 = (FStar_List.splitAt n_tvars args)
in (match (uu____8459) with
| (_tvar_args, rest_args) -> begin
(

let uu____8508 = (FStar_List.hd rest_args)
in (match (uu____8508) with
| (x, uu____8520) -> begin
(

let uu____8521 = (

let uu____8526 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____8526))
in (match (uu____8521) with
| (y, uu____8544) -> begin
(

let uu____8545 = (

let uu____8550 = (

let uu____8557 = (FStar_List.tl rest_args)
in (FStar_List.tl uu____8557))
in (FStar_List.hd uu____8550))
in (match (uu____8545) with
| (z, uu____8579) -> begin
(

let uu____8580 = (unembed ea cb x)
in (FStar_Util.bind_opt uu____8580 (fun x1 -> (

let uu____8586 = (unembed eb cb y)
in (FStar_Util.bind_opt uu____8586 (fun y1 -> (

let uu____8592 = (unembed ec cb z)
in (FStar_Util.bind_opt uu____8592 (fun z1 -> (

let uu____8598 = (

let uu____8599 = (f x1 y1 z1)
in (embed ed cb uu____8599))
in FStar_Pervasives_Native.Some (uu____8598)))))))))))
end))
end))
end))
end)))
in f_wrapped))




