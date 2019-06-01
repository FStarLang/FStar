
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
| Lazy of ((FStar_Syntax_Syntax.lazyinfo, (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t FStar_Common.thunk)
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


let __proj__Lazy__item___0 : t  ->  ((FStar_Syntax_Syntax.lazyinfo, (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t FStar_Common.thunk) = (fun projectee -> (match (projectee) with
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
| Lam (b, args, arity, uu____2755) -> begin
(

let uu____2800 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____2811 = (FStar_Util.string_of_int arity)
in (FStar_Util.format2 "Lam (_, %s args, %s)" uu____2800 uu____2811)))
end
| Accu (a, l) -> begin
(

let uu____2828 = (

let uu____2830 = (atom_to_string a)
in (

let uu____2832 = (

let uu____2834 = (

let uu____2836 = (

let uu____2838 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2838))
in (FStar_String.op_Hat uu____2836 ")"))
in (FStar_String.op_Hat ") (" uu____2834))
in (FStar_String.op_Hat uu____2830 uu____2832)))
in (FStar_String.op_Hat "Accu (" uu____2828))
end
| Construct (fv, us, l) -> begin
(

let uu____2876 = (

let uu____2878 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____2880 = (

let uu____2882 = (

let uu____2884 = (

let uu____2886 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_String.concat "; " uu____2886))
in (

let uu____2892 = (

let uu____2894 = (

let uu____2896 = (

let uu____2898 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2898))
in (FStar_String.op_Hat uu____2896 "]"))
in (FStar_String.op_Hat "] [" uu____2894))
in (FStar_String.op_Hat uu____2884 uu____2892)))
in (FStar_String.op_Hat ") [" uu____2882))
in (FStar_String.op_Hat uu____2878 uu____2880)))
in (FStar_String.op_Hat "Construct (" uu____2876))
end
| FV (fv, us, l) -> begin
(

let uu____2937 = (

let uu____2939 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____2941 = (

let uu____2943 = (

let uu____2945 = (

let uu____2947 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_String.concat "; " uu____2947))
in (

let uu____2953 = (

let uu____2955 = (

let uu____2957 = (

let uu____2959 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2959))
in (FStar_String.op_Hat uu____2957 "]"))
in (FStar_String.op_Hat "] [" uu____2955))
in (FStar_String.op_Hat uu____2945 uu____2953)))
in (FStar_String.op_Hat ") [" uu____2943))
in (FStar_String.op_Hat uu____2939 uu____2941)))
in (FStar_String.op_Hat "FV (" uu____2937))
end
| Constant (c) -> begin
(constant_to_string c)
end
| Univ (u) -> begin
(

let uu____2981 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_String.op_Hat "Universe " uu____2981))
end
| Type_t (u) -> begin
(

let uu____2985 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_String.op_Hat "Type_t " uu____2985))
end
| Arrow (uu____2988) -> begin
"Arrow"
end
| Refinement (f, t) -> begin
(

let x1 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (

let t1 = (

let uu____3034 = (t ())
in (FStar_Pervasives_Native.fst uu____3034))
in (

let uu____3039 = (

let uu____3041 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____3043 = (

let uu____3045 = (

let uu____3047 = (t_to_string t1)
in (

let uu____3049 = (

let uu____3051 = (

let uu____3053 = (

let uu____3055 = (

let uu____3056 = (mkAccuVar x1)
in (f uu____3056))
in (t_to_string uu____3055))
in (FStar_String.op_Hat uu____3053 "}"))
in (FStar_String.op_Hat "{" uu____3051))
in (FStar_String.op_Hat uu____3047 uu____3049)))
in (FStar_String.op_Hat ":" uu____3045))
in (FStar_String.op_Hat uu____3041 uu____3043)))
in (FStar_String.op_Hat "Refinement " uu____3039))))
end
| Unknown -> begin
"Unknown"
end
| Reflect (t) -> begin
(

let uu____3063 = (t_to_string t)
in (FStar_String.op_Hat "Reflect " uu____3063))
end
| Quote (uu____3066) -> begin
"Quote _"
end
| Lazy (FStar_Util.Inl (li), uu____3073) -> begin
(

let uu____3090 = (

let uu____3092 = (FStar_Syntax_Util.unfold_lazy li)
in (FStar_Syntax_Print.term_to_string uu____3092))
in (FStar_Util.format1 "Lazy (Inl {%s})" uu____3090))
end
| Lazy (FStar_Util.Inr (uu____3094, et), uu____3096) -> begin
(

let uu____3113 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3113))
end
| Rec (uu____3116, uu____3117, l, uu____3119, uu____3120, uu____3121, uu____3122) -> begin
(

let uu____3167 = (

let uu____3169 = (

let uu____3171 = (FStar_List.map t_to_string l)
in (FStar_String.concat "; " uu____3171))
in (FStar_String.op_Hat uu____3169 ")"))
in (FStar_String.op_Hat "Rec (" uu____3167))
end))
and atom_to_string : atom  ->  Prims.string = (fun a -> (match (a) with
| Var (v1) -> begin
(

let uu____3182 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_String.op_Hat "Var " uu____3182))
end
| Match (t, uu____3186, uu____3187) -> begin
(

let uu____3210 = (t_to_string t)
in (FStar_String.op_Hat "Match " uu____3210))
end))
and arg_to_string : arg  ->  Prims.string = (fun a -> (

let uu____3214 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3214 t_to_string)))
and args_to_string : args  ->  Prims.string = (fun args -> (

let uu____3221 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3221 (FStar_String.concat " "))))

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

let uu____3692 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mkConstruct uu____3692 us args)))


let lid_as_typ : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun l us args -> (

let uu____3713 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____3713 us args)))


let as_iarg : t  ->  arg = (fun a -> ((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))


let as_arg : t  ->  arg = (fun a -> ((a), (FStar_Pervasives_Native.None)))


let make_arrow1 : t  ->  arg  ->  t = (fun t1 a -> Arrow ((((fun uu____3754 -> Tot (((t1), (FStar_Pervasives_Native.None))))), (((fun uu____3769 -> a))::[]))))


let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ  ->  'a  ->  (unit  ->  t)  ->  t = (fun et x f -> ((

let uu____3812 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____3812) with
| true -> begin
(

let uu____3836 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3836))
end
| uu____3839 -> begin
()
end));
(

let uu____3841 = (FStar_ST.op_Bang FStar_Options.eager_embedding)
in (match (uu____3841) with
| true -> begin
(f ())
end
| uu____3865 -> begin
(

let thunk1 = (FStar_Common.mk_thunk f)
in (

let li = (

let uu____3875 = (FStar_Dyn.mkdyn x)
in ((uu____3875), (et)))
in Lazy (((FStar_Util.Inr (li)), (thunk1)))))
end));
))


let lazy_unembed : 'Auu____3903 'a . 'Auu____3903  ->  FStar_Syntax_Syntax.emb_typ  ->  t  ->  (t  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun cb et x f -> (match (x) with
| Lazy (FStar_Util.Inl (li), thunk1) -> begin
(

let uu____3954 = (FStar_Common.force_thunk thunk1)
in (f uu____3954))
end
| Lazy (FStar_Util.Inr (b, et'), thunk1) -> begin
(

let uu____3974 = ((Prims.op_disEquality et et') || (FStar_ST.op_Bang FStar_Options.eager_embedding))
in (match (uu____3974) with
| true -> begin
(

let res = (

let uu____4003 = (FStar_Common.force_thunk thunk1)
in (f uu____4003))
in ((

let uu____4005 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4005) with
| true -> begin
(

let uu____4029 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____4031 = (FStar_Syntax_Print.emb_typ_to_string et')
in (FStar_Util.print2 "Unembed cancellation failed\n\t%s <> %s\n" uu____4029 uu____4031)))
end
| uu____4034 -> begin
()
end));
res;
))
end
| uu____4036 -> begin
(

let a = (FStar_Dyn.undyn b)
in ((

let uu____4040 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4040) with
| true -> begin
(

let uu____4064 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Unembed cancelled for %s\n" uu____4064))
end
| uu____4067 -> begin
()
end));
FStar_Pervasives_Native.Some (a);
))
end))
end
| uu____4069 -> begin
(

let aopt = (f x)
in ((

let uu____4074 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4074) with
| true -> begin
(

let uu____4098 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4098))
end
| uu____4101 -> begin
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

let uu____4166 = (lid_as_typ FStar_Parser_Const.term_lid [] [])
in (mk_emb em un uu____4166 FStar_Syntax_Syntax.ET_abstract))))


let e_unit : unit embedding = (

let em = (fun _cb a -> Constant (Unit))
in (

let un = (fun _cb t -> FStar_Pervasives_Native.Some (()))
in (

let uu____4200 = (lid_as_typ FStar_Parser_Const.unit_lid [] [])
in (

let uu____4205 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (mk_emb em un uu____4200 uu____4205)))))


let e_bool : Prims.bool embedding = (

let em = (fun _cb a -> Constant (Bool (a)))
in (

let un = (fun _cb t -> (match (t) with
| Constant (Bool (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4246 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4248 = (lid_as_typ FStar_Parser_Const.bool_lid [] [])
in (

let uu____4253 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (mk_emb em un uu____4248 uu____4253)))))


let e_char : FStar_Char.char embedding = (

let em = (fun _cb c -> Constant (Char (c)))
in (

let un = (fun _cb c -> (match (c) with
| Constant (Char (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4295 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4297 = (lid_as_typ FStar_Parser_Const.char_lid [] [])
in (

let uu____4302 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char)
in (mk_emb em un uu____4297 uu____4302)))))


let e_string : Prims.string embedding = (

let em = (fun _cb s -> Constant (String (((s), (FStar_Range.dummyRange)))))
in (

let un = (fun _cb s -> (match (s) with
| Constant (String (s1, uu____4344)) -> begin
FStar_Pervasives_Native.Some (s1)
end
| uu____4348 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4350 = (lid_as_typ FStar_Parser_Const.string_lid [] [])
in (

let uu____4355 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string)
in (mk_emb em un uu____4350 uu____4355)))))


let e_int : FStar_BigInt.t embedding = (

let em = (fun _cb c -> Constant (Int (c)))
in (

let un = (fun _cb c -> (match (c) with
| Constant (Int (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4390 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4391 = (lid_as_typ FStar_Parser_Const.int_lid [] [])
in (

let uu____4396 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int)
in (mk_emb em un uu____4391 uu____4396)))))


let e_option : 'a . 'a embedding  ->  'a FStar_Pervasives_Native.option embedding = (fun ea -> (

let etyp = (

let uu____4417 = (

let uu____4425 = (FStar_All.pipe_right FStar_Parser_Const.option_lid FStar_Ident.string_of_lid)
in ((uu____4425), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4417))
in (

let em = (fun cb o -> (lazy_embed etyp o (fun uu____4450 -> (match (o) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4451 = (

let uu____4452 = (

let uu____4457 = (type_of ea)
in (as_iarg uu____4457))
in (uu____4452)::[])
in (lid_as_constr FStar_Parser_Const.none_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4451))
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4467 = (

let uu____4468 = (

let uu____4473 = (embed ea cb x)
in (as_arg uu____4473))
in (

let uu____4474 = (

let uu____4481 = (

let uu____4486 = (type_of ea)
in (as_iarg uu____4486))
in (uu____4481)::[])
in (uu____4468)::uu____4474))
in (lid_as_constr FStar_Parser_Const.some_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4467))
end))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, args) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| Construct (fvar1, us, ((a, uu____4553))::(uu____4554)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid) -> begin
(

let uu____4581 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____4581 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (a1)))))
end
| uu____4590 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____4593 = (

let uu____4594 = (

let uu____4595 = (

let uu____4600 = (type_of ea)
in (as_arg uu____4600))
in (uu____4595)::[])
in (lid_as_typ FStar_Parser_Const.option_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4594))
in (mk_emb em un uu____4593 etyp))))))


let e_tuple2 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a * 'b) embedding = (fun ea eb -> (

let etyp = (

let uu____4647 = (

let uu____4655 = (FStar_All.pipe_right FStar_Parser_Const.lid_tuple2 FStar_Ident.string_of_lid)
in ((uu____4655), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4647))
in (

let em = (fun cb x -> (lazy_embed etyp x (fun uu____4686 -> (

let uu____4687 = (

let uu____4688 = (

let uu____4693 = (embed eb cb (FStar_Pervasives_Native.snd x))
in (as_arg uu____4693))
in (

let uu____4694 = (

let uu____4701 = (

let uu____4706 = (embed ea cb (FStar_Pervasives_Native.fst x))
in (as_arg uu____4706))
in (

let uu____4707 = (

let uu____4714 = (

let uu____4719 = (type_of eb)
in (as_iarg uu____4719))
in (

let uu____4720 = (

let uu____4727 = (

let uu____4732 = (type_of ea)
in (as_iarg uu____4732))
in (uu____4727)::[])
in (uu____4714)::uu____4720))
in (uu____4701)::uu____4707))
in (uu____4688)::uu____4694))
in (lid_as_constr FStar_Parser_Const.lid_Mktuple2 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4687)))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, ((b, uu____4800))::((a, uu____4802))::(uu____4803)::(uu____4804)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.lid_Mktuple2) -> begin
(

let uu____4843 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____4843 (fun a1 -> (

let uu____4853 = (unembed eb cb b)
in (FStar_Util.bind_opt uu____4853 (fun b1 -> FStar_Pervasives_Native.Some (((a1), (b1)))))))))
end
| uu____4866 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____4871 = (

let uu____4872 = (

let uu____4873 = (

let uu____4878 = (type_of eb)
in (as_arg uu____4878))
in (

let uu____4879 = (

let uu____4886 = (

let uu____4891 = (type_of ea)
in (as_arg uu____4891))
in (uu____4886)::[])
in (uu____4873)::uu____4879))
in (lid_as_typ FStar_Parser_Const.lid_tuple2 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4872))
in (mk_emb em un uu____4871 etyp))))))


let e_either : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a, 'b) FStar_Util.either embedding = (fun ea eb -> (

let etyp = (

let uu____4944 = (

let uu____4952 = (FStar_All.pipe_right FStar_Parser_Const.either_lid FStar_Ident.string_of_lid)
in ((uu____4952), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4944))
in (

let em = (fun cb s -> (lazy_embed etyp s (fun uu____4984 -> (match (s) with
| FStar_Util.Inl (a) -> begin
(

let uu____4986 = (

let uu____4987 = (

let uu____4992 = (embed ea cb a)
in (as_arg uu____4992))
in (

let uu____4993 = (

let uu____5000 = (

let uu____5005 = (type_of eb)
in (as_iarg uu____5005))
in (

let uu____5006 = (

let uu____5013 = (

let uu____5018 = (type_of ea)
in (as_iarg uu____5018))
in (uu____5013)::[])
in (uu____5000)::uu____5006))
in (uu____4987)::uu____4993))
in (lid_as_constr FStar_Parser_Const.inl_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4986))
end
| FStar_Util.Inr (b) -> begin
(

let uu____5036 = (

let uu____5037 = (

let uu____5042 = (embed eb cb b)
in (as_arg uu____5042))
in (

let uu____5043 = (

let uu____5050 = (

let uu____5055 = (type_of eb)
in (as_iarg uu____5055))
in (

let uu____5056 = (

let uu____5063 = (

let uu____5068 = (type_of ea)
in (as_iarg uu____5068))
in (uu____5063)::[])
in (uu____5050)::uu____5056))
in (uu____5037)::uu____5043))
in (lid_as_constr FStar_Parser_Const.inr_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5036))
end))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, ((a, uu____5130))::(uu____5131)::(uu____5132)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid) -> begin
(

let uu____5167 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____5167 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Util.Inl (a1)))))
end
| Construct (fvar1, us, ((b, uu____5183))::(uu____5184)::(uu____5185)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid) -> begin
(

let uu____5220 = (unembed eb cb b)
in (FStar_Util.bind_opt uu____5220 (fun b1 -> FStar_Pervasives_Native.Some (FStar_Util.Inr (b1)))))
end
| uu____5233 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5238 = (

let uu____5239 = (

let uu____5240 = (

let uu____5245 = (type_of eb)
in (as_arg uu____5245))
in (

let uu____5246 = (

let uu____5253 = (

let uu____5258 = (type_of ea)
in (as_arg uu____5258))
in (uu____5253)::[])
in (uu____5240)::uu____5246))
in (lid_as_typ FStar_Parser_Const.either_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5239))
in (mk_emb em un uu____5238 etyp))))))


let e_range : FStar_Range.range embedding = (

let em = (fun cb r -> Constant (Range (r)))
in (

let un = (fun cb t -> (match (t) with
| Constant (Range (r)) -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____5307 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5308 = (lid_as_typ FStar_Parser_Const.range_lid [] [])
in (

let uu____5313 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range)
in (mk_emb em un uu____5308 uu____5313)))))


let e_list : 'a . 'a embedding  ->  'a Prims.list embedding = (fun ea -> (

let etyp = (

let uu____5334 = (

let uu____5342 = (FStar_All.pipe_right FStar_Parser_Const.list_lid FStar_Ident.string_of_lid)
in ((uu____5342), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____5334))
in (

let em = (fun cb l -> (lazy_embed etyp l (fun uu____5369 -> (

let typ = (

let uu____5371 = (type_of ea)
in (as_iarg uu____5371))
in (

let nil = (lid_as_constr FStar_Parser_Const.nil_lid ((FStar_Syntax_Syntax.U_zero)::[]) ((typ)::[]))
in (

let cons1 = (fun hd1 tl1 -> (

let uu____5392 = (

let uu____5393 = (as_arg tl1)
in (

let uu____5398 = (

let uu____5405 = (

let uu____5410 = (embed ea cb hd1)
in (as_arg uu____5410))
in (uu____5405)::(typ)::[])
in (uu____5393)::uu____5398))
in (lid_as_constr FStar_Parser_Const.cons_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____5392)))
in (FStar_List.fold_right cons1 l nil)))))))
in (

let rec un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fv, uu____5458, uu____5459) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| Construct (fv, uu____5479, ((tl1, FStar_Pervasives_Native.None))::((hd1, FStar_Pervasives_Native.None))::((uu____5482, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5483))))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5511 = (unembed ea cb hd1)
in (FStar_Util.bind_opt uu____5511 (fun hd2 -> (

let uu____5519 = (un cb tl1)
in (FStar_Util.bind_opt uu____5519 (fun tl2 -> FStar_Pervasives_Native.Some ((hd2)::tl2)))))))
end
| Construct (fv, uu____5535, ((tl1, FStar_Pervasives_Native.None))::((hd1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5560 = (unembed ea cb hd1)
in (FStar_Util.bind_opt uu____5560 (fun hd2 -> (

let uu____5568 = (un cb tl1)
in (FStar_Util.bind_opt uu____5568 (fun tl2 -> FStar_Pervasives_Native.Some ((hd2)::tl2)))))))
end
| uu____5583 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5586 = (

let uu____5587 = (

let uu____5588 = (

let uu____5593 = (type_of ea)
in (as_arg uu____5593))
in (uu____5588)::[])
in (lid_as_typ FStar_Parser_Const.list_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____5587))
in (mk_emb em un uu____5586 etyp))))))


let e_string_list : Prims.string Prims.list embedding = (e_list e_string)


let e_arrow : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b) embedding = (fun ea eb -> (

let etyp = FStar_Syntax_Syntax.ET_fun (((ea.emb_typ), (eb.emb_typ)))
in (

let em = (fun cb f -> (lazy_embed etyp f (fun uu____5666 -> Lam ((((fun tas -> (

let uu____5696 = (

let uu____5699 = (FStar_List.hd tas)
in (unembed ea cb uu____5699))
in (match (uu____5696) with
| FStar_Pervasives_Native.Some (a) -> begin
(

let uu____5701 = (f a)
in (embed eb cb uu____5701))
end
| FStar_Pervasives_Native.None -> begin
(failwith "cannot unembed function argument")
end)))), (((fun uu____5714 -> (

let uu____5717 = (type_of eb)
in (as_arg uu____5717))))::[]), ((Prims.parse_int "1")), (FStar_Pervasives_Native.None))))))
in (

let un = (fun cb lam -> (

let k = (fun lam1 -> FStar_Pervasives_Native.Some ((fun x -> (

let uu____5775 = (

let uu____5778 = (

let uu____5779 = (

let uu____5780 = (

let uu____5785 = (embed ea cb x)
in (as_arg uu____5785))
in (uu____5780)::[])
in (cb.iapp lam1 uu____5779))
in (unembed eb cb uu____5778))
in (match (uu____5775) with
| FStar_Pervasives_Native.Some (y) -> begin
y
end
| FStar_Pervasives_Native.None -> begin
(failwith "cannot unembed function result")
end)))))
in (lazy_unembed cb etyp lam k)))
in (

let uu____5799 = (

let uu____5800 = (type_of ea)
in (

let uu____5801 = (

let uu____5802 = (type_of eb)
in (as_iarg uu____5802))
in (make_arrow1 uu____5800 uu____5801)))
in (mk_emb em un uu____5799 etyp))))))


let e_norm_step : FStar_Syntax_Embeddings.norm_step embedding = (

let em = (fun cb n1 -> (match (n1) with
| FStar_Syntax_Embeddings.Simpl -> begin
(

let uu____5820 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5820 [] []))
end
| FStar_Syntax_Embeddings.Weak -> begin
(

let uu____5825 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5825 [] []))
end
| FStar_Syntax_Embeddings.HNF -> begin
(

let uu____5830 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5830 [] []))
end
| FStar_Syntax_Embeddings.Primops -> begin
(

let uu____5835 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5835 [] []))
end
| FStar_Syntax_Embeddings.Delta -> begin
(

let uu____5840 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5840 [] []))
end
| FStar_Syntax_Embeddings.Zeta -> begin
(

let uu____5845 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5845 [] []))
end
| FStar_Syntax_Embeddings.Iota -> begin
(

let uu____5850 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5850 [] []))
end
| FStar_Syntax_Embeddings.Reify -> begin
(

let uu____5855 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5855 [] []))
end
| FStar_Syntax_Embeddings.NBE -> begin
(

let uu____5860 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5860 [] []))
end
| FStar_Syntax_Embeddings.UnfoldOnly (l) -> begin
(

let uu____5869 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5870 = (

let uu____5871 = (

let uu____5876 = (

let uu____5877 = (e_list e_string)
in (embed uu____5877 cb l))
in (as_arg uu____5876))
in (uu____5871)::[])
in (mkFV uu____5869 [] uu____5870)))
end
| FStar_Syntax_Embeddings.UnfoldFully (l) -> begin
(

let uu____5899 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5900 = (

let uu____5901 = (

let uu____5906 = (

let uu____5907 = (e_list e_string)
in (embed uu____5907 cb l))
in (as_arg uu____5906))
in (uu____5901)::[])
in (mkFV uu____5899 [] uu____5900)))
end
| FStar_Syntax_Embeddings.UnfoldAttr (l) -> begin
(

let uu____5929 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5930 = (

let uu____5931 = (

let uu____5936 = (

let uu____5937 = (e_list e_string)
in (embed uu____5937 cb l))
in (as_arg uu____5936))
in (uu____5931)::[])
in (mkFV uu____5929 [] uu____5930)))
end))
in (

let un = (fun cb t0 -> (match (t0) with
| FV (fv, uu____5971, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Simpl)
end
| FV (fv, uu____5987, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Weak)
end
| FV (fv, uu____6003, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.HNF)
end
| FV (fv, uu____6019, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Primops)
end
| FV (fv, uu____6035, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Delta)
end
| FV (fv, uu____6051, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Zeta)
end
| FV (fv, uu____6067, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Iota)
end
| FV (fv, uu____6083, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.NBE)
end
| FV (fv, uu____6099, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Reify)
end
| FV (fv, uu____6115, ((l, uu____6117))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly) -> begin
(

let uu____6136 = (

let uu____6142 = (e_list e_string)
in (unembed uu____6142 cb l))
in (FStar_Util.bind_opt uu____6136 (fun ss -> (FStar_All.pipe_left (fun _6162 -> FStar_Pervasives_Native.Some (_6162)) (FStar_Syntax_Embeddings.UnfoldOnly (ss))))))
end
| FV (fv, uu____6164, ((l, uu____6166))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully) -> begin
(

let uu____6185 = (

let uu____6191 = (e_list e_string)
in (unembed uu____6191 cb l))
in (FStar_Util.bind_opt uu____6185 (fun ss -> (FStar_All.pipe_left (fun _6211 -> FStar_Pervasives_Native.Some (_6211)) (FStar_Syntax_Embeddings.UnfoldFully (ss))))))
end
| FV (fv, uu____6213, ((l, uu____6215))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr) -> begin
(

let uu____6234 = (

let uu____6240 = (e_list e_string)
in (unembed uu____6240 cb l))
in (FStar_Util.bind_opt uu____6234 (fun ss -> (FStar_All.pipe_left (fun _6260 -> FStar_Pervasives_Native.Some (_6260)) (FStar_Syntax_Embeddings.UnfoldAttr (ss))))))
end
| uu____6261 -> begin
((

let uu____6263 = (

let uu____6269 = (

let uu____6271 = (t_to_string t0)
in (FStar_Util.format1 "Not an embedded norm_step: %s" uu____6271))
in ((FStar_Errors.Warning_NotEmbedded), (uu____6269)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____6263));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____6275 = (

let uu____6276 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____6276 [] []))
in (

let uu____6281 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step)
in (mk_emb em un uu____6275 uu____6281)))))


let bogus_cbs : nbe_cbs = {iapp = (fun h _args -> h); translate = (fun uu____6290 -> (failwith "bogus_cbs translate"))}


let arg_as_int : arg  ->  FStar_BigInt.t FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_int bogus_cbs)))


let arg_as_bool : arg  ->  Prims.bool FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_bool bogus_cbs)))


let arg_as_char : arg  ->  FStar_Char.char FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_char bogus_cbs)))


let arg_as_string : arg  ->  Prims.string FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_string bogus_cbs)))


let arg_as_list : 'a . 'a embedding  ->  arg  ->  'a Prims.list FStar_Pervasives_Native.option = (fun e a -> (

let uu____6367 = (

let uu____6376 = (e_list e)
in (unembed uu____6376 bogus_cbs))
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6367)))


let arg_as_bounded_int : arg  ->  (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option = (fun uu____6398 -> (match (uu____6398) with
| (a, uu____6406) -> begin
(match (a) with
| FV (fv1, [], ((Constant (Int (i)), uu____6421))::[]) when (

let uu____6438 = (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.ends_with uu____6438 "int_to_t")) -> begin
FStar_Pervasives_Native.Some (((fv1), (i)))
end
| uu____6445 -> begin
FStar_Pervasives_Native.None
end)
end))


let int_as_bounded : FStar_Syntax_Syntax.fv  ->  FStar_BigInt.t  ->  t = (fun int_to_t1 n1 -> (

let c = (embed e_int bogus_cbs n1)
in (

let int_to_t2 = (fun args -> FV (((int_to_t1), ([]), (args))))
in (

let uu____6488 = (

let uu____6495 = (as_arg c)
in (uu____6495)::[])
in (int_to_t2 uu____6488)))))


let lift_unary : 'a 'b . ('a  ->  'b)  ->  'a FStar_Pervasives_Native.option Prims.list  ->  'b FStar_Pervasives_Native.option = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____6549 = (f a)
in FStar_Pervasives_Native.Some (uu____6549))
end
| uu____6550 -> begin
FStar_Pervasives_Native.None
end))


let lift_binary : 'a 'b . ('a  ->  'a  ->  'b)  ->  'a FStar_Pervasives_Native.option Prims.list  ->  'b FStar_Pervasives_Native.option = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____6604 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____6604))
end
| uu____6605 -> begin
FStar_Pervasives_Native.None
end))


let unary_op : 'a . (arg  ->  'a FStar_Pervasives_Native.option)  ->  ('a  ->  t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a f args -> (

let uu____6649 = (FStar_List.map as_a args)
in (lift_unary f uu____6649)))


let binary_op : 'a . (arg  ->  'a FStar_Pervasives_Native.option)  ->  ('a  ->  'a  ->  t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a f args -> (

let uu____6704 = (FStar_List.map as_a args)
in (lift_binary f uu____6704)))


let unary_int_op : (FStar_BigInt.t  ->  FStar_BigInt.t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (unary_op arg_as_int (fun x -> (

let uu____6734 = (f x)
in (embed e_int bogus_cbs uu____6734)))))


let binary_int_op : (FStar_BigInt.t  ->  FStar_BigInt.t  ->  FStar_BigInt.t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_int (fun x y -> (

let uu____6761 = (f x y)
in (embed e_int bogus_cbs uu____6761)))))


let unary_bool_op : (Prims.bool  ->  Prims.bool)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (unary_op arg_as_bool (fun x -> (

let uu____6787 = (f x)
in (embed e_bool bogus_cbs uu____6787)))))


let binary_bool_op : (Prims.bool  ->  Prims.bool  ->  Prims.bool)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_bool (fun x y -> (

let uu____6825 = (f x y)
in (embed e_bool bogus_cbs uu____6825)))))


let binary_string_op : (Prims.string  ->  Prims.string  ->  Prims.string)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_string (fun x y -> (

let uu____6863 = (f x y)
in (embed e_string bogus_cbs uu____6863)))))


let mixed_binary_op : 'a 'b 'c . (arg  ->  'a FStar_Pervasives_Native.option)  ->  (arg  ->  'b FStar_Pervasives_Native.option)  ->  ('c  ->  t)  ->  ('a  ->  'b  ->  'c)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a as_b embed_c f args -> (match (args) with
| (a)::(b)::[] -> begin
(

let uu____6968 = (

let uu____6977 = (as_a a)
in (

let uu____6980 = (as_b b)
in ((uu____6977), (uu____6980))))
in (match (uu____6968) with
| (FStar_Pervasives_Native.Some (a1), FStar_Pervasives_Native.Some (b1)) -> begin
(

let uu____6995 = (

let uu____6996 = (f a1 b1)
in (embed_c uu____6996))
in FStar_Pervasives_Native.Some (uu____6995))
end
| uu____6997 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7006 -> begin
FStar_Pervasives_Native.None
end))


let list_of_string' : Prims.string  ->  t = (fun s -> (

let uu____7015 = (e_list e_char)
in (

let uu____7022 = (FStar_String.list_of_string s)
in (embed uu____7015 bogus_cbs uu____7022))))


let string_of_list' : FStar_Char.char Prims.list  ->  t = (fun l -> (

let s = (FStar_String.string_of_list l)
in Constant (String (((s), (FStar_Range.dummyRange))))))


let string_compare' : Prims.string  ->  Prims.string  ->  t = (fun s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____7061 = (

let uu____7062 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____7062))
in (embed e_int bogus_cbs uu____7061))))


let string_concat' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7096 = (arg_as_string a1)
in (match (uu____7096) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7105 = (arg_as_list e_string a2)
in (match (uu____7105) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____7123 = (embed e_string bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7123)))
end
| uu____7125 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7131 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7135 -> begin
FStar_Pervasives_Native.None
end))


let string_of_int : FStar_BigInt.t  ->  t = (fun i -> (

let uu____7142 = (FStar_BigInt.string_of_big_int i)
in (embed e_string bogus_cbs uu____7142)))


let string_of_bool : Prims.bool  ->  t = (fun b -> (embed e_string bogus_cbs (match (b) with
| true -> begin
"true"
end
| uu____7157 -> begin
"false"
end)))


let string_lowercase : Prims.string  ->  t = (fun s -> (embed e_string bogus_cbs (FStar_String.lowercase s)))


let string_uppercase : Prims.string  ->  t = (fun s -> (embed e_string bogus_cbs (FStar_String.lowercase s)))


let decidable_eq : Prims.bool  ->  args  ->  t FStar_Pervasives_Native.option = (fun neg args -> (

let tru = (embed e_bool bogus_cbs true)
in (

let fal = (embed e_bool bogus_cbs false)
in (match (args) with
| ((_typ, uu____7204))::((a1, uu____7206))::((a2, uu____7208))::[] -> begin
(

let uu____7225 = (eq_t a1 a2)
in (match (uu____7225) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____7229 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____7232 -> begin
fal
end))
end
| uu____7234 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7235 -> begin
(failwith "Unexpected number of arguments")
end))))


let interp_prop_eq2 : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((_u, uu____7250))::((_typ, uu____7252))::((a1, uu____7254))::((a2, uu____7256))::[] -> begin
(

let uu____7277 = (eq_t a1 a2)
in (match (uu____7277) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____7280 = (embed e_bool bogus_cbs true)
in FStar_Pervasives_Native.Some (uu____7280))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____7283 = (embed e_bool bogus_cbs false)
in FStar_Pervasives_Native.Some (uu____7283))
end
| FStar_Syntax_Util.Unknown -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7286 -> begin
(failwith "Unexpected number of arguments")
end))


let interp_prop_eq3 : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((_u, uu____7301))::((_v, uu____7303))::((t1, uu____7305))::((t2, uu____7307))::((a1, uu____7309))::((a2, uu____7311))::[] -> begin
(

let uu____7340 = (

let uu____7341 = (eq_t t1 t2)
in (

let uu____7342 = (eq_t a1 a2)
in (FStar_Syntax_Util.eq_inj uu____7341 uu____7342)))
in (match (uu____7340) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____7345 = (embed e_bool bogus_cbs true)
in FStar_Pervasives_Native.Some (uu____7345))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____7348 = (embed e_bool bogus_cbs false)
in FStar_Pervasives_Native.Some (uu____7348))
end
| FStar_Syntax_Util.Unknown -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7351 -> begin
(failwith "Unexpected number of arguments")
end))


let dummy_interp : FStar_Ident.lid  ->  args  ->  t FStar_Pervasives_Native.option = (fun lid args -> (

let uu____7370 = (

let uu____7372 = (FStar_Ident.string_of_lid lid)
in (FStar_String.op_Hat "No interpretation for " uu____7372))
in (failwith uu____7370)))


let prims_to_fstar_range_step : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((a1, uu____7388))::[] -> begin
(

let uu____7397 = (unembed e_range bogus_cbs a1)
in (match (uu____7397) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7403 = (embed e_range bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7403))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7404 -> begin
(failwith "Unexpected number of arguments")
end))


let string_split' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7440 = (arg_as_list e_char a1)
in (match (uu____7440) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7456 = (arg_as_string a2)
in (match (uu____7456) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.split s1 s2)
in (

let uu____7469 = (

let uu____7470 = (e_list e_string)
in (embed uu____7470 bogus_cbs r))
in FStar_Pervasives_Native.Some (uu____7469)))
end
| uu____7480 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7484 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7490 -> begin
FStar_Pervasives_Native.None
end))


let string_index : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7523 = (

let uu____7533 = (arg_as_string a1)
in (

let uu____7537 = (arg_as_int a2)
in ((uu____7533), (uu____7537))))
in (match (uu____7523) with
| (FStar_Pervasives_Native.Some (s), FStar_Pervasives_Native.Some (i)) -> begin
(FStar_All.try_with (fun uu___981_7561 -> (match (()) with
| () -> begin
(

let r = (FStar_String.index s i)
in (

let uu____7566 = (embed e_char bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7566)))
end)) (fun uu___980_7569 -> FStar_Pervasives_Native.None))
end
| uu____7572 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7582 -> begin
FStar_Pervasives_Native.None
end))


let string_index_of : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7615 = (

let uu____7626 = (arg_as_string a1)
in (

let uu____7630 = (arg_as_char a2)
in ((uu____7626), (uu____7630))))
in (match (uu____7615) with
| (FStar_Pervasives_Native.Some (s), FStar_Pervasives_Native.Some (c)) -> begin
(FStar_All.try_with (fun uu___999_7659 -> (match (()) with
| () -> begin
(

let r = (FStar_String.index_of s c)
in (

let uu____7663 = (embed e_int bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7663)))
end)) (fun uu___998_7665 -> FStar_Pervasives_Native.None))
end
| uu____7668 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7679 -> begin
FStar_Pervasives_Native.None
end))


let string_substring' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::(a3)::[] -> begin
(

let uu____7721 = (

let uu____7735 = (arg_as_string a1)
in (

let uu____7739 = (arg_as_int a2)
in (

let uu____7742 = (arg_as_int a3)
in ((uu____7735), (uu____7739), (uu____7742)))))
in (match (uu____7721) with
| (FStar_Pervasives_Native.Some (s1), FStar_Pervasives_Native.Some (n1), FStar_Pervasives_Native.Some (n2)) -> begin
(

let n11 = (FStar_BigInt.to_int_fs n1)
in (

let n21 = (FStar_BigInt.to_int_fs n2)
in (FStar_All.try_with (fun uu___1022_7775 -> (match (()) with
| () -> begin
(

let r = (FStar_String.substring s1 n11 n21)
in (

let uu____7780 = (embed e_string bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7780)))
end)) (fun uu___1021_7783 -> FStar_Pervasives_Native.None))))
end
| uu____7786 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7800 -> begin
FStar_Pervasives_Native.None
end))


let mk_range : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____7860 = (

let uu____7882 = (arg_as_string fn)
in (

let uu____7886 = (arg_as_int from_line)
in (

let uu____7889 = (arg_as_int from_col)
in (

let uu____7892 = (arg_as_int to_line)
in (

let uu____7895 = (arg_as_int to_col)
in ((uu____7882), (uu____7886), (uu____7889), (uu____7892), (uu____7895)))))))
in (match (uu____7860) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____7930 = (

let uu____7931 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____7933 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____7931 uu____7933)))
in (

let uu____7935 = (

let uu____7936 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____7938 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____7936 uu____7938)))
in (FStar_Range.mk_range fn1 uu____7930 uu____7935)))
in (

let uu____7940 = (embed e_range bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7940)))
end
| uu____7941 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7963 -> begin
FStar_Pervasives_Native.None
end))


let arrow_as_prim_step_1 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8053 = (FStar_List.splitAt n_tvars args)
in (match (uu____8053) with
| (_tvar_args, rest_args) -> begin
(

let uu____8102 = (FStar_List.hd rest_args)
in (match (uu____8102) with
| (x, uu____8114) -> begin
(

let uu____8115 = (unembed ea cb x)
in (FStar_Util.map_opt uu____8115 (fun x1 -> (

let uu____8121 = (f x1)
in (embed eb cb uu____8121)))))
end))
end)))
in f_wrapped))


let arrow_as_prim_step_2 : 'a 'b 'c . 'a embedding  ->  'b embedding  ->  'c embedding  ->  ('a  ->  'b  ->  'c)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb ec f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8230 = (FStar_List.splitAt n_tvars args)
in (match (uu____8230) with
| (_tvar_args, rest_args) -> begin
(

let uu____8279 = (FStar_List.hd rest_args)
in (match (uu____8279) with
| (x, uu____8291) -> begin
(

let uu____8292 = (

let uu____8297 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____8297))
in (match (uu____8292) with
| (y, uu____8315) -> begin
(

let uu____8316 = (unembed ea cb x)
in (FStar_Util.bind_opt uu____8316 (fun x1 -> (

let uu____8322 = (unembed eb cb y)
in (FStar_Util.bind_opt uu____8322 (fun y1 -> (

let uu____8328 = (

let uu____8329 = (f x1 y1)
in (embed ec cb uu____8329))
in FStar_Pervasives_Native.Some (uu____8328))))))))
end))
end))
end)))
in f_wrapped))


let arrow_as_prim_step_3 : 'a 'b 'c 'd . 'a embedding  ->  'b embedding  ->  'c embedding  ->  'd embedding  ->  ('a  ->  'b  ->  'c  ->  'd)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb ec ed f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8457 = (FStar_List.splitAt n_tvars args)
in (match (uu____8457) with
| (_tvar_args, rest_args) -> begin
(

let uu____8506 = (FStar_List.hd rest_args)
in (match (uu____8506) with
| (x, uu____8518) -> begin
(

let uu____8519 = (

let uu____8524 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____8524))
in (match (uu____8519) with
| (y, uu____8542) -> begin
(

let uu____8543 = (

let uu____8548 = (

let uu____8555 = (FStar_List.tl rest_args)
in (FStar_List.tl uu____8555))
in (FStar_List.hd uu____8548))
in (match (uu____8543) with
| (z, uu____8577) -> begin
(

let uu____8578 = (unembed ea cb x)
in (FStar_Util.bind_opt uu____8578 (fun x1 -> (

let uu____8584 = (unembed eb cb y)
in (FStar_Util.bind_opt uu____8584 (fun y1 -> (

let uu____8590 = (unembed ec cb z)
in (FStar_Util.bind_opt uu____8590 (fun z1 -> (

let uu____8596 = (

let uu____8597 = (f x1 y1 z1)
in (embed ed cb uu____8597))
in FStar_Pervasives_Native.Some (uu____8596)))))))))))
end))
end))
end))
end)))
in f_wrapped))




