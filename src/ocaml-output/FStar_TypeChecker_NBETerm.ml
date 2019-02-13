
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
| uu____44 -> begin
false
end))


let uu___is_Bool : constant  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
true
end
| uu____57 -> begin
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
| uu____80 -> begin
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
| uu____105 -> begin
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
| uu____141 -> begin
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
| uu____164 -> begin
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
| uu____547 -> begin
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
| uu____584 -> begin
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
| uu____685 -> begin
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
| uu____805 -> begin
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
| uu____869 -> begin
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
| uu____945 -> begin
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
| uu____1007 -> begin
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
| uu____1027 -> begin
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
| uu____1066 -> begin
false
end))


let uu___is_Arrow : t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arrow (_0) -> begin
true
end
| uu____1098 -> begin
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
| uu____1192 -> begin
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
| uu____1254 -> begin
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
| uu____1278 -> begin
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
| uu____1324 -> begin
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
| uu____1422 -> begin
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
| uu____1556 -> begin
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
| uu____1600 -> begin
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
| uu____1638 -> begin
false
end))


let __proj__Comp__item___0 : comp  ->  comp_typ = (fun projectee -> (match (projectee) with
| Comp (_0) -> begin
_0
end))


let __proj__Mkcomp_typ__item__comp_univs : comp_typ  ->  FStar_Syntax_Syntax.universes = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags1} -> begin
comp_univs
end))


let __proj__Mkcomp_typ__item__effect_name : comp_typ  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags1} -> begin
effect_name
end))


let __proj__Mkcomp_typ__item__result_typ : comp_typ  ->  t = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags1} -> begin
result_typ
end))


let __proj__Mkcomp_typ__item__effect_args : comp_typ  ->  (t * FStar_Syntax_Syntax.aqual) Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags1} -> begin
effect_args
end))


let __proj__Mkcomp_typ__item__flags : comp_typ  ->  cflag Prims.list = (fun projectee -> (match (projectee) with
| {comp_univs = comp_univs; effect_name = effect_name; result_typ = result_typ; effect_args = effect_args; flags = flags1} -> begin
flags1
end))


let uu___is_TOTAL : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TOTAL -> begin
true
end
| uu____1768 -> begin
false
end))


let uu___is_MLEFFECT : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MLEFFECT -> begin
true
end
| uu____1779 -> begin
false
end))


let uu___is_RETURN : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| RETURN -> begin
true
end
| uu____1790 -> begin
false
end))


let uu___is_PARTIAL_RETURN : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PARTIAL_RETURN -> begin
true
end
| uu____1801 -> begin
false
end))


let uu___is_SOMETRIVIAL : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SOMETRIVIAL -> begin
true
end
| uu____1812 -> begin
false
end))


let uu___is_TRIVIAL_POSTCONDITION : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TRIVIAL_POSTCONDITION -> begin
true
end
| uu____1823 -> begin
false
end))


let uu___is_SHOULD_NOT_INLINE : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SHOULD_NOT_INLINE -> begin
true
end
| uu____1834 -> begin
false
end))


let uu___is_LEMMA : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LEMMA -> begin
true
end
| uu____1845 -> begin
false
end))


let uu___is_CPS : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPS -> begin
true
end
| uu____1856 -> begin
false
end))


let uu___is_DECREASES : cflag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DECREASES (_0) -> begin
true
end
| uu____1868 -> begin
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
| Accu (uu____1945) -> begin
true
end
| uu____1957 -> begin
false
end))


let isNotAccu : t  ->  Prims.bool = (fun x -> (match (x) with
| Accu (uu____1967, uu____1968) -> begin
false
end
| uu____1982 -> begin
true
end))


let mkConstruct : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun i us ts -> Construct (((i), (us), (ts))))


let mkFV : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun i us ts -> FV (((i), (us), (ts))))


let mkAccuVar : var  ->  t = (fun v1 -> Accu (((Var (v1)), ([]))))


let mkAccuMatch : t  ->  (t  ->  t)  ->  ((t  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.branch Prims.list)  ->  t = (fun s cases bs -> Accu (((Match (((s), (cases), (bs)))), ([]))))


let equal_if : Prims.bool  ->  FStar_Syntax_Util.eq_result = (fun uu___238_2118 -> (match (uu___238_2118) with
| true -> begin
FStar_Syntax_Util.Equal
end
| uu____2121 -> begin
FStar_Syntax_Util.Unknown
end))


let equal_iff : Prims.bool  ->  FStar_Syntax_Util.eq_result = (fun uu___239_2129 -> (match (uu___239_2129) with
| true -> begin
FStar_Syntax_Util.Equal
end
| uu____2132 -> begin
FStar_Syntax_Util.NotEqual
end))


let eq_inj : FStar_Syntax_Util.eq_result  ->  FStar_Syntax_Util.eq_result  ->  FStar_Syntax_Util.eq_result = (fun r1 r2 -> (match (((r1), (r2))) with
| (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) -> begin
FStar_Syntax_Util.Equal
end
| (FStar_Syntax_Util.NotEqual, uu____2145) -> begin
FStar_Syntax_Util.NotEqual
end
| (uu____2146, FStar_Syntax_Util.NotEqual) -> begin
FStar_Syntax_Util.NotEqual
end
| (FStar_Syntax_Util.Unknown, uu____2147) -> begin
FStar_Syntax_Util.Unknown
end
| (uu____2148, FStar_Syntax_Util.Unknown) -> begin
FStar_Syntax_Util.Unknown
end))


let eq_and : FStar_Syntax_Util.eq_result  ->  (unit  ->  FStar_Syntax_Util.eq_result)  ->  FStar_Syntax_Util.eq_result = (fun f g -> (match (f) with
| FStar_Syntax_Util.Equal -> begin
(g ())
end
| uu____2165 -> begin
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
| (String (s1, uu____2185), String (s2, uu____2187)) -> begin
(equal_iff (Prims.op_Equality s1 s2))
end
| (Char (c11), Char (c21)) -> begin
(equal_iff (Prims.op_Equality c11 c21))
end
| (Range (r1), Range (r2)) -> begin
FStar_Syntax_Util.Unknown
end
| (uu____2200, uu____2201) -> begin
FStar_Syntax_Util.NotEqual
end))


let rec eq_t : t  ->  t  ->  FStar_Syntax_Util.eq_result = (fun t1 t2 -> (match (((t1), (t2))) with
| (Lam (uu____2237), Lam (uu____2238)) -> begin
FStar_Syntax_Util.Unknown
end
| (Accu (a1, as1), Accu (a2, as2)) -> begin
(

let uu____2327 = (eq_atom a1 a2)
in (eq_and uu____2327 (fun uu____2329 -> (eq_args as1 as2))))
end
| (Construct (v1, us1, args1), Construct (v2, us2, args2)) -> begin
(

let uu____2368 = (FStar_Syntax_Syntax.fv_eq v1 v2)
in (match (uu____2368) with
| true -> begin
((match ((Prims.op_disEquality (FStar_List.length args1) (FStar_List.length args2))) with
| true -> begin
(failwith "eq_t, different number of args on Construct")
end
| uu____2382 -> begin
()
end);
(

let uu____2384 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2441 -> (match (uu____2441) with
| ((a1, uu____2455), (a2, uu____2457)) -> begin
(

let uu____2466 = (eq_t a1 a2)
in (eq_inj acc uu____2466))
end)) FStar_Syntax_Util.Equal) uu____2384));
)
end
| uu____2467 -> begin
FStar_Syntax_Util.NotEqual
end))
end
| (FV (v1, us1, args1), FV (v2, us2, args2)) -> begin
(

let uu____2507 = (FStar_Syntax_Syntax.fv_eq v1 v2)
in (match (uu____2507) with
| true -> begin
(

let uu____2510 = (

let uu____2511 = (FStar_Syntax_Util.eq_univs_list us1 us2)
in (equal_iff uu____2511))
in (eq_and uu____2510 (fun uu____2514 -> (eq_args args1 args2))))
end
| uu____2515 -> begin
FStar_Syntax_Util.Unknown
end))
end
| (Constant (c1), Constant (c2)) -> begin
(eq_constant c1 c2)
end
| (Type_t (u1), Type_t (u2)) -> begin
(

let uu____2521 = (FStar_Syntax_Util.eq_univs u1 u2)
in (equal_iff uu____2521))
end
| (Univ (u1), Univ (u2)) -> begin
(

let uu____2525 = (FStar_Syntax_Util.eq_univs u1 u2)
in (equal_iff uu____2525))
end
| (Refinement (r1, t11), Refinement (r2, t21)) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (

let uu____2572 = (

let uu____2573 = (

let uu____2574 = (t11 ())
in (FStar_Pervasives_Native.fst uu____2574))
in (

let uu____2579 = (

let uu____2580 = (t21 ())
in (FStar_Pervasives_Native.fst uu____2580))
in (eq_t uu____2573 uu____2579)))
in (eq_and uu____2572 (fun uu____2588 -> (

let uu____2589 = (

let uu____2590 = (mkAccuVar x)
in (r1 uu____2590))
in (

let uu____2591 = (

let uu____2592 = (mkAccuVar x)
in (r2 uu____2592))
in (eq_t uu____2589 uu____2591)))))))
end
| (Unknown, Unknown) -> begin
FStar_Syntax_Util.Equal
end
| (uu____2593, uu____2594) -> begin
FStar_Syntax_Util.Unknown
end))
and eq_atom : atom  ->  atom  ->  FStar_Syntax_Util.eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| (Var (bv1), Var (bv2)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2))
end
| (uu____2599, uu____2600) -> begin
FStar_Syntax_Util.Unknown
end))
and eq_arg : arg  ->  arg  ->  FStar_Syntax_Util.eq_result = (fun a1 a2 -> (eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)))
and eq_args : args  ->  args  ->  FStar_Syntax_Util.eq_result = (fun as1 as2 -> (match (((as1), (as2))) with
| ([], []) -> begin
FStar_Syntax_Util.Equal
end
| ((x)::xs, (y)::ys) -> begin
(

let uu____2681 = (eq_arg x y)
in (eq_and uu____2681 (fun uu____2683 -> (eq_args xs ys))))
end
| (uu____2684, uu____2685) -> begin
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
| uu____2724 -> begin
"Bool false"
end)
end
| Int (i) -> begin
(FStar_BigInt.string_of_big_int i)
end
| Char (c1) -> begin
(FStar_Util.format1 "\'%s\'" (FStar_Util.string_of_char c1))
end
| String (s, uu____2732) -> begin
(FStar_Util.format1 "\"%s\"" s)
end
| Range (r) -> begin
(

let uu____2737 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "Range %s" uu____2737))
end))


let rec t_to_string : t  ->  Prims.string = (fun x -> (match (x) with
| Lam (b, args, arity, uu____2766) -> begin
(

let uu____2811 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____2822 = (FStar_Util.string_of_int arity)
in (FStar_Util.format2 "Lam (_, %s args, %s)" uu____2811 uu____2822)))
end
| Accu (a, l) -> begin
(

let uu____2839 = (

let uu____2841 = (atom_to_string a)
in (

let uu____2843 = (

let uu____2845 = (

let uu____2847 = (

let uu____2849 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2849))
in (Prims.strcat uu____2847 ")"))
in (Prims.strcat ") (" uu____2845))
in (Prims.strcat uu____2841 uu____2843)))
in (Prims.strcat "Accu (" uu____2839))
end
| Construct (fv, us, l) -> begin
(

let uu____2887 = (

let uu____2889 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____2891 = (

let uu____2893 = (

let uu____2895 = (

let uu____2897 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_String.concat "; " uu____2897))
in (

let uu____2903 = (

let uu____2905 = (

let uu____2907 = (

let uu____2909 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2909))
in (Prims.strcat uu____2907 "]"))
in (Prims.strcat "] [" uu____2905))
in (Prims.strcat uu____2895 uu____2903)))
in (Prims.strcat ") [" uu____2893))
in (Prims.strcat uu____2889 uu____2891)))
in (Prims.strcat "Construct (" uu____2887))
end
| FV (fv, us, l) -> begin
(

let uu____2948 = (

let uu____2950 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____2952 = (

let uu____2954 = (

let uu____2956 = (

let uu____2958 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_String.concat "; " uu____2958))
in (

let uu____2964 = (

let uu____2966 = (

let uu____2968 = (

let uu____2970 = (FStar_List.map (fun x1 -> (t_to_string (FStar_Pervasives_Native.fst x1))) l)
in (FStar_String.concat "; " uu____2970))
in (Prims.strcat uu____2968 "]"))
in (Prims.strcat "] [" uu____2966))
in (Prims.strcat uu____2956 uu____2964)))
in (Prims.strcat ") [" uu____2954))
in (Prims.strcat uu____2950 uu____2952)))
in (Prims.strcat "FV (" uu____2948))
end
| Constant (c) -> begin
(constant_to_string c)
end
| Univ (u) -> begin
(

let uu____2992 = (FStar_Syntax_Print.univ_to_string u)
in (Prims.strcat "Universe " uu____2992))
end
| Type_t (u) -> begin
(

let uu____2996 = (FStar_Syntax_Print.univ_to_string u)
in (Prims.strcat "Type_t " uu____2996))
end
| Arrow (uu____2999) -> begin
"Arrow"
end
| Refinement (f, t) -> begin
(

let x1 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (

let t1 = (

let uu____3045 = (t ())
in (FStar_Pervasives_Native.fst uu____3045))
in (

let uu____3050 = (

let uu____3052 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____3054 = (

let uu____3056 = (

let uu____3058 = (t_to_string t1)
in (

let uu____3060 = (

let uu____3062 = (

let uu____3064 = (

let uu____3066 = (

let uu____3067 = (mkAccuVar x1)
in (f uu____3067))
in (t_to_string uu____3066))
in (Prims.strcat uu____3064 "}"))
in (Prims.strcat "{" uu____3062))
in (Prims.strcat uu____3058 uu____3060)))
in (Prims.strcat ":" uu____3056))
in (Prims.strcat uu____3052 uu____3054)))
in (Prims.strcat "Refinement " uu____3050))))
end
| Unknown -> begin
"Unknown"
end
| Reflect (t) -> begin
(

let uu____3074 = (t_to_string t)
in (Prims.strcat "Reflect " uu____3074))
end
| Quote (uu____3077) -> begin
"Quote _"
end
| Lazy (FStar_Util.Inl (li), uu____3084) -> begin
(

let uu____3101 = (

let uu____3103 = (FStar_Syntax_Util.unfold_lazy li)
in (FStar_Syntax_Print.term_to_string uu____3103))
in (FStar_Util.format1 "Lazy (Inl {%s})" uu____3101))
end
| Lazy (FStar_Util.Inr (uu____3105, et), uu____3107) -> begin
(

let uu____3124 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3124))
end
| Rec (uu____3127, uu____3128, l, uu____3130, uu____3131, uu____3132, uu____3133) -> begin
(

let uu____3178 = (

let uu____3180 = (

let uu____3182 = (FStar_List.map t_to_string l)
in (FStar_String.concat "; " uu____3182))
in (Prims.strcat uu____3180 ")"))
in (Prims.strcat "Rec (" uu____3178))
end))
and atom_to_string : atom  ->  Prims.string = (fun a -> (match (a) with
| Var (v1) -> begin
(

let uu____3193 = (FStar_Syntax_Print.bv_to_string v1)
in (Prims.strcat "Var " uu____3193))
end
| Match (t, uu____3197, uu____3198) -> begin
(

let uu____3221 = (t_to_string t)
in (Prims.strcat "Match " uu____3221))
end))
and arg_to_string : arg  ->  Prims.string = (fun a -> (

let uu____3225 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3225 t_to_string)))
and args_to_string : args  ->  Prims.string = (fun args -> (

let uu____3232 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3232 (FStar_String.concat " "))))

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

let uu____3703 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mkConstruct uu____3703 us args)))


let lid_as_typ : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe Prims.list  ->  args  ->  t = (fun l us args -> (

let uu____3724 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____3724 us args)))


let as_iarg : t  ->  arg = (fun a -> ((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))


let as_arg : t  ->  arg = (fun a -> ((a), (FStar_Pervasives_Native.None)))


let make_arrow1 : t  ->  arg  ->  t = (fun t1 a -> Arrow ((((fun uu____3765 -> Tot (((t1), (FStar_Pervasives_Native.None))))), (((fun uu____3780 -> a))::[]))))


let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ  ->  'a  ->  (unit  ->  t)  ->  t = (fun et x f -> ((

let uu____3823 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____3823) with
| true -> begin
(

let uu____3847 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3847))
end
| uu____3850 -> begin
()
end));
(

let uu____3852 = (FStar_ST.op_Bang FStar_Options.eager_embedding)
in (match (uu____3852) with
| true -> begin
(f ())
end
| uu____3876 -> begin
(

let thunk1 = (FStar_Common.mk_thunk f)
in (

let li = (

let uu____3886 = (FStar_Dyn.mkdyn x)
in ((uu____3886), (et)))
in Lazy (((FStar_Util.Inr (li)), (thunk1)))))
end));
))


let lazy_unembed : 'Auu____3954 'a . 'Auu____3954  ->  FStar_Syntax_Syntax.emb_typ  ->  t  ->  (t  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun cb et x f -> (match (x) with
| Lazy (FStar_Util.Inl (li), thunk1) -> begin
(

let uu____4005 = (FStar_Common.force_thunk thunk1)
in (f uu____4005))
end
| Lazy (FStar_Util.Inr (b, et'), thunk1) -> begin
(

let uu____4065 = ((Prims.op_disEquality et et') || (FStar_ST.op_Bang FStar_Options.eager_embedding))
in (match (uu____4065) with
| true -> begin
(

let res = (

let uu____4094 = (FStar_Common.force_thunk thunk1)
in (f uu____4094))
in ((

let uu____4136 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4136) with
| true -> begin
(

let uu____4160 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____4162 = (FStar_Syntax_Print.emb_typ_to_string et')
in (FStar_Util.print2 "Unembed cancellation failed\n\t%s <> %s\n" uu____4160 uu____4162)))
end
| uu____4165 -> begin
()
end));
res;
))
end
| uu____4167 -> begin
(

let a = (FStar_Dyn.undyn b)
in ((

let uu____4171 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4171) with
| true -> begin
(

let uu____4195 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Unembed cancelled for %s\n" uu____4195))
end
| uu____4198 -> begin
()
end));
FStar_Pervasives_Native.Some (a);
))
end))
end
| uu____4200 -> begin
(

let aopt = (f x)
in ((

let uu____4205 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____4205) with
| true -> begin
(

let uu____4229 = (FStar_Syntax_Print.emb_typ_to_string et)
in (FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4229))
end
| uu____4232 -> begin
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

let uu____4297 = (lid_as_typ FStar_Parser_Const.term_lid [] [])
in (mk_emb em un uu____4297 FStar_Syntax_Syntax.ET_abstract))))


let e_unit : unit embedding = (

let em = (fun _cb a -> Constant (Unit))
in (

let un = (fun _cb t -> FStar_Pervasives_Native.Some (()))
in (

let uu____4331 = (lid_as_typ FStar_Parser_Const.unit_lid [] [])
in (

let uu____4336 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (mk_emb em un uu____4331 uu____4336)))))


let e_bool : Prims.bool embedding = (

let em = (fun _cb a -> Constant (Bool (a)))
in (

let un = (fun _cb t -> (match (t) with
| Constant (Bool (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4377 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4379 = (lid_as_typ FStar_Parser_Const.bool_lid [] [])
in (

let uu____4384 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit)
in (mk_emb em un uu____4379 uu____4384)))))


let e_char : FStar_Char.char embedding = (

let em = (fun _cb c -> Constant (Char (c)))
in (

let un = (fun _cb c -> (match (c) with
| Constant (Char (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4426 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4428 = (lid_as_typ FStar_Parser_Const.char_lid [] [])
in (

let uu____4433 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char)
in (mk_emb em un uu____4428 uu____4433)))))


let e_string : Prims.string embedding = (

let em = (fun _cb s -> Constant (String (((s), (FStar_Range.dummyRange)))))
in (

let un = (fun _cb s -> (match (s) with
| Constant (String (s1, uu____4475)) -> begin
FStar_Pervasives_Native.Some (s1)
end
| uu____4479 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4481 = (lid_as_typ FStar_Parser_Const.string_lid [] [])
in (

let uu____4486 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string)
in (mk_emb em un uu____4481 uu____4486)))))


let e_int : FStar_BigInt.t embedding = (

let em = (fun _cb c -> Constant (Int (c)))
in (

let un = (fun _cb c -> (match (c) with
| Constant (Int (a)) -> begin
FStar_Pervasives_Native.Some (a)
end
| uu____4521 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____4522 = (lid_as_typ FStar_Parser_Const.int_lid [] [])
in (

let uu____4527 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int)
in (mk_emb em un uu____4522 uu____4527)))))


let e_option : 'a . 'a embedding  ->  'a FStar_Pervasives_Native.option embedding = (fun ea -> (

let etyp = (

let uu____4548 = (

let uu____4556 = (FStar_All.pipe_right FStar_Parser_Const.option_lid FStar_Ident.string_of_lid)
in ((uu____4556), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4548))
in (

let em = (fun cb o -> (lazy_embed etyp o (fun uu____4581 -> (match (o) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4582 = (

let uu____4583 = (

let uu____4588 = (type_of ea)
in (as_iarg uu____4588))
in (uu____4583)::[])
in (lid_as_constr FStar_Parser_Const.none_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4582))
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____4598 = (

let uu____4599 = (

let uu____4604 = (embed ea cb x)
in (as_arg uu____4604))
in (

let uu____4605 = (

let uu____4612 = (

let uu____4617 = (type_of ea)
in (as_iarg uu____4617))
in (uu____4612)::[])
in (uu____4599)::uu____4605))
in (lid_as_constr FStar_Parser_Const.some_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4598))
end))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, args) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| Construct (fvar1, us, ((a, uu____4684))::(uu____4685)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid) -> begin
(

let uu____4712 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____4712 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (a1)))))
end
| uu____4721 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____4724 = (

let uu____4725 = (

let uu____4726 = (

let uu____4731 = (type_of ea)
in (as_arg uu____4731))
in (uu____4726)::[])
in (lid_as_typ FStar_Parser_Const.option_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____4725))
in (mk_emb em un uu____4724 etyp))))))


let e_tuple2 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a * 'b) embedding = (fun ea eb -> (

let etyp = (

let uu____4778 = (

let uu____4786 = (FStar_All.pipe_right FStar_Parser_Const.lid_tuple2 FStar_Ident.string_of_lid)
in ((uu____4786), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4778))
in (

let em = (fun cb x -> (lazy_embed etyp x (fun uu____4817 -> (

let uu____4818 = (

let uu____4819 = (

let uu____4824 = (embed eb cb (FStar_Pervasives_Native.snd x))
in (as_arg uu____4824))
in (

let uu____4825 = (

let uu____4832 = (

let uu____4837 = (embed ea cb (FStar_Pervasives_Native.fst x))
in (as_arg uu____4837))
in (

let uu____4838 = (

let uu____4845 = (

let uu____4850 = (type_of eb)
in (as_iarg uu____4850))
in (

let uu____4851 = (

let uu____4858 = (

let uu____4863 = (type_of ea)
in (as_iarg uu____4863))
in (uu____4858)::[])
in (uu____4845)::uu____4851))
in (uu____4832)::uu____4838))
in (uu____4819)::uu____4825))
in (lid_as_constr FStar_Parser_Const.lid_Mktuple2 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____4818)))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, ((b, uu____4931))::((a, uu____4933))::(uu____4934)::(uu____4935)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.lid_Mktuple2) -> begin
(

let uu____4974 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____4974 (fun a1 -> (

let uu____4984 = (unembed eb cb b)
in (FStar_Util.bind_opt uu____4984 (fun b1 -> FStar_Pervasives_Native.Some (((a1), (b1)))))))))
end
| uu____4997 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5002 = (

let uu____5003 = (

let uu____5004 = (

let uu____5009 = (type_of eb)
in (as_arg uu____5009))
in (

let uu____5010 = (

let uu____5017 = (

let uu____5022 = (type_of ea)
in (as_arg uu____5022))
in (uu____5017)::[])
in (uu____5004)::uu____5010))
in (lid_as_typ FStar_Parser_Const.lid_tuple2 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5003))
in (mk_emb em un uu____5002 etyp))))))


let e_either : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a, 'b) FStar_Util.either embedding = (fun ea eb -> (

let etyp = (

let uu____5075 = (

let uu____5083 = (FStar_All.pipe_right FStar_Parser_Const.either_lid FStar_Ident.string_of_lid)
in ((uu____5083), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____5075))
in (

let em = (fun cb s -> (lazy_embed etyp s (fun uu____5115 -> (match (s) with
| FStar_Util.Inl (a) -> begin
(

let uu____5117 = (

let uu____5118 = (

let uu____5123 = (embed ea cb a)
in (as_arg uu____5123))
in (

let uu____5124 = (

let uu____5131 = (

let uu____5136 = (type_of eb)
in (as_iarg uu____5136))
in (

let uu____5137 = (

let uu____5144 = (

let uu____5149 = (type_of ea)
in (as_iarg uu____5149))
in (uu____5144)::[])
in (uu____5131)::uu____5137))
in (uu____5118)::uu____5124))
in (lid_as_constr FStar_Parser_Const.inl_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5117))
end
| FStar_Util.Inr (b) -> begin
(

let uu____5167 = (

let uu____5168 = (

let uu____5173 = (embed eb cb b)
in (as_arg uu____5173))
in (

let uu____5174 = (

let uu____5181 = (

let uu____5186 = (type_of eb)
in (as_iarg uu____5186))
in (

let uu____5187 = (

let uu____5194 = (

let uu____5199 = (type_of ea)
in (as_iarg uu____5199))
in (uu____5194)::[])
in (uu____5181)::uu____5187))
in (uu____5168)::uu____5174))
in (lid_as_constr FStar_Parser_Const.inr_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5167))
end))))
in (

let un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fvar1, us, ((a, uu____5261))::(uu____5262)::(uu____5263)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid) -> begin
(

let uu____5298 = (unembed ea cb a)
in (FStar_Util.bind_opt uu____5298 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Util.Inl (a1)))))
end
| Construct (fvar1, us, ((b, uu____5314))::(uu____5315)::(uu____5316)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid) -> begin
(

let uu____5351 = (unembed eb cb b)
in (FStar_Util.bind_opt uu____5351 (fun b1 -> FStar_Pervasives_Native.Some (FStar_Util.Inr (b1)))))
end
| uu____5364 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5369 = (

let uu____5370 = (

let uu____5371 = (

let uu____5376 = (type_of eb)
in (as_arg uu____5376))
in (

let uu____5377 = (

let uu____5384 = (

let uu____5389 = (type_of ea)
in (as_arg uu____5389))
in (uu____5384)::[])
in (uu____5371)::uu____5377))
in (lid_as_typ FStar_Parser_Const.either_lid ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____5370))
in (mk_emb em un uu____5369 etyp))))))


let e_range : FStar_Range.range embedding = (

let em = (fun cb r -> Constant (Range (r)))
in (

let un = (fun cb t -> (match (t) with
| Constant (Range (r)) -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____5438 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5439 = (lid_as_typ FStar_Parser_Const.range_lid [] [])
in (

let uu____5444 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range)
in (mk_emb em un uu____5439 uu____5444)))))


let e_list : 'a . 'a embedding  ->  'a Prims.list embedding = (fun ea -> (

let etyp = (

let uu____5465 = (

let uu____5473 = (FStar_All.pipe_right FStar_Parser_Const.list_lid FStar_Ident.string_of_lid)
in ((uu____5473), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____5465))
in (

let em = (fun cb l -> (lazy_embed etyp l (fun uu____5500 -> (

let typ = (

let uu____5502 = (type_of ea)
in (as_iarg uu____5502))
in (

let nil = (lid_as_constr FStar_Parser_Const.nil_lid ((FStar_Syntax_Syntax.U_zero)::[]) ((typ)::[]))
in (

let cons1 = (fun hd1 tl1 -> (

let uu____5523 = (

let uu____5524 = (as_arg tl1)
in (

let uu____5529 = (

let uu____5536 = (

let uu____5541 = (embed ea cb hd1)
in (as_arg uu____5541))
in (uu____5536)::(typ)::[])
in (uu____5524)::uu____5529))
in (lid_as_constr FStar_Parser_Const.cons_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____5523)))
in (FStar_List.fold_right cons1 l nil)))))))
in (

let rec un = (fun cb trm -> (lazy_unembed cb etyp trm (fun trm1 -> (match (trm1) with
| Construct (fv, uu____5589, uu____5590) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| Construct (fv, uu____5610, ((tl1, FStar_Pervasives_Native.None))::((hd1, FStar_Pervasives_Native.None))::((uu____5613, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____5614))))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5642 = (unembed ea cb hd1)
in (FStar_Util.bind_opt uu____5642 (fun hd2 -> (

let uu____5650 = (un cb tl1)
in (FStar_Util.bind_opt uu____5650 (fun tl2 -> FStar_Pervasives_Native.Some ((hd2)::tl2)))))))
end
| Construct (fv, uu____5666, ((tl1, FStar_Pervasives_Native.None))::((hd1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5691 = (unembed ea cb hd1)
in (FStar_Util.bind_opt uu____5691 (fun hd2 -> (

let uu____5699 = (un cb tl1)
in (FStar_Util.bind_opt uu____5699 (fun tl2 -> FStar_Pervasives_Native.Some ((hd2)::tl2)))))))
end
| uu____5714 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____5717 = (

let uu____5718 = (

let uu____5719 = (

let uu____5724 = (type_of ea)
in (as_arg uu____5724))
in (uu____5719)::[])
in (lid_as_typ FStar_Parser_Const.list_lid ((FStar_Syntax_Syntax.U_zero)::[]) uu____5718))
in (mk_emb em un uu____5717 etyp))))))


let e_string_list : Prims.string Prims.list embedding = (e_list e_string)


let e_arrow : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b) embedding = (fun ea eb -> (

let etyp = FStar_Syntax_Syntax.ET_fun (((ea.emb_typ), (eb.emb_typ)))
in (

let em = (fun cb f -> (lazy_embed etyp f (fun uu____5797 -> Lam ((((fun tas -> (

let uu____5827 = (

let uu____5830 = (FStar_List.hd tas)
in (unembed ea cb uu____5830))
in (match (uu____5827) with
| FStar_Pervasives_Native.Some (a) -> begin
(

let uu____5832 = (f a)
in (embed eb cb uu____5832))
end
| FStar_Pervasives_Native.None -> begin
(failwith "cannot unembed function argument")
end)))), (((fun uu____5845 -> (

let uu____5848 = (type_of eb)
in (as_arg uu____5848))))::[]), ((Prims.parse_int "1")), (FStar_Pervasives_Native.None))))))
in (

let un = (fun cb lam -> (

let k = (fun lam1 -> FStar_Pervasives_Native.Some ((fun x -> (

let uu____5906 = (

let uu____5909 = (

let uu____5910 = (

let uu____5911 = (

let uu____5916 = (embed ea cb x)
in (as_arg uu____5916))
in (uu____5911)::[])
in (cb.iapp lam1 uu____5910))
in (unembed eb cb uu____5909))
in (match (uu____5906) with
| FStar_Pervasives_Native.Some (y) -> begin
y
end
| FStar_Pervasives_Native.None -> begin
(failwith "cannot unembed function result")
end)))))
in (lazy_unembed cb etyp lam k)))
in (

let uu____5930 = (

let uu____5931 = (type_of ea)
in (

let uu____5932 = (

let uu____5933 = (type_of eb)
in (as_iarg uu____5933))
in (make_arrow1 uu____5931 uu____5932)))
in (mk_emb em un uu____5930 etyp))))))


let e_norm_step : FStar_Syntax_Embeddings.norm_step embedding = (

let em = (fun cb n1 -> (match (n1) with
| FStar_Syntax_Embeddings.Simpl -> begin
(

let uu____5951 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5951 [] []))
end
| FStar_Syntax_Embeddings.Weak -> begin
(

let uu____5956 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5956 [] []))
end
| FStar_Syntax_Embeddings.HNF -> begin
(

let uu____5961 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5961 [] []))
end
| FStar_Syntax_Embeddings.Primops -> begin
(

let uu____5966 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5966 [] []))
end
| FStar_Syntax_Embeddings.Delta -> begin
(

let uu____5971 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5971 [] []))
end
| FStar_Syntax_Embeddings.Zeta -> begin
(

let uu____5976 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5976 [] []))
end
| FStar_Syntax_Embeddings.Iota -> begin
(

let uu____5981 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5981 [] []))
end
| FStar_Syntax_Embeddings.Reify -> begin
(

let uu____5986 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5986 [] []))
end
| FStar_Syntax_Embeddings.NBE -> begin
(

let uu____5991 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____5991 [] []))
end
| FStar_Syntax_Embeddings.UnfoldOnly (l) -> begin
(

let uu____6000 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____6001 = (

let uu____6002 = (

let uu____6007 = (

let uu____6008 = (e_list e_string)
in (embed uu____6008 cb l))
in (as_arg uu____6007))
in (uu____6002)::[])
in (mkFV uu____6000 [] uu____6001)))
end
| FStar_Syntax_Embeddings.UnfoldFully (l) -> begin
(

let uu____6030 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____6031 = (

let uu____6032 = (

let uu____6037 = (

let uu____6038 = (e_list e_string)
in (embed uu____6038 cb l))
in (as_arg uu____6037))
in (uu____6032)::[])
in (mkFV uu____6030 [] uu____6031)))
end
| FStar_Syntax_Embeddings.UnfoldAttr (l) -> begin
(

let uu____6060 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____6061 = (

let uu____6062 = (

let uu____6067 = (

let uu____6068 = (e_list e_string)
in (embed uu____6068 cb l))
in (as_arg uu____6067))
in (uu____6062)::[])
in (mkFV uu____6060 [] uu____6061)))
end))
in (

let un = (fun cb t0 -> (match (t0) with
| FV (fv, uu____6102, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Simpl)
end
| FV (fv, uu____6118, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Weak)
end
| FV (fv, uu____6134, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.HNF)
end
| FV (fv, uu____6150, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Primops)
end
| FV (fv, uu____6166, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Delta)
end
| FV (fv, uu____6182, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Zeta)
end
| FV (fv, uu____6198, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Iota)
end
| FV (fv, uu____6214, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.NBE)
end
| FV (fv, uu____6230, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Embeddings.Reify)
end
| FV (fv, uu____6246, ((l, uu____6248))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly) -> begin
(

let uu____6267 = (

let uu____6273 = (e_list e_string)
in (unembed uu____6273 cb l))
in (FStar_Util.bind_opt uu____6267 (fun ss -> (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) (FStar_Syntax_Embeddings.UnfoldOnly (ss))))))
end
| FV (fv, uu____6294, ((l, uu____6296))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully) -> begin
(

let uu____6315 = (

let uu____6321 = (e_list e_string)
in (unembed uu____6321 cb l))
in (FStar_Util.bind_opt uu____6315 (fun ss -> (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) (FStar_Syntax_Embeddings.UnfoldFully (ss))))))
end
| FV (fv, uu____6342, ((l, uu____6344))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr) -> begin
(

let uu____6363 = (

let uu____6369 = (e_list e_string)
in (unembed uu____6369 cb l))
in (FStar_Util.bind_opt uu____6363 (fun ss -> (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) (FStar_Syntax_Embeddings.UnfoldAttr (ss))))))
end
| uu____6389 -> begin
((

let uu____6391 = (

let uu____6397 = (

let uu____6399 = (t_to_string t0)
in (FStar_Util.format1 "Not an embedded norm_step: %s" uu____6399))
in ((FStar_Errors.Warning_NotEmbedded), (uu____6397)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____6391));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____6403 = (

let uu____6404 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mkFV uu____6404 [] []))
in (

let uu____6409 = (FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step)
in (mk_emb em un uu____6403 uu____6409)))))


let bogus_cbs : nbe_cbs = {iapp = (fun h _args -> h); translate = (fun uu____6418 -> (failwith "bogus_cbs translate"))}


let arg_as_int : arg  ->  FStar_BigInt.t FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_int bogus_cbs)))


let arg_as_bool : arg  ->  Prims.bool FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_bool bogus_cbs)))


let arg_as_char : arg  ->  FStar_Char.char FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_char bogus_cbs)))


let arg_as_string : arg  ->  Prims.string FStar_Pervasives_Native.option = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_string bogus_cbs)))


let arg_as_list : 'a . 'a embedding  ->  arg  ->  'a Prims.list FStar_Pervasives_Native.option = (fun e a -> (

let uu____6495 = (

let uu____6504 = (e_list e)
in (unembed uu____6504 bogus_cbs))
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6495)))


let arg_as_bounded_int : arg  ->  (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option = (fun uu____6526 -> (match (uu____6526) with
| (a, uu____6534) -> begin
(match (a) with
| FV (fv1, [], ((Constant (Int (i)), uu____6549))::[]) when (

let uu____6566 = (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.ends_with uu____6566 "int_to_t")) -> begin
FStar_Pervasives_Native.Some (((fv1), (i)))
end
| uu____6573 -> begin
FStar_Pervasives_Native.None
end)
end))


let int_as_bounded : FStar_Syntax_Syntax.fv  ->  FStar_BigInt.t  ->  t = (fun int_to_t1 n1 -> (

let c = (embed e_int bogus_cbs n1)
in (

let int_to_t2 = (fun args -> FV (((int_to_t1), ([]), (args))))
in (

let uu____6616 = (

let uu____6623 = (as_arg c)
in (uu____6623)::[])
in (int_to_t2 uu____6616)))))


let lift_unary : 'a 'b . ('a  ->  'b)  ->  'a FStar_Pervasives_Native.option Prims.list  ->  'b FStar_Pervasives_Native.option = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____6677 = (f a)
in FStar_Pervasives_Native.Some (uu____6677))
end
| uu____6678 -> begin
FStar_Pervasives_Native.None
end))


let lift_binary : 'a 'b . ('a  ->  'a  ->  'b)  ->  'a FStar_Pervasives_Native.option Prims.list  ->  'b FStar_Pervasives_Native.option = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____6732 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____6732))
end
| uu____6733 -> begin
FStar_Pervasives_Native.None
end))


let unary_op : 'a . (arg  ->  'a FStar_Pervasives_Native.option)  ->  ('a  ->  t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a f args -> (

let uu____6777 = (FStar_List.map as_a args)
in (lift_unary f uu____6777)))


let binary_op : 'a . (arg  ->  'a FStar_Pervasives_Native.option)  ->  ('a  ->  'a  ->  t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a f args -> (

let uu____6832 = (FStar_List.map as_a args)
in (lift_binary f uu____6832)))


let unary_int_op : (FStar_BigInt.t  ->  FStar_BigInt.t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (unary_op arg_as_int (fun x -> (

let uu____6862 = (f x)
in (embed e_int bogus_cbs uu____6862)))))


let binary_int_op : (FStar_BigInt.t  ->  FStar_BigInt.t  ->  FStar_BigInt.t)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_int (fun x y -> (

let uu____6889 = (f x y)
in (embed e_int bogus_cbs uu____6889)))))


let unary_bool_op : (Prims.bool  ->  Prims.bool)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (unary_op arg_as_bool (fun x -> (

let uu____6915 = (f x)
in (embed e_bool bogus_cbs uu____6915)))))


let binary_bool_op : (Prims.bool  ->  Prims.bool  ->  Prims.bool)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_bool (fun x y -> (

let uu____6953 = (f x y)
in (embed e_bool bogus_cbs uu____6953)))))


let binary_string_op : (Prims.string  ->  Prims.string  ->  Prims.string)  ->  args  ->  t FStar_Pervasives_Native.option = (fun f -> (binary_op arg_as_string (fun x y -> (

let uu____6991 = (f x y)
in (embed e_string bogus_cbs uu____6991)))))


let mixed_binary_op : 'a 'b 'c . (arg  ->  'a FStar_Pervasives_Native.option)  ->  (arg  ->  'b FStar_Pervasives_Native.option)  ->  ('c  ->  t)  ->  ('a  ->  'b  ->  'c)  ->  args  ->  t FStar_Pervasives_Native.option = (fun as_a as_b embed_c f args -> (match (args) with
| (a)::(b)::[] -> begin
(

let uu____7096 = (

let uu____7105 = (as_a a)
in (

let uu____7108 = (as_b b)
in ((uu____7105), (uu____7108))))
in (match (uu____7096) with
| (FStar_Pervasives_Native.Some (a1), FStar_Pervasives_Native.Some (b1)) -> begin
(

let uu____7123 = (

let uu____7124 = (f a1 b1)
in (embed_c uu____7124))
in FStar_Pervasives_Native.Some (uu____7123))
end
| uu____7125 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7134 -> begin
FStar_Pervasives_Native.None
end))


let list_of_string' : Prims.string  ->  t = (fun s -> (

let uu____7143 = (e_list e_char)
in (

let uu____7150 = (FStar_String.list_of_string s)
in (embed uu____7143 bogus_cbs uu____7150))))


let string_of_list' : FStar_Char.char Prims.list  ->  t = (fun l -> (

let s = (FStar_String.string_of_list l)
in Constant (String (((s), (FStar_Range.dummyRange))))))


let string_compare' : Prims.string  ->  Prims.string  ->  t = (fun s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____7189 = (

let uu____7190 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____7190))
in (embed e_int bogus_cbs uu____7189))))


let string_concat' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7224 = (arg_as_string a1)
in (match (uu____7224) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7233 = (arg_as_list e_string a2)
in (match (uu____7233) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____7251 = (embed e_string bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7251)))
end
| uu____7253 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7259 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7263 -> begin
FStar_Pervasives_Native.None
end))


let string_of_int : FStar_BigInt.t  ->  t = (fun i -> (

let uu____7270 = (FStar_BigInt.string_of_big_int i)
in (embed e_string bogus_cbs uu____7270)))


let string_of_bool : Prims.bool  ->  t = (fun b -> (embed e_string bogus_cbs (match (b) with
| true -> begin
"true"
end
| uu____7285 -> begin
"false"
end)))


let decidable_eq : Prims.bool  ->  args  ->  t FStar_Pervasives_Native.option = (fun neg args -> (

let tru = (embed e_bool bogus_cbs true)
in (

let fal = (embed e_bool bogus_cbs false)
in (match (args) with
| ((_typ, uu____7314))::((a1, uu____7316))::((a2, uu____7318))::[] -> begin
(

let uu____7335 = (eq_t a1 a2)
in (match (uu____7335) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____7339 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____7342 -> begin
fal
end))
end
| uu____7344 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7345 -> begin
(failwith "Unexpected number of arguments")
end))))


let interp_prop_eq2 : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((_u, uu____7360))::((_typ, uu____7362))::((a1, uu____7364))::((a2, uu____7366))::[] -> begin
(

let uu____7387 = (eq_t a1 a2)
in (match (uu____7387) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____7390 = (embed e_bool bogus_cbs true)
in FStar_Pervasives_Native.Some (uu____7390))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____7393 = (embed e_bool bogus_cbs false)
in FStar_Pervasives_Native.Some (uu____7393))
end
| FStar_Syntax_Util.Unknown -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7396 -> begin
(failwith "Unexpected number of arguments")
end))


let interp_prop_eq3 : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((_u, uu____7411))::((_v, uu____7413))::((t1, uu____7415))::((t2, uu____7417))::((a1, uu____7419))::((a2, uu____7421))::[] -> begin
(

let uu____7450 = (

let uu____7451 = (eq_t t1 t2)
in (

let uu____7452 = (eq_t a1 a2)
in (FStar_Syntax_Util.eq_inj uu____7451 uu____7452)))
in (match (uu____7450) with
| FStar_Syntax_Util.Equal -> begin
(

let uu____7455 = (embed e_bool bogus_cbs true)
in FStar_Pervasives_Native.Some (uu____7455))
end
| FStar_Syntax_Util.NotEqual -> begin
(

let uu____7458 = (embed e_bool bogus_cbs false)
in FStar_Pervasives_Native.Some (uu____7458))
end
| FStar_Syntax_Util.Unknown -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7461 -> begin
(failwith "Unexpected number of arguments")
end))


let dummy_interp : FStar_Ident.lid  ->  args  ->  t FStar_Pervasives_Native.option = (fun lid args -> (

let uu____7480 = (

let uu____7482 = (FStar_Ident.string_of_lid lid)
in (Prims.strcat "No interpretation for " uu____7482))
in (failwith uu____7480)))


let prims_to_fstar_range_step : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| ((a1, uu____7498))::[] -> begin
(

let uu____7507 = (unembed e_range bogus_cbs a1)
in (match (uu____7507) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7513 = (embed e_range bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7513))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7514 -> begin
(failwith "Unexpected number of arguments")
end))


let string_split' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7550 = (arg_as_list e_char a1)
in (match (uu____7550) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7566 = (arg_as_string a2)
in (match (uu____7566) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.split s1 s2)
in (

let uu____7579 = (

let uu____7580 = (e_list e_string)
in (embed uu____7580 bogus_cbs r))
in FStar_Pervasives_Native.Some (uu____7579)))
end
| uu____7590 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7594 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7600 -> begin
FStar_Pervasives_Native.None
end))


let string_substring' : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (a1)::(a2)::(a3)::[] -> begin
(

let uu____7642 = (

let uu____7656 = (arg_as_string a1)
in (

let uu____7660 = (arg_as_int a2)
in (

let uu____7663 = (arg_as_int a3)
in ((uu____7656), (uu____7660), (uu____7663)))))
in (match (uu____7642) with
| (FStar_Pervasives_Native.Some (s1), FStar_Pervasives_Native.Some (n1), FStar_Pervasives_Native.Some (n2)) -> begin
(

let n11 = (FStar_BigInt.to_int_fs n1)
in (

let n21 = (FStar_BigInt.to_int_fs n2)
in (FStar_All.try_with (fun uu___241_7696 -> (match (()) with
| () -> begin
(

let r = (FStar_String.substring s1 n11 n21)
in (

let uu____7701 = (embed e_string bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7701)))
end)) (fun uu___240_7704 -> FStar_Pervasives_Native.None))))
end
| uu____7707 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7721 -> begin
FStar_Pervasives_Native.None
end))


let mk_range : args  ->  t FStar_Pervasives_Native.option = (fun args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____7781 = (

let uu____7803 = (arg_as_string fn)
in (

let uu____7807 = (arg_as_int from_line)
in (

let uu____7810 = (arg_as_int from_col)
in (

let uu____7813 = (arg_as_int to_line)
in (

let uu____7816 = (arg_as_int to_col)
in ((uu____7803), (uu____7807), (uu____7810), (uu____7813), (uu____7816)))))))
in (match (uu____7781) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____7851 = (

let uu____7852 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____7854 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____7852 uu____7854)))
in (

let uu____7856 = (

let uu____7857 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____7859 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____7857 uu____7859)))
in (FStar_Range.mk_range fn1 uu____7851 uu____7856)))
in (

let uu____7861 = (embed e_range bogus_cbs r)
in FStar_Pervasives_Native.Some (uu____7861)))
end
| uu____7862 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7884 -> begin
FStar_Pervasives_Native.None
end))


let arrow_as_prim_step_1 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____7974 = (FStar_List.splitAt n_tvars args)
in (match (uu____7974) with
| (_tvar_args, rest_args) -> begin
(

let uu____8023 = (FStar_List.hd rest_args)
in (match (uu____8023) with
| (x, uu____8035) -> begin
(

let uu____8036 = (unembed ea cb x)
in (FStar_Util.map_opt uu____8036 (fun x1 -> (

let uu____8042 = (f x1)
in (embed eb cb uu____8042)))))
end))
end)))
in f_wrapped))


let arrow_as_prim_step_2 : 'a 'b 'c . 'a embedding  ->  'b embedding  ->  'c embedding  ->  ('a  ->  'b  ->  'c)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb ec f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8151 = (FStar_List.splitAt n_tvars args)
in (match (uu____8151) with
| (_tvar_args, rest_args) -> begin
(

let uu____8200 = (FStar_List.hd rest_args)
in (match (uu____8200) with
| (x, uu____8212) -> begin
(

let uu____8213 = (

let uu____8218 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____8218))
in (match (uu____8213) with
| (y, uu____8236) -> begin
(

let uu____8237 = (unembed ea cb x)
in (FStar_Util.bind_opt uu____8237 (fun x1 -> (

let uu____8243 = (unembed eb cb y)
in (FStar_Util.bind_opt uu____8243 (fun y1 -> (

let uu____8249 = (

let uu____8250 = (f x1 y1)
in (embed ec cb uu____8250))
in FStar_Pervasives_Native.Some (uu____8249))))))))
end))
end))
end)))
in f_wrapped))


let arrow_as_prim_step_3 : 'a 'b 'c 'd . 'a embedding  ->  'b embedding  ->  'c embedding  ->  'd embedding  ->  ('a  ->  'b  ->  'c  ->  'd)  ->  Prims.int  ->  FStar_Ident.lid  ->  nbe_cbs  ->  args  ->  t FStar_Pervasives_Native.option = (fun ea eb ec ed f n_tvars _fv_lid cb -> (

let f_wrapped = (fun args -> (

let uu____8378 = (FStar_List.splitAt n_tvars args)
in (match (uu____8378) with
| (_tvar_args, rest_args) -> begin
(

let uu____8427 = (FStar_List.hd rest_args)
in (match (uu____8427) with
| (x, uu____8439) -> begin
(

let uu____8440 = (

let uu____8445 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____8445))
in (match (uu____8440) with
| (y, uu____8463) -> begin
(

let uu____8464 = (

let uu____8469 = (

let uu____8476 = (FStar_List.tl rest_args)
in (FStar_List.tl uu____8476))
in (FStar_List.hd uu____8469))
in (match (uu____8464) with
| (z, uu____8498) -> begin
(

let uu____8499 = (unembed ea cb x)
in (FStar_Util.bind_opt uu____8499 (fun x1 -> (

let uu____8505 = (unembed eb cb y)
in (FStar_Util.bind_opt uu____8505 (fun y1 -> (

let uu____8511 = (unembed ec cb z)
in (FStar_Util.bind_opt uu____8511 (fun z1 -> (

let uu____8517 = (

let uu____8518 = (f x1 y1 z1)
in (embed ed cb uu____8518))
in FStar_Pervasives_Native.Some (uu____8517)))))))))))
end))
end))
end))
end)))
in f_wrapped))




