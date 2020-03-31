open Prims


type 'Ap spinoff = 'Ap

let id : 'Aa . 'Aa -> 'Aa = fun x  -> x 
type ('Aa,'Auu____55) trivial_pure_post = unit
type ('Auu____62,'Auu____63) ambient = unit

type 'Aheap st_pre_h = unit
type ('Aheap,'Aa,'Apre) st_post_h' = unit
type ('Aheap,'Aa) st_post_h = unit
type ('Aheap,'Aa) st_wp_h = unit
type ('Aheap,'Aa,'Ax,'Ap,'Auu___0_124) st_return = 'Ap
type ('Aheap,'Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap,'Ah0) st_bind_wp = 'Awp1
type ('Aheap,'Aa,'Ap,'Awp_then,'Awp_else,'Apost,'Ah0) st_if_then_else = unit
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) st_ite_wp = unit
type ('Aheap,'Aa,'Awp1,'Awp2) st_stronger = unit
type ('Aheap,'Aa,'Ab,'Awp,'Ap,'Ah) st_close_wp = unit
type ('Aheap,'Aa,'Awp) st_trivial = unit
type 'Aa result =
  | V of 'Aa 
  | E of Prims.exn 
  | Err of Prims.string 
let uu___is_V : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | V v -> true | uu____370 -> false 
let __proj__V__item__v : 'Aa . 'Aa result -> 'Aa =
  fun projectee  -> match projectee with | V v -> v 
let uu___is_E : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____408 -> false 
let __proj__E__item__e : 'Aa . 'Aa result -> Prims.exn =
  fun projectee  -> match projectee with | E e -> e 
let uu___is_Err : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  ->
    match projectee with | Err msg -> true | uu____447 -> false
  
let __proj__Err__item__msg : 'Aa . 'Aa result -> Prims.string =
  fun projectee  -> match projectee with | Err msg -> msg 
type ex_pre = unit
type ('Aa,'Apre) ex_post' = unit
type 'Aa ex_post = unit
type 'Aa ex_wp = unit
type ('Aa,'Ax,'Ap) ex_return = 'Ap
type ('Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap) ex_bind_wp = unit
type ('Aa,'Ap,'Awp_then,'Awp_else,'Apost) ex_if_then_else = unit
type ('Aa,'Awp,'Apost) ex_ite_wp = unit
type ('Aa,'Awp1,'Awp2) ex_stronger = unit
type ('Aa,'Ab,'Awp,'Ap) ex_close_wp = unit
type ('Aa,'Awp) ex_trivial = 'Awp
type ('Aa,'Awp,'Ap) lift_div_exn = 'Awp
type 'Ah all_pre_h = unit
type ('Ah,'Aa,'Apre) all_post_h' = unit
type ('Ah,'Aa) all_post_h = unit
type ('Ah,'Aa) all_wp_h = unit
type ('Aheap,'Aa,'Ax,'Ap,'Auu___3_720) all_return = 'Ap
type ('Aheap,'Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap,'Ah0) all_bind_wp = 'Awp1
type ('Aheap,'Aa,'Ap,'Awp_then,'Awp_else,'Apost,'Ah0) all_if_then_else = unit
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) all_ite_wp = unit
type ('Aheap,'Aa,'Awp1,'Awp2) all_stronger = unit
type ('Aheap,'Aa,'Ab,'Awp,'Ap,'Ah) all_close_wp = unit
type ('Aheap,'Aa,'Awp) all_trivial = unit
type 'Auu____929 inversion = unit


type ('Aa,'Ab) either =
  | Inl of 'Aa 
  | Inr of 'Ab 
let uu___is_Inl : 'Aa 'Ab . ('Aa,'Ab) either -> Prims.bool =
  fun projectee  -> match projectee with | Inl v -> true | uu____980 -> false 
let __proj__Inl__item__v : 'Aa 'Ab . ('Aa,'Ab) either -> 'Aa =
  fun projectee  -> match projectee with | Inl v -> v 
let uu___is_Inr : 'Aa 'Ab . ('Aa,'Ab) either -> Prims.bool =
  fun projectee  ->
    match projectee with | Inr v -> true | uu____1034 -> false
  
let __proj__Inr__item__v : 'Aa 'Ab . ('Aa,'Ab) either -> 'Ab =
  fun projectee  -> match projectee with | Inr v -> v 
let dfst : 'Aa 'Ab . ('Aa,'Ab) Prims.dtuple2 -> 'Aa =
  fun t  -> Prims.__proj__Mkdtuple2__item___1 t 
let dsnd : 'Aa 'Ab . ('Aa,'Ab) Prims.dtuple2 -> 'Ab =
  fun t  -> Prims.__proj__Mkdtuple2__item___2 t 
type ('Aa,'Ab,'Ac) dtuple3 =
  | Mkdtuple3 of 'Aa * 'Ab * 'Ac 
let uu___is_Mkdtuple3 : 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> Prims.bool =
  fun projectee  -> true 
let __proj__Mkdtuple3__item___1 : 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> 'Aa
  = fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _1 
let __proj__Mkdtuple3__item___2 : 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> 'Ab
  = fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _2 
let __proj__Mkdtuple3__item___3 : 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> 'Ac
  = fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _3 
type ('Aa,'Ab,'Ac,'Ad) dtuple4 =
  | Mkdtuple4 of 'Aa * 'Ab * 'Ac * 'Ad 
let uu___is_Mkdtuple4 :
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> Prims.bool =
  fun projectee  -> true 
let __proj__Mkdtuple4__item___1 :
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Aa =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _1 
let __proj__Mkdtuple4__item___2 :
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Ab =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _2 
let __proj__Mkdtuple4__item___3 :
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Ac =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _3 
let __proj__Mkdtuple4__item___4 :
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Ad =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _4 

let rec false_elim : 'Auu____1599 . unit -> 'Auu____1599 =
  fun uu____1604  -> false_elim () 
type __internal_ocaml_attributes =
  | PpxDerivingShow 
  | PpxDerivingShowConstant of Prims.string 
  | PpxDerivingYoJson 
  | CInline 
  | Substitute 
  | Gc 
  | Comment of Prims.string 
  | CPrologue of Prims.string 
  | CEpilogue of Prims.string 
  | CConst of Prims.string 
  | CCConv of Prims.string 
  | CAbstractStruct 
  | CIfDef 
  | CMacro 
let (uu___is_PpxDerivingShow : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | PpxDerivingShow  -> true | uu____1650 -> false
  
let (uu___is_PpxDerivingShowConstant :
  __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
    | uu____1663 -> false
  
let (__proj__PpxDerivingShowConstant__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | PpxDerivingShowConstant _0 -> _0 
let (uu___is_PpxDerivingYoJson : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | PpxDerivingYoJson  -> true | uu____1684 -> false
  
let (uu___is_CInline : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1695 -> false
  
let (uu___is_Substitute : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1706 -> false
  
let (uu___is_Gc : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  -> match projectee with | Gc  -> true | uu____1717 -> false 
let (uu___is_Comment : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1730 -> false
  
let (__proj__Comment__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_CPrologue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPrologue _0 -> true | uu____1753 -> false
  
let (__proj__CPrologue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | CPrologue _0 -> _0 
let (uu___is_CEpilogue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CEpilogue _0 -> true | uu____1776 -> false
  
let (__proj__CEpilogue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | CEpilogue _0 -> _0 
let (uu___is_CConst : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CConst _0 -> true | uu____1799 -> false
  
let (__proj__CConst__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | CConst _0 -> _0 
let (uu___is_CCConv : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CCConv _0 -> true | uu____1822 -> false
  
let (__proj__CCConv__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | CCConv _0 -> _0 
let (uu___is_CAbstractStruct : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAbstractStruct  -> true | uu____1843 -> false
  
let (uu___is_CIfDef : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CIfDef  -> true | uu____1854 -> false
  
let (uu___is_CMacro : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CMacro  -> true | uu____1865 -> false
  














let normalize_term : 'Auu____1886 . 'Auu____1886 -> 'Auu____1886 =
  fun x  -> x 
type 'Aa normalize = 'Aa
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | NBE 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____1929 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1940 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1951 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1962 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1973 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1984 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1995 -> false
  
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____2006 -> false 
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____2017 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____2032 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____2063 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____2094 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (simplify : norm_step) = Simpl 
let (weak : norm_step) = Weak 
let (hnf : norm_step) = HNF 
let (primops : norm_step) = Primops 
let (delta : norm_step) = Delta 
let (zeta : norm_step) = Zeta 
let (iota : norm_step) = Iota 
let (nbe : norm_step) = NBE 
let (reify_ : norm_step) = Reify 
let (delta_only : Prims.string Prims.list -> norm_step) =
  fun s  -> UnfoldOnly s 
let (delta_fully : Prims.string Prims.list -> norm_step) =
  fun s  -> UnfoldFully s 
let (delta_attr : Prims.string Prims.list -> norm_step) =
  fun s  -> UnfoldAttr s 
let (norm : norm_step Prims.list -> unit -> Obj.t -> Obj.t) =
  fun uu____2172  -> fun uu____2173  -> fun x  -> x 





let singleton : 'Auu____2187 . 'Auu____2187 -> 'Auu____2187 = fun x  -> x 
let with_type : 'Auu____2198 . 'Auu____2198 -> 'Auu____2198 = fun e  -> e 
let (__cache_version_number__ : Prims.int) = (Prims.of_int (20)) 