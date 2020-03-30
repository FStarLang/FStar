open Prims


type 'p spinoff = 'p

let id : 'a . 'a -> 'a = fun x  -> x 
type ('a,'uuuuuu55) trivial_pure_post = unit
type ('uuuuuu62,'uuuuuu63) ambient = unit

type 'heap st_pre_h = unit
type ('heap,'a,'pre) st_post_h' = unit
type ('heap,'a) st_post_h = unit
type ('heap,'a) st_wp_h = unit
type ('heap,'a,'x,'p,'uuuuu0u124) st_return = 'p
type ('heap,'r1,'a,'b,'wp1,'wp2,'p,'h0) st_bind_wp = 'wp1
type ('heap,'a,'p,'wputhen,'wpuelse,'post,'h0) st_if_then_else = unit
type ('heap,'a,'wp,'post,'h0) st_ite_wp = unit
type ('heap,'a,'wp1,'wp2) st_stronger = unit
type ('heap,'a,'b,'wp,'p,'h) st_close_wp = unit
type ('heap,'a,'wp) st_trivial = unit
type 'a result =
  | V of 'a 
  | E of Prims.exn 
  | Err of Prims.string 
let uu___is_V : 'a . 'a result -> Prims.bool =
  fun projectee  -> match projectee with | V v -> true | uu____370 -> false 
let __proj__V__item__v : 'a . 'a result -> 'a =
  fun projectee  -> match projectee with | V v -> v 
let uu___is_E : 'a . 'a result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____408 -> false 
let __proj__E__item__e : 'a . 'a result -> Prims.exn =
  fun projectee  -> match projectee with | E e -> e 
let uu___is_Err : 'a . 'a result -> Prims.bool =
  fun projectee  ->
    match projectee with | Err msg -> true | uu____447 -> false
  
let __proj__Err__item__msg : 'a . 'a result -> Prims.string =
  fun projectee  -> match projectee with | Err msg -> msg 
type ex_pre = unit
type ('a,'pre) ex_post' = unit
type 'a ex_post = unit
type 'a ex_wp = unit
type ('a,'x,'p) ex_return = 'p
type ('r1,'a,'b,'wp1,'wp2,'p) ex_bind_wp = unit
type ('a,'p,'wputhen,'wpuelse,'post) ex_if_then_else = unit
type ('a,'wp,'post) ex_ite_wp = unit
type ('a,'wp1,'wp2) ex_stronger = unit
type ('a,'b,'wp,'p) ex_close_wp = unit
type ('a,'wp) ex_trivial = 'wp
type ('a,'wp,'p) lift_div_exn = 'wp
type 'h all_pre_h = unit
type ('h,'a,'pre) all_post_h' = unit
type ('h,'a) all_post_h = unit
type ('h,'a) all_wp_h = unit
type ('heap,'a,'x,'p,'uuuuu3u720) all_return = 'p
type ('heap,'r1,'a,'b,'wp1,'wp2,'p,'h0) all_bind_wp = 'wp1
type ('heap,'a,'p,'wputhen,'wpuelse,'post,'h0) all_if_then_else = unit
type ('heap,'a,'wp,'post,'h0) all_ite_wp = unit
type ('heap,'a,'wp1,'wp2) all_stronger = unit
type ('heap,'a,'b,'wp,'p,'h) all_close_wp = unit
type ('heap,'a,'wp) all_trivial = unit
type 'uuuuuu929 inversion = unit


type ('a,'b) either =
  | Inl of 'a 
  | Inr of 'b 
let uu___is_Inl : 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  -> match projectee with | Inl v -> true | uu____980 -> false 
let __proj__Inl__item__v : 'a 'b . ('a,'b) either -> 'a =
  fun projectee  -> match projectee with | Inl v -> v 
let uu___is_Inr : 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  ->
    match projectee with | Inr v -> true | uu____1034 -> false
  
let __proj__Inr__item__v : 'a 'b . ('a,'b) either -> 'b =
  fun projectee  -> match projectee with | Inr v -> v 
let dfst : 'a 'b . ('a,'b) Prims.dtuple2 -> 'a =
  fun t  -> Prims.__proj__Mkdtuple2__item___1 t 
let dsnd : 'a 'b . ('a,'b) Prims.dtuple2 -> 'b =
  fun t  -> Prims.__proj__Mkdtuple2__item___2 t 
type ('a,'b,'c) dtuple3 =
  | Mkdtuple3 of 'a * 'b * 'c 
let uu___is_Mkdtuple3 : 'a 'b 'c . ('a,'b,'c) dtuple3 -> Prims.bool =
  fun projectee  -> true 
let __proj__Mkdtuple3__item___1 : 'a 'b 'c . ('a,'b,'c) dtuple3 -> 'a =
  fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _1 
let __proj__Mkdtuple3__item___2 : 'a 'b 'c . ('a,'b,'c) dtuple3 -> 'b =
  fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _2 
let __proj__Mkdtuple3__item___3 : 'a 'b 'c . ('a,'b,'c) dtuple3 -> 'c =
  fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _3 
type ('a,'b,'c,'d) dtuple4 =
  | Mkdtuple4 of 'a * 'b * 'c * 'd 
let uu___is_Mkdtuple4 : 'a 'b 'c 'd . ('a,'b,'c,'d) dtuple4 -> Prims.bool =
  fun projectee  -> true 
let __proj__Mkdtuple4__item___1 : 'a 'b 'c 'd . ('a,'b,'c,'d) dtuple4 -> 'a =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _1 
let __proj__Mkdtuple4__item___2 : 'a 'b 'c 'd . ('a,'b,'c,'d) dtuple4 -> 'b =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _2 
let __proj__Mkdtuple4__item___3 : 'a 'b 'c 'd . ('a,'b,'c,'d) dtuple4 -> 'c =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _3 
let __proj__Mkdtuple4__item___4 : 'a 'b 'c 'd . ('a,'b,'c,'d) dtuple4 -> 'd =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _4 

let rec false_elim : 'uuuuuu1599 . unit -> 'uuuuuu1599 =
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
  














let normalize_term : 'uuuuuu1886 . 'uuuuuu1886 -> 'uuuuuu1886 = fun x  -> x 
type 'a normalize = 'a
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





let singleton : 'uuuuuu2187 . 'uuuuuu2187 -> 'uuuuuu2187 = fun x  -> x 
let with_type : 'uuuuuu2198 . 'uuuuuu2198 -> 'uuuuuu2198 = fun e  -> e 
let (__cache_version_number__ : Prims.int) = (Prims.of_int (18)) 