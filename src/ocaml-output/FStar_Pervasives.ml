open Prims
let id : 'Aa . 'Aa -> 'Aa = fun x  -> x 
type ('Aa,'Auu____45) trivial_pure_post = unit
type ('Aa,'Ax) ambient = unit

type 'Aheap st_pre_h = unit
type ('Aheap,'Aa,'Apre) st_post_h' = unit
type ('Aheap,'Aa) st_post_h = unit
type ('Aheap,'Aa) st_wp_h = unit
type ('Aheap,'Aa,'Ax,'Ap,'Auu___0_114) st_return = 'Ap
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
  fun projectee  -> match projectee with | V v -> true | uu____360 -> false 
let __proj__V__item__v : 'Aa . 'Aa result -> 'Aa =
  fun projectee  -> match projectee with | V v -> v 
let uu___is_E : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____398 -> false 
let __proj__E__item__e : 'Aa . 'Aa result -> Prims.exn =
  fun projectee  -> match projectee with | E e -> e 
let uu___is_Err : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  ->
    match projectee with | Err msg -> true | uu____437 -> false
  
let __proj__Err__item__msg : 'Aa . 'Aa result -> Prims.string =
  fun projectee  -> match projectee with | Err msg -> msg 
type ex_pre = unit
type ('Aa,'Apre) ex_post' = unit
type 'Aa ex_post = unit
type 'Aa ex_wp = unit
type ('Aa,'Ax,'Ap) ex_return = 'Ap
type ('Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap) ex_bind_wp = unit
type ('Aa,'Awp,'Apost) ex_ite_wp = unit
type ('Aa,'Ap,'Awp_then,'Awp_else,'Apost) ex_if_then_else = unit
type ('Aa,'Awp1,'Awp2) ex_stronger = unit
type ('Aa,'Ab,'Awp,'Ap) ex_close_wp = unit
type ('Aa,'Awp) ex_trivial = 'Awp
type ('Aa,'Awp,'Ap) lift_div_exn = 'Awp
type 'Ah all_pre_h = unit
type ('Ah,'Aa,'Apre) all_post_h' = unit
type ('Ah,'Aa) all_post_h = unit
type ('Ah,'Aa) all_wp_h = unit
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) all_ite_wp = unit
type ('Aheap,'Aa,'Ax,'Ap,'Auu___3_741) all_return = 'Ap
type ('Aheap,'Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap,'Ah0) all_bind_wp = 'Awp1
type ('Aheap,'Aa,'Ap,'Awp_then,'Awp_else,'Apost,'Ah0) all_if_then_else = unit
type ('Aheap,'Aa,'Awp1,'Awp2) all_stronger = unit
type ('Aheap,'Aa,'Ab,'Awp,'Ap,'Ah) all_close_wp = unit
type ('Aheap,'Aa,'Awp) all_trivial = unit
type 'Aa inversion = unit


type ('a,'b) either =
  | Inl of 'a 
  | Inr of 'b 
let uu___is_Inl : 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  -> match projectee with | Inl v -> true | uu____970 -> false 
let __proj__Inl__item__v : 'a 'b . ('a,'b) either -> 'a =
  fun projectee  -> match projectee with | Inl v -> v 
let uu___is_Inr : 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  ->
    match projectee with | Inr v -> true | uu____1024 -> false
  
let __proj__Inr__item__v : 'a 'b . ('a,'b) either -> 'b =
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

let rec false_elim : 'Aa . unit -> 'Aa = fun u  -> false_elim () 
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
    match projectee with | PpxDerivingShow  -> true | uu____1640 -> false
  
let (uu___is_PpxDerivingShowConstant :
  __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
    | uu____1653 -> false
  
let (__proj__PpxDerivingShowConstant__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | PpxDerivingShowConstant _0 -> _0 
let (uu___is_PpxDerivingYoJson : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | PpxDerivingYoJson  -> true | uu____1674 -> false
  
let (uu___is_CInline : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1685 -> false
  
let (uu___is_Substitute : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1696 -> false
  
let (uu___is_Gc : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  -> match projectee with | Gc  -> true | uu____1707 -> false 
let (uu___is_Comment : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1720 -> false
  
let (__proj__Comment__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_CPrologue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPrologue _0 -> true | uu____1743 -> false
  
let (__proj__CPrologue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | CPrologue _0 -> _0 
let (uu___is_CEpilogue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CEpilogue _0 -> true | uu____1766 -> false
  
let (__proj__CEpilogue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | CEpilogue _0 -> _0 
let (uu___is_CConst : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CConst _0 -> true | uu____1789 -> false
  
let (__proj__CConst__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | CConst _0 -> _0 
let (uu___is_CCConv : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CCConv _0 -> true | uu____1812 -> false
  
let (__proj__CCConv__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | CCConv _0 -> _0 
let (uu___is_CAbstractStruct : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAbstractStruct  -> true | uu____1833 -> false
  
let (uu___is_CIfDef : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CIfDef  -> true | uu____1844 -> false
  
let (uu___is_CMacro : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CMacro  -> true | uu____1855 -> false
  












let normalize_term : 'Aa . 'Aa -> 'Aa = fun x  -> x 
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
    match projectee with | Simpl  -> true | uu____1917 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1928 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1939 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1950 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1961 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1972 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1983 -> false
  
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____1994 -> false 
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____2005 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____2020 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____2051 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____2082 -> false
  
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
  fun s  -> fun a  -> fun x  -> x 





let singleton : 'Aa . 'Aa -> 'Aa = fun x  -> x 
let with_type : 'At . 'At -> 'At = fun e  -> e 