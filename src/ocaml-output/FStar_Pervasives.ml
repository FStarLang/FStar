open Prims
type ('Aa,'Auu____34) trivial_pure_post = unit
type ('Aa,'Ax) ambient = unit

type 'Aheap st_pre_h = unit
type ('Aheap,'Aa,'Apre) st_post_h' = unit
type ('Aheap,'Aa) st_post_h = unit
type ('Aheap,'Aa) st_wp_h = unit
<<<<<<< HEAD
<<<<<<< HEAD
type ('Aheap,'Aa,'Ax,'Ap,'Auu___0_122) st_return = 'Ap
=======
type ('Aheap,'Aa,'Ax,'Ap,'Auu___0_105) st_return = 'Ap
>>>>>>> snap
=======
type ('Aheap,'Aa,'Ax,'Ap,'Auu___0_111) st_return = 'Ap
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
  fun projectee  -> match projectee with | V v -> true | uu____368 -> false 
let __proj__V__item__v : 'Aa . 'Aa result -> 'Aa =
  fun projectee  -> match projectee with | V v -> v 
let uu___is_E : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____406 -> false 
=======
  fun projectee  -> match projectee with | V v -> true | uu____351 -> false 
let __proj__V__item__v : 'Aa . 'Aa result -> 'Aa =
  fun projectee  -> match projectee with | V v -> v 
let uu___is_E : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____389 -> false 
>>>>>>> snap
=======
  fun projectee  -> match projectee with | V v -> true | uu____357 -> false 
let __proj__V__item__v : 'Aa . 'Aa result -> 'Aa =
  fun projectee  -> match projectee with | V v -> v 
let uu___is_E : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____395 -> false 
>>>>>>> snap
let __proj__E__item__e : 'Aa . 'Aa result -> Prims.exn =
  fun projectee  -> match projectee with | E e -> e 
let uu___is_Err : 'Aa . 'Aa result -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Err msg -> true | uu____445 -> false
=======
    match projectee with | Err msg -> true | uu____428 -> false
>>>>>>> snap
=======
    match projectee with | Err msg -> true | uu____434 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
type ('Aheap,'Aa,'Ax,'Ap,'Auu___3_757) all_return = 'Ap
=======
type ('Aheap,'Aa,'Ax,'Ap,'Auu___3_731) all_return = 'Ap
>>>>>>> snap
=======
type ('Aheap,'Aa,'Ax,'Ap,'Auu___3_732) all_return = 'Ap
>>>>>>> snap
=======
type ('Aheap,'Aa,'Ax,'Ap,'Auu___3_746) all_return = 'Ap
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
  fun projectee  -> match projectee with | Inl v -> true | uu____988 -> false 
=======
  fun projectee  -> match projectee with | Inl v -> true | uu____960 -> false 
>>>>>>> snap
=======
  fun projectee  -> match projectee with | Inl v -> true | uu____961 -> false 
>>>>>>> snap
=======
  fun projectee  -> match projectee with | Inl v -> true | uu____977 -> false 
>>>>>>> snap
let __proj__Inl__item__v : 'a 'b . ('a,'b) either -> 'a =
  fun projectee  -> match projectee with | Inl v -> v 
let uu___is_Inr : 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Inr v -> true | uu____1042 -> false
=======
    match projectee with | Inr v -> true | uu____1014 -> false
>>>>>>> snap
=======
    match projectee with | Inr v -> true | uu____1015 -> false
>>>>>>> snap
=======
    match projectee with | Inr v -> true | uu____1031 -> false
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | PpxDerivingShow  -> true | uu____1660 -> false
=======
    match projectee with | PpxDerivingShow  -> true | uu____1630 -> false
>>>>>>> snap
=======
    match projectee with | PpxDerivingShow  -> true | uu____1631 -> false
>>>>>>> snap
=======
    match projectee with | PpxDerivingShow  -> true | uu____1649 -> false
>>>>>>> snap
  
let (uu___is_PpxDerivingShowConstant :
  __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    | uu____1673 -> false
=======
    | uu____1643 -> false
>>>>>>> snap
=======
    | uu____1644 -> false
>>>>>>> snap
=======
    | uu____1662 -> false
>>>>>>> snap
  
let (__proj__PpxDerivingShowConstant__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | PpxDerivingShowConstant _0 -> _0 
let (uu___is_PpxDerivingYoJson : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | PpxDerivingYoJson  -> true | uu____1694 -> false
=======
    match projectee with | PpxDerivingYoJson  -> true | uu____1683 -> false
>>>>>>> snap
  
let (uu___is_CInline : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1694 -> false
  
let (uu___is_Substitute : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1705 -> false
  
let (uu___is_Gc : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  -> match projectee with | Gc  -> true | uu____1716 -> false 
let (uu___is_Comment : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Comment _0 -> true | uu____1740 -> false
=======
    match projectee with | PpxDerivingYoJson  -> true | uu____1664 -> false
=======
    match projectee with | PpxDerivingYoJson  -> true | uu____1665 -> false
>>>>>>> snap
  
let (uu___is_CInline : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1676 -> false
  
let (uu___is_Substitute : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1687 -> false
  
let (uu___is_Gc : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  -> match projectee with | Gc  -> true | uu____1698 -> false 
let (uu___is_Comment : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Comment _0 -> true | uu____1710 -> false
>>>>>>> snap
=======
    match projectee with | Comment _0 -> true | uu____1711 -> false
>>>>>>> snap
=======
    match projectee with | Comment _0 -> true | uu____1729 -> false
>>>>>>> snap
  
let (__proj__Comment__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_CPrologue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | CPrologue _0 -> true | uu____1763 -> false
=======
    match projectee with | CPrologue _0 -> true | uu____1733 -> false
>>>>>>> snap
=======
    match projectee with | CPrologue _0 -> true | uu____1734 -> false
>>>>>>> snap
=======
    match projectee with | CPrologue _0 -> true | uu____1752 -> false
>>>>>>> snap
  
let (__proj__CPrologue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | CPrologue _0 -> _0 
let (uu___is_CEpilogue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | CEpilogue _0 -> true | uu____1786 -> false
=======
    match projectee with | CEpilogue _0 -> true | uu____1756 -> false
>>>>>>> snap
=======
    match projectee with | CEpilogue _0 -> true | uu____1757 -> false
>>>>>>> snap
=======
    match projectee with | CEpilogue _0 -> true | uu____1775 -> false
>>>>>>> snap
  
let (__proj__CEpilogue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee  -> match projectee with | CEpilogue _0 -> _0 
let (uu___is_CConst : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | CConst _0 -> true | uu____1809 -> false
=======
    match projectee with | CConst _0 -> true | uu____1779 -> false
>>>>>>> snap
=======
    match projectee with | CConst _0 -> true | uu____1780 -> false
>>>>>>> snap
=======
    match projectee with | CConst _0 -> true | uu____1798 -> false
>>>>>>> snap
  
let (__proj__CConst__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | CConst _0 -> _0 
let (uu___is_CCConv : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | CCConv _0 -> true | uu____1832 -> false
=======
    match projectee with | CCConv _0 -> true | uu____1802 -> false
>>>>>>> snap
=======
    match projectee with | CCConv _0 -> true | uu____1803 -> false
>>>>>>> snap
=======
    match projectee with | CCConv _0 -> true | uu____1821 -> false
>>>>>>> snap
  
let (__proj__CCConv__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee  -> match projectee with | CCConv _0 -> _0 
let (uu___is_CAbstractStruct : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | CAbstractStruct  -> true | uu____1853 -> false
=======
    match projectee with | CAbstractStruct  -> true | uu____1842 -> false
>>>>>>> snap
  
let (uu___is_CIfDef : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CIfDef  -> true | uu____1853 -> false
  
let (uu___is_CMacro : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | CMacro  -> true | uu____1875 -> false
=======
    match projectee with | CAbstractStruct  -> true | uu____1823 -> false
=======
    match projectee with | CAbstractStruct  -> true | uu____1824 -> false
>>>>>>> snap
  
let (uu___is_CIfDef : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
    match projectee with | CIfDef  -> true | uu____1835 -> false
  
let (uu___is_CMacro : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | CMacro  -> true | uu____1845 -> false
>>>>>>> snap
=======
    match projectee with | CMacro  -> true | uu____1846 -> false
>>>>>>> snap
=======
    match projectee with | CMacro  -> true | uu____1864 -> false
>>>>>>> snap
  












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
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | Simpl  -> true | uu____1940 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1951 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1962 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1973 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1984 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1995 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____2006 -> false
  
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____2017 -> false 
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____2028 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____2043 -> false
=======
    match projectee with | Simpl  -> true | uu____1907 -> false
=======
    match projectee with | Simpl  -> true | uu____1908 -> false
>>>>>>> snap
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1919 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1930 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1941 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1952 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1963 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1974 -> false
  
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____1985 -> false 
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____1996 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | UnfoldOnly _0 -> true | uu____2010 -> false
>>>>>>> snap
=======
    match projectee with | UnfoldOnly _0 -> true | uu____2011 -> false
>>>>>>> snap
=======
    match projectee with | Simpl  -> true | uu____1930 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____1941 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____1952 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____1963 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____1974 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____1985 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____1996 -> false
  
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____2007 -> false 
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____2018 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____2033 -> false
>>>>>>> snap
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | UnfoldFully _0 -> true | uu____2074 -> false
=======
    match projectee with | UnfoldFully _0 -> true | uu____2041 -> false
>>>>>>> snap
=======
    match projectee with | UnfoldFully _0 -> true | uu____2042 -> false
>>>>>>> snap
=======
    match projectee with | UnfoldFully _0 -> true | uu____2064 -> false
>>>>>>> snap
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
    match projectee with | UnfoldAttr _0 -> true | uu____2105 -> false
=======
    match projectee with | UnfoldAttr _0 -> true | uu____2072 -> false
>>>>>>> snap
=======
    match projectee with | UnfoldAttr _0 -> true | uu____2073 -> false
>>>>>>> snap
=======
    match projectee with | UnfoldAttr _0 -> true | uu____2095 -> false
>>>>>>> snap
  
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