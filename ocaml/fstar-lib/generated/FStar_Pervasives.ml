open Prims
type pattern = unit


type eqtype_u = unit
type 'p spinoff = 'p
let id : 'a . 'a -> 'a = fun x -> x
type ('a, 'uuuuu) trivial_pure_post = unit
type ('uuuuu, 'uuuuu1) ambient = unit
let normalize_term : 'uuuuu . 'uuuuu -> 'uuuuu = fun x -> x
type 'a normalize = 'a
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | ZetaFull 
  | Iota 
  | NBE 
  | Reify 
  | NormDebug 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | UnfoldQual of Prims.string Prims.list 
  | UnfoldNamespace of Prims.string Prims.list 
  | Unmeta 
  | Unascribe 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Simpl -> true | uu___ -> false
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu___ -> false
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu___ -> false
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Primops -> true | uu___ -> false
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Delta -> true | uu___ -> false
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu___ -> false
let (uu___is_ZetaFull : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | ZetaFull -> true | uu___ -> false
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu___ -> false
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu___ -> false
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu___ -> false
let (uu___is_NormDebug : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | NormDebug -> true | uu___ -> false
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu___ -> false
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu___ -> false
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu___ -> false
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldQual : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldQual _0 -> true | uu___ -> false
let (__proj__UnfoldQual__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldQual _0 -> _0
let (uu___is_UnfoldNamespace : norm_step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldNamespace _0 -> true | uu___ -> false
let (__proj__UnfoldNamespace__item___0 :
  norm_step -> Prims.string Prims.list) =
  fun projectee -> match projectee with | UnfoldNamespace _0 -> _0
let (uu___is_Unmeta : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu___ -> false
let (uu___is_Unascribe : norm_step -> Prims.bool) =
  fun projectee -> match projectee with | Unascribe -> true | uu___ -> false
let (simplify : norm_step) = Simpl
let (weak : norm_step) = Weak
let (hnf : norm_step) = HNF
let (primops : norm_step) = Primops
let (delta : norm_step) = Delta
let (norm_debug : norm_step) = NormDebug
let (zeta : norm_step) = Zeta
let (zeta_full : norm_step) = ZetaFull
let (iota : norm_step) = Iota
let (nbe : norm_step) = NBE
let (reify_ : norm_step) = Reify
let (delta_only : Prims.string Prims.list -> norm_step) =
  fun s -> UnfoldOnly s
let (delta_fully : Prims.string Prims.list -> norm_step) =
  fun s -> UnfoldFully s
let (delta_attr : Prims.string Prims.list -> norm_step) =
  fun s -> UnfoldAttr s
let (delta_qualifier : Prims.string Prims.list -> norm_step) =
  fun s -> UnfoldAttr s
let (delta_namespace : Prims.string Prims.list -> norm_step) =
  fun s -> UnfoldNamespace s
let (unmeta : norm_step) = Unmeta
let (unascribe : norm_step) = Unascribe
let (norm : norm_step Prims.list -> unit -> Obj.t -> Obj.t) =
  fun uu___ -> fun uu___1 -> fun x -> x
type ('a, 'x, 'uuuuu) pure_return = unit
type ('a, 'b, 'wp1, 'wp2, 'uuuuu) pure_bind_wp = 'wp1
type ('a, 'p, 'wputhen, 'wpuelse, 'uuuuu) pure_if_then_else = unit
type ('a, 'wp, 'uuuuu) pure_ite_wp = unit
type ('a, 'b, 'wp, 'uuuuu) pure_close_wp = unit
type ('a, 'uuuuu) pure_null_wp = unit
type ('p, 'uuuuu) pure_assert_wp = unit
type ('p, 'uuuuu) pure_assume_wp = unit
type ('a, 'pre, 'post, 'uuuuu) div_hoare_to_wp = unit
type 'heap st_pre_h = unit
type ('heap, 'a, 'pre) st_post_h' = unit
type ('heap, 'a) st_post_h = unit
type ('heap, 'a) st_wp_h = unit
type ('heap, 'a, 'x, 'p, 'uuuuu) st_return = 'p
type ('heap, 'a, 'b, 'wp1, 'wp2, 'p, 'h0) st_bind_wp = 'wp1
type ('heap, 'a, 'p, 'wputhen, 'wpuelse, 'post, 'h0) st_if_then_else = unit
type ('heap, 'a, 'wp, 'post, 'h0) st_ite_wp = unit
type ('heap, 'a, 'wp1, 'wp2) st_stronger = unit
type ('heap, 'a, 'b, 'wp, 'p, 'h) st_close_wp = unit
type ('heap, 'a, 'wp) st_trivial = unit
type 'a result =
  | V of 'a 
  | E of Prims.exn 
  | Err of Prims.string 
let uu___is_V : 'a . 'a result -> Prims.bool =
  fun projectee -> match projectee with | V v -> true | uu___ -> false
let __proj__V__item__v : 'a . 'a result -> 'a =
  fun projectee -> match projectee with | V v -> v
let uu___is_E : 'a . 'a result -> Prims.bool =
  fun projectee -> match projectee with | E e -> true | uu___ -> false
let __proj__E__item__e : 'a . 'a result -> Prims.exn =
  fun projectee -> match projectee with | E e -> e
let uu___is_Err : 'a . 'a result -> Prims.bool =
  fun projectee -> match projectee with | Err msg -> true | uu___ -> false
let __proj__Err__item__msg : 'a . 'a result -> Prims.string =
  fun projectee -> match projectee with | Err msg -> msg
type ex_pre = unit
type ('a, 'pre) ex_post' = unit
type 'a ex_post = unit
type 'a ex_wp = unit
type ('a, 'x, 'p) ex_return = 'p
type ('a, 'b, 'wp1, 'wp2, 'p) ex_bind_wp = unit
type ('a, 'p, 'wputhen, 'wpuelse, 'post) ex_if_then_else = unit
type ('a, 'wp, 'post) ex_ite_wp = unit
type ('a, 'wp1, 'wp2) ex_stronger = unit
type ('a, 'b, 'wp, 'p) ex_close_wp = unit
type ('a, 'wp) ex_trivial = 'wp
type ('a, 'wp, 'p) lift_div_exn = 'wp
type 'h all_pre_h = unit
type ('h, 'a, 'pre) all_post_h' = unit
type ('h, 'a) all_post_h = unit
type ('h, 'a) all_wp_h = unit
type ('heap, 'a, 'x, 'p, 'uuuuu) all_return = 'p
type ('heap, 'a, 'b, 'wp1, 'wp2, 'p, 'h0) all_bind_wp = 'wp1
type ('heap, 'a, 'p, 'wputhen, 'wpuelse, 'post, 'h0) all_if_then_else = unit
type ('heap, 'a, 'wp, 'post, 'h0) all_ite_wp = unit
type ('heap, 'a, 'wp1, 'wp2) all_stronger = unit
type ('heap, 'a, 'b, 'wp, 'p, 'h) all_close_wp = unit
type ('heap, 'a, 'wp) all_trivial = unit
type 'uuuuu inversion = unit
type ('a, 'b) either =
  | Inl of 'a 
  | Inr of 'b 
let uu___is_Inl : 'a 'b . ('a, 'b) either -> Prims.bool =
  fun projectee -> match projectee with | Inl v -> true | uu___ -> false
let __proj__Inl__item__v : 'a 'b . ('a, 'b) either -> 'a =
  fun projectee -> match projectee with | Inl v -> v
let uu___is_Inr : 'a 'b . ('a, 'b) either -> Prims.bool =
  fun projectee -> match projectee with | Inr v -> true | uu___ -> false
let __proj__Inr__item__v : 'a 'b . ('a, 'b) either -> 'b =
  fun projectee -> match projectee with | Inr v -> v
let dfst : 'a 'b . ('a, 'b) Prims.dtuple2 -> 'a =
  fun t -> Prims.__proj__Mkdtuple2__item___1 t
let dsnd : 'a 'b . ('a, 'b) Prims.dtuple2 -> 'b =
  fun t -> Prims.__proj__Mkdtuple2__item___2 t
type ('a, 'b, 'c) dtuple3 =
  | Mkdtuple3 of 'a * 'b * 'c 
let uu___is_Mkdtuple3 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> Prims.bool =
  fun projectee -> true
let __proj__Mkdtuple3__item___1 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> 'a =
  fun projectee -> match projectee with | Mkdtuple3 (_1, _2, _3) -> _1
let __proj__Mkdtuple3__item___2 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> 'b =
  fun projectee -> match projectee with | Mkdtuple3 (_1, _2, _3) -> _2
let __proj__Mkdtuple3__item___3 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> 'c =
  fun projectee -> match projectee with | Mkdtuple3 (_1, _2, _3) -> _3
type ('a, 'b, 'c, 'd) dtuple4 =
  | Mkdtuple4 of 'a * 'b * 'c * 'd 
let uu___is_Mkdtuple4 : 'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> Prims.bool
  = fun projectee -> true
let __proj__Mkdtuple4__item___1 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'a =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _1
let __proj__Mkdtuple4__item___2 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'b =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _2
let __proj__Mkdtuple4__item___3 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'c =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _3
let __proj__Mkdtuple4__item___4 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'd =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _4
type ('a, 'b, 'c, 'd, 'e) dtuple5 =
  | Mkdtuple5 of 'a * 'b * 'c * 'd * 'e 
let uu___is_Mkdtuple5 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> Prims.bool =
  fun projectee -> true
let __proj__Mkdtuple5__item___1 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'a =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _1
let __proj__Mkdtuple5__item___2 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'b =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _2
let __proj__Mkdtuple5__item___3 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'c =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _3
let __proj__Mkdtuple5__item___4 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'd =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _4
let __proj__Mkdtuple5__item___5 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'e =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _5
let rec false_elim : 'uuuuu . unit -> 'uuuuu = fun uu___ -> false_elim ()
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
  | CNoInline 
let (uu___is_PpxDerivingShow : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee ->
    match projectee with | PpxDerivingShow -> true | uu___ -> false
let (uu___is_PpxDerivingShowConstant :
  __internal_ocaml_attributes -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
    | uu___ -> false
let (__proj__PpxDerivingShowConstant__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee -> match projectee with | PpxDerivingShowConstant _0 -> _0
let (uu___is_PpxDerivingYoJson : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee ->
    match projectee with | PpxDerivingYoJson -> true | uu___ -> false
let (uu___is_CInline : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | CInline -> true | uu___ -> false
let (uu___is_Substitute : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | Substitute -> true | uu___ -> false
let (uu___is_Gc : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | Gc -> true | uu___ -> false
let (uu___is_Comment : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | Comment _0 -> true | uu___ -> false
let (__proj__Comment__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_CPrologue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee ->
    match projectee with | CPrologue _0 -> true | uu___ -> false
let (__proj__CPrologue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee -> match projectee with | CPrologue _0 -> _0
let (uu___is_CEpilogue : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee ->
    match projectee with | CEpilogue _0 -> true | uu___ -> false
let (__proj__CEpilogue__item___0 :
  __internal_ocaml_attributes -> Prims.string) =
  fun projectee -> match projectee with | CEpilogue _0 -> _0
let (uu___is_CConst : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | CConst _0 -> true | uu___ -> false
let (__proj__CConst__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee -> match projectee with | CConst _0 -> _0
let (uu___is_CCConv : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | CCConv _0 -> true | uu___ -> false
let (__proj__CCConv__item___0 : __internal_ocaml_attributes -> Prims.string)
  = fun projectee -> match projectee with | CCConv _0 -> _0
let (uu___is_CAbstractStruct : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee ->
    match projectee with | CAbstractStruct -> true | uu___ -> false
let (uu___is_CIfDef : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | CIfDef -> true | uu___ -> false
let (uu___is_CMacro : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | CMacro -> true | uu___ -> false
let (uu___is_CNoInline : __internal_ocaml_attributes -> Prims.bool) =
  fun projectee -> match projectee with | CNoInline -> true | uu___ -> false
let singleton : 'uuuuu . 'uuuuu -> 'uuuuu = fun x -> x
type 'a eqtype_as_type = 'a
let coerce_eq : 'a 'b . unit -> 'a -> 'b =
  fun uu___1 -> fun uu___ -> (fun uu___ -> fun x -> Obj.magic x) uu___1 uu___