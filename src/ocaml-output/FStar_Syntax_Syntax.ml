open Prims
type ('a,'t) withinfo_t = {
  v: 'a;
  ty: 't;
  p: FStar_Range.range;}
type 't var = (FStar_Ident.lident,'t) withinfo_t
type sconst = FStar_Const.sconst
type pragma =
  | SetOptions of Prims.string
  | ResetOptions of Prims.string FStar_Pervasives_Native.option
  | LightOff
let uu___is_SetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____103 -> false
let __proj__SetOptions__item___0: pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0
let uu___is_ResetOptions: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____117 -> false
let __proj__ResetOptions__item___0:
  pragma -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0
let uu___is_LightOff: pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____134 -> false
type 'a memo = 'a FStar_Pervasives_Native.option FStar_ST.ref
type arg_qualifier =
  | Implicit of Prims.bool
  | Equality
let uu___is_Implicit: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit _0 -> true | uu____151 -> false
let __proj__Implicit__item___0: arg_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Implicit _0 -> _0
let uu___is_Equality: arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____162 -> false
type aqual = arg_qualifier FStar_Pervasives_Native.option
type universe =
  | U_zero
  | U_succ of universe
  | U_max of universe Prims.list
  | U_bvar of Prims.int
  | U_name of FStar_Ident.ident
  | U_unif of universe FStar_Pervasives_Native.option FStar_Unionfind.uvar
  | U_unknown
let uu___is_U_zero: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_zero  -> true | uu____194 -> false
let uu___is_U_succ: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_succ _0 -> true | uu____199 -> false
let __proj__U_succ__item___0: universe -> universe =
  fun projectee  -> match projectee with | U_succ _0 -> _0
let uu___is_U_max: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_max _0 -> true | uu____213 -> false
let __proj__U_max__item___0: universe -> universe Prims.list =
  fun projectee  -> match projectee with | U_max _0 -> _0
let uu___is_U_bvar: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_bvar _0 -> true | uu____231 -> false
let __proj__U_bvar__item___0: universe -> Prims.int =
  fun projectee  -> match projectee with | U_bvar _0 -> _0
let uu___is_U_name: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_name _0 -> true | uu____243 -> false
let __proj__U_name__item___0: universe -> FStar_Ident.ident =
  fun projectee  -> match projectee with | U_name _0 -> _0
let uu___is_U_unif: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_unif _0 -> true | uu____259 -> false
let __proj__U_unif__item___0:
  universe -> universe FStar_Pervasives_Native.option FStar_Unionfind.uvar =
  fun projectee  -> match projectee with | U_unif _0 -> _0
let uu___is_U_unknown: universe -> Prims.bool =
  fun projectee  ->
    match projectee with | U_unknown  -> true | uu____282 -> false
type univ_name = FStar_Ident.ident
type universe_uvar =
  universe FStar_Pervasives_Native.option FStar_Unionfind.uvar
type univ_names = univ_name Prims.list
type universes = universe Prims.list
type monad_name = FStar_Ident.lident
type delta_depth =
  | Delta_constant
  | Delta_defined_at_level of Prims.int
  | Delta_equational
  | Delta_abstract of delta_depth
let uu___is_Delta_constant: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta_constant  -> true | uu____302 -> false
let uu___is_Delta_defined_at_level: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Delta_defined_at_level _0 -> true
    | uu____307 -> false
let __proj__Delta_defined_at_level__item___0: delta_depth -> Prims.int =
  fun projectee  -> match projectee with | Delta_defined_at_level _0 -> _0
let uu___is_Delta_equational: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta_equational  -> true | uu____318 -> false
let uu___is_Delta_abstract: delta_depth -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta_abstract _0 -> true | uu____323 -> false
let __proj__Delta_abstract__item___0: delta_depth -> delta_depth =
  fun projectee  -> match projectee with | Delta_abstract _0 -> _0
type term' =
  | Tm_bvar of bv
  | Tm_name of bv
  | Tm_fvar of fv
  | Tm_uinst of ((term',term') syntax,universes)
  FStar_Pervasives_Native.tuple2
  | Tm_constant of sconst
  | Tm_type of universe
  | Tm_abs of
  ((bv,aqual) FStar_Pervasives_Native.tuple2 Prims.list,(term',term') syntax,
  (lcomp,(FStar_Ident.lident,cflags Prims.list)
           FStar_Pervasives_Native.tuple2)
    FStar_Util.either FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3
  | Tm_arrow of
  ((bv,aqual) FStar_Pervasives_Native.tuple2 Prims.list,(comp',Prims.unit)
                                                          syntax)
  FStar_Pervasives_Native.tuple2
  | Tm_refine of (bv,(term',term') syntax) FStar_Pervasives_Native.tuple2
  | Tm_app of
  ((term',term') syntax,((term',term') syntax,aqual)
                          FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Tm_match of
  ((term',term') syntax,((pat',term') withinfo_t,(term',term') syntax
                                                   FStar_Pervasives_Native.option,
                          (term',term') syntax)
                          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2
  | Tm_ascribed of
  ((term',term') syntax,(((term',term') syntax,(comp',Prims.unit) syntax)
                           FStar_Util.either,(term',term') syntax
                                               FStar_Pervasives_Native.option)
                          FStar_Pervasives_Native.tuple2,FStar_Ident.lident
                                                           FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3
  | Tm_let of
  ((Prims.bool,letbinding Prims.list) FStar_Pervasives_Native.tuple2,
  (term',term') syntax) FStar_Pervasives_Native.tuple2
  | Tm_uvar of
  ((term',term') syntax uvar_basis FStar_Unionfind.uvar,(term',term') syntax)
  FStar_Pervasives_Native.tuple2
  | Tm_delayed of
  ((((term',term') syntax,(subst_elt Prims.list Prims.list,FStar_Range.range
                                                             FStar_Pervasives_Native.option)
                            FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2,Prims.unit -> (term',term') syntax)
     FStar_Util.either,(term',term') syntax memo)
  FStar_Pervasives_Native.tuple2
  | Tm_meta of ((term',term') syntax,metadata)
  FStar_Pervasives_Native.tuple2
  | Tm_unknown
and pat' =
  | Pat_constant of sconst
  | Pat_cons of
  (fv,((pat',term') withinfo_t,Prims.bool) FStar_Pervasives_Native.tuple2
        Prims.list)
  FStar_Pervasives_Native.tuple2
  | Pat_var of bv
  | Pat_wild of bv
  | Pat_dot_term of (bv,(term',term') syntax) FStar_Pervasives_Native.tuple2
and letbinding =
  {
  lbname: (bv,fv) FStar_Util.either;
  lbunivs: univ_name Prims.list;
  lbtyp: (term',term') syntax;
  lbeff: FStar_Ident.lident;
  lbdef: (term',term') syntax;}
and comp_typ =
  {
  comp_univs: universes;
  effect_name: FStar_Ident.lident;
  result_typ: (term',term') syntax;
  effect_args:
    ((term',term') syntax,aqual) FStar_Pervasives_Native.tuple2 Prims.list;
  flags: cflags Prims.list;}
and comp' =
  | Total of ((term',term') syntax,universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | GTotal of ((term',term') syntax,universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Comp of comp_typ
and cflags =
  | TOTAL
  | MLEFFECT
  | RETURN
  | PARTIAL_RETURN
  | SOMETRIVIAL
  | LEMMA
  | CPS
  | DECREASES of (term',term') syntax
and metadata =
  | Meta_pattern of ((term',term') syntax,aqual)
  FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  | Meta_named of FStar_Ident.lident
  | Meta_labeled of (Prims.string,FStar_Range.range,Prims.bool)
  FStar_Pervasives_Native.tuple3
  | Meta_desugared of meta_source_info
  | Meta_monadic of (monad_name,(term',term') syntax)
  FStar_Pervasives_Native.tuple2
  | Meta_monadic_lift of (monad_name,monad_name,(term',term') syntax)
  FStar_Pervasives_Native.tuple3
and 'a uvar_basis =
  | Uvar
  | Fixed of 'a
and meta_source_info =
  | Data_app
  | Sequence
  | Primop
  | Masked_effect
  | Meta_smt_pat
  | Mutable_alloc
  | Mutable_rval
and fv_qual =
  | Data_ctor
  | Record_projector of (FStar_Ident.lident,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2
  | Record_ctor of (FStar_Ident.lident,FStar_Ident.ident Prims.list)
  FStar_Pervasives_Native.tuple2
and subst_elt =
  | DB of (Prims.int,bv) FStar_Pervasives_Native.tuple2
  | NM of (bv,Prims.int) FStar_Pervasives_Native.tuple2
  | NT of (bv,(term',term') syntax) FStar_Pervasives_Native.tuple2
  | UN of (Prims.int,universe) FStar_Pervasives_Native.tuple2
  | UD of (univ_name,Prims.int) FStar_Pervasives_Native.tuple2
and ('a,'b) syntax =
  {
  n: 'a;
  tk: 'b memo;
  pos: FStar_Range.range;
  vars: free_vars memo;}
and bv =
  {
  ppname: FStar_Ident.ident;
  index: Prims.int;
  sort: (term',term') syntax;}
and fv =
  {
  fv_name: (term',term') syntax var;
  fv_delta: delta_depth;
  fv_qual: fv_qual FStar_Pervasives_Native.option;}
and free_vars =
  {
  free_names: bv FStar_Util.set;
  free_uvars:
    ((term',term') syntax uvar_basis FStar_Unionfind.uvar,(term',term')
                                                            syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set;
  free_univs: universe_uvar FStar_Util.set;
  free_univ_names: univ_name FStar_Util.fifo_set;}
and lcomp =
  {
  eff_name: FStar_Ident.lident;
  res_typ: (term',term') syntax;
  cflags: cflags Prims.list;
  comp: Prims.unit -> (comp',Prims.unit) syntax;}
let uu___is_Tm_bvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_bvar _0 -> true | uu____1040 -> false
let __proj__Tm_bvar__item___0: term' -> bv =
  fun projectee  -> match projectee with | Tm_bvar _0 -> _0
let uu___is_Tm_name: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_name _0 -> true | uu____1052 -> false
let __proj__Tm_name__item___0: term' -> bv =
  fun projectee  -> match projectee with | Tm_name _0 -> _0
let uu___is_Tm_fvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_fvar _0 -> true | uu____1064 -> false
let __proj__Tm_fvar__item___0: term' -> fv =
  fun projectee  -> match projectee with | Tm_fvar _0 -> _0
let uu___is_Tm_uinst: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_uinst _0 -> true | uu____1084 -> false
let __proj__Tm_uinst__item___0:
  term' -> ((term',term') syntax,universes) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Tm_uinst _0 -> _0
let uu___is_Tm_constant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_constant _0 -> true | uu____1120 -> false
let __proj__Tm_constant__item___0: term' -> sconst =
  fun projectee  -> match projectee with | Tm_constant _0 -> _0
let uu___is_Tm_type: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_type _0 -> true | uu____1132 -> false
let __proj__Tm_type__item___0: term' -> universe =
  fun projectee  -> match projectee with | Tm_type _0 -> _0
let uu___is_Tm_abs: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_abs _0 -> true | uu____1172 -> false
let __proj__Tm_abs__item___0:
  term' ->
    ((bv,aqual) FStar_Pervasives_Native.tuple2 Prims.list,(term',term')
                                                            syntax,(lcomp,
                                                                    (FStar_Ident.lident,
                                                                    cflags
                                                                    Prims.list)
                                                                    FStar_Pervasives_Native.tuple2)
                                                                    FStar_Util.either
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Tm_abs _0 -> _0
let uu___is_Tm_arrow: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_arrow _0 -> true | uu____1282 -> false
let __proj__Tm_arrow__item___0:
  term' ->
    ((bv,aqual) FStar_Pervasives_Native.tuple2 Prims.list,(comp',Prims.unit)
                                                            syntax)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tm_arrow _0 -> _0
let uu___is_Tm_refine: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_refine _0 -> true | uu____1344 -> false
let __proj__Tm_refine__item___0:
  term' -> (bv,(term',term') syntax) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Tm_refine _0 -> _0
let uu___is_Tm_app: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_app _0 -> true | uu____1398 -> false
let __proj__Tm_app__item___0:
  term' ->
    ((term',term') syntax,((term',term') syntax,aqual)
                            FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tm_app _0 -> _0
let uu___is_Tm_match: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_match _0 -> true | uu____1494 -> false
let __proj__Tm_match__item___0:
  term' ->
    ((term',term') syntax,((pat',term') withinfo_t,(term',term') syntax
                                                     FStar_Pervasives_Native.option,
                            (term',term') syntax)
                            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tm_match _0 -> _0
let uu___is_Tm_ascribed: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_ascribed _0 -> true | uu____1630 -> false
let __proj__Tm_ascribed__item___0:
  term' ->
    ((term',term') syntax,(((term',term') syntax,(comp',Prims.unit) syntax)
                             FStar_Util.either,(term',term') syntax
                                                 FStar_Pervasives_Native.option)
                            FStar_Pervasives_Native.tuple2,FStar_Ident.lident
                                                             FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Tm_ascribed _0 -> _0
let uu___is_Tm_let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_let _0 -> true | uu____1758 -> false
let __proj__Tm_let__item___0:
  term' ->
    ((Prims.bool,letbinding Prims.list) FStar_Pervasives_Native.tuple2,
      (term',term') syntax) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tm_let _0 -> _0
let uu___is_Tm_uvar: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_uvar _0 -> true | uu____1828 -> false
let __proj__Tm_uvar__item___0:
  term' ->
    ((term',term') syntax uvar_basis FStar_Unionfind.uvar,(term',term')
                                                            syntax)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tm_uvar _0 -> _0
let uu___is_Tm_delayed: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_delayed _0 -> true | uu____1926 -> false
let __proj__Tm_delayed__item___0:
  term' ->
    ((((term',term') syntax,(subst_elt Prims.list Prims.list,FStar_Range.range
                                                               FStar_Pervasives_Native.option)
                              FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple2,Prims.unit -> (term',term') syntax)
       FStar_Util.either,(term',term') syntax memo)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tm_delayed _0 -> _0
let uu___is_Tm_meta: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_meta _0 -> true | uu____2060 -> false
let __proj__Tm_meta__item___0:
  term' -> ((term',term') syntax,metadata) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Tm_meta _0 -> _0
let uu___is_Tm_unknown: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tm_unknown  -> true | uu____2095 -> false
let uu___is_Pat_constant: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_constant _0 -> true | uu____2100 -> false
let __proj__Pat_constant__item___0: pat' -> sconst =
  fun projectee  -> match projectee with | Pat_constant _0 -> _0
let uu___is_Pat_cons: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_cons _0 -> true | uu____2126 -> false
let __proj__Pat_cons__item___0:
  pat' ->
    (fv,((pat',term') withinfo_t,Prims.bool) FStar_Pervasives_Native.tuple2
          Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Pat_cons _0 -> _0
let uu___is_Pat_var: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_var _0 -> true | uu____2180 -> false
let __proj__Pat_var__item___0: pat' -> bv =
  fun projectee  -> match projectee with | Pat_var _0 -> _0
let uu___is_Pat_wild: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_wild _0 -> true | uu____2192 -> false
let __proj__Pat_wild__item___0: pat' -> bv =
  fun projectee  -> match projectee with | Pat_wild _0 -> _0
let uu___is_Pat_dot_term: pat' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_dot_term _0 -> true | uu____2212 -> false
let __proj__Pat_dot_term__item___0:
  pat' -> (bv,(term',term') syntax) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Pat_dot_term _0 -> _0
let uu___is_Total: comp' -> Prims.bool =
  fun projectee  ->
    match projectee with | Total _0 -> true | uu____2358 -> false
let __proj__Total__item___0:
  comp' ->
    ((term',term') syntax,universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Total _0 -> _0
let uu___is_GTotal: comp' -> Prims.bool =
  fun projectee  ->
    match projectee with | GTotal _0 -> true | uu____2410 -> false
let __proj__GTotal__item___0:
  comp' ->
    ((term',term') syntax,universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | GTotal _0 -> _0
let uu___is_Comp: comp' -> Prims.bool =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____2452 -> false
let __proj__Comp__item___0: comp' -> comp_typ =
  fun projectee  -> match projectee with | Comp _0 -> _0
let uu___is_TOTAL: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____2463 -> false
let uu___is_MLEFFECT: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2467 -> false
let uu___is_RETURN: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2471 -> false
let uu___is_PARTIAL_RETURN: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2475 -> false
let uu___is_SOMETRIVIAL: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2479 -> false
let uu___is_LEMMA: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2483 -> false
let uu___is_CPS: cflags -> Prims.bool =
  fun projectee  -> match projectee with | CPS  -> true | uu____2487 -> false
let uu___is_DECREASES: cflags -> Prims.bool =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2496 -> false
let __proj__DECREASES__item___0: cflags -> (term',term') syntax =
  fun projectee  -> match projectee with | DECREASES _0 -> _0
let uu___is_Meta_pattern: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_pattern _0 -> true | uu____2532 -> false
let __proj__Meta_pattern__item___0:
  metadata ->
    ((term',term') syntax,aqual) FStar_Pervasives_Native.tuple2 Prims.list
      Prims.list
  = fun projectee  -> match projectee with | Meta_pattern _0 -> _0
let uu___is_Meta_named: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_named _0 -> true | uu____2580 -> false
let __proj__Meta_named__item___0: metadata -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Meta_named _0 -> _0
let uu___is_Meta_labeled: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_labeled _0 -> true | uu____2598 -> false
let __proj__Meta_labeled__item___0:
  metadata ->
    (Prims.string,FStar_Range.range,Prims.bool)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Meta_labeled _0 -> _0
let uu___is_Meta_desugared: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_desugared _0 -> true | uu____2628 -> false
let __proj__Meta_desugared__item___0: metadata -> meta_source_info =
  fun projectee  -> match projectee with | Meta_desugared _0 -> _0
let uu___is_Meta_monadic: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_monadic _0 -> true | uu____2648 -> false
let __proj__Meta_monadic__item___0:
  metadata ->
    (monad_name,(term',term') syntax) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta_monadic _0 -> _0
let uu___is_Meta_monadic_lift: metadata -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_monadic_lift _0 -> true | uu____2694 -> false
let __proj__Meta_monadic_lift__item___0:
  metadata ->
    (monad_name,monad_name,(term',term') syntax)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Meta_monadic_lift _0 -> _0
let uu___is_Uvar projectee =
  match projectee with | Uvar  -> true | uu____2743 -> false
let uu___is_Fixed projectee =
  match projectee with | Fixed _0 -> true | uu____2758 -> false
let __proj__Fixed__item___0 projectee = match projectee with | Fixed _0 -> _0
let uu___is_Data_app: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Data_app  -> true | uu____2779 -> false
let uu___is_Sequence: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Sequence  -> true | uu____2783 -> false
let uu___is_Primop: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Primop  -> true | uu____2787 -> false
let uu___is_Masked_effect: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Masked_effect  -> true | uu____2791 -> false
let uu___is_Meta_smt_pat: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta_smt_pat  -> true | uu____2795 -> false
let uu___is_Mutable_alloc: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable_alloc  -> true | uu____2799 -> false
let uu___is_Mutable_rval: meta_source_info -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable_rval  -> true | uu____2803 -> false
let uu___is_Data_ctor: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Data_ctor  -> true | uu____2807 -> false
let uu___is_Record_projector: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_projector _0 -> true | uu____2816 -> false
let __proj__Record_projector__item___0:
  fv_qual ->
    (FStar_Ident.lident,FStar_Ident.ident) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Record_projector _0 -> _0
let uu___is_Record_ctor: fv_qual -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_ctor _0 -> true | uu____2846 -> false
let __proj__Record_ctor__item___0:
  fv_qual ->
    (FStar_Ident.lident,FStar_Ident.ident Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Record_ctor _0 -> _0
let uu___is_DB: subst_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | DB _0 -> true | uu____2880 -> false
let __proj__DB__item___0:
  subst_elt -> (Prims.int,bv) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | DB _0 -> _0
let uu___is_NM: subst_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | NM _0 -> true | uu____2908 -> false
let __proj__NM__item___0:
  subst_elt -> (bv,Prims.int) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | NM _0 -> _0
let uu___is_NT: subst_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | NT _0 -> true | uu____2940 -> false
let __proj__NT__item___0:
  subst_elt -> (bv,(term',term') syntax) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | NT _0 -> _0
let uu___is_UN: subst_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UN _0 -> true | uu____2980 -> false
let __proj__UN__item___0:
  subst_elt -> (Prims.int,universe) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | UN _0 -> _0
let uu___is_UD: subst_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UD _0 -> true | uu____3008 -> false
let __proj__UD__item___0:
  subst_elt -> (univ_name,Prims.int) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | UD _0 -> _0
type pat = (pat',term') withinfo_t
type term = (term',term') syntax
type branch =
  ((pat',term') withinfo_t,(term',term') syntax
                             FStar_Pervasives_Native.option,(term',term')
                                                              syntax)
    FStar_Pervasives_Native.tuple3
type comp = (comp',Prims.unit) syntax
type ascription =
  (((term',term') syntax,(comp',Prims.unit) syntax) FStar_Util.either,
    (term',term') syntax FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2
type typ = (term',term') syntax
type arg = ((term',term') syntax,aqual) FStar_Pervasives_Native.tuple2
type args =
  ((term',term') syntax,aqual) FStar_Pervasives_Native.tuple2 Prims.list
type binder = (bv,aqual) FStar_Pervasives_Native.tuple2
type binders = (bv,aqual) FStar_Pervasives_Native.tuple2 Prims.list
type uvar = (term',term') syntax uvar_basis FStar_Unionfind.uvar
type lbname = (bv,fv) FStar_Util.either
type letbindings =
  (Prims.bool,letbinding Prims.list) FStar_Pervasives_Native.tuple2
type subst_ts =
  (subst_elt Prims.list Prims.list,FStar_Range.range
                                     FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2
type freenames = bv FStar_Util.set
type uvars =
  ((term',term') syntax uvar_basis FStar_Unionfind.uvar,(term',term') syntax)
    FStar_Pervasives_Native.tuple2 FStar_Util.set
type residual_comp =
  (FStar_Ident.lident,cflags Prims.list) FStar_Pervasives_Native.tuple2
type tscheme = (univ_name Prims.list,typ) FStar_Pervasives_Native.tuple2
type freenames_l = bv Prims.list
type formula = typ
type formulae = typ Prims.list
type qualifier =
  | Assumption
  | New
  | Private
  | Unfold_for_unification_and_vcgen
  | Visible_default
  | Irreducible
  | Abstract
  | Inline_for_extraction
  | NoExtract
  | Noeq
  | Unopteq
  | TotalEffect
  | Logic
  | Reifiable
  | Reflectable of FStar_Ident.lident
  | Discriminator of FStar_Ident.lident
  | Projector of (FStar_Ident.lident,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2
  | RecordType of (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
  FStar_Pervasives_Native.tuple2
  | RecordConstructor of
  (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
  FStar_Pervasives_Native.tuple2
  | Action of FStar_Ident.lident
  | ExceptionConstructor
  | HasMaskedEffect
  | Effect
  | OnlyName
let uu___is_Assumption: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____3473 -> false
let uu___is_New: qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____3477 -> false
let uu___is_Private: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____3481 -> false
let uu___is_Unfold_for_unification_and_vcgen: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____3485 -> false
let uu___is_Visible_default: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible_default  -> true | uu____3489 -> false
let uu___is_Irreducible: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____3493 -> false
let uu___is_Abstract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____3497 -> false
let uu___is_Inline_for_extraction: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____3501 -> false
let uu___is_NoExtract: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____3505 -> false
let uu___is_Noeq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____3509 -> false
let uu___is_Unopteq: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____3513 -> false
let uu___is_TotalEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____3517 -> false
let uu___is_Logic: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____3521 -> false
let uu___is_Reifiable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____3525 -> false
let uu___is_Reflectable: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable _0 -> true | uu____3530 -> false
let __proj__Reflectable__item___0: qualifier -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Reflectable _0 -> _0
let uu___is_Discriminator: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Discriminator _0 -> true | uu____3542 -> false
let __proj__Discriminator__item___0: qualifier -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Discriminator _0 -> _0
let uu___is_Projector: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____3558 -> false
let __proj__Projector__item___0:
  qualifier ->
    (FStar_Ident.lident,FStar_Ident.ident) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Projector _0 -> _0
let uu___is_RecordType: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | RecordType _0 -> true | uu____3590 -> false
let __proj__RecordType__item___0:
  qualifier ->
    (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | RecordType _0 -> _0
let uu___is_RecordConstructor: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | RecordConstructor _0 -> true | uu____3634 -> false
let __proj__RecordConstructor__item___0:
  qualifier ->
    (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | RecordConstructor _0 -> _0
let uu___is_Action: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Action _0 -> true | uu____3670 -> false
let __proj__Action__item___0: qualifier -> FStar_Ident.lident =
  fun projectee  -> match projectee with | Action _0 -> _0
let uu___is_ExceptionConstructor: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExceptionConstructor  -> true
    | uu____3681 -> false
let uu___is_HasMaskedEffect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | HasMaskedEffect  -> true | uu____3685 -> false
let uu___is_Effect: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect  -> true | uu____3689 -> false
let uu___is_OnlyName: qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | OnlyName  -> true | uu____3693 -> false
type attribute = term
type tycon = (FStar_Ident.lident,binders,typ) FStar_Pervasives_Native.tuple3
type monad_abbrev = {
  mabbrev: FStar_Ident.lident;
  parms: binders;
  def: typ;}
type sub_eff =
  {
  source: FStar_Ident.lident;
  target: FStar_Ident.lident;
  lift_wp: tscheme FStar_Pervasives_Native.option;
  lift: tscheme FStar_Pervasives_Native.option;}
type action =
  {
  action_name: FStar_Ident.lident;
  action_unqualified_name: FStar_Ident.ident;
  action_univs: univ_names;
  action_params: binders;
  action_defn: term;
  action_typ: typ;}
type eff_decl =
  {
  cattributes: cflags Prims.list;
  mname: FStar_Ident.lident;
  univs: univ_names;
  binders: binders;
  signature: term;
  ret_wp: tscheme;
  bind_wp: tscheme;
  if_then_else: tscheme;
  ite_wp: tscheme;
  stronger: tscheme;
  close_wp: tscheme;
  assert_p: tscheme;
  assume_p: tscheme;
  null_wp: tscheme;
  trivial: tscheme;
  repr: term;
  return_repr: tscheme;
  bind_repr: tscheme;
  actions: action Prims.list;}
type sig_metadata =
  {
  sigmeta_active: Prims.bool;
  sigmeta_fact_db_ids: Prims.string Prims.list;}
type sigelt' =
  | Sig_inductive_typ of
  (FStar_Ident.lident,univ_names,binders,typ,FStar_Ident.lident Prims.list,
  FStar_Ident.lident Prims.list) FStar_Pervasives_Native.tuple6
  | Sig_bundle of (sigelt Prims.list,FStar_Ident.lident Prims.list)
  FStar_Pervasives_Native.tuple2
  | Sig_datacon of
  (FStar_Ident.lident,univ_names,typ,FStar_Ident.lident,Prims.int,FStar_Ident.lident
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple6
  | Sig_declare_typ of (FStar_Ident.lident,univ_names,typ)
  FStar_Pervasives_Native.tuple3
  | Sig_let of
  (letbindings,FStar_Ident.lident Prims.list,attribute Prims.list)
  FStar_Pervasives_Native.tuple3
  | Sig_main of term
  | Sig_assume of (FStar_Ident.lident,formula)
  FStar_Pervasives_Native.tuple2
  | Sig_new_effect of eff_decl
  | Sig_new_effect_for_free of eff_decl
  | Sig_sub_effect of sub_eff
  | Sig_effect_abbrev of
  (FStar_Ident.lident,univ_names,binders,comp,cflags Prims.list)
  FStar_Pervasives_Native.tuple5
  | Sig_pragma of pragma
and sigelt =
  {
  sigel: sigelt';
  sigrng: FStar_Range.range;
  sigquals: qualifier Prims.list;
  sigmeta: sig_metadata;}
let uu___is_Sig_inductive_typ: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_inductive_typ _0 -> true | uu____4158 -> false
let __proj__Sig_inductive_typ__item___0:
  sigelt' ->
    (FStar_Ident.lident,univ_names,binders,typ,FStar_Ident.lident Prims.list,
      FStar_Ident.lident Prims.list) FStar_Pervasives_Native.tuple6
  = fun projectee  -> match projectee with | Sig_inductive_typ _0 -> _0
let uu___is_Sig_bundle: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_bundle _0 -> true | uu____4226 -> false
let __proj__Sig_bundle__item___0:
  sigelt' ->
    (sigelt Prims.list,FStar_Ident.lident Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Sig_bundle _0 -> _0
let uu___is_Sig_datacon: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_datacon _0 -> true | uu____4276 -> false
let __proj__Sig_datacon__item___0:
  sigelt' ->
    (FStar_Ident.lident,univ_names,typ,FStar_Ident.lident,Prims.int,FStar_Ident.lident
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple6
  = fun projectee  -> match projectee with | Sig_datacon _0 -> _0
let uu___is_Sig_declare_typ: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_declare_typ _0 -> true | uu____4336 -> false
let __proj__Sig_declare_typ__item___0:
  sigelt' ->
    (FStar_Ident.lident,univ_names,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Sig_declare_typ _0 -> _0
let uu___is_Sig_let: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_let _0 -> true | uu____4376 -> false
let __proj__Sig_let__item___0:
  sigelt' ->
    (letbindings,FStar_Ident.lident Prims.list,attribute Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Sig_let _0 -> _0
let uu___is_Sig_main: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_main _0 -> true | uu____4418 -> false
let __proj__Sig_main__item___0: sigelt' -> term =
  fun projectee  -> match projectee with | Sig_main _0 -> _0
let uu___is_Sig_assume: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_assume _0 -> true | uu____4434 -> false
let __proj__Sig_assume__item___0:
  sigelt' -> (FStar_Ident.lident,formula) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Sig_assume _0 -> _0
let uu___is_Sig_new_effect: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_new_effect _0 -> true | uu____4458 -> false
let __proj__Sig_new_effect__item___0: sigelt' -> eff_decl =
  fun projectee  -> match projectee with | Sig_new_effect _0 -> _0
let uu___is_Sig_new_effect_for_free: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Sig_new_effect_for_free _0 -> true
    | uu____4470 -> false
let __proj__Sig_new_effect_for_free__item___0: sigelt' -> eff_decl =
  fun projectee  -> match projectee with | Sig_new_effect_for_free _0 -> _0
let uu___is_Sig_sub_effect: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_sub_effect _0 -> true | uu____4482 -> false
let __proj__Sig_sub_effect__item___0: sigelt' -> sub_eff =
  fun projectee  -> match projectee with | Sig_sub_effect _0 -> _0
let uu___is_Sig_effect_abbrev: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_effect_abbrev _0 -> true | uu____4506 -> false
let __proj__Sig_effect_abbrev__item___0:
  sigelt' ->
    (FStar_Ident.lident,univ_names,binders,comp,cflags Prims.list)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Sig_effect_abbrev _0 -> _0
let uu___is_Sig_pragma: sigelt' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sig_pragma _0 -> true | uu____4554 -> false
let __proj__Sig_pragma__item___0: sigelt' -> pragma =
  fun projectee  -> match projectee with | Sig_pragma _0 -> _0
type sigelts = sigelt Prims.list
type modul =
  {
  name: FStar_Ident.lident;
  declarations: sigelts;
  exports: sigelts;
  is_interface: Prims.bool;}
type path = Prims.string Prims.list
type subst_t = subst_elt Prims.list
type ('a,'b) mk_t_a =
  'b FStar_Pervasives_Native.option -> FStar_Range.range -> ('a,'b) syntax
type mk_t = (term',term') mk_t_a
let contains_reflectable: qualifier Prims.list -> Prims.bool =
  fun l  ->
    FStar_Util.for_some
      (fun uu___87_4649  ->
         match uu___87_4649 with
         | Reflectable uu____4650 -> true
         | uu____4651 -> false) l
let withinfo v1 s r = { v = v1; ty = s; p = r }
let withsort v1 s = withinfo v1 s FStar_Range.dummyRange
let bv_eq: bv -> bv -> Prims.bool =
  fun bv1  ->
    fun bv2  ->
      ((bv1.ppname).FStar_Ident.idText = (bv2.ppname).FStar_Ident.idText) &&
        (bv1.index = bv2.index)
let order_bv: bv -> bv -> Prims.int =
  fun x  ->
    fun y  ->
      let i =
        FStar_String.compare (x.ppname).FStar_Ident.idText
          (y.ppname).FStar_Ident.idText in
      if i = (Prims.parse_int "0") then x.index - y.index else i
let order_fv: FStar_Ident.lident -> FStar_Ident.lident -> Prims.int =
  fun x  ->
    fun y  -> FStar_String.compare x.FStar_Ident.str y.FStar_Ident.str
let range_of_lbname: lbname -> FStar_Range.range =
  fun l  ->
    match l with
    | FStar_Util.Inl x -> (x.ppname).FStar_Ident.idRange
    | FStar_Util.Inr fv -> FStar_Ident.range_of_lid (fv.fv_name).v
let range_of_bv: bv -> FStar_Range.range =
  fun x  -> (x.ppname).FStar_Ident.idRange
let set_range_of_bv: bv -> FStar_Range.range -> bv =
  fun x  ->
    fun r  ->
      let uu___94_4731 = x in
      {
        ppname = (FStar_Ident.mk_ident (((x.ppname).FStar_Ident.idText), r));
        index = (uu___94_4731.index);
        sort = (uu___94_4731.sort)
      }
let syn p k f = f k p
let mk_fvs uu____4774 = FStar_Util.mk_ref FStar_Pervasives_Native.None
let mk_uvs uu____4788 = FStar_Util.mk_ref FStar_Pervasives_Native.None
let new_bv_set: Prims.unit -> bv FStar_Util.set =
  fun uu____4795  ->
    FStar_Util.new_set order_bv
      (fun x  ->
         x.index + (FStar_Util.hashcode (x.ppname).FStar_Ident.idText))
let new_fv_set: Prims.unit -> FStar_Ident.lident FStar_Util.set =
  fun uu____4803  ->
    FStar_Util.new_set order_fv
      (fun x  -> FStar_Util.hashcode x.FStar_Ident.str)
let new_uv_set:
  Prims.unit ->
    ((term',term') syntax uvar_basis FStar_Unionfind.uvar,(term',term')
                                                            syntax)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun uu____4809  ->
    FStar_Util.new_set
      (fun uu____4826  ->
         fun uu____4827  ->
           match (uu____4826, uu____4827) with
           | ((x,uu____4893),(y,uu____4895)) ->
               let uu____4976 = FStar_Unionfind.uvar_id x in
               let uu____4983 = FStar_Unionfind.uvar_id y in
               uu____4976 - uu____4983)
      (fun uu____4990  ->
         match uu____4990 with | (x,uu____5008) -> FStar_Unionfind.uvar_id x)
let new_universe_uvar_set:
  Prims.unit ->
    universe FStar_Pervasives_Native.option FStar_Unionfind.uvar
      FStar_Util.set
  =
  fun uu____5043  ->
    FStar_Util.new_set
      (fun x  ->
         fun y  ->
           let uu____5060 = FStar_Unionfind.uvar_id x in
           let uu____5063 = FStar_Unionfind.uvar_id y in
           uu____5060 - uu____5063) (fun x  -> FStar_Unionfind.uvar_id x)
let new_universe_names_fifo_set:
  Prims.unit -> FStar_Ident.ident FStar_Util.fifo_set =
  fun uu____5079  ->
    FStar_Util.new_fifo_set
      (fun x  ->
         fun y  ->
           FStar_String.compare (FStar_Ident.text_of_id x)
             (FStar_Ident.text_of_id y))
      (fun x  -> FStar_Util.hashcode (FStar_Ident.text_of_id x))
let no_names: bv FStar_Util.set = new_bv_set ()
let no_fvars: FStar_Ident.lident FStar_Util.set = new_fv_set ()
let no_uvs: uvars = new_uv_set ()
let no_universe_uvars: universe_uvar FStar_Util.set =
  new_universe_uvar_set ()
let no_universe_names: univ_name FStar_Util.fifo_set =
  new_universe_names_fifo_set ()
let empty_free_vars: free_vars =
  {
    free_names = no_names;
    free_uvars = no_uvs;
    free_univs = no_universe_uvars;
    free_univ_names = no_universe_names
  }
let memo_no_uvs: uvars FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref (FStar_Pervasives_Native.Some no_uvs)
let memo_no_names:
  bv FStar_Util.set FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref (FStar_Pervasives_Native.Some no_names)
let freenames_of_list: bv Prims.list -> bv FStar_Util.set =
  fun l  -> FStar_List.fold_right FStar_Util.set_add l no_names
let list_of_freenames: freenames -> bv Prims.list =
  fun fvs  -> FStar_Util.set_elements fvs
let mk t topt r =
  let uu____5156 = FStar_Util.mk_ref topt in
  let uu____5161 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  { n = t; tk = uu____5156; pos = r; vars = uu____5161 }
let bv_to_tm: bv -> (term',term') syntax =
  fun bv  ->
    let uu____5173 = range_of_bv bv in
    mk (Tm_bvar bv) (FStar_Pervasives_Native.Some ((bv.sort).n)) uu____5173
let bv_to_name: bv -> (term',term') syntax =
  fun bv  ->
    let uu____5177 = range_of_bv bv in
    mk (Tm_name bv) (FStar_Pervasives_Native.Some ((bv.sort).n)) uu____5177
let mk_Tm_app:
  typ ->
    arg Prims.list ->
      term' FStar_Pervasives_Native.option ->
        FStar_Range.range -> (term',term') syntax
  =
  fun t1  ->
    fun args  ->
      fun k  ->
        fun p  ->
          match args with
          | [] -> t1
          | uu____5198 -> mk (Tm_app (t1, args)) k p
let mk_Tm_uinst: term -> universes -> term =
  fun t  ->
    fun uu___88_5208  ->
      match uu___88_5208 with
      | [] -> t
      | us ->
          (match t.n with
           | Tm_fvar uu____5210 ->
               mk (Tm_uinst (t, us)) FStar_Pervasives_Native.None t.pos
           | uu____5211 -> failwith "Unexpected universe instantiation")
let extend_app_n:
  term ->
    args ->
      term' FStar_Pervasives_Native.option ->
        FStar_Range.range -> (term',term') syntax
  =
  fun t  ->
    fun args'  ->
      fun kopt  ->
        fun r  ->
          match t.n with
          | Tm_app (head1,args) ->
              mk_Tm_app head1 (FStar_List.append args args') kopt r
          | uu____5268 -> mk_Tm_app t args' kopt r
let extend_app:
  term ->
    arg ->
      term' FStar_Pervasives_Native.option ->
        FStar_Range.range -> (term',term') syntax
  = fun t  -> fun arg  -> fun kopt  -> fun r  -> extend_app_n t [arg] kopt r
let mk_Tm_delayed:
  ((term,subst_ts) FStar_Pervasives_Native.tuple2,Prims.unit -> term)
    FStar_Util.either -> FStar_Range.range -> (term',term') syntax
  =
  fun lr  ->
    fun pos  ->
      let uu____5310 =
        let uu____5315 =
          let uu____5316 =
            let uu____5355 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
            (lr, uu____5355) in
          Tm_delayed uu____5316 in
        mk uu____5315 in
      uu____5310 FStar_Pervasives_Native.None pos
let mk_Total':
  typ -> universe FStar_Pervasives_Native.option -> (comp',Prims.unit) syntax
  = fun t  -> fun u  -> mk (Total (t, u)) FStar_Pervasives_Native.None t.pos
let mk_GTotal':
  typ -> universe FStar_Pervasives_Native.option -> (comp',Prims.unit) syntax
  = fun t  -> fun u  -> mk (GTotal (t, u)) FStar_Pervasives_Native.None t.pos
let mk_Total: typ -> comp =
  fun t  -> mk_Total' t FStar_Pervasives_Native.None
let mk_GTotal: typ -> comp =
  fun t  -> mk_GTotal' t FStar_Pervasives_Native.None
let mk_Comp: comp_typ -> (comp',Prims.unit) syntax =
  fun ct  -> mk (Comp ct) FStar_Pervasives_Native.None (ct.result_typ).pos
let mk_lb:
  (lbname,univ_name Prims.list,FStar_Ident.lident,typ,term)
    FStar_Pervasives_Native.tuple5 -> letbinding
  =
  fun uu____5445  ->
    match uu____5445 with
    | (x,univs,eff,t,e) ->
        { lbname = x; lbunivs = univs; lbtyp = t; lbeff = eff; lbdef = e }
let default_sigmeta: sig_metadata =
  { sigmeta_active = true; sigmeta_fact_db_ids = [] }
let mk_sigelt: sigelt' -> sigelt =
  fun e  ->
    {
      sigel = e;
      sigrng = FStar_Range.dummyRange;
      sigquals = [];
      sigmeta = default_sigmeta
    }
let mk_subst: subst_t -> subst_t = fun s  -> s
let extend_subst: subst_elt -> subst_elt Prims.list -> subst_elt Prims.list =
  fun x  -> fun s  -> x :: s
let argpos: arg -> FStar_Range.range =
  fun x  -> (FStar_Pervasives_Native.fst x).pos
let tun: (term',term') syntax =
  mk Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange
let teff: (term',term') syntax =
  mk (Tm_constant FStar_Const.Const_effect)
    (FStar_Pervasives_Native.Some Tm_unknown) FStar_Range.dummyRange
let is_teff: term -> Prims.bool =
  fun t  ->
    match t.n with
    | Tm_constant (FStar_Const.Const_effect ) -> true
    | uu____5501 -> false
let is_type: term -> Prims.bool =
  fun t  -> match t.n with | Tm_type uu____5505 -> true | uu____5506 -> false
let null_id: FStar_Ident.ident =
  FStar_Ident.mk_ident ("_", FStar_Range.dummyRange)
let null_bv: term -> bv =
  fun k  -> { ppname = null_id; index = (Prims.parse_int "0"); sort = k }
let mk_binder:
  bv ->
    (bv,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun a  -> (a, FStar_Pervasives_Native.None)
let null_binder:
  term ->
    (bv,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____5518 = null_bv t in (uu____5518, FStar_Pervasives_Native.None)
let imp_tag: arg_qualifier = Implicit false
let iarg:
  term ->
    (term,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun t  -> (t, (FStar_Pervasives_Native.Some imp_tag))
let as_arg:
  term ->
    (term,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun t  -> (t, FStar_Pervasives_Native.None)
let is_null_bv: bv -> Prims.bool =
  fun b  -> (b.ppname).FStar_Ident.idText = null_id.FStar_Ident.idText
let is_null_binder: binder -> Prims.bool =
  fun b  -> is_null_bv (FStar_Pervasives_Native.fst b)
let is_top_level: letbinding Prims.list -> Prims.bool =
  fun uu___89_5541  ->
    match uu___89_5541 with
    | { lbname = FStar_Util.Inr uu____5544; lbunivs = uu____5545;
        lbtyp = uu____5546; lbeff = uu____5547; lbdef = uu____5548;_}::uu____5549
        -> true
    | uu____5562 -> false
let freenames_of_binders: binders -> bv FStar_Util.set =
  fun bs  ->
    FStar_List.fold_right
      (fun uu____5574  ->
         fun out  ->
           match uu____5574 with | (x,uu____5585) -> FStar_Util.set_add x out)
      bs no_names
let binders_of_list:
  bv Prims.list ->
    (bv,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fvs  ->
    FStar_All.pipe_right fvs
      (FStar_List.map (fun t  -> (t, FStar_Pervasives_Native.None)))
let binders_of_freenames: freenames -> binders =
  fun fvs  ->
    let uu____5615 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____5615 binders_of_list
let is_implicit: aqual -> Prims.bool =
  fun uu___90_5622  ->
    match uu___90_5622 with
    | FStar_Pervasives_Native.Some (Implicit uu____5623) -> true
    | uu____5624 -> false
let as_implicit: Prims.bool -> arg_qualifier FStar_Pervasives_Native.option =
  fun uu___91_5627  ->
    if uu___91_5627
    then FStar_Pervasives_Native.Some imp_tag
    else FStar_Pervasives_Native.None
let pat_bvs: pat -> bv Prims.list =
  fun p  ->
    let rec aux b p1 =
      match p1.v with
      | Pat_dot_term uu____5659 -> b
      | Pat_constant uu____5668 -> b
      | Pat_wild x -> x :: b
      | Pat_var x -> x :: b
      | Pat_cons (uu____5671,pats) ->
          FStar_List.fold_left
            (fun b1  ->
               fun uu____5704  ->
                 match uu____5704 with | (p2,uu____5718) -> aux b1 p2) b pats in
    let uu____5727 = aux [] p in
    FStar_All.pipe_left FStar_List.rev uu____5727
let gen_reset:
  (Prims.unit -> Prims.int,Prims.unit -> Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let x = FStar_Util.mk_ref (Prims.parse_int "0") in
  let gen1 uu____5748 = FStar_Util.incr x; FStar_ST.read x in
  let reset uu____5758 = FStar_ST.write x (Prims.parse_int "0") in
  (gen1, reset)
let next_id: Prims.unit -> Prims.int = FStar_Pervasives_Native.fst gen_reset
let reset_gensym: Prims.unit -> Prims.unit =
  FStar_Pervasives_Native.snd gen_reset
let range_of_ropt:
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Range.range =
  fun uu___92_5781  ->
    match uu___92_5781 with
    | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange
    | FStar_Pervasives_Native.Some r -> r
let gen_bv:
  Prims.string ->
    FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv
  =
  fun s  ->
    fun r  ->
      fun t  ->
        let id = FStar_Ident.mk_ident (s, (range_of_ropt r)) in
        let uu____5799 = next_id () in
        { ppname = id; index = uu____5799; sort = t }
let new_bv: FStar_Range.range FStar_Pervasives_Native.option -> typ -> bv =
  fun ropt  -> fun t  -> gen_bv FStar_Ident.reserved_prefix ropt t
let freshen_bv: bv -> bv =
  fun bv  ->
    let uu____5813 = is_null_bv bv in
    if uu____5813
    then
      let uu____5814 =
        let uu____5817 = range_of_bv bv in
        FStar_Pervasives_Native.Some uu____5817 in
      new_bv uu____5814 bv.sort
    else
      (let uu___95_5819 = bv in
       let uu____5820 = next_id () in
       {
         ppname = (uu___95_5819.ppname);
         index = uu____5820;
         sort = (uu___95_5819.sort)
       })
let new_univ_name:
  FStar_Range.range FStar_Pervasives_Native.option -> FStar_Ident.ident =
  fun ropt  ->
    let id = next_id () in
    let uu____5829 =
      let uu____5834 =
        let uu____5835 = FStar_Util.string_of_int id in
        Prims.strcat FStar_Ident.reserved_prefix uu____5835 in
      (uu____5834, (range_of_ropt ropt)) in
    FStar_Ident.mk_ident uu____5829
let mkbv: FStar_Ident.ident -> Prims.int -> (term',term') syntax -> bv =
  fun x  -> fun y  -> fun t  -> { ppname = x; index = y; sort = t }
let lbname_eq:
  (bv,FStar_Ident.lident) FStar_Util.either ->
    (bv,FStar_Ident.lident) FStar_Util.either -> Prims.bool
  =
  fun l1  ->
    fun l2  ->
      match (l1, l2) with
      | (FStar_Util.Inl x,FStar_Util.Inl y) -> bv_eq x y
      | (FStar_Util.Inr l,FStar_Util.Inr m) -> FStar_Ident.lid_equals l m
      | uu____5903 -> false
let fv_eq: fv -> fv -> Prims.bool =
  fun fv1  ->
    fun fv2  -> FStar_Ident.lid_equals (fv1.fv_name).v (fv2.fv_name).v
let fv_eq_lid: fv -> FStar_Ident.lident -> Prims.bool =
  fun fv  -> fun lid  -> FStar_Ident.lid_equals (fv.fv_name).v lid
let set_bv_range: bv -> FStar_Range.range -> bv =
  fun bv  ->
    fun r  ->
      let uu___96_5946 = bv in
      {
        ppname = (FStar_Ident.mk_ident (((bv.ppname).FStar_Ident.idText), r));
        index = (uu___96_5946.index);
        sort = (uu___96_5946.sort)
      }
let lid_as_fv:
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> fv
  =
  fun l  ->
    fun dd  ->
      fun dq  ->
        let uu____5960 = withinfo l tun (FStar_Ident.range_of_lid l) in
        { fv_name = uu____5960; fv_delta = dd; fv_qual = dq }
let fv_to_tm: fv -> (term',term') syntax =
  fun fv  ->
    mk (Tm_fvar fv) FStar_Pervasives_Native.None
      (FStar_Ident.range_of_lid (fv.fv_name).v)
let fvar:
  FStar_Ident.lident ->
    delta_depth -> fv_qual FStar_Pervasives_Native.option -> term
  =
  fun l  ->
    fun dd  ->
      fun dq  -> let uu____5994 = lid_as_fv l dd dq in fv_to_tm uu____5994
let lid_of_fv: fv -> FStar_Ident.lident = fun fv  -> (fv.fv_name).v
let range_of_fv: fv -> FStar_Range.range =
  fun fv  ->
    let uu____6005 = lid_of_fv fv in FStar_Ident.range_of_lid uu____6005
let set_range_of_fv: fv -> FStar_Range.range -> fv =
  fun fv  ->
    fun r  ->
      let uu___97_6012 = fv in
      let uu____6013 =
        let uu___98_6020 = fv.fv_name in
        let uu____6027 =
          let uu____6028 = lid_of_fv fv in
          FStar_Ident.set_lid_range uu____6028 r in
        { v = uu____6027; ty = (uu___98_6020.ty); p = (uu___98_6020.p) } in
      {
        fv_name = uu____6013;
        fv_delta = (uu___97_6012.fv_delta);
        fv_qual = (uu___97_6012.fv_qual)
      }
let has_simple_attribute: term Prims.list -> Prims.string -> Prims.bool =
  fun l  ->
    fun s  ->
      FStar_List.existsb
        (fun uu___93_6062  ->
           match uu___93_6062 with
           | { n = Tm_constant (FStar_Const.Const_string (data,uu____6068));
               tk = uu____6069; pos = uu____6070; vars = uu____6071;_} when
               (FStar_Util.string_of_unicode data) = s -> true
           | uu____6080 -> false) l